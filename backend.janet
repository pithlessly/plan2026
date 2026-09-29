(import pat)
(import ./utils :prefix "")
(import ./ssa)

# The scheduling algorithm determines whether an SSA variable can be inlined at
# its use sites, or whether it must be lowered to an assignment.
# A *schedule* is a data structure summarizing the effects associated with a
# piece of JS code. Schedules are built in reverse (from the end to the
# beginning of the control flow tree), can can be constructed before, but in
# anticipation of, the actual emitted JS code.
# Along with occurrence analysis, the schedule can be used to implement a
# conservative approximation of inline safety. The definition of a schedule is
# subject to change, but for now it looks like:

# <schedule> ::= nil | [<schedule-entry> <schedule>]
# <schedule-entry> ::= ['use <ssa-node>]
#                    | ['phi <register>]
#                    | ['ups <register>]
#                    | ['opaque <set of registers>]
#                    | ['side-effect]

(defn- schedule/used-regs [schedule]
  (def result @{})
  (var sch schedule)
  (while (not (nil? sch))
    (def [entry kont] sch)
    (set sch kont)
    (pat/match entry
      [(or 'phi 'ups) r]  (put result r true)
      ['opaque rs]        (merge-into result rs)
      (or ['use _]
          ['side-effect]) nil) )
  result)

(defn- schedule/concat [sch1 sch2]
  (pat/match sch1
    nil sch2
    [entry1 sch1-rest] [entry1 (schedule/concat sch1-rest sch2)] ))

(defn- schedule/value [v]
  (assert (ssa/value? v))
  (pat/match v
    |symbol?                       [['use v] nil]
    (or |int? |keyword? |boolean?) nil))

(defn- schedule/count-uses [sch v]
  (assert (symbol? v))
  (pat/match sch
    nil 0
    [stmt cont]
      (+ (schedule/count-uses cont v)
         (pat/match stmt
           ['use (= v)] 1
           _            0))))

(defn- schedule/uses-value-inlineably? [sch is-reordering-barrier? v]
  (assert (symbol? v))
  (pat/match sch
    nil
      true
    [|is-reordering-barrier? cont]
      (= 0 (schedule/count-uses sch v))
    [_ cont]
      (schedule/uses-value-inlineably? cont is-reordering-barrier? v) ))

(defn- schedule/substitute-uses [sch v new-sch]
  (pat/match sch
    nil nil
    [stmt (map |(schedule/substitute-uses $ v new-sch) tail)]
      (pat/match stmt
        ['use (= v)] (schedule/concat new-sch tail)
        _            [stmt tail] )))

# JS code is generated in an intermediate form, called script.
# Converting script to actual JS consists of replacing variables
# with their definitions if they are marked as to be inlined,
# making a few other substitutions based on the nature of these values,
# and then flattening.
# <script> ::= string
#           | [:name <ssa-name>]
#           | [:val <ssa-name>]
#           | [:truthy? <ssa-name>]
#           | [:args <ssa-name>]
#           | [:put-def <ssa-name> <script>]
#           | [<script>*]

(defn- tx-label [lbl]
  (assert (int? lbl))
  (string/format "b%d" lbl) )

(defn- tx-register [r]
  (assert (ssa/register? r))
  (pat/match r
    :args-stack "args"
    |int?       (string/format "r%d" r) ))

# Collates some common context for JS code generation.
# Fields:
# - :ssa             SsaFunction
# - :inline-node?    symbol ↦ bool
# - :node-definition symbol ↦ <script>

# A barrier is a function which decides whether a piece of code
# can be reordered across part of a schedule.
# <barrier> ::= fn [<schedule-entry>] → bool

(defn barrier/assigns-reg? [r]
  |(pat/match $ ['ups (= r)] true
                ['opaque s]  (s r)
                _            false))
(defn barrier/side-effect? [entry]
  (pat/match entry ['side-effect] true
                   ['opaque _]    true
                   _              false))
(defn barrier/none [_] false)

# A *plan* is a function that performs code generation along with a summary
# in the form of a schedule.
# <plan> ::= {
#   :sch   <schedule>
#   :code  <script>
# }
# A plan can also be extended with two fields which describe
# <extended-plan> ::= <plan> & {
#   :max-occurrences  int | nil
#   :barrier          <barrier>
# }

(defn plan/concat [p1 p2]
  { :sch  (schedule/concat (p1 :sch) (p2 :sch))
    :code [(p1 :code) (p2 :code)] })

(def plan/empty
  { :sch nil
    :code [] })

(defn plan/if-else [v plan1 plan2]
  (def regs (merge (schedule/used-regs (plan1 :sch))
                   (if-not plan2 {} (schedule/used-regs (plan2 :sch))) ))
  { :sch  (schedule/concat (schedule/value v) [['opaque regs] nil])
    :code ["if (" [:truthy? v] ") { "
           (plan1 :code)
           " }"
           (if-not plan2 []
             [" else { "
              (plan2 :code)
              " }"]) ]})

(defn plan/infinite-loop [lbl body-plan]
  (def regs (schedule/used-regs (body-plan :sch)))
  { :sch  [['opaque regs] nil]
    :code [(tx-label lbl) ": for (;;) { " (body-plan :code) " }"] })

(defn plan/do-while-false [lbl body-plan]
  (def regs (schedule/used-regs (body-plan :sch)))
  { :sch  [['opaque regs] nil]
    :code [(tx-label lbl) ": do { " (body-plan :code) " } while (false);"] })

(defn plan/upsilon [v r]
  { :sch             (schedule/concat (schedule/value v) [['ups r] nil])
    :code            [(tx-register r) " = " [:val v] ";"] })

(defn plan/phi [r]
  { :max-occurrences nil # phis can be inlined even if used more than once
    :barrier         (barrier/assigns-reg? r)
    :sch             [['phi r] nil]
    :code            (tx-register r) })

(defn plan/pure-expr [vs code]
  { :max-occurrences 1
    :barrier         barrier/none
    :sch             (fold-right |(schedule/concat (schedule/value $0) $1) nil vs)
    :code            code })

(defn plan/pure-call [f-name & vs]
  (plan/pure-expr vs [f-name "(" (interpose "," (map |[:val $] vs)) ")"]) )

(defn plan/impure-expr [vs code]
  { :max-occurrences 1
    :barrier         barrier/side-effect?
    :sch             (fold-right |(schedule/concat (schedule/value $0) $1)
                                 [['side-effect] nil] vs)
    :code            code })

(defn plan/impure-call [f-name & vs]
  (plan/impure-expr vs [f-name "(" (interpose "," (map |[:val $] vs)) ")"]) )

(defn plan/assign-name [ssa inline-node? output-name rhs-xplan cont-plan]
  (assert (symbol? output-name))
  (def max-occurrences rhs-xplan)
  (def occurrences (((ssa :occurrences) output-name) 2))
  (def do-inline?
    (and # there must not be too many occurrences
         (if max-occurrences (<= occurrences max-occurrences) true)
         # we must be able to find all the occurrences in the tail schedule
         (= occurrences (schedule/count-uses (cont-plan :sch) output-name))
         # and these occurrences must not occur after a barrier in the schedule
         (schedule/uses-value-inlineably? (cont-plan :sch) (rhs-xplan :barrier) output-name) ))
  (put inline-node? output-name do-inline?)
  (if do-inline?
    # we marked that this node will be inlined, so we don't
    # have to emit a let binding
    { :sch  (schedule/substitute-uses (cont-plan :sch) output-name (rhs-xplan :sch))
      :code [[:put-def output-name (rhs-xplan :code)] (cont-plan :code)]
    }
    # if we don't inline it, then we do compute its definition
    # up front, and the schedule needs to reflect this
    { :sch  (schedule/concat (rhs-xplan :sch) (cont-plan :sch))
      :code ["let " [:name output-name] " = " (rhs-xplan :code) ";" (cont-plan :code)]
    }))

# Collects some state involved in lowering from script to actual JS code.

(def- Translator {
  :ssa-node (fn ssa-node [self v]
    (assert (symbol? v))
    (def v (:resolve-name (self :ssa) v))
    (pat/match ((self :inline-node?) v)
      true  (assert ((self :node-definition) v))
      false (string v) ))

  :ssa-val (fn ssa-val [self v]
    (assert (ssa/value? v))
    (pat/match (:resolve-name (self :ssa) v)
      (or |int? |boolean?) (string v)
      |symbol?             (:ssa-node self v)
      :empty               "[]"
      :nil                 "undefined"
      |keyword?            (string/format "a%s" v) )) # parameters

  :ssa-truthy? (fn ssa-truthy? [self v]
    (assert (ssa/value? v))
    (def v (:resolve-name (self :ssa) v))
    (def is-already-a-boolean?
      (pat/match v
        true     true
        false    true
        :nil     true
        |symbol? (:boolean? (:definition (self :ssa) v))
        _        false))
    (if is-already-a-boolean?
      (:ssa-val self v)
      ["truthy(" (:ssa-val self v) ")"] ))

  :ssa-args (fn ssa-args [self v]
    (assert (ssa/value? v))
    (def v (:resolve-name (self :ssa) v))
    (def inline? (and (symbol? v) ((self :inline-node?) v)))
    (def definition (if inline? (:destruct (:definition (self :ssa) v))))
    (pat/match [v definition]
      [:empty _]
        ""
      [_ [_ 'push [v1 v2] nil]]
        (let [v1-code (:ssa-args self v1)
              v2-code (:ssa-val self v2)]
          (if (= v1-code "") v2-code [v1-code ", " v2-code]) )
      # else
        ["..." (:ssa-val self v)] ))

  :script (fn script [self script]
    (pat/match script
      |string?       script
      [:name v]      (:ssa-node self v)
      [:val v]       (:ssa-val self v)
      [:truthy? v]   (:ssa-truthy? self v)
      [:args v]      (:ssa-args self v)
      [:put-def o s] (do (put (self :node-definition) o (:script self s)) [])
      |indexed?      (map |(:script self $) script) ))
})

(defn new-translator [ssa inline-node?]
  (struct/with-proto Translator
    :ssa ssa :inline-node? inline-node? :node-definition @{} ))

(defn to-javascript [ssa top-level-cf]
  (def inline-node? @{})
  (defn tx-insn [insn kont]
    (defn statement [stmt-plan] (plan/concat stmt-plan kont))
    (defn assign-name [o rhs-xplan] (plan/assign-name ssa inline-node? o rhs-xplan kont))
    (pat/match (:destruct insn)
      [nil 'ups [v] r]      (statement (plan/upsilon v r))
      [o 'phi [] r]         (assign-name o (plan/phi r))
      [o 'ldc [] i]         (assign-name o (plan/pure-expr [] ["ldc(" (string i) ")"]))
      [o 'mktab [] nil]     (assign-name o (plan/impure-expr [] "new Map()"))
      [o 'mkstu [args] nil] (assign-name o (plan/impure-call "mkstu" args)) # mkstu() can error
      [o 'len [v] nil]      (assign-name o (plan/impure-call "len" v)) # length() can error
      [o 'addim [v] x]      (assign-name o (plan/impure-expr [v]
                              ["add(" [:val v] ", " (string x) ")"] ))
      [o 'add [v1 v2] nil]  (assign-name o (plan/impure-call "add" v1 v2)) # add() can error
      [o 'sub [v1 v2] nil]  (assign-name o (plan/impure-call "sub" v1 v2)) # sub() can error
      [o 'lt [v1 v2] nil]   (assign-name o (plan/pure-call "lt" v1 v2))
      [o 'neq [v1 v2] nil]  (assign-name o (plan/pure-call "neq" v1 v2))
      [o 'get [v1 v2] nil]  (assign-name o (plan/impure-call "get" v1 v2)) # get() can error
      [o 'geti [v] i]       (assign-name o (plan/impure-expr [v]           # get() can error
                              ["get(" [:val v] ", " (string i) ")"] ))
      [nil 'put [v1 v2 v3] nil]
                            (statement (plan/impure-expr [v1 v2 v3]
                              ["put(" [:val v1] ", " [:val v2] ", " [:val v3] ");"] ))
      [o 'push [args v] nil]
                            # :max-occurrences is 1 here, but it shouldn't be possible for a
                            # push() to have multiple occurrences anyway
                            (assign-name o (plan/pure-expr [args v]
                              ["[" [:args args] ", " [:val v] "]"] ))
      [o 'call [args f] nil]
                            (assign-name o (plan/impure-expr [f args]
                              [[:val f] "(" [:args args] ")"] ))
      # else
        # (string/format "/* unhandled insn: %q */" insn)
        (errorf "unhandled insn: %Q" insn) ))

  (defn tx-control-flow [cf]
    (pat/match cf
      []
        plan/empty
      [[(or 'loop-break 'block-break) lbl]]
        { :sch nil :code ["break " (tx-label lbl) ";"] }
      [['loop-continue lbl]]
        { :sch nil :code ["continue " (tx-label lbl) ";"] }
      [['tcall args f]]
        { :sch  (schedule/concat (schedule/value f) (schedule/value args))
          :code ["return " [:val f] "(" [:args args] ");"] }
      [['ret x]]
        { :sch  (schedule/value x)
          :code ["return " [:val x] ";"] }
      [stmt & rest]
        (let [rest-plan (tx-control-flow rest) [rest-sch rest-code] (tx-control-flow rest)]
          (pat/match stmt
            ['if v cf1 cf2]
              (plan/concat (plan/if-else v (tx-control-flow cf1)
                                           (if-not (empty? cf2) (tx-control-flow cf2)) )
                           rest-plan)
            ['loop lbl & body]
              (plan/concat (plan/infinite-loop lbl (tx-control-flow body)) rest-plan)
            ['block lbl & body]
              (plan/concat (plan/do-while-false lbl (tx-control-flow body)) rest-plan)
            ['do & insns]
              (fold-right tx-insn rest-plan insns) ))))

  (def top-level-plan (tx-control-flow top-level-cf))
  (def declared-local-vars (map tx-register (sort (keys (ssa :all-phi-regs)))))

  (def tx (new-translator ssa inline-node?))
  (def js (:script tx (top-level-plan :code)))
  (put ssa :inlining-decisions inline-node?)
  (string/join
    (flatten
      [(if (empty? declared-local-vars)
         []
         ["let " (interpose "," declared-local-vars) ";\n"])
       js])))
