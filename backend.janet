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

# JS code is generated as a tree of strings which is ultimately flattened.
# <js> ::= string | [<js>*]

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
# - :node-definition symbol ↦ <js>

(def- Translator @{
  :ssa-node (fn [self v]
    (assert (symbol? v))
    (pat/match ((self :inline-node?) v)
      true  (assert ((self :node-definition) v))
      false (string v) ))

  :ssa-val (fn [self v]
    (assert (ssa/value? v))
    (pat/match (:resolve-name (self :ssa) v)
      (or |int? |boolean?) (string v)
      |symbol?             (:ssa-node self v)
      :empty               "[]"
      |keyword?            (string/format "a%s" v) )) # parameters

  :ssa-truthy? (fn [self vv]
    (assert (ssa/value? vv))
    (def v (:resolve-name (self :ssa) vv))
    (def opcode (if (symbol? v) (get-in self [:ssa :occurrences v 1 1])))
    (def is-already-a-boolean?
      (pat/match [v opcode]
        [true _] true
        [false _] true
        [_ (or 'lt 'neq)] true
        _ false))
    (if is-already-a-boolean?
      (:ssa-val self v)
      ["truthy(" (:ssa-val self v) ")"] ))

  :ssa-args (fn [self vv]
    (assert (ssa/value? vv))
    (def v (:resolve-name (self :ssa) vv))
    (def inline? (and (symbol? v) ((self :inline-node?) v)))
    (def definition (if inline? (get-in self [:ssa :occurrences v 1])))
    (pat/match [v definition]
      [:empty _]
        ""
      [_ [_ 'push [v1 v2] nil]]
        (let [v1-code (:ssa-args self v1)
              v2-code (:ssa-val self v2)]
          (if (= v1-code "") v2-code [v1-code ", " v2-code]) )
      # else
        ["..." (:ssa-val self v)] ))
})

# A barrier is a function which decides whether a piece of code
# can be reordered across part of a schedule.
# <barrier> ::= fn [schedule-entry] → bool

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
#   :emit  fn [Translator] → <js>
# }
# A plan can also be extended with two fields which describe
# <extended-plan> ::= <plan> & {
#   :max-occurrences  int | nil
#   :barrier          <barrier>
# }

(defn plan/concat [p1 p2]
  { :sch  (schedule/concat (p1 :sch) (p2 :sch))
    :emit |[((p1 :emit) $) ((p2 :emit) $)] })

(def plan/empty
  { :sch nil
    :emit (fn [_] []) })

(defn plan/if-else [v plan1 plan2]
  (def regs (merge (schedule/used-regs (plan1 :sch))
                   (if-not plan2 {} (schedule/used-regs (plan2 :sch))) ))
  { :sch  (schedule/concat (schedule/value v) [['opaque regs] nil])
    :emit |["if (" (:ssa-truthy? $ v) ") { "
            ((plan1 :emit) $)
            " }"
            (if-not plan2 []
              [" else { "
               ((plan2 :emit) $)
               " }"]) ]})

(defn plan/infinite-loop [lbl body-plan]
  (def regs (schedule/used-regs (body-plan :sch)))
  { :sch  [['opaque regs] nil]
    :emit |[(tx-label lbl) ": for (;;) { " ((body-plan :emit) $) " }"] })

(defn plan/do-while-false [lbl body-plan]
  (def regs (schedule/used-regs (body-plan :sch)))
  { :sch  [['opaque regs] nil]
    :emit |[(tx-label lbl) ": do { " ((body-plan :emit) $) " } while (false);"] })

(defn plan/upsilon [v r]
  { :sch             (schedule/concat (schedule/value v) [['ups r] nil])
    :emit            |[(tx-register r) " = " (:ssa-val $ v) ";"] })

(defn plan/phi [r]
  { :max-occurrences nil # phis can be inlined even if used more than once
    :barrier         (barrier/assigns-reg? r)
    :sch             [['phi r] nil]
    :emit            (fn [_] (tx-register r)) })

(defn plan/pure-expr [vs emit]
  { :max-occurrences 1
    :barrier         barrier/none
    :sch             (fold-right |(schedule/concat (schedule/value $0) $1) nil vs)
    :emit            emit })

(defn plan/pure-call [f-name & vs]
  (plan/pure-expr vs (fn [tx]
                       [f-name "(" (interpose "," (map |(:ssa-val tx $) vs)) ")"] ) ))

(defn plan/impure-expr [vs emit]
  { :max-occurrences 1
    :barrier         barrier/side-effect?
    :sch             (fold-right |(schedule/concat (schedule/value $0) $1)
                                 [['side-effect] nil] vs)
    :emit            emit })

(defn plan/impure-call [f-name & vs]
  (plan/impure-expr vs (fn [tx]
                         [f-name "(" (interpose "," (map |(:ssa-val tx $) vs)) ")"]) ))

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
    # have to emit any extra code for its definition up front
    { :sch  (schedule/substitute-uses (cont-plan :sch) output-name (rhs-xplan :sch))
      :emit (fn [tx]
              (put (tx :node-definition) output-name ((rhs-xplan :emit) tx))
              ((cont-plan :emit) tx) )
    }
    # if we don't inline it, then we do compute its definition
    # up front, and the schedule needs to reflect this
    { :sch  (schedule/concat (rhs-xplan :sch) (cont-plan :sch))
      :emit (fn [tx]
              ["let " (:ssa-node tx output-name) " = " ((rhs-xplan :emit) tx) ";"
               ((cont-plan :emit) tx) ])
    }))

(defn to-javascript [ssa top-level-cf]
  # `tx-insn` and `tx-control-flow` return a plan. The plan's emit function
  # can only be called after `inlining-decisions` is completely populated,
  # and returns the compiled JS.

  (def inline-node? @{})
  (defn tx-insn [insn kont]
    (defn statement [stmt-plan] (plan/concat stmt-plan kont))
    (defn assign-name [o rhs-xplan] (plan/assign-name ssa inline-node? o rhs-xplan kont))
    (pat/match insn
      [nil 'ups [v] r]      (statement (plan/upsilon v r))
      [o 'phi [] r]         (assign-name o (plan/phi r))
      [o 'ldc [] i]         (assign-name o (plan/pure-expr [] (fn [_] ["ldc(" (string i) ")"])))
      [o 'mktab [] nil]     (assign-name o (plan/impure-expr [] (fn [_] "new Map()")))
      [o 'mkstu [args] nil] (assign-name o (plan/impure-call "mkstu" args)) # mkstu() can error
      [o 'len [v] nil]      (assign-name o (plan/impure-call "len" v)) # length() can error
      [o 'addim [v] x]      (assign-name o (plan/impure-expr [v]
                              |["add(" (:ssa-val $ v) ", " (string x) ")"] ))
      [o 'sub [v1 v2] nil]  (assign-name o (plan/impure-call "sub" v1 v2)) # sub() can ereror
      [o 'lt [v1 v2] nil]   (assign-name o (plan/pure-call "lt" v1 v2))
      [o 'neq [v1 v2] nil]  (assign-name o (plan/pure-call "neq" v1 v2))
      [o 'get [v1 v2] nil]  (assign-name o (plan/impure-call "get" v1 v2)) # get() can error
      [nil 'put [v1 v2 v3] nil]
                            (statement (plan/impure-expr [v1 v2 v3]
                              |["put(" (:ssa-val $ v1) ", " (:ssa-val $ v2) ", " (:ssa-val $ v3) ");"] ))
      [o 'push [args v] nil]
                            # :max-occurrences is 1 here, but it shouldn't be possible for a
                            # push() to have multiple occurrences anyway
                            (assign-name o (plan/pure-expr [args v]
                              |["[" (:ssa-args $ args) ", " (:ssa-val $ v) "]"] ))
      [o 'call [args f] nil]
                            (assign-name o (plan/impure-expr [f args]
                              |[(:ssa-val $ f) "(" (:ssa-args $ args) ")"] ))
      # else
        # (string/format "/* unhandled insn: %q */" insn)
        (errorf "unhandled insn: %Q" insn) ))

  (defn tx-control-flow [cf]
    (pat/match cf
      []
        plan/empty
      [[(or 'loop-break 'block-break) lbl]]
        { :sch nil :emit (fn [_] ["break " (tx-label lbl) ";"]) }
      [['loop-continue lbl]]
        { :sch nil :emit (fn [_] ["continue " (tx-label lbl) ";"]) }
      [['tcall args f]]
        { :sch  (schedule/concat (schedule/value f) (schedule/value args))
          :emit |["return " (:ssa-val $ f) "(" (:ssa-args $ args) ");"] }
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

  (def tx (table/setproto @{:ssa ssa :inline-node? inline-node? :node-definition @{}} Translator))
  (def js ((top-level-plan :emit) tx))
  (put ssa :inlining-decisions inline-node?)
  (string/join
    (flatten
      [(if (empty? declared-local-vars)
         []
         ["let " (interpose "," declared-local-vars) ";\n"])
       js])))
