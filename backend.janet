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

(defn schedule/used-regs [schedule]
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

(defn schedule/concat [sch1 sch2]
  (pat/match sch1
    nil sch2
    [entry1 sch1-rest] [entry1 (schedule/concat sch1-rest sch2)] ))

(defn schedule/value [v]
  (assert (ssa/value? v))
  (pat/match v
    |symbol?                       [['use v] nil]
    (or |int? |keyword? |boolean?) nil))

(defn schedule/count-uses [sch v]
  (assert (symbol? v))
  (pat/match sch
    nil 0
    [stmt cont]
      (+ (schedule/count-uses cont v)
         (pat/match stmt
           ['use (= v)] 1
           _            0))))

(defn schedule/uses-value-inlineably? [sch is-reordering-barrier? v]
  (assert (symbol? v))
  (pat/match sch
    nil
      true
    [|is-reordering-barrier? cont]
      (= 0 (schedule/count-uses sch v))
    [_ cont]
      (schedule/uses-value-inlineably? cont is-reordering-barrier? v) ))

(defn schedule/substitute-uses [sch v new-sch]
  (pat/match sch
    nil nil
    [stmt (map |(schedule/substitute-uses $ v new-sch) tail)]
      (pat/match stmt
        ['use (= v)] (schedule/concat new-sch tail)
        _            [stmt tail] )))

(defn to-javascript [ssa top-level-cf]
  (defn tx-label [lbl]
    (assert (int? lbl))
    (string/format "b%d" lbl) )
  (defn tx-register [r]
    (assert (ssa/register? r))
    (pat/match r
      :args-stack "args"
      |int?       (string/format "r%d" r) ))
  (def inline-node? @{})    # ssa-node ↦ bool       (populated in 1st phase)
  (def node-definition @{}) # ssa-node ↦ definition (populated in 2nd phase)
  (defn tx-ssa-node [v]
    (assert (symbol? v))
    (pat/match (inline-node? v)
      true  (assert (node-definition v))
      false (string v) ))
  (defn tx-ssa-val [v]
    (assert (ssa/value? v))
    (pat/match (:resolve-name ssa v)
      (or |int? |boolean?) (string v)
      |symbol?             (tx-ssa-node v)
      :empty               "[]"
      |keyword?            (string/format "a%s" v) )) # parameters
  (defn tx-ssa-truthy [vv]
    (def v (:resolve-name ssa vv))
    (assert (ssa/value? v))
    (def opcode (if (symbol? v) (get-in ssa [:occurrences v 1 1])))
    (def is-already-a-boolean?
      (pat/match [v opcode]
        [true _] true
        [false _] true
        [_ (or 'lt 'neq)] true
        _ false))
    (if is-already-a-boolean?
      (tx-ssa-val v)
      ["truthy(" (tx-ssa-val v) ")"] ))
  (defn tx-ssa-args [vv]
    (def v (:resolve-name ssa vv))
    (def inline? (and (symbol? v) (inline-node? v)))
    (def definition (if inline? (get-in ssa [:occurrences v 1])))
    (pat/match [v definition]
      [:empty _]
        ""
      [_ [_ 'push [v1 v2] nil]]
        (let [v1-code (tx-ssa-args v1)
              v2-code (tx-ssa-val v2)]
          (if (= v1-code "") v2-code [v1-code ", " v2-code]) )
      # else
        ["..." (tx-ssa-val v)] ))

  # `tx-insn` and `tx-control-flow` return a schedule and a nullary function `f`.
  # `f` can only be called after `inlining-decisions` is completely populated,
  # and returns the compiled JS.

  (defn tx-insn [insn [rest-sch rest-code]]
    (def [output-name] insn)

    (defn produce-assignment-to-ssa-name
      [max-occurrences is-reordering-barrier? defining-sch defining-expr]
      (assert (symbol? output-name))
      (def occurrences (((ssa :occurrences) output-name) 2))
      (def do-inline?
        (and # there must not be too many occurrences
             (if max-occurrences (<= occurrences max-occurrences) true)
             # we must be able to find all the occurrences in the tail schedule
             (= occurrences (schedule/count-uses rest-sch output-name))
             # and these occurrences must not occur after a barrier in the schedule
             (schedule/uses-value-inlineably? rest-sch is-reordering-barrier? output-name) ))
      (put inline-node? output-name do-inline?)
      (if do-inline?
        [(schedule/substitute-uses rest-sch output-name defining-sch)
         (fn []
           # we marked that this node will be inlined, so we don't
           # have to emit any extra code for its definition up front
           (put node-definition output-name (defining-expr))
           (rest-code) )]
        # if we don't inline it, then we do compute its definition
        # up front, and the schedule needs to reflect this
        [(schedule/concat defining-sch rest-sch)
         |[(tx-ssa-node output-name) " = " (defining-expr) ";" (rest-code)] ]))

    (defn barrier/assigns-reg? [r]
      |(pat/match $ ['ups (= r)] true
                    ['opaque s]  (s r)
                    _            false))
    (defn barrier/side-effect? [entry]
      (pat/match entry ['side-effect] true
                       ['opaque _]    true
                       _              false))
    (defn barrier/none [_] false)

    (pat/match insn
      [_ 'ups [v] r]
        [(schedule/concat (schedule/value v)
           [['ups r] rest-sch] )
         |[(tx-register r) " = " (tx-ssa-val v) ";" (rest-code)] ]
      [_ 'phi [] r]
        (produce-assignment-to-ssa-name
          nil # phis can be inlined even if used more than once
          (barrier/assigns-reg? r)
          [['phi r] nil]
          |[(tx-register r)] )
      [_ 'mktab [] r]
        (produce-assignment-to-ssa-name
          1            # inlining a table used more than once would break physical identity
          barrier/none # no other operation is a barrier
          nil          # doesn't introduce any operation into the schedule
          |["new Map()"] )
      [_ 'len [v] nil]
        # len() has a side effect, because it can error
        (produce-assignment-to-ssa-name
          1 barrier/side-effect?
          (schedule/concat (schedule/value v) [['side-effect] nil])
          |["length(" (tx-ssa-val v) ")"] )
      [_ 'lt [v1 v2] nil]
        (produce-assignment-to-ssa-name
          1            # avoid code duplication
          barrier/none # no other operation is a barrier
          (schedule/concat (schedule/value v1) (schedule/value v2))
          |["lt(" (tx-ssa-val v1) ", " (tx-ssa-val v2) ")"] )
      [_ 'sub [v1 v2] nil]
        (produce-assignment-to-ssa-name
          1 barrier/side-effect?
          (schedule/concat (schedule/value v1)
            (schedule/concat (schedule/value v2)
              [['side-effect] nil]))
          |["sub(" (tx-ssa-val v1) ", " (tx-ssa-val v2) ")"] )
      [_ 'get [v1 v2] nil]
        (produce-assignment-to-ssa-name
          1 barrier/side-effect?
          (schedule/concat (schedule/value v1)
            (schedule/concat (schedule/value v2)
              [['side-effect] nil]))
          |["get(" (tx-ssa-val v1) ", " (tx-ssa-val v2) ")"] )
      [_ 'neq [v1 v2] nil]
        (produce-assignment-to-ssa-name
          1            # avoid code duplication
          barrier/none # no other operation is a barrier
          (schedule/concat (schedule/value v1) (schedule/value v2))
          |["neq(" (tx-ssa-val v1) ", " (tx-ssa-val v2) ")"] )
      [_ 'mkstu [args] nil]
        # mkstu() has a side effect, because it can error
        (produce-assignment-to-ssa-name
          1 barrier/side-effect?
          (schedule/concat (schedule/value args) [['side-effect] nil])
          |["mkstu(" (tx-ssa-val args) ")"] )
      [_ 'push [args v] nil]
        (produce-assignment-to-ssa-name
          1            # shouldn't be possible for a push() to have multiple occurrences anyway
          barrier/none # no other operation is a barrier
          (schedule/concat (schedule/value args) (schedule/value v))
          |["[" (tx-ssa-args args) ", " (tx-ssa-val v) "]"] )
      [_ 'call [args f] nil]
        (produce-assignment-to-ssa-name
          1 barrier/side-effect?
          (schedule/concat (schedule/value f)
            (schedule/concat (schedule/value args)
              [['side-effect] nil]))
          |[(tx-ssa-val f) "(" (tx-ssa-args args) ")"] )
      [nil 'put [v1 v2 v3] nil]
        [(schedule/concat (schedule/value v1)
           (schedule/concat (schedule/value v2)
             (schedule/concat (schedule/value v3)
               [['side-effect] rest-sch] )))
         |["put(" (tx-ssa-val v1) ", " (tx-ssa-val v2) ", " (tx-ssa-val v3) ");" (rest-code)] ]
      [_ 'addim [v] x]
        # add() has a side effect, because it can error
        # so it should not be reordered with other side effects
        (produce-assignment-to-ssa-name
          1 barrier/side-effect?
          (schedule/concat (schedule/value v) [['side-effect] nil])
          |["add(" (tx-ssa-val v) ", " (string x) ")"] )
      [_ 'ldc [] i]
        (produce-assignment-to-ssa-name
          1 barrier/none nil |["ldc(" (string i) ")"] )
      # else
        # (string/format "/* unhandled insn: %q */" insn)
        (errorf "unhandled insn: %Q" insn) ))

  (defn tx-control-flow [cf]
    (pat/match cf
      []
        [nil |[]]
      [[(or 'loop-break 'block-break) lbl]]
        [nil |["break " (tx-label lbl) ";"]]
      [['loop-continue lbl]]
        [nil |["continue " (tx-label lbl) ";"]]
      [['tcall args f]]
        [(schedule/concat (schedule/value f)
                           (schedule/value args) )
         |["return " (tx-ssa-val f) "(" (tx-ssa-args args) ");"] ]
      [stmt & rest]
        (let [[rest-sch rest-code] (tx-control-flow rest)]
          (pat/match stmt
            ['if v cf1 cf2]
              (let [[cf1-sch cf1-code] (tx-control-flow cf1)
                    [cf2-sch cf2-code] (tx-control-flow cf2)]
                [(schedule/concat (schedule/value v)
                   [['opaque (merge (schedule/used-regs cf1-sch)
                                    (schedule/used-regs cf2-sch) )]
                    rest-sch])
                 |["if (" (tx-ssa-truthy v) ") { "
                   (cf1-code)
                   " }"
                   (if (empty? cf2)
                     []
                     [" else { "
                      (cf2-code)
                      " }" ])
                   (rest-code) ]])
            ['loop lbl & body]
              (let [[body-sch body-code] (tx-control-flow body)]
                [[['opaque (schedule/used-regs body-sch)] rest-sch]
                 |[(tx-label lbl) ": for (;;) { " (body-code) " }" (rest-code)] ])
            ['block lbl & body]
              (let [[body-sch body-code] (tx-control-flow body)]
                [[['opaque (schedule/used-regs body-sch)] rest-sch]
                 |[(tx-label lbl) ": do { " (body-code) " } while (false);" (rest-code)] ])
            ['do & insns]
              (fold-right tx-insn [rest-sch rest-code] insns) ))))

  (def [top-level-sch top-level-js] (tx-control-flow top-level-cf))
  (def declared-local-vars
    [;(map tx-register (sort (keys (ssa :all-phi-regs))))
     ;(seq [[node do-inline?] :pairs inline-node?
            :unless do-inline?] node)])
  (def js (top-level-js))
  (put ssa :inlining-decisions inline-node?)
  (string/join
    (flatten
      [(if (empty? declared-local-vars)
         []
         ["let " (interpose "," declared-local-vars) ";\n"])
       js])))
