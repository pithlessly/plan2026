(import pat)

(defn dump-cfg [cfg]
  (setdyn *pretty-format* "%m")
  (each [bb-start bb] (sorted-by 0 (pairs cfg))
    (printf "== bb: %p ==" bb-start)
    (print "old:")
    (each [opcode data] (bb :old-insns)
      (printf "             %-5s %p" opcode (freeze data)) )
    (print "new:")
    (each [output-name opcode input-names immediates] (bb :insns)
      (printf "    %-8s %-5s %p%V"
        (string/format "%V" output-name)
        opcode
        (tuple/join input-names)
        (and immediates (string/format " %p" immediates)) ))
    (print "defined-regs:")
    (each [r v] (sort (pairs (bb :defined-regs)))
      (printf "    %-10s %q" (string r) v) )
    (print "phi-regs:")
    (each [r v] (sort (pairs (bb :phi-regs)))
      (printf "    %-10s %q" (string r) v) )
    (printf "preds: %p succs: %p" (bb :preds) (bb :succs))
    (def bb-clone (table/clone bb))
    (put bb-clone :defined-regs nil)
    (put bb-clone :phi-regs nil)
    (put bb-clone :preds nil)
    (put bb-clone :succs nil)
    (put bb-clone :old-insns nil)
    (put bb-clone :insns nil)
    (pp bb-clone)
    (print) ))

(defn dbg [fmt x] (printf fmt x) x)
(defn update-each [ds f]
  (eachk k ds (update ds k f))
  ds)

(def Queue @{
  :enqueue (fn [self x] (array/push (self :alt) x))
  :dequeue (fn [self]
    (var main (self :main))
    (unless (< (self :pos) (length main))
      (array/clear main)
      (set (self :pos) 0)
      (set main (self :alt))
      (when (empty? main)
        (break nil)) # queue is empty
      (set (self :alt) (self :main))
      (set (self :main) main))
    (def pos (self :pos))
    (def elt (main pos))
    (set (main pos) nil) # so GC knows we're done with it
    (set (self :pos) (inc pos))
    elt)
  :as-list (fn [self]
    (tuple/join (slice (self :main) (self :pos)) (self :alt)) )
})

(defn new-queue []
  (table/setproto @{:pos 0 :main @[] :alt @[]} Queue))

(def Worklist @{
  :next (fn [self]
    (def elt (:dequeue (self :queue)))
    (put (self :contains) elt nil)
    elt)
  :add (fn [self elt]
    (unless ((self :contains) elt)
      (put (self :contains) elt true)
      (:enqueue (self :queue) elt) ))
})

(defn new-worklist []
  (table/setproto @{:queue (new-queue) :contains @{}} Worklist))

# return a tuple of:
# - the register outputs of this insn (or nil)
# - the register inputs of this insn
# - any non-register argument of this insn (or nil)
# - the offsets of successors
(defn classify-args [insn]
  (defn one-output [] [(insn 1) (slice insn 2) nil [1]])
  (defn no-output  [] [nil      (slice insn 1) nil [1]])
  (pat/match insn

    ['addim y x c] [y   [x] c   [1]]
    ['call _ _]    (one-output)
    ['get _ _ _]   (one-output)
    ['jmpno x o]   [nil [x] nil [1 o]]
    ['jmp o]       [nil []  nil [o]]
    ['ldc y c]     [y   []  c   [1]]
    ['ldi y c]     [y   []  c   [1]]
    ['ldt y]       (one-output)
    ['len _ _]     (one-output)
    ['lt _ _ _]    (one-output)
    ['mkstu _]     (one-output)
    ['mktab _]     (one-output)
    ['movf x y]    (y   [x] nil [1])
    ['movn _ _]    (one-output)
    ['neq _ _ _]   (one-output)
    ['push x]      (no-output)
    ['push2 x y]   (no-output)
    ['push3 x y z] (no-output)
    ['put x y z]   (no-output)
    ['sub _ _ _]   (one-output)
    ['tcall x]     [nil [x] nil []]

    o              (errorf "%q" o) ))

(defn build-cfg [bytecode]

  (def bytecode-args (map classify-args bytecode))
  (def successors (seq [[idx args] :pairs bytecode-args]
                    [;(map |(+ idx $) (args 3))] ))

  # count entry points to each instruction
  (def entry-points (array/new-filled (length bytecode) 0))
  (defn visit [idx]
    (def n (entry-points idx))
    (set (entry-points idx) (inc n))
    (when (zero? n)
      (each s (successors idx) (visit s))))
  (visit 0)

  # identify basic blocks
  (def cfg @{})
  (defn build-bb [start]
    (if (has-key? cfg start) (break))
    (def insns @[])
    (def bb (set (cfg start) @{ :insns insns }))
    (var idx start)
    (forever
      (let [[opcode & _] (bytecode      idx)
            insn-args    (bytecode-args idx)]
        (array/push insns [opcode insn-args]) )
      (unless (= 1 (length (successors idx))) (break))
      (def next-idx (first (successors idx)))
      (unless (= 1 (entry-points next-idx)) (break))
      (set idx next-idx))
    (set (bb :succs) (successors idx))
    (each s (successors idx) (build-bb s) ))
  (build-bb 0)
  (put (cfg 0) :entry-point? true)

  # compute predecessors for each BB
  (eachp [bb-id bb] cfg
    (each succ (bb :succs)
      (update-in cfg [succ :preds bb-id] (fn [_] true)) ))
  (each bb cfg
    (update bb :preds
      |[;(sorted (keys (or $ [])))] ))

  cfg)

(defn register? [r]
  (or (int? r) (= r :args-stack)) )

(defn ssa-value? [r]
  (or (int? r)
      (symbol? r)
      (keyword? r)
      (boolean? r) ))

(def SsaBasicBlock @{
  :assert-mutable (fn [self] (assert (not (self :frozen?))))
  :freeze! (fn [self] (put self :frozen? true))
  :fresh-phi (fn [self r]
    (:assert-mutable self)
    (assert (register? r) r)
    (set ((self :phi-regs) r) (gensym)) )
  :lookup-reg+ (fn [self r]
    (assert (register? r) r)
    (if-let [v ((self :defined-regs) r)] [v true]
      (if-let [v ((self :phi-regs) r)] [v true]
        (let [v (:fresh-phi self r)] [v false]) )))
  :lookup-reg (fn [self r] (first (:lookup-reg+ self r)))
  :update-reg (fn [self r v]
    (:assert-mutable self)
    (assert (register? r) r)
    (assert (ssa-value? v) v)
    (set ((self :defined-regs) r) v) )
  :update-reg-if-absent (fn [self r v]
    (unless (has-key? (self :defined-regs) r)
      (:update-reg self r v) ))
  :emit-insn (fn [self insn]
    (:assert-mutable self)
    (array/push (self :insns) insn) )
  :take-args-stack (fn [self]
    (def args-stack (:lookup-reg self :args-stack))
    (:update-reg self :args-stack :empty)
    args-stack)
  :emit-push (fn [self v]
    (assert (ssa-value? v) v)
    (def output-name (gensym))
    (:emit-insn self [output-name 'push [(:lookup-reg self :args-stack) v] nil])
    (:update-reg self :args-stack output-name) )
})

(defn new-ssa-basic-block [cfg-bb]
  (def self
    (table/setproto @{
      :entry-point? (cfg-bb :entry-point?)
      :preds        (cfg-bb :preds)
      :succs        (cfg-bb :succs)
      :old-insns    (cfg-bb :insns)

      :insns        @[]
      :defined-regs @{}
      :phi-regs     @{}
    } SsaBasicBlock))
  (when (self :entry-point?)
    (:update-reg self :args-stack :empty) )
  self)

# populate each basic block in the CFG with new fields:
# - `new-insns` is the new list of instructions in SSA form.
# - `defined-regs` associates a register with
#   the final value assigned to it in this bb, if any.
# - `phi-regs` associates a register with the name of the
#   phi node used to initialize it in this bb.
# - `fresh-phi` is a *function* which creates a phi node
#   in this block associated with a given register.

(defn build-ssa [parameter-slots cfg]
  (defn parameter? [r] (and (int? r) (< r parameter-slots)))
  (each [bb-id old-bb] (pairs cfg)
    (def bb (set (cfg bb-id) (new-ssa-basic-block old-bb)))
    (each [opcode [output-reg input-regs immediates _]] (bb :old-insns)
      (def input-names
        (seq [r :in input-regs]
          (if (parameter? r) (keyword r)
                             (:lookup-reg bb r) )))
      (def output-name |(and output-reg
                          (:update-reg bb output-reg (gensym))))
      (pat/match opcode
        (or 'movn 'movf)
          (:update-reg bb output-reg (first input-names))
        'ldi
          (:update-reg bb output-reg immediates)
        'ldt
          (:update-reg bb output-reg true)
        (or 'push 'push2 'push3)
          (each i input-names
            (:emit-push bb i))
        (or 'mkstu 'call 'tcall)
          (:emit-insn bb [(output-name) opcode [(:take-args-stack bb) ;input-names] nil])
        # else
          (:emit-insn bb [(output-name) opcode [;input-names] immediates]))))

  @{})

(defn compute-reverse-postorder-traversal [cfg]
  (def order @[])
  (def visited @{})
  (defn visit [bb-id]
    (unless (visited bb-id)
      (put visited bb-id true)
      (each bb-succ (reverse ((cfg bb-id) :succs)) (visit bb-succ))
      (array/push order bb-id) ))
  (visit 0)
  (reverse! order)
  (eachp [i bb-id] order
    (set ((cfg bb-id) :postorder) i) )
  order)

# Simple phi node minimization
# (roughly following Braun, Buchwald, Hack, Leißa, Mallon, and Zwinkau 2013)
(defn simplify-ssa [parameter-slots cfg ssa reverse-postorder]

  (def elided-phi-nodes @{})
  (defn resolve-name [name]
    (if-let [new-name (elided-phi-nodes name)]
      (let [resolved (resolve-name new-name)]
        (assert (symbol? name) name)
        (unless (= new-name resolved)
          (put elided-phi-nodes new-name resolved) )
        resolved)
      name))

  (put ssa :resolve-name resolve-name)

  (def worklist (new-worklist))
  (each bb-id reverse-postorder (:add worklist bb-id))

  (defn resolve-register [bb-id r]
    (assert (>= r parameter-slots) r)
    (def [v new?] (:lookup-reg+ (cfg bb-id) r))
    (when new? (:add worklist bb-id) )
    (resolve-name v) )

  (loop [bb-id :iterate (:next worklist) :let [bb (cfg bb-id)]]
    # (printf "improving basic block: %P %P" bb-id (:as-list (worklist :queue)))
    (var did-improve false)
    (each [r phi] (pairs (bb :phi-regs))
      (assert (not (has-key? elided-phi-nodes phi)))
      (def phi-args (map |(resolve-register $ r) (bb :preds)))
      (def unique-phi-args @{})
      (each arg phi-args (put unique-phi-args arg true))
      (put unique-phi-args phi nil)
      (when-let [elision-target (case (length unique-phi-args)
                                  0 :undef
                                  1 (first (keys unique-phi-args)) )]
        (put elided-phi-nodes phi elision-target)
        (:update-reg-if-absent bb r elision-target)
        (put (bb :phi-regs) r nil)
        # (printf "bb %p: improved r=%p %p → %p" bb-id r phi elision-target)
        (set did-improve true) ))
    (when did-improve
      # (print "* found improvements for this bb")
      (each succ (bb :succs)
        (:add worklist succ) ))))

(defn resolve-all-names [cfg ssa]
  (def {:resolve-name resolve-name} ssa)
  (each bb cfg
    (update-each (bb :insns)
      (fn [[output opcode inputs immediates]]
        [(resolve-name output) opcode [;(map resolve-name inputs)] immediates] ))
    (update-each (bb :defined-regs) resolve-name) ))

(defn to-phi-upsilon-form [cfg]
  (each bb cfg
    (when (= 1 (length (bb :preds)))
      (assert (empty? (bb :phi-regs))) ))
  (def requisite-insns @{}) # bb-id ↦ (reg ↦ value-name)
  (loop [bb      :in cfg
         [r phi] :pairs (bb :phi-regs)
         pred    :in (bb :preds)]
    (def [value-in-pred new?] (:lookup-reg+ (cfg pred) r))
    # FIXME: if this value came from a phi node in pred, it's probably redundant
    # to assign it again. So we should probably just be consulting ((cfg pred) :defined-regs).
    (assert new?)
    (update-in requisite-insns [pred r]
      (fn [old-value]
        (when old-value (assert (= old-value value-in-pred)))
        value-in-pred) ))
  (eachp [bb-id bb] cfg
    (eachp [r v] (or (requisite-insns bb-id) {})
      (update bb :upsilon-insns
        (fn [old]
          (array/push (or old @[]) [nil 'ups [v] r]) )))))

(defn occurrence-analysis [cfg reverse-postorder ssa]
  (def {:resolve-name resolve-name} ssa)
  # name ↦ @[bb-id definition occurrences]
  # `definition` is the defining insn, or ~(phi ,r) for phi nodes
  (def occurrences @{})
  (def all-phi-regs @{})
  # populate with the insns in each bb
  (loop [bb-id :in reverse-postorder :let [bb (cfg bb-id)]]
    (eachp [r phi] (bb :phi-regs)
      # this phi node must define a new name
      (assert (not (has-key? occurrences phi)))
      (put all-phi-regs r true)
      (put occurrences phi @[bb-id ~(phi ,r) 0]) )
    (each insn (bb :insns)
      (def [output _ inputs _] insn)
      (each input inputs
        (when (symbol? input)
          (def resolved (resolve-name input))
          # definitions dominate uses, and we visit in reverse postorder,
          # so the definition must have already been visited
          (assert (has-key? occurrences resolved))
          (update (occurrences resolved) 2 inc) ))
      (when output
        (assert (not (has-key? occurrences output)))
        (put occurrences output @[bb-id insn 0]) )))
  {:occurrences occurrences
   :all-phi-regs all-phi-regs})

# Construct the dominator tree, following Cooper, Harvey, and Kennedy (2001).
(defn dominator-tree [cfg reverse-postorder]
  (def immediate-dominator @{0 :root}) # 0 is known as the root 

  # invariant: if a ≠ 0, immediate-dominator[a] = b, then immediate-dominator[b] is set.
  (defn intersect [b1 b2]
    (def [o1 o2] [((cfg b1) :postorder) ((cfg b2) :postorder)])
    (cond (< o1 o2) (intersect b1 (immediate-dominator b2))
          (> o1 o2) (intersect (immediate-dominator b1) b2)
                    (assert (= b1 b2)) b1) )

  # I would prefer a worklist-based implementation to reduce unnecessary
  # recompuation, but I couldn't be convinced that it's sufficient to
  # recompute a block when one of its predecessors changes
  (while (do
    (var changed false)
    (loop [bb-id :in reverse-postorder :unless (= 0 bb-id) :let [bb (cfg bb-id)]]
      (def old-dominator (immediate-dominator bb-id))
      # (printf "* before doms[%Q] = %Q" bb-id old-dominator)
      (def processed-predecessors (filter immediate-dominator (bb :preds)))
      (def new-dominator (reduce2 intersect processed-predecessors))
      # (printf "* after  doms[%Q] = %Q" bb-id new-dominator)
      (unless (= old-dominator new-dominator)
        (put immediate-dominator bb-id new-dominator)
        (set changed true) ))
    changed))

  (def children @{:root @[]})
  (loop [bb-id :in reverse-postorder]
    (array/push (children (immediate-dominator bb-id)) bb-id)
    (put children bb-id @[]))

  (defn dominates? [b1 b2]
    (or (= b1 b2)
        (and (not= b2 :root)
             (dominates? b1 (immediate-dominator b2)) )))

  {:immediate-dominator immediate-dominator
   :dominates?          dominates?
   :children            children})

# Convert to structured control flow, following Ramsey 2022.
# Grammar of the returned list:
# <control-flow> ::=
#   (block <label> <control-flow>) <control-flow>
#   (loop <label> <control-flow>)
#   (jmp <label>)
#   (tcall <value>)
#   (if <value> (<control-flow>) (<control-flow>))
#   (do <ssa-insn>*) <control-flow>
(defn to-structured-control-flow [cfg reverse-postorder do-tree]
  (def loop-headers @{})
  (eachp [bb1-id bb1] cfg
    (each bb2-id (bb1 :succs) # edge bb1 → bb2
      (def bb2 (cfg bb2-id))
      (when (<= (bb2 :postorder) (bb1 :postorder)) # this is a back-edge
        (assert ((do-tree :dominates?) bb2-id bb1-id) "unstructured control flow ;-;")
        (put loop-headers bb2-id true) )))
  # (printf "to-structured-control-flow: loop-headers=%Q" loop-headers)

  (defn inline? [bb]
    (assert (table? bb))
    (and (not (bb :entry-point?))
         (= 1 (length (bb :preds))) ))

  (defn recurse [bb-id]
    # (printf "(recurse %Q)" bb-id)
    (defn inline-or-jmp [bb-id]
      # (printf "(inline-or-jmp %Q)" bb-id)
      (if (inline? (cfg bb-id)) (recurse bb-id)
                                ~[(jmp ,bb-id)] ))
    (def bb (cfg bb-id))
    (def {:insns insns :succs succs} bb)
    (var [code bb-body]
      (pat/match (last insns)
        [nil 'jmp [] nil]
          [(inline-or-jmp (first succs))
           (array/slice insns 0 -2)]
        [nil 'jmpno [x] nil]
          [[['if x (inline-or-jmp (succs 0)) (inline-or-jmp (succs 1))]]
           (array/slice insns 0 -2)]
        [nil 'tcall [args f] nil]
          [[['tcall args f]]
           (array/slice insns 0 -2)]
        # else
          (do (assert (= 1 (length succs)))
              (def bb-next (first succs))
              (assert (not (inline? (cfg bb-next))))
              [(inline-or-jmp bb-next) insns] )))
    (def bb-body [
      ;(seq [[r phi] :pairs (bb :phi-regs)] [phi 'phi [] r])
      ;bb-body
      ;(or (bb :upsilon-insns) [])
    ])
    (unless (empty? bb-body)
      (set code [['do ;bb-body] ;code]) )
    (def blocks-to-break-to (filter |(not (inline? (cfg $))) ((do-tree :children) bb-id)))
    (each bb-next blocks-to-break-to
      (set code [['block bb-next ;code] ;(recurse bb-next)]) )
    (when (loop-headers bb-id)
      (set code [['loop bb-id ;code]]) )
    code)
  (recurse 0) )

(defn simplify-structured-control-flow [control-flow]
  (defn recurse [cf innermost-label ctx]
    # (printf "(recurse %Q %Q %Q)" cf innermost-label ctx)
    (pat/match cf
      [['block lbl & cf1] & cf2]
        (let [cf2-simplified (recurse cf2 innermost-label ctx)]
          (assert (not (has-key? ctx lbl)))
          (if (empty? cf2-simplified)
            (recurse cf1 innermost-label (merge ctx {lbl (ctx innermost-label)}))
            (let [fresh-ctx-entry
                    @{ :used-explicitly false
                       :true-label      lbl
                       :mark-as-used-explicitly (fn [self] (put self :used-explicitly true))
                       :syntax-of               (fn [self] ~(block-break ,lbl)) }
                  cf1-simplified (recurse cf1 lbl (merge ctx {lbl fresh-ctx-entry})) ]
              (if (fresh-ctx-entry :used-explicitly)
                [['block lbl ;cf1-simplified] ;cf2-simplified]
                [;cf1-simplified ;cf2-simplified] ))))
      [['loop lbl & cf1]]
        (do
          (assert (not (has-key? ctx lbl)))
          [['loop lbl
            ;(recurse cf1 lbl
               (merge ctx
                 { innermost-label
                    (when innermost-label
                       @{ :true-label  ((ctx innermost-label) :true-label)
                          :mark-as-used-explicitly (fn [self])
                          :syntax-of               (fn [self] ~(loop-break ,lbl)) })
                   lbl
                     @{ :true-label lbl
                        :mark-as-used-explicitly (fn [self])
                        :syntax-of               (fn [self] ~(loop-continue ,lbl)) }}))]])
      [['jmp i]]
        (let [ctx-entry (ctx i)
              implicit  (= (ctx-entry :true-label) innermost-label) ]
          (if implicit []
                       (do (:mark-as-used-explicitly ctx-entry)
                           [(:syntax-of ctx-entry)] )))
      [['tcall args f]]
        [['tcall args f]]
      [['if condition cf1 cf2]]
        [['if condition (recurse cf1 innermost-label ctx) (recurse cf2 innermost-label ctx)]]
      [['do & insns] & cf1]
        [['do ;insns] ;(recurse cf1 innermost-label ctx)]
      # else
        (errorf "unknown control flow: %Q" cf) ))
  (recurse control-flow nil {}) )

(defn recompile [assembly]

  (def { :bytecode bytecode } assembly)
  # registers below this refer to function parameters;
  # registers equal or greater refer to temporaries/locals
  (def parameter-slots
    (+ (assembly :arity)               # slots dedicated to fixed parameters
       (if (assembly :varargs) 1 0) )) # a slot for the rest of the varargs

  (def cfg (build-cfg bytecode))
  (def ssa (build-ssa parameter-slots cfg))
  (def reverse-postorder (compute-reverse-postorder-traversal cfg))
  (simplify-ssa parameter-slots cfg ssa reverse-postorder)
  (resolve-all-names cfg ssa) # not strictly necessary, but useful for pretty printing
  (to-phi-upsilon-form cfg)
  (each bb cfg (:freeze! bb))
  (def occurrences (occurrence-analysis cfg reverse-postorder ssa))
  (def do-tree (dominator-tree cfg reverse-postorder))
  (def control-flow
    (simplify-structured-control-flow
      (to-structured-control-flow cfg reverse-postorder do-tree) ))

  (pp occurrences)
  (pp control-flow)

  { :bytecode bytecode :cfg cfg :occurrences occurrences })

(defn sum3
  "Solve the 3SUM problem in O(n^2) time."
  [s]
  (def tab @{})
  (def solutions @{})
  (def len (length s))
  (for k 0 len
    (put tab (s k) k))
  (for i 0 len
    (for j 0 len
      (def k (get tab (- 0 (s i) (s j))))
      (when (and k (not= k i) (not= k j) (not= i j))
        (put solutions {i true j true k true} true))))
  (map keys (keys solutions)))

(def {:cfg cfg :occurrences occurrences}
  (with-dyns [*out* stderr *pretty-format* "%P"]
    (recompile (disasm sum3)) ))

(printf "%m" occurrences)
(dump-cfg cfg)
