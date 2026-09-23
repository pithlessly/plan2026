(import pat)
(import ./ssa/insn)

(def DominatorTree {
  :dominates? (fn dominates? [self b1 b2]
    (or (= b1 b2)
        (and (not= b2 :root)
             (:dominates? self b1 ((self :immediate-dominator) b2)) )))
})

# Construct the dominator tree, following Cooper, Harvey, and Kennedy (2001).
(defn dominator-tree [{:cfg cfg :reverse-postorder reverse-postorder}]
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
    (put children bb-id @[]) )

  (struct/with-proto DominatorTree
    :immediate-dominator immediate-dominator
    :children            children))

# Convert to structured control flow, following Ramsey 2022.
# Grammar of the returned list:
# <control-flow> ::=
#   (block <label> <control-flow>) <control-flow>
#   (loop <label> <control-flow>)
#   (jmp <label>)
#   (tcall <value>)
#   (if <value> (<control-flow>) (<control-flow>))
#   (do <ssa-insn>*) <control-flow>
(defn to-structured-control-flow [{:cfg cfg :reverse-postorder reverse-postorder :do-tree do-tree}]
  (def loop-headers @{})
  (eachp [bb1-id bb1] cfg
    (each bb2-id (bb1 :succs) # edge bb1 → bb2
      (def bb2 (cfg bb2-id))
      (when (<= (bb2 :postorder) (bb1 :postorder)) # this is a back-edge
        (assert (:dominates? do-tree bb2-id bb1-id) "unstructured control flow ;-;")
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
      (pat/match (-?> (last insns) (:destruct))
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
        i
          (do (assert (= 1 (length succs)) (string/format "%q" i))
              (def bb-next (first succs))
              (assert (not (inline? (cfg bb-next))))
              [(inline-or-jmp bb-next) insns] )))
    (def bb-body [
      ;(seq [[r phi] :pairs (bb :phi-regs)] (insn/new phi 'phi [] r))
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
