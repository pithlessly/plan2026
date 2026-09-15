(import pat)

# return a tuple of:
# - the register outputs of this insn (or nil)
# - the register inputs of this insn
# - any non-register argument of this insn (or nil)
# - the offsets of successors
(defn- classify-args [insn]
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

(defn build [bytecode]
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
