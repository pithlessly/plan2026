(import pat)
(import ./build-cfg)
(import ./ssa)
(import ./ssa/func :as ssa)
(import ./ssa/opt :as ssa/opt)
(import ./reconstruct-control-flow :as cf)
(import ./backend)

(defn dump-cfg [cfg]
  (setdyn *pretty-format* "%m")
  (each [bb-start bb] (sorted-by 0 (pairs cfg))
    (printf "== bb: %p ==" bb-start)
    (print "old:")
    (each [opcode data] (bb :old-insns)
      (printf "             %-5s %p" opcode (freeze data)) )
    (print "new:")
    (each insn (bb :insns)
      (printf "    %-8s %-5s %p%V"
        (string/format "%V" (insn :out))
        (insn :opcode)
        (tuple/join (insn :inputs))
        (-?>> (insn :immediates) (string/format " %p")) ))
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

(defn recompile [assembly]

  (def { :bytecode bytecode } assembly)
  # registers below this refer to function parameters;
  # registers equal or greater refer to temporaries/locals
  (def parameter-slots
    (+ (assembly :arity)               # slots dedicated to fixed parameters
       (if (assembly :varargs) 1 0) )) # a slot for the rest of the varargs

  (def cfg (build-cfg/build bytecode))
  (def ssa (ssa/new-function parameter-slots))
  (merge-into ssa (ssa/build-cfg ssa cfg))
  (merge-into ssa (ssa/opt/reverse-postorder-traversal (ssa :cfg)))
  (merge-into ssa (ssa/opt/simplify-phis! ssa))
  (ssa/opt/resolve-all-names! ssa) # not strictly necessary, but useful for pretty printing
  (ssa/opt/to-phi-upsilon-form! (ssa :cfg))
  (each bb (ssa :cfg) (:freeze! bb))
  (merge-into ssa (ssa/opt/occurrence-analysis ssa))
  (merge-into ssa {:do-tree (cf/dominator-tree ssa)})
  (def control-flow (cf/to-structured-control-flow ssa))
  (def control-flow (cf/simplify-structured-control-flow control-flow))
  (def js (backend/to-javascript ssa control-flow))

  (pp assembly)

  { :cfg (ssa :cfg)
    :occurrences (ssa :occurrences)
    :control-flow control-flow
    :inlining-decisions (ssa :inlining-decisions)
    :js js
  })

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

(def compilation-results
  (with-dyns [*out* stderr *pretty-format* "%P"]
    (recompile (disasm sum3)) ))

(def debug-output-file "_debug.janet")
(def js-output-file "compiled.js")

(with [f (file/open js-output-file :wn)]
  (with [proc (os/spawn ["prettier" "--parser" "babel"] :px { :in :pipe :out f })]
    (:write (proc :in) (compilation-results :js)) ))
(eprintf "wrote compiled JS to %s." js-output-file)

(with [f (file/open debug-output-file :wn)]
  (with-dyns [*out* f]
    (printf "%m" (compilation-results :occurrences))
    (dump-cfg (compilation-results :cfg))
    (printf "%m" (compilation-results :control-flow))
    (printf "%m" (compilation-results :inlining-decisions))
    (printf "%m" (compilation-results :js)) )
  (eprintf "wrote debug info %s." debug-output-file) )
