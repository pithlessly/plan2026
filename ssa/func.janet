(import pat)
(import ../ssa :prefix "")
(import ./insn)

(def BasicBlock @{
  :assert-mutable (fn assert-mutable [self] (assert (not (self :frozen?))))
  :freeze! (fn freeze! [self] (put self :frozen? true))
  :fresh-phi (fn fresh-phi [self r]
    (:assert-mutable self)
    (assert (register? r) r)
    (set ((self :phi-regs) r) (gensym)) )
  :lookup-reg+ (fn lookup-reg+ [self r]
    (assert (register? r) r)
    (if-let [v ((self :defined-regs) r)] [v false]
      (if-let [v ((self :phi-regs) r)] [v false]
        (let [v (:fresh-phi self r)] [v true]) )))
  :lookup-reg (fn lookup-reg [self r] (first (:lookup-reg+ self r)))
  :update-reg (fn update-reg [self r v]
    (:assert-mutable self)
    (assert (register? r) r)
    (assert (value? v) v)
    (set ((self :defined-regs) r) v) )
  :update-reg-if-absent (fn update-reg-if-absent [self r v]
    (unless (has-key? (self :defined-regs) r)
      (:update-reg self r v) ))
  :emit-insn (fn emit-insn [self insn]
    (:assert-mutable self)
    (assert (insn/insn? insn) insn)
    (array/push (self :insns) insn) )
  :take-args-stack (fn take-args-stack [self]
    (def args-stack (:lookup-reg self :args-stack))
    (:update-reg self :args-stack :empty)
    args-stack)
  :emit-push (fn emit-push [self v]
    (assert (value? v) v)
    (def push (insn/new (gensym) 'push [(:lookup-reg self :args-stack) v]))
    (:emit-insn self push)
    (:update-reg self :args-stack (push :out)) )
})

(defn- new-basic-block [cfg-bb]
  (def self
    (table/setproto @{
      :entry-point? (cfg-bb :entry-point?)
      :preds        (cfg-bb :preds)
      :succs        (cfg-bb :succs)
      :old-insns    (cfg-bb :insns)

      :insns        @[]
      :defined-regs @{}
      :phi-regs     @{}
    } BasicBlock))
  (when (self :entry-point?)
    (:update-reg self :args-stack :empty) )
  self)

(def Function @{
  :parameter? (fn parameter? [self r]
    (and (int? r) (< r (self :parameter-slots))) )
  # requires :elided-phi-nodes to be set
  :resolve-name (fn resolve-name [self name]
    (or ((self :elided-phi-nodes) name) name) )
})

(defn new-function [parameter-slots]
  (table/setproto @{
    :parameter-slots parameter-slots
  } Function))

# populate each basic block in the CFG with new fields:
# - `new-insns` is the new list of instructions in SSA form.
# - `defined-regs` associates a register with
#   the final value assigned to it in this bb, if any.
# - `phi-regs` associates a register with the name of the
#   phi node used to initialize it in this bb.
# - `fresh-phi` is a *function* which creates a phi node
#   in this block associated with a given register.

(defn- build-basic-block [func bb]
  (each [opcode [output-reg input-regs immediates _]] (bb :old-insns)
    (def input-names
      (seq [r :in input-regs]
        (if (:parameter? func r) (keyword r)
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
        (:emit-insn bb (insn/new (output-name) opcode [(:take-args-stack bb) ;input-names]))
      # else
        (:emit-insn bb (insn/new (output-name) opcode [;input-names] immediates)) )))

(defn build-cfg [func old-cfg]
  (def new-cfg
    (tabseq [[bb-id old-bb] :pairs old-cfg] bb-id
      (def bb (new-basic-block old-bb))
      (build-basic-block func bb)
      bb))
  {:cfg new-cfg} )
