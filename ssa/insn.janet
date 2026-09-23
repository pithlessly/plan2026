(import pat)
(import ../ssa)

(def Insn {
  :is-insn true
  :destruct (fn destruct [self]
    [(self :out) (self :opcode) (self :inputs) (self :immediates)] )
  :boolean? (fn boolean? [self]
    (pat/match (self :opcode)
      'lt  true
      'neq true
      _    false))
})

(defn insn? [i] (and (dictionary? i) (true? (i :is-insn))))

(defn new [out opcode inputs &opt immediates]
  (assert (or (nil? out) (symbol? out)))
  (assert (symbol? opcode))
  (assert (all ssa/value? inputs))
  (assert (or (nil? immediates) (int? immediates)))
  (struct/with-proto Insn
    :out out
    :opcode opcode
    :inputs @[;inputs]
    :immediates immediates))
