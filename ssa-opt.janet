(import pat)
(import ./utils :prefix "")

(defn reverse-postorder-traversal [cfg]
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
  {:reverse-postorder order})

# Simple phi node minimization
# (roughly following Braun, Buchwald, Hack, Leißa, Mallon, and Zwinkau 2013)
(defn simplify-phis! [func]
  (def {:cfg cfg} func)

  # maps phi names to their known sources.
  # a source is an SSA value that is definitely not elidable,
  # either because it isn't an SSA node, or because it has
  # multiple sources that are definitely distinct.
  # initially it maps all phi nodes to `false`, meaning no
  # source is known.
  (def phi-sources
    (tabseq [bb :in cfg phi :in (bb :phi-regs)] phi :undef) )

  (var did-improve true)
  (defn resolve-register [bb-id r]
    (assert (not (:parameter? func r)) r)
    (def [v new?] (:lookup-reg+ (cfg bb-id) r))
    (when new?
      # (printf "resolve-register created φ(%Q) in BB %Q" r bb-id)
      (set did-improve true)
      (assert (symbol? v))
      (assert (not (has-key? phi-sources v)))
      (put phi-sources v :undef) )
    v)

  (while did-improve
    (set did-improve false)
    (loop [bb-id :in (func :reverse-postorder)
           :let [bb (cfg bb-id)]
           [r phi] :in (pairs (bb :phi-regs))
           :let [old-source (phi-sources phi)]
           :when [(not= old-source phi)] ]
      (def phi-args (map |(resolve-register $ r) (bb :preds)))
      (def unique-phi-sources @{})
      (each arg phi-args
        (put unique-phi-sources (or (phi-sources arg) arg) true) )
      (put unique-phi-sources :undef nil)
      (def new-source (case (length unique-phi-sources)
                        0 :undef
                        1 (first (keys unique-phi-sources))
                          phi))
      (assert new-source)
      (when (not= old-source new-source)
        # (printf "improving %Q(r=%Q): %Q → %Q → %Q" phi r old-source unique-phi-sources new-source)
        (put phi-sources phi new-source)
        (set did-improve true) )))

  # (printf "%M" phi-sources)
  (def elided-phi-nodes
    (tabseq [[phi source] :pairs phi-sources]
      phi
      (pat/match source
        :undef  nil
        (= phi) nil
        _       source)))
  # (printf "%M" elided-phi-nodes)
  (each bb cfg
    (each [r phi] (pairs (bb :phi-regs))
      (when-let [elision-target (elided-phi-nodes phi)]
        # (printf "eliding phi node: %Q" phi)
        (put (bb :phi-regs) r nil)
        (:update-reg-if-absent bb r elision-target) )))

  {
    # :phi-sources phi-sources
    :elided-phi-nodes elided-phi-nodes
  })

(defn resolve-all-names! [func]
  (def {:cfg cfg} func)
  (each bb cfg
    (update-each (bb :insns)
      (fn [[output opcode inputs immediates]]
        [(:resolve-name func output) opcode [;(map |(:resolve-name func $) inputs)] immediates] ))
    (update-each (bb :defined-regs) |(:resolve-name func $)) ))

(defn to-phi-upsilon-form! [cfg]
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
    (assert (not new?))
    (update-in requisite-insns [pred r]
      (fn [old-value]
        (when old-value (assert (= old-value value-in-pred)))
        value-in-pred) ))
  (eachp [bb-id bb] cfg
    (eachp [r v] (or (requisite-insns bb-id) {})
      (update bb :upsilon-insns
        (fn [old]
          (array/push (or old @[]) [nil 'ups [v] r]) )))))

(defn occurrence-analysis [func]
  (def {:cfg cfg :reverse-postorder reverse-postorder} func)
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
    (each insn [;(bb :insns) ;(or (bb :upsilon-insns) [])]
      (def [output _ inputs _] insn)
      (each input inputs
        (when (symbol? input)
          (def resolved (:resolve-name func input))
          # definitions dominate uses, and we visit in reverse postorder,
          # so the definition must have already been visited
          (assert (has-key? occurrences resolved))
          (update (occurrences resolved) 2 inc) ))
      (when output
        (assert (not (has-key? occurrences output)))
        (put occurrences output @[bb-id insn 0]) )))
  {:occurrences occurrences
   :all-phi-regs all-phi-regs})
