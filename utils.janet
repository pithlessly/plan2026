(defn dbg [fmt x] (printf fmt x) x)

(defn update-each [ds f]
  (eachk k ds (update ds k f))
  ds)

(defn fold-right [f init xs]
  (var acc init)
  (each x (reverse xs)
    (set acc (f x acc)) )
  acc)

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
