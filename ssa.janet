(defn register? [r]
  (or (int? r) (= r :args-stack)) )

(defn value? [r]
  (or (int? r)
      (symbol? r)
      (keyword? r)
      (boolean? r) ))
