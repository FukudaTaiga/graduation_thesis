(declare-const x0 String)
(declare-const x1 String)

(assert (= x0 x1))
(assert (not (= x0 x1)))

(check-sat)
(get-model)
