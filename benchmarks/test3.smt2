(declare-fun x0 () String)
(declare-fun x1 () String)

(assert (not (= x0 x1)))
(assert (= (str.len x0) (str.len x1)))
(assert (= (str.len x0) 5))

(check-sat)
(get-model)
