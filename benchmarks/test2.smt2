(declare-fun x0 () String)
(declare-fun x1 () String)

(assert (not (= x0 x1)))
(assert (not (= (str.len x0) 0)))
(assert (not (= (str.len x1) 0)))

(check-sat)
(get-model)
