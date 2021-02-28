(declare-const x0 String)
(declare-const x1 String)
(declare-const x2 String)
(declare-const x3 String)
(declare-const x4 String)
(declare-const x5 String)


(assert (str.in.re x0 (re.union (str.to.re "a") )))
(assert (str.in.re x1 (re.union (str.to.re "a") (str.to.re "b") )))
(assert (str.in.re x2 (re.union (str.to.re "a") (str.to.re "b") (str.to.re "c") )))
(assert (str.in.re x3 (re.union (str.to.re "a") (str.to.re "b") (str.to.re "c") (str.to.re "d") )))
(assert (str.in.re x4 (str.to.re "a") ))
;(re.union (str.to.re "a") (str.to.re "a") (str.to.re "a") (str.to.re "a"))))

(assert (not (= x1 x2)))
(assert (not (= x2 x3)))
(assert (not (= x3 x1)))
;(assert (not (= x4 x0)))

(check-sat)
(get-model)
