
(declare-fun x0 () String)
(declare-fun x1 () String)
(declare-fun x2 () String)
(declare-fun x3 () String)
(declare-fun x4 () String)
(declare-fun x5 () String)
(declare-fun x6 () String)
(declare-fun x7 () String)
(declare-fun x8 () String)
(declare-fun x9 () String)
(declare-fun x10 () String)
(declare-fun x11 () String)
(declare-fun x12 () String)
(declare-fun x13 () String)
(declare-fun x14 () String)
(declare-fun x15 () String)
(declare-fun x16 () String)

(assert (str.in.re x0 (str.to.re "aaba")))
(assert (= x1 (str.replace x0 "bacdfgba" "cbacdfgba")))
(assert (= x2 (str.replace x1 "c" "d")))
(assert (= x3 (str.replace x2 "d" "e")))
(assert (= x4 (str.replace x3 "e" "f")))
(assert (= x5 (str.replace x4 "f" "g")))
(assert (= x6 (str.replace x5 "g" "h")))
(assert (= x7 (str.replace x6 "h" "i")))
(assert (= x8 (str.replace x7 "i" "j")))
(assert (= x9 (str.replace x8 "j" "k")))
(assert (= x10 (str.replace x9 "k" "l")))
(assert (= x11 (str.replace x10 "l" "m")))
(assert (= x12 (str.replace x11 "m" "n")))
(assert (= x13 (str.replace x12 "n" "o")))
(assert (= x14 (str.replace x13 "o" "p")))
(assert (= x15 (str.replace x14 "p" "q")))
(assert (= x16 (str.replace x15 "q" "r")))

(check-sat)
(get-model)