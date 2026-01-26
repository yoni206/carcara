(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))
(assert (= x (_ bv0 8)))
(assert (distinct ((_ extract 3 2) x) (_ bv0 2)))
(check-sat)

