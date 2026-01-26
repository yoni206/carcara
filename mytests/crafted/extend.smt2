(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))
(assert (= x (_ bv0 8)))
(assert (distinct ((_ zero_extend 3) x) (_ bv0 11)))
(assert (distinct ((_ sign_extend 3) x) (_ bv0 11)))
(check-sat)

