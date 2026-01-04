(declare-const T (_ BitVec 1))
(assert (bvule (bvsub (bvshl ((_ zero_extend 31) T) (_ bv1 32)) (_ bv1 32)) (_ bv0 32)))
(check-sat)
