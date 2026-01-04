(declare-const T (_ BitVec 1))
(assert (let ((?v_1 (bvadd (_ bv0 32) (bvshl ((_ zero_extend 31) T) (_ bv1 32))))) (bvule ((_ zero_extend 24) ((_ extract 7 0) (bvsub ?v_1 (_ bv1 32)))) (_ bv0 32))))
(check-sat)
