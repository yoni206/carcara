(declare-const T (_ BitVec 1))
(assert (= (_ bv0 32) (bvadd (_ bv1 32) (concat (concat (_ bv0 30) T) (_ bv0 1)))))
(check-sat)
