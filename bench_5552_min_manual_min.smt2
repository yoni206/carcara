(declare-fun T4_10598 () (_ BitVec 8))
(assert (and (bvult (_ bv100 8) (bvudiv (_ bv102 8) T4_10598)   ) (= (bvudiv (_ bv102 8) T4_10598)    (_ bv0 8))))
(check-sat)
