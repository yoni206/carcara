
(set-logic AUFBVFPDTNIRA)
(set-info :smt-lib-version 2.6)
(declare-datatypes ((tuple0 0))
  (((Tuple0))))

(declare-sort us_private 0)

(declare-const us_null_ext__ us_private)

(define-fun in_range ((x Int)) Bool
  (and (<= (- 2147483648) x) (<= x 2147483647)))

(declare-fun value (tuple0) Int)

(declare-fun value__function_guard (Int
  tuple0) Bool)

(assert
  (forall ((us_void_param tuple0))
    (! (let ((result (value us_void_param)))
         (=> (value__function_guard result us_void_param) (in_range result))) :pattern (
    (value
      us_void_param)) )))

(declare-fun f1 (tuple0) Int)

(declare-fun f1__function_guard (Int
  tuple0) Bool)

(assert
  (forall ((us_void_param tuple0))
    (! (let ((result (f1 us_void_param)))
         (=> (f1__function_guard result us_void_param) (in_range result))) :pattern (
    (f1
      us_void_param)) )))

(assert
  (forall ((us_void_param tuple0))
    (! (= (f1 us_void_param) 1) :pattern ((f1 us_void_param)) )))

(assert
  (not
  (let ((temp___210 (value Tuple0)))
    (=>
      (and (value__function_guard temp___210 Tuple0) (in_range temp___210))
      (forall ((spark__branch Bool))
        (=>
          (= spark__branch (ite (= temp___210 0) true false))
          (=>
            (= spark__branch true)
            (=> (f1__function_guard (f1 Tuple0) Tuple0) (= (f1 Tuple0) 1)))))))))

(check-sat)

