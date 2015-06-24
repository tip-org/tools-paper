(define-fun
  twice ()
   (=> (=> Int Int) (=> Int Int))
   (lambda ((f (=> Int Int)))
   (lambda ((x Int))
   (@ f (@ f x)))))
(define-fun double () (=> Int Int)
  (lambda ((x Int)) (+ x x)))
(assert-not
  (forall ((x Int))
    (= (@ (@ twice double) x) (* x 4))))
(check-sat)
