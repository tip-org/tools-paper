(declare-datatypes (a) ((list (nil) (cons (head a) (tail (list a))))))
(define-fun-rec
  (par (a b)
    (map ((f (=> a b)) (xs (list a))) (list b)
      (match xs (case nil (as nil (list b)))
                (case (cons x xs) (cons (@ f x) (map f xs)))))))
; (assert-not
;   (par (a b c)
;     (forall ((f (=> b c)) (g (=> a b)) (xs (list a)))
;        (= (map (lambda ((x a)) (@ f (@ g x))) xs)
;           (map f (map g xs))))))
(assert-not
  (par (a)
    (forall ((xs (list a)))
       (= xs (map (lambda ((x a)) x) xs)))))
(check-sat)
