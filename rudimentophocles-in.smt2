(declare-datatypes (a)
  ((list (nil) (cons (head a) (tail (list a))))))
(define-fun-rec (par (a)
  (append ((xs (list a)) (ys (list a))) (list a)
    (match xs
      (case nil ys)
      (case (cons z zs) (cons z (append zs ys)))))))
(define-fun-rec (par (a)
  (reverse ((xs (list a))) (list a)
   (match xs
     (case nil (as nil (list a)))
     (case (cons y ys)
       (append (reverse ys) (cons y (as nil (list a)))))))))
(assert-not (par (a)
  (forall ((xs (list a))) (= (reverse (reverse xs)) xs))))
(check-sat)
