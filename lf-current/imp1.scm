;; This extracted scheme code relies on some additional macros
;; available at http://www.pps.univ-paris-diderot.fr/~letouzey/scheme
(load "macros_extr.scm")


(define negb (lambda (b) (match b
                            ((True) `(False))
                            ((False) `(True)))))

(define add (lambdas (n m) (match n
                              ((O) m)
                              ((S p) `(S ,(@ add p m))))))
  
(define mul (lambdas (n m) (match n
                              ((O) `(O))
                              ((S p) (@ add m (@ mul p m))))))
  
(define sub (lambdas (n m) (match n
                              ((O) n)
                              ((S k) (match m
                                        ((O) n)
                                        ((S l) (@ sub k l)))))))
  
(define bool_dec (lambdas (b1 b2)
  (match b1
     ((True) (match b2
                ((True) `(Left))
                ((False) `(Right))))
     ((False) (match b2
                 ((True) `(Right))
                 ((False) `(Left)))))))

(define eqb (lambdas (n m)
  (match n
     ((O) (match m
             ((O) `(True))
             ((S _) `(False))))
     ((S n~) (match m
                ((O) `(False))
                ((S m~) (@ eqb n~ m~)))))))
  
(define leb (lambdas (n m) (match n
                              ((O) `(True))
                              ((S n~) (match m
                                         ((O) `(False))
                                         ((S m~) (@ leb n~ m~)))))))
  
(define ascii_dec (lambdas (a b)
  (match a
     ((Ascii b0 b1 b2 b3 b4 b5 b6 b7)
       (match b
          ((Ascii b8 b9 b10 b11 b12 b13 b14 b15)
            (match (@ bool_dec b0 b8)
               ((Left)
                 (match (@ bool_dec b1 b9)
                    ((Left)
                      (match (@ bool_dec b2 b10)
                         ((Left)
                           (match (@ bool_dec b3 b11)
                              ((Left)
                                (match (@ bool_dec b4 b12)
                                   ((Left)
                                     (match (@ bool_dec b5 b13)
                                        ((Left)
                                          (match (@ bool_dec b6 b14)
                                             ((Left)
                                               (match (@ bool_dec b7 b15)
                                                  ((Left) `(Left))
                                                  ((Right) `(Right))))
                                             ((Right) `(Right))))
                                        ((Right) `(Right))))
                                   ((Right) `(Right))))
                              ((Right) `(Right))))
                         ((Right) `(Right))))
                    ((Right) `(Right))))
               ((Right) `(Right)))))))))

(define string_dec (lambdas (s x)
  (match s
     ((EmptyString) (match x
                       ((EmptyString) `(Left))
                       ((String _ _) `(Right))))
     ((String a s0)
       (match x
          ((EmptyString) `(Right))
          ((String a0 s1)
            (match (@ ascii_dec a a0)
               ((Left) (match (@ string_dec s0 s1)
                          ((Left) `(Left))
                          ((Right) `(Right))))
               ((Right) `(Right)))))))))
  
(define eqb_string (lambdas (x y) (match (@ string_dec x y)
                                     ((Left) `(True))
                                     ((Right) `(False)))))

(define t_update (lambdas (m x v x~) (match (@ eqb_string x x~)
                                        ((True) v)
                                        ((False) (m x~)))))

(define aeval (lambdas (st a)
  (match a
     ((ANum n) n)
     ((AId x) (st x))
     ((APlus a1 a2) (@ add (@ aeval st a1) (@ aeval st a2)))
     ((AMinus a1 a2) (@ sub (@ aeval st a1) (@ aeval st a2)))
     ((AMult a1 a2) (@ mul (@ aeval st a1) (@ aeval st a2))))))
  
(define beval (lambdas (st b)
  (match b
     ((BTrue) `(True))
     ((BFalse) `(False))
     ((BEq a1 a2) (@ eqb (@ aeval st a1) (@ aeval st a2)))
     ((BLe a1 a2) (@ leb (@ aeval st a1) (@ aeval st a2)))
     ((BNot b1) (negb (@ beval st b1)))
     ((BAnd b1 b2) (match (@ beval st b1)
                      ((True) (@ beval st b2))
                      ((False) `(False)))))))
  
(define ceval_step (lambdas (st c i)
  (match i
     ((O) `(None))
     ((S i~)
       (match c
          ((CSkip) `(Some ,st))
          ((CAss l a1) `(Some ,(@ t_update st l (@ aeval st a1))))
          ((CSeq c1 c2) (match (@ ceval_step st c1 i~)
                           ((Some st~) (@ ceval_step st~ c2 i~))
                           ((None) `(None))))
          ((CIf b c1 c2)
            (match (@ beval st b)
               ((True) (@ ceval_step st c1 i~))
               ((False) (@ ceval_step st c2 i~))))
          ((CWhile b1 c1)
            (match (@ beval st b1)
               ((True) (match (@ ceval_step st c1 i~)
                          ((Some st~) (@ ceval_step st~ c i~))
                          ((None) `(None))))
               ((False) `(Some ,st)))))))))
  
