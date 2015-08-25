#lang racket
(require "pmatch.rkt")
(require cKanren)
(require cKanren/tree-unify)
(require cKanren/attributes)
(require cKanren/neq)
(provide (all-defined-out))

(define-syntax test-check
  (syntax-rules ()
    ((_ title tested-expression expected-result)
     (begin
       (printf "Testing ~s\n" title)
       (let* ((expected expected-result)
              (produced tested-expression))
         (or (equal? expected produced)
             (error 'test-check
               "Failed: ~a~%Expected: ~a~%Computed: ~a~%"
               'tested-expression expected produced)))))))

(define membero
  (lambda (x ls)
    (fresh (a d)
      (== `(,a . ,d) ls)
      (conde
        [(== a x) (fresh (b c)
		    (conde
		      ((== `(All ,b are ,c) x))
		      ((== `(Some ,b are ,c) x))
		      ((== `(No ,b are ,c) x))
                      ((== `(Least as many ,b ,c) x))))]
        [(=/= a x) (membero x d)]))))

(define LLeast
  (lambda (phi gamma proof)
    (fresh (a b)
      (== `(Least as many ,a ,b) phi)
      (conde
        ;; Card-Trans 
        ((fresh (c r1 r2)
          (== `((,r1 ,r2) => ,phi) proof)
          (L `(Least as many ,a ,c) gamma r1)
          (L `(Least as many ,c ,b) gamma r2)))
        ;; Subset-Size
        ((fresh (r1)
          (== `((,r1) => ,phi) proof)
          (L `(All ,b are ,a) gamma r1)))
        ;; No Rule Found
        ((fresh (r1)
          (== `((,r1) => ,phi) proof)
          (L `(No ,b are ,b) gamma r1)))))))

(define LAll
  (lambda (phi gamma proof)
    (fresh (a b)
      (== `(All ,a are ,b) phi)
      (conde
        ;; Axiom
        ((== a b) (== phi proof))
        ;; Card-Mix
        ((fresh (r1 r2)
           (== `((,r1 ,r2) => ,phi) proof)
           (L `(All ,b are ,a) gamma r1)
           (L `(Least as many ,b ,a) gamma r2)))
        ;; Barbara
        ((fresh (c r1 r2)
           (== `((,r1 ,r2) => ,phi) proof)
           (=/= a c)
           (=/= b c)
           (L `(All ,a are ,c) gamma r1)
           (L `(All ,c are ,b) gamma r2)))
        ;; No Rule Found
        ((fresh (p q r1 r2)
           (== `((,r1 ,r2) => ,phi) proof)
           (L `(Some ,p are ,q) gamma r1)
           (L `(No ,p are ,q) gamma r2)))
        ;; Zero || One (?)
        ((fresh (r1)
           (== `((,r1) => ,phi) proof)
           (L `(No ,a are ,a) gamma r1)))))))

(define LSome
  (lambda (phi gamma proof)
    (fresh (a b)
      (== `(Some ,a are ,b) phi)
      (conde
        ;; Card-E
        [(== a b)
         (fresh (c r1 r2)
           (== `((,r1 ,r2) => ,phi) proof)
           (L `(Some ,c are ,c) gamma r1)
           (L `(Least as many ,a ,c) gamma r2))]
        ;; Some
        [(== a b)
         (fresh (r1 c)
           (== `((,r1) => ,phi) proof)
           (L `(Some ,a are ,c) gamma r1))]
        ;; Conversion
        [(fresh (r1)
           (== `((,r1) => ,phi) proof)
           (L `(Some ,b are ,a) gamma r1))]
        ;; Darii
        [(fresh (c r1 r2)
           (== `((,r1 ,r2) => ,phi) proof)
           (L `(All ,c are ,b) gamma r1)
           (L `(Some ,a are ,c) gamma r2))]
        ;; No Rule Found
        [(fresh (p q r1 r2)
           (== `((,r1 ,r2) => ,phi) proof)
           (L `(Some ,p are ,q) gamma r1)
           (L `(No ,p are ,q) gamma r2))]))))

(define LNo
  (lambda (phi gamma proof)
    (fresh (a b)
      (== `(No ,a are ,b) phi)
      (conde
        [(fresh (r1)
           (== `((,r1) => ,phi) proof)
           (L `(No ,a are ,a) gamma r1))]
        [(fresh (r1)
           (== `((,r1) => ,phi) proof)
           (L `(No ,b are ,a) gamma r1))]
        [(fresh (c r1 r2)
           (== `((,r1 ,r2) => ,phi) proof)
           (L `(All ,a are ,c) gamma r1)
           (L `(No ,c are ,b) gamma r2))]
        [(fresh (p q r1 r2)
           (== `((,r1 ,r2) => ,phi) proof)
           (L `(Some ,p are ,q) gamma r1)
           (L `(No ,p are ,q) gamma r2))]))))

(define L
  (lambda (phi gamma proof)
    (conde
      [(membero phi gamma) (== phi proof)]      
      [(LLeast phi gamma proof)]
      [(LAll phi gamma proof)]
      [(LSome phi gamma proof)]
      [(LNo phi gamma proof)])))


(test-check "Barbara"
  (run 1 (o) (L '(All r are q) '((All p are q) (All r are p)) o))
  '((((All r are p) (All p are q)) => (All r are q))))

(test-check "Celarent"
  (run 1 (o) (L `(No q are p) `((All p are n) (No n are q)) o))
  '((((((All p are n) (No n are q)) => (No p are q)))
     =>
     (No q are p))))

(test-check "Darii"
  (run 1 (o) (L '(Some r are q) '((All p are q) (Some r are p)) o))
  '((((All p are q) (Some r are p)) => (Some r are q))))

(test-check "Cesare"
  (run 1 (o) (L '(No r are p) '((No p are q) (All r are q)) o))
  '((((All r are q) (((No p are q)) => (No q are p)))
     =>
     (No r are p))))

(test-check "Camestres"
  (run 1 (o) (L '(No r are p) '((All p are q) (No r are q)) o))
  '((((((All p are q) (((No r are q)) => (No q are r)))
       =>
       (No p are r)))
     =>
     (No r are p))))

(test-check "E-conversion"
  (run 1 (o) (L `(No q are p) `((No p are q)) o))
  '((((No p are q)) => (No q are p))))

(test-check "Example 13"
  (run 1 (o) (L `(Some p are q) `((All n are q) (All n are p) (Some n are n)) o))
  '((((All n are q)
      (((((All n are p) (Some n are n)) => (Some n are p)))
       =>
       (Some p are n)))
     =>
     (Some p are q))))

(test-check "Basic example"
  (run 1 (q) (L '(Least as many x y) '((All y are x)) q))
  '((((All y are x)) => (Least as many x y))))

(test-check "2nd example"
  (run 1 (q) (L '(Least as many x z) '((Least as many x y) (Least as many y z)) q))
  '((((Least as many x y) (Least as many y z)) => (Least as many x z))))

(test-check "3rd example"
  (run 1 (q) (L '(All x are y) '((All y are x) (Least as many y x)) q))
  '((((All y are x) (Least as many y x)) => (All x are y))))

(test-check "4th example"
  (run 1 (q) (L '(Some x are x) '((Some y are y) (Least as many x y)) q))
  '((((Some y are y) (Least as many x y)) => (Some x are x))))

(test-check "5th example"
  (run 1 (q) (L '(Least as many x y) '((No y are y)) q))
  '((((No y are y)) => (Least as many x y))))

(test-check "Jason's Example"
  (run 1 (q) (L '(Least as many x z) '((All y are x) (Least as many y z)) q))
  '((((((All y are x)) => (Least as many x y)) (Least as many y z)) => (Least as many x z))))


(test-check "Example 14"
  (run 1 (o) (L `(No p are q) `((All q are w) (All p are v) (No v are w)) o))
  '((((All p are v)
    (((((All q are w) (((No v are w)) => (No w are v)))
        =>
        (No q are v)))
      =>
      (No v are q)))
   =>
   (No p are q))))
