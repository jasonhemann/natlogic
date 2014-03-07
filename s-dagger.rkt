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
        [(== a x)
         (fresh (b c)
           (noun b)
           (noun c)
           (conde
             ((== `(All ,b are ,c) x))
             ((== `(Some ,b are ,c) x))))]
        [(=/= a x) (membero x d)]))))

(define noun
  (lambda (n)
    (conde
      ((symbol n))
      ((fresh (x)
	 (symbol x)
	 (== `(not ,x) n))))))

(define negate
  (lambda (n o)
    (conde
      ((symbol n)
       (== `(not ,n) o))
      ((symbol o)
       (== `(not ,o) n)))))

(define Sd
  (lambda (exp prems tr)
    (fresh (a b)
      (noun a)
      (noun b)
      (conde
	((membero exp prems) (== exp tr))
	((== `(All ,a are ,b) exp)
	 (conde
	   ((== a b) (== exp tr)) ;; Axiom
	   ((fresh (c r1 r2) ;; Barbara
	      (== `((,r1 ,r2) => ,exp) tr)
	      (=/= a b) ;; This shouldn't be, but is for performance reasons ....
	      (noun c)
	      (Sd `(All ,a are ,c) prems r1)
	      (Sd `(All ,c are ,b) prems r2)))
	   ((fresh (a-not r1) ;; Zero
	      (== `((,r1) => ,exp) tr)
	      (negate a a-not)
	      (Sd `(All ,a are ,a-not) prems r1)))
	   ((fresh (b-not r1) ;; One
	      (== `((,r1) => ,exp) tr)
	      (negate b b-not)
	      (Sd `(All ,b-not are ,b) prems r1)))
	   ((fresh (b-not a-not r1) ;; Antitone
	      (== `((,r1) => ,exp) tr)
	      (negate b b-not)
	      (negate a a-not)
	      (Sd `(All ,b-not are ,a-not) prems r1)))
	   ((fresh (p q q-not r1 r2) ;; X1
	      (== `((,r1 ,r2) => ,exp) tr)
              (negate q q-not)
	      (noun p)
	      (Sd `(All ,p are ,q) prems r1)
	      (Sd `(Some ,p are ,q-not) prems r2)))))
	((== `(Some ,a are ,b) exp)
	 (conde
	   ((== a b) ;; Some1
	    (fresh (r1 c)
	      (== `((,r1) => ,exp) tr)
	      (noun c)
	      (Sd `(Some ,a are ,c) prems r1)))
	   ((fresh (r1) ;; Some2
	      (== `((,r1) => ,exp) tr)
	      (Sd `(Some ,b are ,a) prems r1)))
	   ((fresh (c r1 r2) ;; Darii
	      (== `((,r1 ,r2) => ,exp) tr)
	      (noun c)
	      (Sd `(All ,c are ,b) prems r1)
	      (Sd `(Some ,a are ,c) prems r2)))
	   ((fresh (p q q-not r1 r2) ;; X2
	      (== `((,r1 ,r2) => ,exp) tr)
	      (negate q q-not)
	      (noun p)
	      (Sd `(All ,p are ,q) prems r1)
	      (Sd `(Some ,p are ,q-not) prems r2)))))))))

(test-check "negate"
  (run 3 (q) (fresh (a b) (negate a b) (== `(,a ,b) q)))
  '(((_.0 (not _.0)) : (symbol _.0)) (((not _.0) _.0) : (symbol _.0))))

(test-check "noun"
  (run 1 (o) (noun o))
  '((_.0 : (symbol _.0))))

(test-check "2 noun"
  (run 2 (o) (noun o))
  '((_.0 : (symbol _.0)) ((not _.0) : (symbol _.0))))

(test-check "Example 13"
  (run 1 (o) (Sd `(Some p are q) `((All n are q) (All n are p) (Some n are n)) o))
  '((((All n are q)
      (((((All n are p) (Some n are n)) => (Some n are p)))
       =>
       (Some p are n)))
     =>
     (Some p are q))))

(test-check "Celarent"
  (run 1 (q) (Sd '(All r are (not q)) '((All p are (not q)) (All r are p)) q))
  '((((All r are p) (All p are (not q)))
     =>
     (All r are (not q)))))

(test-check "Ferio"
  (run 1 (q) (Sd '(Some r are (not q)) '((All p are (not q)) (Some r are p)) q))
  '((((All p are (not q)) (Some r are p)) => (Some r are (not q)))))

(test-check "Cesare"
  (run 1 (q) (Sd '(All r are (not p)) '((All p are (not q)) (All r are q)) q))
  '((((All r are q)
      (((All p are (not q))) => (All q are (not p))))
     =>
     (All r are (not p)))))

(test-check "Camestres"
  (run 1 (q) (Sd '(All r are (not p)) '((All p are q) (All r are (not q))) q))
  '((((All r are (not q))
      (((All p are q)) => (All (not q) are (not p))))
     =>
     (All r are (not p)))))

(test-check "Festino"
  (run 1 (q) (Sd '(Some r are (not p)) '((All p are (not q)) (Some r are q)) q))
  '((((((All p are (not q))) => (All q are (not p)))
      (Some r are q))
     =>
     (Some r are (not p)))))

(test-check "Baroco"
  (run 1 (q) (Sd '(Some r are (not p)) '((All p are q) (Some p are (not q))) q))
  '((((All p are q) (Some p are (not q)))
     =>
     (Some r are (not p)))))

(test-check "Barbara"
  (run 1 (o) (Sd '(All r are q) '((All p are q) (All r are p)) o))
  '((((All r are p) (All p are q)) => (All r are q))))

(test-check "Darii"
  (run 1 (o) (Sd '(Some r are q) '((All p are q) (Some r are p)) o))
  '((((All p are q) (Some r are p)) => (Some r are q))))

(test-check "Axiom"
  (run 1 (q) (Sd '(All p are p) '() q))
  '((All p are p)))

(test-check "Some1"
  (run 1 (q) (Sd '(Some p are p) '((Some p are q)) q))
  '((((Some p are q)) => (Some p are p))))

(test-check "Some2"
  (run 1 (q) (Sd '(Some q are p) '((Some p are q)) q))
  '((((Some p are q)) => (Some q are p))))

(test-check "Zero"
  (run 1 (q) (Sd '(All q are p) '((All q are (not q))) q))
  '((((All q are (not q))) => (All q are p))))

(test-check "One"
  (run 1 (q) (Sd '(All p are q) '((All (not q) are q)) q))
  '((((All (not q) are q)) => (All p are q))))

(test-check "Antitone"
  (run 1 (q) (Sd '(All p are (not q)) '((All q are (not p))) q))
  '((((All q are (not p))) => (All p are (not q)))))
  
(test-check "X1"
  (run 1 (q) (fresh (a b)
               (Sd `(All ,a are ,b) '((All p are q) (Some p are (not q))) q)))
  '(((All _.0 are _.0) : (symbol _.0))))

(test-check "X2"
  (run 1 (q) (fresh (a b)
               (Sd `(Some ,a are ,b) '((All p are q) (Some p are (not q))) q)))
  '((Some p are (not q))))
  
(test-check "X1-2"
  (run 2 (q) (fresh (a b)
               (Sd `(All ,a are ,b) '((All p are q) (Some p are (not q))) q)))
  '(((All _.0 are _.0) : (symbol _.0)) (All p are q)))

(test-check "X2-2"
  (run 2 (q) (fresh (a b)
               (Sd `(Some ,a are ,b) '((All p are q) (Some p are (not q))) q)))
  '((Some p are (not q)) (Some p are (not q))))

;; Multiple completions
(test-check "X1-3"
  (run 10 (q) (fresh (a b)
               (Sd `(All ,a are ,b) '((All p are q) (Some p are (not q))) q)))
  '(((All _.0 are _.0) : (symbol _.0))
    (All p are q)
    ((All (not _.0) are (not _.0)) : (symbol _.0))
    (All p are q)
    (All p are q)
    (All p are q)
    (((All p are p) (All p are q)) => (All p are q))
    (((All p are p) (All p are q)) => (All p are q))
    (((All p are p) (All p are q)) => (All p are q))
    (((All p are p) (All p are q)) => (All p are q))))

;; Multiple completions
(test-check "X2-3"
  (run 10 (q) (fresh (a b)
               (Sd `(Some ,a are ,b) '((All p are q) (Some p are (not q))) q)))
  '((Some p are (not q))
    (Some p are (not q))
    (Some p are (not q))
    (Some p are (not q))
    (((Some p are (not q))) => (Some p are p))
    (((Some p are (not q))) => (Some (not q) are p))
    (((Some p are (not q))) => (Some p are p))
    (((Some p are (not q))) => (Some (not q) are p))
    (((Some p are (not q))) => (Some p are p))
    (((Some p are (not q))) => (Some (not q) are p))))

(test-check "Example 15"
  (run 1 (q) (Sd '(All x are z)
                        '((All (not y) are p)
                          (All p are q)
                          (All q are y)
                          (All y are p)
                          (All q are z))
                        q))
  '((((((((All (not y) are p) (((All p are q) (All q are y)) => (All p are y))) => (All (not y) are y))) => (All x are y)) (((All y are p) (((All p are q) (All q are z)) => (All p are z))) => (All y are z))) => (All x are z))))

(test-check "Exercise 12"
  (run 1 (q) (Sd '(All x are p)
                        '((All y are p) (All (not y) are p))
                        q))
  '((((((((All (not y) are p)) => (All (not p) are y))
      (All y are p))
     =>
     (All (not p) are p)))
   =>
   (All x are p))))

(test-check "Exercise 14-5"
  (run 1 (q) (Sd '(All q are (not q))
                        '((All q are n)
                          (All q are (not n)))
                        q))
  '((((All q are (not n))
      (((All q are n)) => (All (not n) are (not q))))
     =>
     (All q are (not q)))))

(test-check "Similar to Exercise 13"
  (run 1 (q) (Sd '(Some p are (not q))
                 '((All y are p)
                   (All (not y) are p)
                   (All q are z)
                   (Some y are (not z)))
                 q))
  '((((((All q are z)) => (All (not z) are (not q)))
      (((((All y are p)
          (((Some y are (not z))) => (Some (not z) are y)))
         =>
         (Some (not z) are p)))
       =>
       (Some p are (not z))))
     =>
     (Some p are (not q)))))

;; (test-check "Similar to Exercise 13"
;;   (run 1 (q) (Sd '(Some p are (not q))
;;                  '((All y are p)
;;                    (All (not y) are p)
;;                    (All q are z)
;;                    (Some x are (not z)))
;;                  q))
;;   'takes-quite-some-time)

