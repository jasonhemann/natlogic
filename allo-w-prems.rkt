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
        [(== a x)]
        [(=/= a x) (membero x d)]))))

(define allo
  (lambda (exp prems tr)
    (fresh (a b)
      (== `(All ,a are ,b) exp)
      (conde
        ((== a b) (== exp tr))
        ((membero exp prems) (== exp tr))
        ((fresh (c r1 r2)
	   (== `((,r1 ,r2) => ,exp) tr)
	   (allo `(All ,a are ,c) prems r1)
	   (allo `(All ,c are ,b) prems r2)))))))

(test-check "allo-w-prems 1"
  (run 1 (q) (allo '(All a are a) '()  q))
  '((All a are a)))

(test-check "allo-w-prems 2"
  (run 2 (q) (allo '(All a are a) '() q))
  '((All a are a)
    (((All a are a) (All a are a)) => (All a are a))))

(test-check "allo-w-prems 3"
  (run 5 (q) (allo `(All a are b) `((All a are b)) q))
  '((All a are b)
    (((All a are a) (All a are b)) => (All a are b))
    (((All a are b) (All b are b)) => (All a are b))
    (((All a are a)
      (((All a are a) (All a are b)) => (All a are b)))
     =>
     (All a are b))
    (((All a are a)
      (((All a are b) (All b are b)) => (All a are b)))
     =>
     (All a are b))))
