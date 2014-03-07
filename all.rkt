#lang racket
(require "pmatch.rkt")
(require cKanren)
(require cKanren/tree-unify)
(require cKanren/attributes)
(require cKanren/neq)
(provide (all-defined-out))

(define allo
  (lambda (exp tr)
    (fresh (a b)
      (== `(All ,a are ,b) exp)      
      (conde
	((== a b) (== exp tr))
	((fresh (c r1 r2)
	   (== `((,r1 ,r2) => ,exp) tr)
	   (allo `(All ,a are ,c) r1)
	   (allo `(All ,c are ,b) r2)))))))