#lang racket
(require "pmatch.rkt")
(require cKanren)
(require cKanren/tree-unify)
(require cKanren/attributes)
(require cKanren/neq)
(provide (all-defined-out))

;; Key
;; 0 Bottom
;; -1 Constant
;; -2 Unary atom
;; -3 Binary atom
;; -4 Variable

;; (define-syntax test-check
;;   (syntax-rules ()
;;     ((_ title tested-expression expected-result)
;;      (begin
;;        (printf "Testing ~s\n" title)
;;        (let* ((expected expected-result)
;;               (produced tested-expression))
;;          (or (equal? expected produced)
;;              (error 'test-check
;;                "Failed: ~a~%Expected: ~a~%Computed: ~a~%"
;;                'tested-expression expected produced)))))))

(define constanto
  (lambda (c)
    (fresh (sym)
      (symbol sym)
      (== c `(-1 . ,sym)))))

(define make-constant
  (lambda (sym)
    `(-1 . ,sym)))

(define un-atomo
  (lambda (a)
    (fresh (sym)
      (== a `(-2 . ,sym))
      (symbol sym))))

(define make-un-atom
  (lambda (sym)
    `(-2 . ,sym)))

;; Notice, we don't prevent unary and binary atoms from being using the
;; same symbol. I believe there are examples where this is a feature, but
;; right now none are coming to mind.

(define bin-atomo
  (lambda (a)
    (fresh (sym)
      (symbol sym)
      (== a `(-3 . ,sym)))))

(define make-bin-atom
  (lambda (sym)
    `(-3 . ,sym)))

(define un-literalo
  (lambda (l)
    (conde
      ((un-atomo l))
      ((fresh (a)
         (== l `(not ,a))
         (un-atomo a))))))

(define negate-un-literal
  (lambda (n)
    (pmatch n
      (`(not (-2 . ,x)) (guard (symbol? x))
       `(-2 . ,x))
      (`(-2 . ,x) (guard (symbol? x))
       `(not (-2 . ,x))))))

(define bin-literalo
  (lambda (l)
    (conde
      ((bin-atomo l))
      ((fresh (a)
         (bin-atomo a)
         (== l `(not ,a)))))))

(define negate-bin-literal
  (lambda (n)
    (pmatch n
      (`(not (-3 . ,x)) (guard (symbol? x))
       `(-3 . ,x))
      (`(-3 . ,x) (guard (symbol? x))
       `(not (-3 . ,x))))))

(define set-termo
  (lambda (s)
    (conde
      ((un-literalo s))
      ((fresh (c r)
         (conde
           ((== s `(exists ,c ,r));; 3xists
            (set-termo c)
            (bin-literalo r)) 
           ((== s `(forall ,c ,r));; 4-all
            (set-termo c)
            (bin-literalo r))))))))

(define sentenceo
  (lambda (s)
    (conde
      ((fresh (c d)
         (== s `(exists ,c ,d))
         (set-termo c)
         (set-termo d)))
      ((fresh (c d)
         (== s `(forall ,c ,d))
         (set-termo c)
         (set-termo d)))
      ((fresh (c j)
         (== s `(,c ,j))
         (set-termo c)
         (constanto j)))
      ((fresh (r j k)
         (== s `(,r ,j ,k))
         (bin-literalo r)
         (constanto j)
         (constanto k))))))

(define variableo
  (lambda (v)
    (fresh (sym)
      (symbol sym)
      (== v `(-4 . ,sym)))))

(define make-variable
  (lambda (sym)
    `(-4 . ,sym)))

(define ind-termo
  (lambda (t)
    (conde
      ((variableo t))
      ((constanto t)))))

(define bottomo
  (lambda (n)
    (== n '(0 . 0))))

(define bottom '(0 . 0))

(define ino
  (lambda (x ls)
    (fresh (a d)
      (== ls `(,a . ,d))
      (conde
        ((== x a))
        ((=/= x a) (ino x d))))))

(define !ino
  (lambda (x ls)
    (conde
      ((== '() ls))
      ((fresh (a d)
         (== ls `(,a . ,d))
         (=/= x a)
         (!ino x d))))))

(define flat-uniono
  (lambda (s1 s2 s3)
    (conde
      ((== '() s1) (== s2 s3))
      ((fresh (a d)
         (== s1 `(,a . ,d))
         (conde
           ((ino a s2) (flat-uniono d s2 s3))
           ((!ino a s2)
            (fresh (res)
              (== `(,a . ,res) s3)
              (flat-uniono d s2 res)))))))))

(define gen-sentenceo
  (lambda (g)
    (conde
      ((bottomo g))
      ((fresh (c x)
         (== g `(,c ,x))
         (set-termo c)
         (variableo x)))
      ((fresh (r x y)
         (== g `(,r ,x ,y))
         (variableo x)
         (variableo y)))
      ((sentenceo g)))))

(define all-sentenceo
  (lambda (prms)
    (conde
      ((== '() prms))
      ((fresh (a d)
         (== prms `(,a . ,d))
         (sentenceo a)
         (all-sentenceo d))))))

(define negateo
  (lambda (e ne)
    (conde
      ((== ne `(not ,e))
       (conde
         ((un-atomo e))
         ((bin-atomo e))))
      ((fresh (e^)
         (== e `(not ,e^))
         (== ne e^)
         (conde
           ((un-atomo e^))
           ((bin-atomo e^)))))
      ((fresh (l r)
         (== e `(exists ,l ,r))
         (un-literalo l)
         (bin-literalo r)
         (fresh (res)
           (== ne `(forall ,l ,res))
           (negateo r res))))
      ((fresh (l r)
         (== e `(forall ,l ,r))
         (un-literalo l)
         (bin-literalo r)
         (fresh (res)
           (== ne `(exists ,l ,res))
           (negateo r res))))
      ((fresh (c d)
         (== e `(exists ,c ,d))
         (set-termo d)
         (set-termo c)
         (fresh (res)
           (== ne `(forall ,c ,res))
           (negateo d res))))
      ((fresh (c d)
         (== e `(forall ,c ,d))
         (set-termo d)
         (set-termo c)
         (fresh (res)
           (== ne `(exists ,c ,res))
           (negateo d res))))
      ((fresh (c x/j)
         (== e `(,c ,x/j))
         (conde
           ((variableo x/j))
           ((constanto x/j)))
         (set-termo c)
         (fresh (res)
           (== ne `(,res ,x/j))
           (negateo c res))))
      ((fresh (r x/j y/k)
         (== e `(,r ,x/j ,y/k))
         (bin-literalo r)
         (conde
           ((variableo x/j) (variableo y/k))
           ((constanto x/j) (constanto y/k)))
         (fresh (res)
           (== ne `(,res ,x/j ,y/k))
           (negateo r res))))
      ((bottomo e) (== `(not ,e) ne))
      ((bottomo ne) (== `(not ,ne) e)))))

(define !-o
  (lambda (thm prms tr)
    (conde
      ((ino thm prms) (== tr thm) (gen-sentenceo thm))
      ((!ino thm prms)
       (conde
         ((fresh (d t) ;; rule 1
            (== thm `(,d ,t))
            (ind-termo t)
            (set-termo d)
            (fresh (c tr-1 tr-2)
              (== tr `((,tr-1 ,tr-2) => ,thm))
              (set-termo c)           
              (!-o `(,c ,t) prms tr-1)
              (!-o `(forall ,c ,d) prms tr-2))))
         ((fresh (r t u) ;; rule 2
            (== thm `(,r ,t ,u))
            (bin-literalo r)
            (ind-termo t)
            (ind-termo u)
            (fresh (c tr-1 tr-2)
              (set-termo c)
              (== tr `((,tr-1 ,tr-2) => ,thm))
              (!-o `(,c ,u) prms tr-1)
              (!-o `((forall ,c ,r) ,t) prms tr-2))))
         ((fresh (c d) ;; rule 3
            (== thm `(exists ,c ,d))
            (set-termo c)
            (set-termo d)
            (fresh (t tr-1 tr-2)
              (ind-termo t)
              (== tr `((,tr-1 ,tr-2) => ,thm))
              (!-o `(,c ,t) prms tr-1)
              (!-o `(,d ,t) prms tr-2))))
         ((fresh (c r t) ;; rule 4
            (== thm `((exists ,c ,r) ,t))
            (set-termo c)
            (bin-literalo r)
            (ind-termo t)
            (fresh (u tr-1 tr-2)
              (ind-termo u)
              (== tr `((,tr-1 ,tr-2) => ,thm))
              (!-o `(,r ,t ,u) prms tr-1)
              (!-o `(,c ,u) prms tr-2))))
         ((fresh (c d) ;; rule 5
            (== thm `(forall ,c ,d))
            (set-termo c)
            (set-termo d)
            (fresh (x tr-1 res)
              (variableo x)
              (== tr `((,tr-1) => ,thm))
              (flat-uniono `((,c ,x)) prms res)
              (!-o `(,d ,x) res tr-1))))
         ((fresh (c r t) ;; rule 6
            (== thm `((forall ,c ,r) ,t))
            (set-termo c)
            (bin-literalo r)
            (ind-termo t)
            (fresh (x tr-1 res)
              (variableo x)
              (== tr `((,tr-1) => ,thm))
              (flat-uniono `((,c ,x)) prms res)
              (!-o `(,r ,t ,x) res tr-1))))
         ((gen-sentenceo thm)
          (fresh (c d)
            (set-termo c)
            (set-termo d)
            (fresh (tr-1)
              (!-o `(exists ,c ,d) prms tr-1)
              (fresh (x prms^)
                (variableo x)
                (flat-uniono `((,c ,x)) prms prms^)
                (fresh (prms^^)
                  (flat-uniono `((,d ,x)) prms^ prms^^)
                  (fresh (tr-2)
                    (== tr `((,tr-1 ,tr-2) => ,thm))
                    (!-o thm prms^^ tr-2)))))))
         ((gen-sentenceo thm)
          (fresh (c r t)
            (set-termo c)
            (bin-literalo r)
            (ind-termo t)            
            (fresh (tr-1)
              (!-o `((exists ,c ,r) ,t) prms tr-1)
              (fresh (x prms^)
                (variableo x)
                (flat-uniono `((,c ,x)) prms prms^)
                (fresh (prms^^)
                  (flat-uniono `((,r ,t ,x)) prms^ prms^^)
                  (fresh (tr-2)
                    (== tr `((,tr-1 ,tr-2) => ,thm))
                    (!-o thm prms^^ tr-2)))))))
         ((bottomo thm) ;; rule 9
          (fresh (e)
            (gen-sentenceo e)
            (fresh (ne)
              (negateo e ne)
              (fresh (tr-1 tr-2)
                (== tr `((,tr-1 ,tr-2) => ,thm))
                (!-o e prms tr-1)
                (!-o ne prms tr-2)))))
         ((sentenceo thm) ;; rule 10
          (fresh (nthm)
            (negateo thm nthm)
            (fresh (res)
              (flat-uniono `(,nthm) prms res)
              (fresh (tr-1 b)
                (== tr `((,tr-1) => ,thm))
                (bottomo b)
                (!-o b res tr-1))))))))))

;; (load "test-w-vars.ss")


