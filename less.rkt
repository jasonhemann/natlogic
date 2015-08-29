#lang racket
(require "mk.rkt")
(require "matche.rkt")
(provide (combine-out (all-defined-out) (all-from-out "mk.rkt")))

(define (membero x ls)
  (fresh (a d)
    (== `(,a . ,d) ls)
    (conde
      ((== a x))
      ((=/= a x) (membero x d)))))

(define-syntax double-prim-term
  (syntax-rules ()
     [(_ logic proof φ Γ e1 e2 vars ...)
      (fresh (vars ... prim1 prim2 proof1 proof2)
        (== `((,proof1 ,proof2) => ,φ) proof)
        (== prim1 e1)
        (== prim2 e2)
        (logic prim1 Γ proof1)
        (logic prim2 Γ proof2))]))

(define-syntax double-prim-extra-term
  (syntax-rules ()
     [(_ logic proof φ Γ e1 e2 (e ...) vars ...)
      (fresh (vars ... prim1 prim2 proof1 proof2)
        (== `((,proof1 ,proof2) => ,φ) proof)
        e ...
        (== prim1 e1)
        (== prim2 e2)
        (logic prim1 Γ proof1)
        (logic prim2 Γ proof2))]))

(define-syntax single-prim-term
  (syntax-rules ()
     [(_ logic proof φ Γ e1 vars ...)
      (fresh (vars ... prim1 proof1)
        (== `((,proof1) => ,φ) proof)
        (== prim1 e1)
        (logic prim1 Γ proof1))]))

(define-syntax single-prim-extra-term
  (syntax-rules ()
     [(_ logic proof φ Γ e1 (e ...) vars ...)
      (fresh (vars ... prim1 proof1)
        (== `((,proof1) => ,φ) proof)
        e ...
        (== prim1 e1)
        (logic prim1 Γ proof1))]))

(define (logic φ Γ proof)
  (matche φ
    [(∀ ,a ,a) (== a a)] ;; Axiom
    [(∀, n, q) ;; Barbara
     (double-prim-term logic proof φ Γ `(∀ ,n ,p) `(∀ ,p ,q) p)] 
    [(∃ ,p ,p) ;; ∃
     (single-prim-term logic proof φ Γ `(∃ ,p ,q) q)] 
    [(∃ ,p ,q) ;; Conversion
     (single-prim-term logic proof φ Γ `(∃ ,q ,p))]
    [(∃ ,p ,q) ;; Darii
     (double-prim-term logic proof φ Γ `(∃ ,p ,n) `(∀ ,n ,q) n)]
    [(∀ ,q ,p) ;; Card-Mix
     (double-prim-term logic proof φ Γ `(∀ ,p ,q) `(∃≥ ,p ,q))]
    [(∃≥ ,q ,p) ;; Subset-Size
     (single-prim-term logic proof φ Γ `(∀ ,p ,q))]
    [(∃≥ ,n ,q) ;; Card-Trans
     (double-prim-term logic proof φ Γ `(∃≥ ,n ,p) `(∃≥ ,p ,q) p)]
    [(∃ ,q ,q) ;; Card-E 
     (double-prim-term logic proof φ Γ `(∃ ,p ,p) `(∃≥ ,q ,p) p)]
    [(∃≥ ,p ,q) ;; More-At-Last
     (single-prim-term logic proof φ Γ `(∃> ,p ,q))]
    [(∃> ,n ,q) ;; More-Left
     (double-prim-term logic proof φ Γ `(∃> ,n ,p) `(∃≥ ,p ,q) p)]
    [(∃> ,n ,q) ;; More-Right
     (double-prim-term logic proof φ Γ `(∃≥ ,n ,p) `(∃> ,p ,q) p)]
    [,x (membero x Γ) (== proof `(,x in-Γ))]  ;; Lookup
    [,x ;; X
     (double-prim-term logic proof φ Γ `(∃≥ ,p ,q) `(∃≥ ,q ,p) p q)]))

;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; ;; One
;; ∀ ,q, p
;; (fresh (np)
;;   (== np (neg p))
;;   (== prim `(∀ ,np ,p)))
;; 
;; ;; More
;; ∃> ,p ,q
;; (fresh (nq)
;;   (== nq (neg q))
;;   (== prim1 `(∀ ,q ,p))
;;   (== prim2 `(∃ ,p ,nq)))
;; 
;; ;; More-∃
;; ∃ ,p ,nq
;; (fresh (q)
;;   (== q (neg nq))
;;   (== prim `(∃> ,p ,q)))
;;
;; ELIDED, FINISH FOR REPO
