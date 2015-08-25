
(define-syntax double-prim-term
  (syntax-rules ()
     [(_ logic proof phi gamma e1 e2 vars ...)
      (fresh (vars ... prim1 prim2 proof1 proof2)
        (== `((,proof1 ,proof2) => ,phi) proof)
        (== prim1 e1)
        (== prim2 e2)
        (logic prim1 gamma proof1)
        (logic prim2 gamma proof2))]))

(define-syntax double-prim-extra-term
  (syntax-rules ()
     [(_ logic proof phi gamma e1 e2 (e ...) vars ...)
      (fresh (vars ... prim1 prim2 proof1 proof2)
        (== `((,proof1 ,proof2) => ,phi) proof)
        e ...
        (== prim1 e1)
        (== prim2 e2)
        (logic prim1 gamma proof1)
        (logic prim2 gamma proof2))]))

(define-syntax single-prim-term
  (syntax-rules ()
     [(_ logic proof phi gamma e1 vars ...)
      (fresh (vars ... prim1 proof1)
        (== `((,proof1) => ,phi) proof)
        (== prim1 e1)
        (logic prim1 gamma proof1))]))

(define-syntax single-prim-extra-term
  (syntax-rules ()
     [(_ logic proof phi gamma e1 (e ...) vars ...)
      (fresh (vars ... prim1 proof1)
        (== `((,proof1) => ,phi) proof)
        e ...
        (== prim1 e1)
        (logic prim1 gamma proof1))]))

(define logic
  (lambda (phi gamma proof)
    (matche phi
      ;; Axiom
      [(All ,a ,a) (== a a)]
      ;; Barbara
      [(All, n, q)
       (double-prim-term logic proof phi gamma `(All ,n ,p) `(All ,p ,q) p)]
      ;; Some
      [(Some ,p ,p) 
       (single-prim-term logic proof phi gamma `(Some ,p ,q) q)]
      ;; Conversion
      [(Some ,p ,q)
       (single-prim-term logic proof phi gamma `(Some ,q ,p))]
      ;; Darii
      [(Some ,p ,q)
       (double-prim-term logic proof phi gamma `(Some ,p ,n) `(All ,n ,q) n)]
      ;; Card-Mix
      [(All ,q ,p)
       (double-prim-term logic proof phi gamma `(All ,p ,q) `(Least ,p ,q))]
      ;; Subset-Size
      [(Least ,q ,p)
       (single-prim-term logic proof phi gamma `(All ,p ,q))]
      ;; Card-Trans
      [(Least ,n ,q)
       (double-prim-term logic proof phi gamma `(Least ,n ,p) `(Least ,p ,q) p)]
      ;; Card-E 
      [(Some ,q ,q)
       (double-prim-term logic proof phi gamma `(Some ,p ,p) `(Least ,q ,p))]
      ;; More-At-Last
      [(Least ,p ,q)
       (single-prim-term logic proof phi gamma `(Less ,p ,q))]
      ;; More-Left
      [(Less ,n ,q)
       (double-prim-term logic proof phi gamma `(Less ,n ,p) `(Least ,p ,q) p)]
      ;; More-Right
      [(Less ,n ,q)
       (double-prim-term logic proof phi gamma `(Least ,n ,p) `(Less ,p ,q) p)]
      ;; X
      [,x
       (double-prim-term logic proof phi gamma `(Least ,p ,q) `(Least ,q ,p) p q)]))

;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; ;; One
;; All ,q, p
;; (fresh (np)
;;   (== np (neg p))
;;   (== prim `(All ,np ,p)))
;; 
;; ;; More
;; Less ,p ,q
;; (fresh (nq)
;;   (== nq (neg q))
;;   (== prim1 `(All ,q ,p))
;;   (== prim2 `(Some ,p ,nq)))
;; 
;; ;; More-Some
;; Some ,p ,nq
;; (fresh (q)
;;   (== q (neg nq))
;;   (== prim `(Less ,p ,q)))
;;
;; ELIDED, FINISH FOR REPO
