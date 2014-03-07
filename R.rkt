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

(define-attribute unary-atomo
  #:satisfied-when symbol?
  #:incompatible-attributes (number bin-atomo))

(define-attribute bin-atomo
  #:satisfied-when string?
  #:incompatible-attributes (number unary-atomo))

(define symbol-or-string?
  (lambda (s)
    (or (symbol? s) (string? s))))

(define-attribute un-literalo
  #:satisfied-when symbol-or-string?
  #:incompatible-attributes (number))

(define-constraint-interaction
  [(un-literalo x) (unary-atomo x)] => [(unary-atomo x)])

(define-constraint-interaction
  [(un-literalo x) (bin-atomo x)] => [(bin-atomo x)])

(test-check "un-literalo"
  (run 100 (q) (un-literalo q))
  '((_.0 : (un-literalo _.0))))

(define negate-un-literalo
  (lambda (l o)
    (conde
      ((unary-atomo l)
       (== o `(not ,l)))
      ((== l `(not ,o))
       (unary-atomo o)))))

(define bin-literalo
  (lambda (l)
    (conde
      ((bin-atomo l))
      ((fresh (a)
         (bin-atomo a)
         (== l `(not ,a)))))))

(test-check "bin-literalo"
  (run 100 (q) (bin-literalo q))
  '((_.0 : (bin-atomo _.0)) ((not _.0) : (bin-atomo _.0))))

(define negate-bin-literalo
  (lambda (l o)
    (conde
      ((bin-atomo l)
       (== `(not ,l) o))
      ((bin-atomo o)
       (== l `(not ,o))))))

(test-check "negate-bin-literalo"
  (run 100 (q) (fresh (a b) (negate-bin-literalo a b) (== `(,a ,b) q)))
  '(((_.0 (not _.0)) : (bin-atomo _.0)) (((not _.0) _.0) : (bin-atomo _.0))))

(define set-termo
  (lambda (s)
    (conde
      ((un-literalo s))
      ((fresh (p r)
         (conde
           ((== s `(exists ,p ,r))
            (un-literalo p)
            (bin-literalo r)) 
           ((== s `(forall ,p ,r))
            (un-literalo p)
            (bin-literalo r))))))))

(test-check "set-termo"
  (run 100 (q) (set-termo q))
  '((_.0 : (unary-atomo _.0))
    ((not _.0) : (unary-atomo _.0))
    ((exists _.0 _.1) : (bin-atomo _.1) (unary-atomo _.0))
    ((forall _.0 _.1) : (bin-atomo _.1) (unary-atomo _.0))
    ((exists (not _.0) _.1) : (bin-atomo _.1) (unary-atomo _.0))
    ((forall (not _.0) _.1) : (bin-atomo _.1) (unary-atomo _.0))
    ((exists _.0 (not _.1)) : (bin-atomo _.1) (unary-atomo _.0))
    ((forall _.0 (not _.1)) : (bin-atomo _.1) (unary-atomo _.0))
    ((exists (not _.0) (not _.1)) : (bin-atomo _.1) (unary-atomo _.0))
    ((forall (not _.0) (not _.1)) : (bin-atomo _.1) (unary-atomo _.0))))

(define sentenceo
  (lambda (s)
    (conde
      ((fresh (p c)
         (== `(exists ,p ,c) s)
         (un-literalo p)
         (set-termo c)))
      ((fresh (p c)
         (== `(forall ,p ,c) s)
         (un-literalo p)
         (set-termo c))))))

(test-check "sentenceo"
  (run 100 (q) (sentenceo q))
  '(((exists _.0 _.1) : (unary-atomo _.0 _.1))
    ((forall _.0 _.1) : (unary-atomo _.0 _.1))
    ((exists (not _.0) _.1) : (unary-atomo _.0 _.1))
    ((forall (not _.0) _.1) : (unary-atomo _.0 _.1))
    ((exists _.0 (not _.1)) : (unary-atomo _.0 _.1))
    ((forall _.0 (not _.1)) : (unary-atomo _.0 _.1))
    ((exists (not _.0) (not _.1)) : (unary-atomo _.0 _.1))
    ((forall (not _.0) (not _.1)) : (unary-atomo _.0 _.1))
    ((exists _.0 (exists _.1 _.2)) : (bin-atomo _.2) (unary-atomo _.0 _.1))
    ((forall _.0 (exists _.1 _.2)) : (bin-atomo _.2) (unary-atomo _.0 _.1))
    ((exists _.0 (forall _.1 _.2)) : (bin-atomo _.2) (unary-atomo _.0 _.1))
    ((forall _.0 (forall _.1 _.2)) : (bin-atomo _.2) (unary-atomo _.0 _.1))
    ((exists (not _.0) (exists _.1 _.2)) : (bin-atomo _.2) (unary-atomo _.0 _.1))
    ((forall (not _.0) (exists _.1 _.2)) : (bin-atomo _.2) (unary-atomo _.0 _.1))
    ((exists (not _.0) (forall _.1 _.2)) : (bin-atomo _.2) (unary-atomo _.0 _.1))
    ((forall (not _.0) (forall _.1 _.2)) : (bin-atomo _.2) (unary-atomo _.0 _.1))
    ((exists _.0 (exists (not _.1) _.2)) : (bin-atomo _.2) (unary-atomo _.0 _.1))
    ((forall _.0 (exists (not _.1) _.2)) : (bin-atomo _.2) (unary-atomo _.0 _.1))
    ((exists _.0 (forall (not _.1) _.2)) : (bin-atomo _.2) (unary-atomo _.0 _.1))
    ((forall _.0 (forall (not _.1) _.2)) : (bin-atomo _.2) (unary-atomo _.0 _.1))
    ((exists (not _.0) (exists (not _.1) _.2))
     :
     (bin-atomo _.2)
     (unary-atomo _.0 _.1))
    ((forall (not _.0) (exists (not _.1) _.2))
     :
     (bin-atomo _.2)
     (unary-atomo _.0 _.1))
    ((exists _.0 (exists _.1 (not _.2))) : (bin-atomo _.2) (unary-atomo _.0 _.1))
    ((forall _.0 (exists _.1 (not _.2))) : (bin-atomo _.2) (unary-atomo _.0 _.1))
    ((exists (not _.0) (forall (not _.1) _.2))
     :
     (bin-atomo _.2)
     (unary-atomo _.0 _.1))
    ((forall (not _.0) (forall (not _.1) _.2))
     :
     (bin-atomo _.2)
     (unary-atomo _.0 _.1))
    ((exists _.0 (forall _.1 (not _.2))) : (bin-atomo _.2) (unary-atomo _.0 _.1))
    ((forall _.0 (forall _.1 (not _.2))) : (bin-atomo _.2) (unary-atomo _.0 _.1))
    ((exists (not _.0) (exists _.1 (not _.2)))
     :
     (bin-atomo _.2)
     (unary-atomo _.0 _.1))
    ((forall (not _.0) (exists _.1 (not _.2)))
     :
     (bin-atomo _.2)
     (unary-atomo _.0 _.1))
    ((exists (not _.0) (forall _.1 (not _.2)))
     :
     (bin-atomo _.2)
     (unary-atomo _.0 _.1))
    ((forall (not _.0) (forall _.1 (not _.2)))
     :
     (bin-atomo _.2)
     (unary-atomo _.0 _.1))
    ((exists _.0 (exists (not _.1) (not _.2)))
     :
     (bin-atomo _.2)
     (unary-atomo _.0 _.1))
    ((forall _.0 (exists (not _.1) (not _.2)))
     :
     (bin-atomo _.2)
     (unary-atomo _.0 _.1))
    ((exists _.0 (forall (not _.1) (not _.2)))
     :
     (bin-atomo _.2)
     (unary-atomo _.0 _.1))
    ((forall _.0 (forall (not _.1) (not _.2)))
     :
     (bin-atomo _.2)
     (unary-atomo _.0 _.1))
    ((exists (not _.0) (exists (not _.1) (not _.2)))
     :
     (bin-atomo _.2)
     (unary-atomo _.0 _.1))
    ((forall (not _.0) (exists (not _.1) (not _.2)))
     :
     (bin-atomo _.2)
     (unary-atomo _.0 _.1))
    ((exists (not _.0) (forall (not _.1) (not _.2)))
     :
     (bin-atomo _.2)
     (unary-atomo _.0 _.1))
    ((forall (not _.0) (forall (not _.1) (not _.2)))
     :
     (bin-atomo _.2)
     (unary-atomo _.0 _.1))))

(define negate-quant
  (lambda (q q^)
    (conde
      ((== q 'forall) (== q^ 'exists))
      ((== q 'exists) (== q^ 'forall)))))

(test-check "negate-quant"
  (run 100 (q) (fresh (a b) (negate-quant a b) (== `(,a ,b) q)))
  '((forall exists) (exists forall)))

(define negateo
  (lambda (s o)
    (fresh (qf1 p c)
      (== `(,qf1 ,p ,c) s)
      (un-literalo p)
      (conde
        ((un-literalo c)
         (fresh (qf1^ c^)
           (== `(,qf1^ ,p ,c^) c)
           (negate-quant qf1 qf1^)
           (negate-un-literalo c c^)))
        ((fresh (qf2 q r)
           (== `(,qf2 ,q ,r) c)
           (un-literalo q)
           (fresh (qf1^ qf2^ r^)
             (== `(,qf1^ ,p (,qf2^ ,q ,r^)) o)
             (negate-quant qf1 qf1^)
             (negate-quant qf2 qf2^)
             (negate-bin-literalo r r^))))))))

(test-check "negateo"
  (run 100 (q) (fresh (a b) (negateo a b) (== `(,a ,b) q)))
  '((((forall _.0 (forall _.1 _.2)) (exists _.0 (exists _.1 (not _.2))))
     :
     (bin-atomo _.2)
     (unary-atomo _.0 _.1))
    (((forall (not _.0) (forall _.1 _.2))
      (exists (not _.0) (exists _.1 (not _.2))))
     :
     (bin-atomo _.2)
     (unary-atomo _.0 _.1))
    (((forall _.0 (forall (not _.1) _.2))
      (exists _.0 (exists (not _.1) (not _.2))))
     :
     (bin-atomo _.2)
     (unary-atomo _.0 _.1))
    (((forall (not _.0) (forall (not _.1) _.2))
      (exists (not _.0) (exists (not _.1) (not _.2))))
     :
     (bin-atomo _.2)
     (unary-atomo _.0 _.1))
    (((forall _.0 (forall _.1 (not _.2))) (exists _.0 (exists _.1 _.2)))
     :
     (bin-atomo _.2)
     (unary-atomo _.0 _.1))
    (((forall (not _.0) (forall _.1 (not _.2)))
      (exists (not _.0) (exists _.1 _.2)))
     :
     (bin-atomo _.2)
     (unary-atomo _.0 _.1))
    (((forall _.0 (forall (not _.1) (not _.2)))
      (exists _.0 (exists (not _.1) _.2)))
     :
     (bin-atomo _.2)
     (unary-atomo _.0 _.1))
    (((forall (not _.0) (forall (not _.1) (not _.2)))
      (exists (not _.0) (exists (not _.1) _.2)))
     :
     (bin-atomo _.2)
     (unary-atomo _.0 _.1))
    (((exists _.0 (forall _.1 _.2)) (forall _.0 (exists _.1 (not _.2))))
     :
     (bin-atomo _.2)
     (unary-atomo _.0 _.1))
    (((exists (not _.0) (forall _.1 _.2))
      (forall (not _.0) (exists _.1 (not _.2))))
     :
     (bin-atomo _.2)
     (unary-atomo _.0 _.1))
    (((exists _.0 (forall (not _.1) _.2))
      (forall _.0 (exists (not _.1) (not _.2))))
     :
     (bin-atomo _.2)
     (unary-atomo _.0 _.1))
    (((exists (not _.0) (forall (not _.1) _.2))
      (forall (not _.0) (exists (not _.1) (not _.2))))
     :
     (bin-atomo _.2)
     (unary-atomo _.0 _.1))
    (((exists _.0 (forall _.1 (not _.2))) (forall _.0 (exists _.1 _.2)))
     :
     (bin-atomo _.2)
     (unary-atomo _.0 _.1))
    (((exists (not _.0) (forall _.1 (not _.2)))
      (forall (not _.0) (exists _.1 _.2)))
     :
     (bin-atomo _.2)
     (unary-atomo _.0 _.1))
    (((exists _.0 (forall (not _.1) (not _.2)))
      (forall _.0 (exists (not _.1) _.2)))
     :
     (bin-atomo _.2)
     (unary-atomo _.0 _.1))
    (((exists (not _.0) (forall (not _.1) (not _.2)))
      (forall (not _.0) (exists (not _.1) _.2)))
     :
     (bin-atomo _.2)
     (unary-atomo _.0 _.1))
    (((forall _.0 (exists _.1 _.2)) (exists _.0 (forall _.1 (not _.2))))
     :
     (bin-atomo _.2)
     (unary-atomo _.0 _.1))
    (((forall (not _.0) (exists _.1 _.2))
      (exists (not _.0) (forall _.1 (not _.2))))
     :
     (bin-atomo _.2)
     (unary-atomo _.0 _.1))
    (((forall _.0 (exists (not _.1) _.2))
      (exists _.0 (forall (not _.1) (not _.2))))
     :
     (bin-atomo _.2)
     (unary-atomo _.0 _.1))
    (((forall (not _.0) (exists (not _.1) _.2))
      (exists (not _.0) (forall (not _.1) (not _.2))))
     :
     (bin-atomo _.2)
     (unary-atomo _.0 _.1))
    (((exists _.0 (exists _.1 _.2)) (forall _.0 (forall _.1 (not _.2))))
     :
     (bin-atomo _.2)
     (unary-atomo _.0 _.1))
    (((exists (not _.0) (exists _.1 _.2))
      (forall (not _.0) (forall _.1 (not _.2))))
     :
     (bin-atomo _.2)
     (unary-atomo _.0 _.1))
    (((exists _.0 (exists (not _.1) _.2))
      (forall _.0 (forall (not _.1) (not _.2))))
     :
     (bin-atomo _.2)
     (unary-atomo _.0 _.1))
    (((exists (not _.0) (exists (not _.1) _.2))
      (forall (not _.0) (forall (not _.1) (not _.2))))
     :
     (bin-atomo _.2)
     (unary-atomo _.0 _.1))
    (((forall _.0 (exists _.1 (not _.2))) (exists _.0 (forall _.1 _.2)))
     :
     (bin-atomo _.2)
     (unary-atomo _.0 _.1))
    (((forall (not _.0) (exists _.1 (not _.2)))
      (exists (not _.0) (forall _.1 _.2)))
     :
     (bin-atomo _.2)
     (unary-atomo _.0 _.1))
    (((exists _.0 (exists _.1 (not _.2))) (forall _.0 (forall _.1 _.2)))
     :
     (bin-atomo _.2)
     (unary-atomo _.0 _.1))
    (((exists (not _.0) (exists _.1 (not _.2)))
      (forall (not _.0) (forall _.1 _.2)))
     :
     (bin-atomo _.2)
     (unary-atomo _.0 _.1))
    (((forall _.0 (exists (not _.1) (not _.2)))
      (exists _.0 (forall (not _.1) _.2)))
     :
     (bin-atomo _.2)
     (unary-atomo _.0 _.1))
    (((exists _.0 (exists (not _.1) (not _.2)))
      (forall _.0 (forall (not _.1) _.2)))
     :
     (bin-atomo _.2)
     (unary-atomo _.0 _.1))
    (((forall (not _.0) (exists (not _.1) (not _.2)))
      (exists (not _.0) (forall (not _.1) _.2)))
     :
     (bin-atomo _.2)
     (unary-atomo _.0 _.1))
    (((exists (not _.0) (exists (not _.1) (not _.2)))
      (forall (not _.0) (forall (not _.1) _.2)))
     :
     (bin-atomo _.2)
     (unary-atomo _.0 _.1))))

(define membero
  (lambda (x ls)
    (fresh (a d)
      (== `(,a . ,d) ls)
      (conde
        [(== a x)]
        [(=/= a x) (membero x d)]))))

(test-check "membero"
  (run 8 (q) (fresh (a b) (membero a b) (== `(,a ,b) q)))
  '((_.0 (_.0 . _.1))
    ((_.0 (_.1 _.0 . _.2)) : (=/= ((_.0 . _.1))))
    ((_.0 (_.1 _.2 _.0 . _.3)) : (=/= ((_.0 . _.1)) ((_.0 . _.2))))
    ((_.0 (_.1 _.2 _.3 _.0 . _.4))
     :
     (=/= ((_.0 . _.1)) ((_.0 . _.2)) ((_.0 . _.3))))
    ((_.0 (_.1 _.2 _.3 _.4 _.0 . _.5))
     :
     (=/= ((_.0 . _.1)) ((_.0 . _.2)) ((_.0 . _.3)) ((_.0 . _.4))))
    ((_.0 (_.1 _.2 _.3 _.4 _.5 _.0 . _.6))
     :
     (=/= ((_.0 . _.1)) ((_.0 . _.2)) ((_.0 . _.3)) ((_.0 . _.4)) ((_.0 . _.5))))
    ((_.0 (_.1 _.2 _.3 _.4 _.5 _.6 _.0 . _.7))
     :
     (=/=
      ((_.0 . _.1))
      ((_.0 . _.2))
      ((_.0 . _.3))
      ((_.0 . _.4))
      ((_.0 . _.5))
      ((_.0 . _.6))))
    ((_.0 (_.1 _.2 _.3 _.4 _.5 _.6 _.7 _.0 . _.8))
     :
     (=/=
      ((_.0 . _.1))
      ((_.0 . _.2))
      ((_.0 . _.3))
      ((_.0 . _.4))
      ((_.0 . _.5))
      ((_.0 . _.6))
      ((_.0 . _.7))))))

(define R
  (lambda (G phi proof)
    (conde
      ((membero phi G)
       (== `(Gamma : ,G => ,phi) proof))      
      ((fresh (p c) ;; D1
         (== `(exists ,p ,c) phi)
         (unary-atomo p)
         (set-termo c)
         (fresh (q r1 r2)
           (== `((,r1 ,r2) D1=> ,phi) proof)
           (unary-atomo q)
           (R G `(exists ,p ,q) r1)
           (R G `(forall ,q ,c) r2))))
      ((fresh (p c) ;; B
         (== `(forall ,p ,c) phi)
         (unary-atomo p)
         (set-termo c)
         (fresh (q r1 r2)
           (== `((,r1 ,r2) B=> ,phi) proof)
           (unary-atomo q)
           (R G `(forall ,p ,q) r1)
           (R G `(exists ,p ,c) r2))))
      ((fresh (p c) ;; D2
         (== `(exists ,p ,c) phi)
         (unary-atomo p)
         (set-termo c)
         (fresh (q r1 r2)
           (== `((,r1 ,r2) D2=> ,phi) proof)
           (unary-atomo q)
           (R G `(forall ,q ,p) r1)
           (R G `(exists ,q ,c) r2))))
      ((fresh (p) ;; T
         (== `(forall ,p ,p) phi)
         (== phi proof)
         (un-literalo p)))
      ((fresh (p) ;; I
         (== `(exists ,p ,p) phi)
         (un-literalo p)
         (fresh (c r)
           (set-termo c)
           (== `((,r) I=> ,phi) proof)
           (R G `(exists ,p ,c) r))))
      ((fresh (p nq) ;; D3
         (== `(exists ,p ,nq) phi)
         (unary-atomo p)
         (fresh (q c nc r1 r2)
           (== `((,r1 ,r2) D3=> ,phi) proof)
           (negateo c nc)
           (un-literalo q) ;; these two lines could be better specialized. 
           (negate-un-literalo q nq)
           (R G `(forall ,q ,nc) r1)
           (R G `(exists ,p ,c) r2))))      
      ((fresh (p c) ;; A
         (== `(forall ,p ,c) phi)
         (un-literalo p)
         (set-termo c)
         (fresh (np r)
           (negate-un-literalo p np)
           (== `((,r) A=> ,phi) proof)
           (R G `(forall ,p ,np) r))))
      ((fresh (p) ;; II
         (== `(exists ,p ,p) phi)
         (unary-atomo p)
         (fresh (q r t)
           (unary-atomo q)
           (bin-literalo t)
           (== `((,r) II=> ,phi) proof)
           (R G `(exists ,q (exists ,p ,t)) r))))
      ((fresh (p q t) ;; AA
         (== `(forall ,p (exists ,q ,t)) phi)
         (unary-atomo p)
         (unary-atomo q)
         (bin-literalo t)
         (fresh (q^ r1 r2)
           (== `((,r1 ,r2) AA=> ,phi) proof)
           (unary-atomo q^)
           (R G `(forall ,p (forall ,q^ ,t)) r1)
           (R G `(exists ,q ,q^) r2))))
      ((fresh (p q t) ;; EE
         (== `(exists ,p (exists ,q ,t)) phi)
         (unary-atomo p)
         (unary-atomo q)
         (bin-literalo t)
         (fresh (q^ r1 r2)
           (== `((,r1 ,r2) EE=> ,phi) proof)
           (unary-atomo q^)
           (R G `(exists ,p (exists ,q^ ,t)) r1)
           (R G `(forall ,q^ ,q) r2))))
      ((fresh (p q t) ;; AE
         (== `(forall ,p (exists ,q ,t)) phi)
         (unary-atomo p)
         (unary-atomo q)
         (bin-literalo t)
         (fresh (q^ r1 r2)
           (== `((,r1 ,r2) AE=> ,phi) proof)
           (unary-atomo q^)
           (R G `(forall ,p (exists ,q^ ,t)) r1)
           (R G `(forall ,q^ ,q) r2))))
      ((sentenceo phi) ;; RAA
       (fresh (p np nphi r)
         (negate-un-literalo p np)
         (negateo phi nphi)
         (== `((,r) RAA=> ,phi) proof)
         (R `(,nphi . ,G) `(exists ,p ,np) r))))))

(run 30 (q)
     (fresh (b c p1 p2 p3)
       (R `(,p1 ,p2 ,p3) b c)
       (=/= b p1)
       (=/= b p2)
       (=/= b p3)
       (== `((,p1 ,p2 ,p3) ,b ,c) q)))

;; Commented out, but uses RAA
;; (define lots-of-ans
;;   (run 2000 (q)
;;        (fresh (b c p1 p2 p3)
;;          (R `(,p1 ,p2 ,p3) b c)
;;          (=/= b p1)
;;          (=/= b p2)
;;          (=/= b p3)
;;          (== `((,p1 ,p2 ,p3) ,b ,c) q))))
