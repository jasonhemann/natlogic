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

(define unary-atomo
  (lambda (a)
    (fresh (sym)
      (== `(-2 ,sym) a)
      (symbol sym))))

(test-check "unary-atomo"
  (run 100 (q) (unary-atomo q))
  '(((-2 _.0) : (symbol _.0))))

(define make-un-atom
  (lambda (sym)
    `(-2 . ,sym)))

(define bin-atomo
  (lambda (a)
    (fresh (sym)
      (symbol sym)
      (== a `(-3 . ,sym)))))

(test-check "bin-atomo"
  (run 100 (q) (bin-atomo q))
  '(((-3 . _.0) : (symbol _.0))))

(define make-bin-atom
  (lambda (sym)
    `(-3 . ,sym)))

(define un-literalo
  (lambda (l)
    (conde
      ((unary-atomo l))
      ((fresh (a)
         (== l `(not ,a))
         (unary-atomo a))))))

(test-check "un-literalo"
  (run 100 (q) (un-literalo q))
  '(((-2 _.0) : (symbol _.0)) ((not (-2 _.0)) : (symbol _.0))))

(define negate-un-literal
  (lambda (n)
    (pmatch n
      (`(not (-2 . ,x)) (guard (symbol? x))
       `(-2 . ,x))
      (`(-2 . ,x) (guard (symbol? x))
       `(not (-2 . ,x))))))

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
  '(((-3 . _.0) : (symbol _.0)) ((not (-3 . _.0)) : (symbol _.0))))

(define negate-bin-literalo
  (lambda (l o)
    (conde
      ((bin-atomo l)
       (== `(not ,l) o))
      ((bin-atomo o)
       (== l `(not ,o))))))

(test-check "negate-bin-literalo"
  (run 100 (q) (fresh (a b) (negate-bin-literalo a b) (== `(,a ,b) q)))
  '((((-3 . _.0) (not (-3 . _.0))) : (symbol _.0))
    (((not (-3 . _.0)) (-3 . _.0)) : (symbol _.0))))

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
      ((fresh (p r)
         (conde
           ((== s `(∃ ,p ,r))
            (un-literalo p)
            (bin-literalo r)) 
           ((== s `(∀ ,p ,r))
            (un-literalo p)
            (bin-literalo r))))))))

(test-check "set-termo"
  (run 100 (q) (set-termo q))
  '(((-2 _.0) : (symbol _.0)) ((not (-2 _.0)) : (symbol _.0))
    ((∃ (-2 _.0) (-3 . _.1)) : (symbol _.0 _.1))
    ((∀ (-2 _.0) (-3 . _.1)) : (symbol _.0 _.1))
    ((∃ (not (-2 _.0)) (-3 . _.1)) : (symbol _.0 _.1))
    ((∀ (not (-2 _.0)) (-3 . _.1)) : (symbol _.0 _.1))
    ((∃ (-2 _.0) (not (-3 . _.1))) : (symbol _.0 _.1))
    ((∀ (-2 _.0) (not (-3 . _.1))) : (symbol _.0 _.1))
    ((∃ (not (-2 _.0)) (not (-3 . _.1))) : (symbol _.0 _.1))
    ((∀ (not (-2 _.0)) (not (-3 . _.1))) : (symbol _.0 _.1))))

(define sentenceo
  (lambda (s)
    (conde
      ((fresh (p c)
         (== `(∃ ,p ,c) s)
         (un-literalo p)
         (set-termo c)))
      ((fresh (p c)
         (== `(∀ ,p ,c) s)
         (un-literalo p)
         (set-termo c))))))

(test-check "sentenceo"
  (run 100 (q) (sentenceo q))
  '(((∃ (-2 _.0) (-2 _.1)) : (symbol _.0 _.1))
    ((∀ (-2 _.0) (-2 _.1)) : (symbol _.0 _.1))
    ((∃ (not (-2 _.0)) (-2 _.1)) : (symbol _.0 _.1))
    ((∀ (not (-2 _.0)) (-2 _.1)) : (symbol _.0 _.1))
    ((∃ (-2 _.0) (not (-2 _.1))) : (symbol _.0 _.1))
    ((∀ (-2 _.0) (not (-2 _.1))) : (symbol _.0 _.1))
    ((∃ (not (-2 _.0)) (not (-2 _.1))) : (symbol _.0 _.1))
    ((∀ (not (-2 _.0)) (not (-2 _.1))) : (symbol _.0 _.1))
    ((∃ (-2 _.0) (∃ (-2 _.1) (-3 . _.2))) : (symbol _.0 _.1 _.2))
    ((∀ (-2 _.0) (∃ (-2 _.1) (-3 . _.2))) : (symbol _.0 _.1 _.2))
    ((∃ (-2 _.0) (∀ (-2 _.1) (-3 . _.2))) : (symbol _.0 _.1 _.2))
    ((∀ (-2 _.0) (∀ (-2 _.1) (-3 . _.2))) : (symbol _.0 _.1 _.2))
    ((∃ (not (-2 _.0)) (∃ (-2 _.1) (-3 . _.2)))
     : (symbol _.0 _.1 _.2))
    ((∀ (not (-2 _.0)) (∃ (-2 _.1) (-3 . _.2)))
     : (symbol _.0 _.1 _.2))
    ((∃ (not (-2 _.0)) (∀ (-2 _.1) (-3 . _.2)))
     : (symbol _.0 _.1 _.2))
    ((∀ (not (-2 _.0)) (∀ (-2 _.1) (-3 . _.2)))
     : (symbol _.0 _.1 _.2))
    ((∃ (-2 _.0) (∃ (not (-2 _.1)) (-3 . _.2)))
     : (symbol _.0 _.1 _.2))
    ((∀ (-2 _.0) (∃ (not (-2 _.1)) (-3 . _.2)))
     : (symbol _.0 _.1 _.2))
    ((∃ (-2 _.0) (∀ (not (-2 _.1)) (-3 . _.2)))
     : (symbol _.0 _.1 _.2))
    ((∀ (-2 _.0) (∀ (not (-2 _.1)) (-3 . _.2)))
     : (symbol _.0 _.1 _.2))
    ((∃ (not (-2 _.0)) (∃ (not (-2 _.1)) (-3 . _.2)))
     : (symbol _.0 _.1 _.2))
    ((∀ (not (-2 _.0)) (∃ (not (-2 _.1)) (-3 . _.2)))
     : (symbol _.0 _.1 _.2))
    ((∃ (-2 _.0) (∃ (-2 _.1) (not (-3 . _.2))))
     : (symbol _.0 _.1 _.2))
    ((∀ (-2 _.0) (∃ (-2 _.1) (not (-3 . _.2))))
     : (symbol _.0 _.1 _.2))
    ((∃ (not (-2 _.0)) (∀ (not (-2 _.1)) (-3 . _.2)))
     : (symbol _.0 _.1 _.2))
    ((∀ (not (-2 _.0)) (∀ (not (-2 _.1)) (-3 . _.2)))
     : (symbol _.0 _.1 _.2))
    ((∃ (-2 _.0) (∀ (-2 _.1) (not (-3 . _.2))))
     : (symbol _.0 _.1 _.2))
    ((∀ (-2 _.0) (∀ (-2 _.1) (not (-3 . _.2))))
     : (symbol _.0 _.1 _.2))
    ((∃ (not (-2 _.0)) (∃ (-2 _.1) (not (-3 . _.2))))
     : (symbol _.0 _.1 _.2))
    ((∀ (not (-2 _.0)) (∃ (-2 _.1) (not (-3 . _.2))))
     : (symbol _.0 _.1 _.2))
    ((∃ (not (-2 _.0)) (∀ (-2 _.1) (not (-3 . _.2))))
     : (symbol _.0 _.1 _.2))
    ((∀ (not (-2 _.0)) (∀ (-2 _.1) (not (-3 . _.2))))
     : (symbol _.0 _.1 _.2))
    ((∃ (-2 _.0) (∃ (not (-2 _.1)) (not (-3 . _.2))))
     : (symbol _.0 _.1 _.2))
    ((∀ (-2 _.0) (∃ (not (-2 _.1)) (not (-3 . _.2))))
     : (symbol _.0 _.1 _.2))
    ((∃ (-2 _.0) (∀ (not (-2 _.1)) (not (-3 . _.2))))
     : (symbol _.0 _.1 _.2))
    ((∀ (-2 _.0) (∀ (not (-2 _.1)) (not (-3 . _.2))))
     : (symbol _.0 _.1 _.2))
    ((∃ (not (-2 _.0)) (∃ (not (-2 _.1)) (not (-3 . _.2))))
     : (symbol _.0 _.1 _.2))
    ((∀ (not (-2 _.0)) (∃ (not (-2 _.1)) (not (-3 . _.2))))
     : (symbol _.0 _.1 _.2))
    ((∃ (not (-2 _.0)) (∀ (not (-2 _.1)) (not (-3 . _.2))))
     : (symbol _.0 _.1 _.2))
    ((∀ (not (-2 _.0)) (∀ (not (-2 _.1)) (not (-3 . _.2))))
     : (symbol _.0 _.1 _.2))))

(define negate-quant
  (lambda (q q^)
    (conde
      ((== q '∀) (== q^ '∃))
      ((== q '∃) (== q^ '∀)))))

(test-check "negate-quant"
  (run 100 (q) (fresh (a b) (negate-quant a b) (== `(,a ,b) q)))
  '((∀ ∃) (∃ ∀)))

(define negateo
  (lambda (s o)
    (fresh (qf1 p c)
      (== `(,qf1 ,p ,c) s)
      (conde
        ((un-literalo c)
         (fresh (qf1^ c^)
           (== `(,qf1^ ,p ,c^) c)
           (negate-quant qf1 qf1^)
           (negate-un-literalo c c^)))
        ((fresh (qf2 q r)
           (== `(,qf2 ,q ,r) c)
           (fresh (qf1^ qf2^ r^)
             (== `(,qf1^ ,p (,qf2^ ,q ,r^)) o)
             (negate-quant qf1 qf1^)
             (negate-quant qf2 qf2^)
             (negate-bin-literalo r r^))))))))

(test-check "negateo"
  (run 100 (q) (fresh (a b) (negateo a b) (== `(,a ,b) q)))
  '((((∀ _.0 (∀ _.1 (-3 . _.2)))
      (∃ _.0 (∃ _.1 (not (-3 . _.2)))))
     : (symbol _.2))
    (((∀ _.0 (∀ _.1 (not (-3 . _.2))))
      (∃ _.0 (∃ _.1 (-3 . _.2))))
     : (symbol _.2))
    (((∃ _.0 (∀ _.1 (-3 . _.2)))
      (∀ _.0 (∃ _.1 (not (-3 . _.2)))))
     : (symbol _.2))
    (((∃ _.0 (∀ _.1 (not (-3 . _.2))))
      (∀ _.0 (∃ _.1 (-3 . _.2))))
     : (symbol _.2))
    (((∀ _.0 (∃ _.1 (-3 . _.2)))
      (∃ _.0 (∀ _.1 (not (-3 . _.2)))))
     : (symbol _.2))
    (((∃ _.0 (∃ _.1 (-3 . _.2)))
      (∀ _.0 (∀ _.1 (not (-3 . _.2)))))
     : (symbol _.2))
    (((∀ _.0 (∃ _.1 (not (-3 . _.2))))
      (∃ _.0 (∀ _.1 (-3 . _.2))))
     : (symbol _.2))
    (((∃ _.0 (∃ _.1 (not (-3 . _.2))))
      (∀ _.0 (∀ _.1 (-3 . _.2))))
     : (symbol _.2))))

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
    ((_.0 (_.1 _.2 _.3 _.0 . _.4)) : (=/= ((_.0 . _.1)) ((_.0 . _.2)) ((_.0 . _.3))))
    ((_.0 (_.1 _.2 _.3 _.4 _.0 . _.5)) : (=/= ((_.0 . _.1)) ((_.0 . _.2)) ((_.0 . _.3)) ((_.0 . _.4))))
    ((_.0 (_.1 _.2 _.3 _.4 _.5 _.0 . _.6)) : (=/= ((_.0 . _.1)) ((_.0 . _.2)) ((_.0 . _.3)) ((_.0 . _.4)) ((_.0 . _.5))))
    ((_.0 (_.1 _.2 _.3 _.4 _.5 _.6 _.0 . _.7)) : (=/= ((_.0 . _.1)) ((_.0 . _.2)) ((_.0 . _.3)) ((_.0 . _.4)) ((_.0 . _.5)) ((_.0 . _.6))))
    ((_.0 (_.1 _.2 _.3 _.4 _.5 _.6 _.7 _.0 . _.8)) : (=/= ((_.0 . _.1)) ((_.0 . _.2)) ((_.0 . _.3)) ((_.0 . _.4)) ((_.0 . _.5)) ((_.0 . _.6)) ((_.0 . _.7))))))

(define R
  (lambda (G phi proof)
    (conde
      ((membero phi G)
       (== `(Gamma : ,G => ,phi) proof))      
      ((fresh (p c) ;; D1
         (== `(∃ ,p ,c) phi)
         (unary-atomo p)
         (set-termo c)
         (fresh (q r1 r2)
           (== `((,r1 ,r2) D1=> ,phi) proof)
           (unary-atomo q)
           (R G `(∃ ,p ,q) r1)
           (R G `(∀ ,q ,c) r2))))
      ((fresh (p c) ;; B
         (== `(∀ ,p ,c) phi)
         (unary-atomo p)
         (set-termo c)
         (fresh (q r1 r2)
           (== `((,r1 ,r2) B=> ,phi) proof)
           (unary-atomo q)
           (R G `(∀ ,p ,q) r1)
           (R G `(∃ ,p ,c) r2))))
      ((fresh (p c) ;; D2
         (== `(∃ ,p ,c) phi)
         (unary-atomo p)
         (set-termo c)
         (fresh (q r1 r2)
           (== `((,r1 ,r2) D2=> ,phi) proof)
           (unary-atomo q)
           (R G `(∀ ,q ,p) r1)
           (R G `(∃ ,q ,c) r2))))
      ((fresh (p) ;; T
         (== `(∀ ,p ,p) phi)
         (== phi proof)
         (un-literalo p)))
      ((fresh (p) ;; I
         (== `(∃ ,p ,p) phi)
         (un-literalo p)
         (fresh (c r)
           (set-termo c)
           (== `((,r) I=> ,phi) proof)
           (R G `(∃ ,p ,c) r))))
      ((fresh (p nq) ;; D3
         (== `(∃ ,p ,nq) phi)
         (unary-atomo p)
         (fresh (q c nc r1 r2)
           (== `((,r1 ,r2) D3=> ,phi) proof)
           (negateo c nc)
           (un-literalo q) ;; these two lines could be better specialized. 
           (negate-un-literalo q nq)
           (R G `(∀ ,q ,nc) r1)
           (R G `(∃ ,p ,c) r2))))      
      ((fresh (p c) ;; A
         (== `(∀ ,p ,c) phi)
         (un-literalo p)
         (set-termo c)
         (fresh (np r)
           (negate-un-literalo p np)
           (== `((,r) A=> ,phi) proof)
           (R G `(∀ ,p ,np) r))))
      ((fresh (p) ;; II
         (== `(∃ ,p ,p) phi)
         (unary-atomo p)
         (fresh (q r t)
           (unary-atomo q)
           (bin-literalo t)
           (== `((,r) II=> ,phi) proof)
           (R G `(∃ ,q (∃ ,p ,t)) r))))
      ((fresh (p q t) ;; AA
         (== `(∀ ,p (∃ ,q ,t)) phi)
         (unary-atomo p)
         (unary-atomo q)
         (bin-literalo t)
         (fresh (q^ r1 r2)
           (== `((,r1 ,r2) AA=> ,phi) proof)
           (unary-atomo q^)
           (R G `(∀ ,p (∀ ,q^ ,t)) r1)
           (R G `(∃ ,q ,q^) r2))))
      ((fresh (p q t) ;; EE
         (== `(∃ ,p (∃ ,q ,t)) phi)
         (unary-atomo p)
         (unary-atomo q)
         (bin-literalo t)
         (fresh (q^ r1 r2)
           (== `((,r1 ,r2) EE=> ,phi) proof)
           (unary-atomo q^)
           (R G `(∃ ,p (∃ ,q^ ,t)) r1)
           (R G `(∀ ,q^ ,q) r2))))
      ((fresh (p q t) ;; AE
         (== `(∀ ,p (∃ ,q ,t)) phi)
         (unary-atomo p)
         (unary-atomo q)
         (bin-literalo t)
         (fresh (q^ r1 r2)
           (== `((,r1 ,r2) AE=> ,phi) proof)
           (unary-atomo q^)
           (R G `(∀ ,p (∃ ,q^ ,t)) r1)
           (R G `(∀ ,q^ ,q) r2))))
      ((sentenceo phi) ;; RAA
       (fresh (p np nphi r)
         (negate-un-literalo p np)
         (negateo phi nphi)
         (== `((,r) RAA=> ,phi) proof)
         (R `(,nphi . ,G) `(∃ ,p ,np) r))))))

;; Requires unicode support to print prettily
(run 30 (q)
     (fresh (b c p1 p2 p3 p4 p5)
       (R `(,p1 ,p2 ,p3 ,p4 ,p5) b c)
       (=/= b p1)
       (=/= b p2)
       (=/= b p3)
       (=/= b p4)
       (=/= b p5)
       (== `((,p1 ,p2 ,p3 ,p4 ,p5) ,b ,c) q)))

(run 30 (q)
       (fresh (b c p1 p2 p3)
         (R `(,p1 ,p2 ,p3) b c)
         (=/= b p1)
         (=/= b p2)
         (=/= b p3)
         (== `((,p1 ,p2 ,p3) ,b ,c) q)))

