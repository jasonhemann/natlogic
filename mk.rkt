#lang racket
(provide run run* == =/= conde absento symbolo numbero not-pairo fresh prt project)
(require racket/trace)

;; extra stuff for racket
(define (list-sort f l) (sort l f))
(define (remp f l) (filter-not f l))
(define (call-with-string-output-port f)
  (define p (open-output-string))
  (f p)
  (get-output-string p))
(define (exists f l) (ormap f l))
(define for-all andmap)
(define (find f l)
  (cond [(memf f l) => car] [else #f]))
(define memp memf)
(define (var*? v) (var? (car v)))

;; actual code

(include "mk.scm")
