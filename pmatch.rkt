#lang racket
(provide pmatch pmatch-who)

; This is an updated version of pmatch (August 28, 2013).
; Modified by Jason Hemann and Dan Friedman
; Recently modified to be Racket-compatible -- JBH 12/13

; It comprises two versions, pmatch and pmatch-who. The pmatch macro
; does not allow a name for the pmatch, while pmatch-who mandates
; one. Using a different name in each pmatch-who should help
; determine where and how a match failed.

; A major change in this implementation of pmatch is the requirement
; that the pattern of each clause be preceded by a quasiquote.

; Code written by Oleg Kiselyov
; (http://pobox.com/~oleg/ftp/)
;
; A simple linear pattern matcher
; It is efficient (generates code at macro-expansion time) and simple:
; it should work on any R5RS (and R6RS) Scheme system.

; (pmatch exp <clause> ...{<else-clause>}) |
; (pmatch-who name exp <clause> ...{<else-clause>})
; <clause> ::= (`<pattern> {<guard>} exp ...)
; <else-clause> ::= (else exp ...)
; <guard> ::= (guard boolean-exp ...)
; <pattern> :: =
;        ,var  -- matches always and binds the var
;                 pattern must be linear! No check is done
;         __    -- matches always, does not bind
;        exp   -- comparison with exp (using equal?)
;        (<pattern1> <pattern2> ...) -- matches the list of patterns
;        (<pattern1> . <pattern2>)  -- matches the pair of patterns

(define-syntax pmatch
  (syntax-rules ()
    ((_ v c ...) (pmatch-who #f v c ...))))

(define-syntax pmatch-who
  (syntax-rules (else guard)
    ((_ name (rator rand ...) c ...)
     (let ((v (rator rand ...)))
       (pmatch-aux '(rator rand ...) name v c ...)))
    ((_ name v c ...)
     (pmatch-aux 'v name v c ...))))

(define-syntax pmatch-aux
  (syntax-rules (else guard quasiquote)
    ((_ w name v)
     (begin
       (if 'name
           (printf "pmatch ~s failed\n" 'name)
           (printf "pmatch failed\n"))
       (printf "with input ~s evaluating to ~s\n" w v)
       (error 'pmatch "match failed")))
    ((_ w name v (else e0 e ...)) (begin e0 e ...))
    ((_ w name v ((quasiquote pat) (guard g ...) e0 e ...) cs ...)
     (let ((fk (lambda () (pmatch-aux w name v cs ...))))
       (ppat v pat (if (and g ...) (begin e0 e ...) (fk)) (fk))))
    ((_ w name v ((quasiquote pat) e0 e ...) cs ...)
     (let ((fk (lambda () (pmatch-aux w name v cs ...))))
       (ppat v pat (begin e0 e ...) (fk))))))

(define-syntax ppat
  (syntax-rules (unquote __)
    ((_ v __ kt kf) kt)
    ((_ v (unquote var) kt kf) (let ((var v)) kt))
    ((_ v (x . y) kt kf)
     (if (pair? v)
       (let ((vx (car v)) (vy (cdr v)))
	 (ppat vx x (ppat vy y kt kf) kf))
       kf))
    ((_ v lit kt kf) (if (equal? v (quote lit)) kt kf))))
