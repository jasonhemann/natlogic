(load "pmatch.scm")

;; To use:
;; Call (inf-pr <tree>)
;; Produces output compatible with semantic.sty latex package.
;; Inspired by similar design by Yusuke Kubota
;; http://phiz.c.u-tokyo.ac.jp/~yk/latex/tree-to-infr.el

(define datum->string
  (lambda (x)
    (call-with-string-output-port
      (lambda (p) (display x p)))))

(define inf-pr
  (lambda (tr)
    (pmatch tr
      [`(,quant ,p are ,q) (guard (memv quant '(All Some No Least)))
       (let ((str (fold-right (lambda (s sr) (string-append "~" (datum->string s) sr)) "" tr)))
         (string-append "{" "(" (substring str 1 (string-length str))  ")" "}" ))]
      [`((,tr1 ,tr2) => ,exp)
       (let ((str1 (inf-pr tr1)) (str2 (inf-pr tr2)))
         (string-append "{\\inference{"  str1 str2 "}" "{""{" (inf-pr exp) "}""}" "}"))]
      [`(,tr => ,exp) (string-append "{\\inference{" (inf-pr tr)  "}""{""{" (inf-pr exp) "}""}""}")])))

