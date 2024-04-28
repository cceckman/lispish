; TODO: The general procedure alows multiple args,
; but that would lead to mutual recursion with foldl.
; Don't do that for now, until we have foldl working.
; (define eq? (lambda (a b) (sys:eq? a b)))

(define #t nil)
(define #f nil)
(set! #t (quote #t))
(set! #f (quote #f))

;; (define foldl (
;;   lambda (proc init x)
;;   ; TODO: Use a let-expression here
;;   (if (eq? (x) ())
;;       (init)
;;       (foldl (proc init (car x)) (cdr x))
;;   )
;; ))
;; (define + (
;;   lambda (a . z)
;;   (foldl sys:add a z)
;; ))
