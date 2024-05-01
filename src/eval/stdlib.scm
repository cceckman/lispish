; TODO: The general procedure alows multiple args,
; but that would lead to mutual recursion with foldl.
; Don't do that for now, until we have foldl working.
(define eq? (lambda (a b) (sys:eq? a b)))
(define eqv? (lambda (a b) (sys:eqv? a b)))

(define nil ())
(define #t nil)
(define #f nil)
(set! #t (quote #t))
(set! #f (quote #f))

(define cons (lambda (a b) (sys:cons a b)))
(define car (lambda (a) (sys:car a)))
(define cdr (lambda (a) (sys:cdr a)))


; Boolean operators:
(define not (lambda (a)
(if a #f #t)
))

(define and (lambda (a b)
(if a b #f)
))
(define or (lambda (a b)
(if a a b)
))
(define xor (lambda (a b)
(not (eq? a b))
))


(define foldl (
  lambda (proc init x)
  (if (eq? x ())
      (init)
      (foldl (proc init (car x)) (cdr x))
  )
))
(define + (lambda (a z) (sys:add a z)))
