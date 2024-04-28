(define foldl (
  lambda (proc init x)
  ; TODO: Use a let-expression here
  (if (eq? (x) ())
      (init)
      (foldl (proc init (car x)) (cdr x))
  )
))
(define + (
  lambda (a . z)
  (foldl sys:add a z)
))
