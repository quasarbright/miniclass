#lang racket

; tests classical.rkt

(module+ test (require rackunit))

(require "./local-expand-loop.rkt")

(module+ test
  (test-case "simple class"
    (define foo%
      (class
        (field x)
        (define (add y) (+ x y))))
    (define foo (new foo% 1))
    (check-equal? (send foo add 2) 3))
  (test-case "empty class"
    (define foo% (class))
    (new foo%)
    (void))
  (test-case "internal method call"
    (define foo%
      (class
        (define (f x)
          (send this g x))
        (define (g x)
          (add1 x))))
    (define foo (new foo%))
    (check-equal? (send foo f 1) 2))
  (test-case "mutually recursive methods"
    (define parity%
      (class
        (define (even? n)
          (if (= n 0)
              #t
              (send this odd? (sub1 n))))
        (define (odd? n)
          (if (= n 0)
              #f
              (send this even? (sub1 n))))))
    (define parity (new parity%))
    (check-equal? (send parity even? 10) #t)
    (check-equal? (send parity even? 11) #f))
  (test-case "mutating a field"
    (define counter%
      (class
        (field count)
        (define (inc) (set! count (add1 count)))
        (define (get) count)))
    (define counter (new counter% 0))
    (send counter inc)
    (send counter inc)
    (send counter inc)
    (check-equal? (send counter get) 3))
  (test-case "use a macro that expands to a definition"
    (define-syntax-rule (m x) (define x (lambda () 2)))
    (define foo%
      (class
        (m x)))
    (define foo (new foo%))
    (check-equal? (send foo x) 2))
  (test-case "use a macro that expands to field"
    (define-syntax-rule (m x) (field x))
    (define foo%
      (class
        (m x)
        (define (f) (add1 x))))
    (define foo (new foo% 1))
    (check-equal? (send foo f) 2))
  (test-case "define and use a macro inside of a class"
    (define foo%
      (class
        (define-syntax-rule (m x) (field x))
        (define-syntax-rule (my-add1 x) (add1 x))
        (m x)
        (define (f) (my-add1 x))))
    (define foo (new foo% 1))
    (check-equal? (send foo f) 2)))
