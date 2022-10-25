#lang racket

; tests classical.rkt

(module+ test (require rackunit))

(require "./classical.rkt")

(module+ test
  (test-case "simple class"
    (define foo%
      (class
        (field x)
        (define (add y) (+ x y))))
    ;(define foo (new foo% 1))
    #;(check-equal? (send foo add 2) 3)))
