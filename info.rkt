#lang info
(define collection "miniclass")
; use my fork for now since it has implicit compile-binder! and compile-reference
(define deps '("base" "https://github.com/quasarbright/syntax-spec.git"))
(define build-deps '("scribble-lib" "racket-doc" "rackunit-lib"))
(define scribblings '(("scribblings/miniclass.scrbl" ())))
(define pkg-desc "Description Here")
(define version "0.0")
(define pkg-authors '(mdelmonaco))
(define license '(Apache-2.0 OR MIT))
