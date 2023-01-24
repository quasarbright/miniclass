#lang racket/base

; runtime support that is common between all variants

(provide (struct-out class-info)
         (struct-out object)
         make-name->index
         new
         send)

(require (for-syntax racket/base syntax/parse))

(struct class-info [name->method-index method-table constructor])
; A ClassInfo is a (class-info (symbol -> natural) (any ... -> Object)) where
; name->method-index maps a method name to its vector index in the method-table
; method-table is a vector of methods
; Represents a class itself

(struct object [fields class])
; An Object is a (object (vector any) (vector Method) Class) where
; fields is a vector of field-values
; class is the class of which this object is an instance
; Represents an object, which is an instance of a class

; A Method is a (any any ... -> any)
; Where the first argument is "this"
; Represents a method on a class

#;((listof symbol?) -> (symbol? -> natural?))
; Create a function that maps method names to their method table indices
(define (make-name->index names)
  (let ([table (for/hasheq ([name names]
                            [idx (in-naturals)])
                 (values name idx))])
    (lambda (name)
      (hash-ref table name (lambda () (error 'send "no such method ~a" name))))))

(define (new cls . fields)
  (apply (class-info-constructor cls) fields))

(define-syntax send
  (syntax-parser
    [(_ obj:expr method-name:id arg:expr ...)
     #'(send-rt obj 'method-name (list arg ...))]
    [(_ obj:expr method-name:id . args)
     #'(send-rt obj 'method-name args)]))

#;(object? symbol? (listof any/c) -> any/c)
(define (send-rt obj method-name args)
  (let* ([cls (object-class obj)]
         [index ((class-info-name->method-index cls) method-name)]
         [method-table (class-info-method-table cls)]
         [method (vector-ref method-table index)])
    (apply method obj args)))
