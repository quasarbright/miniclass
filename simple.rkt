#lang racket

; This file is a simple implementation of a very small class system.

(module+ test (require rackunit))
(provide (all-defined-out))

(require racket/stxparam racket/syntax syntax/id-table (for-syntax syntax/parse syntax/transformer))

(struct class-info [name->method-index method-table constructor])
; A ClassInfo is a (class-info (identifier -> natural) (any ... -> Object)) where
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

; define literals that error out when used outside of a class
(define-syntax define-class-literals
  (syntax-parser
    [(_ lit:id ...)
     #'(begin (define-syntax lit (make-literal-transformer 'lit))
              ...)]))

(begin-for-syntax
  #;(symbol? -> transformer?)
  ; creates a transformer that errors out when used outside of a class
  (define (make-literal-transformer id-sym)
    (syntax-parser
      [_ (raise-syntax-error id-sym "used outside of a class" this-syntax)])))

; define syntax parameters that error out when used outside of a class
(define-syntax define-class-syntax-parameters
  (syntax-parser
    [(_ name:id ...)
     #'(begin (define-syntax-parameter name (make-literal-transformer 'name))
              ...)]))

(define-class-literals field)
(define-class-syntax-parameters this)

(define-syntax class
  (syntax-parser
    [(_ (~alt (~optional ((~literal field) field-name:id ...) #:defaults ([(field-name 1) null]))
              ((~literal define) (method-name:id method-arg:id ...) method-body:expr ...))
      ...)
     (define num-fields (length (attribute field-name)))
     (define/syntax-parse (field-index ...) (build-list num-fields (lambda (n) #`#,n)))
     #'(letrec ([method-table
                 (vector (lambda (this-arg method-arg ...)
                           ; to support class-level expressions that may call methods and fields,
                           ; this will have to be done around class-level expressions too
                           (let ([fields (object-fields this-arg)])
                             (let-syntax ([field-name (make-vector-ref-transformer #'fields #'field-index)]
                                          ...)
                               (syntax-parameterize ([this (make-variable-like-transformer #'this-arg)])
                                 method-body
                                 ...))))
                         ...)]
                [constructor
                 (lambda (field-name ...)
                   (object (vector field-name ...) cls))]
                [method-name->index
                 (make-name->index (list #'method-name ...))]
                [cls
                 (class-info method-name->index method-table constructor)])
         cls)]))

#;((listof identifier?) -> (identifier? -> natural?))
; Create a function that maps method names to their method table indices
(define (make-name->index names)
  (let ([table (make-immutable-free-id-table (map cons names (build-list (length names) identity)))])
    (lambda (name)
      (free-id-table-ref table name (lambda () (error 'send "no such method ~a" name))))))

(begin-for-syntax
  ; Creates a set!-transformer that accesses and mutates an elment of a vector
  (define (make-vector-ref-transformer vector-stx index-stx)
    (make-variable-like-transformer
     #`(vector-ref #,vector-stx #,index-stx)
     #`(lambda (v) (vector-set! #,vector-stx #,index-stx v)))))

(define (new cls . fields)
  (apply (class-info-constructor cls) fields))

(define-syntax send
  (syntax-parser
    [(_ obj:expr method-name:id arg:expr ...)
     #'(send-rt obj #'method-name arg ...)]))

(define (send-rt obj method-name-stx . args)
  (let* ([cls (object-class obj)]
         [index ((class-info-name->method-index cls) method-name-stx)]
         [method-table (class-info-method-table cls)]
         [method (vector-ref method-table index)])
    (apply method obj args)))

(module+ test)
