#lang racket

; This file uses syntax-spec to implement a small class system.
; This improves over the local expand loop style by not re-evaluating syntax definitions.
; However, it can potentially lead to quadratic re-expansions.

(provide (all-defined-out))

(require syntax-spec
         racket/stxparam
         syntax/transformer
         "common.rkt"
         (for-syntax racket/list
                     syntax/parse
                     syntax/transformer))

(define-syntax-parameter this
  (make-expression-transformer
   (syntax-parser
     [_ (raise-syntax-error 'this "used outside of a class" this-syntax)])))

(begin-for-syntax
  (define-syntax-class lambda-id
    (pattern (~or (~literal lambda) (~literal #%plain-lambda)))))

(syntax-spec
  (nonterminal/two-pass class-form
    #:allow-extension racket-macro
    (field name:racket-var ...)
    #:binding (export name)
    ((~literal define-values) (m:racket-var) (lambda:lambda-id (arg:id ...) body:racket-expr ...))
    #:binding (export m)

    ((~literal define-syntaxes) (x:racket-macro ...) e:expr)
    #:binding (export-syntaxes x e)

    ((~literal begin) e:class-form ...)
    #:binding (re-export e)

    e:racket-expr)

  (host-interface/expression
    (class e:class-form ...)
    #:binding {(recursive e)}
    (define-values (defns fields exprs) (group-class-decls (splice-begins (attribute e))))
    (compile-class-body defns fields exprs)))

(begin-for-syntax
  #;((listof syntax?) -> (listof syntax?))
  ; splices begins (recursively), returns flattened list of exprs.
  (define (splice-begins exprs)
    (syntax-parse exprs
      [() this-syntax]
      [(expr . rest-exprs)
       (syntax-parse #'expr
         #:literals (begin)
         [(begin e ...)
          (splice-begins (append (attribute e) #'rest-exprs))]
         [_ (cons this-syntax (splice-begins #'rest-exprs))])]))

  #;((listof syntax?) -> (values (listof syntax?) (listof syntax?) (listof syntax?)))
  ; accepts a list of partially expanded class-level definitions and returns them grouped into
  ; syntax definitions, value definitions, field declarations, and top-level exprs
  (define (group-class-decls exprs)
    (syntax-parse exprs
      #:literals (define-values define-syntaxes field)
      [((~alt (~and defn (define-values . _))
              ; ignore bc they don't end up in the generated code
              (~and stx-defn (define-syntaxes . _))
              (~and field-decl (field . _))
              expr)
        ...)
       (values (attribute defn)
               (attribute field-decl)
               (attribute expr))]))

  #;((listof syntax?) (listof syntax?) (listof syntax?) -> syntax?)
  ; compile the partially expanded class-level definitions into pure racket code.
  ; This is the actual class logic.
  (define (compile-class-body defns fields exprs)
    (syntax-parse (list defns fields exprs)
      #:literals (define-values field)
      [(((define-values (method-name:id) (_ (method-arg:id ...) method-body:expr ...)) ...)
        ; only 1 field definition allowed
        ((~optional (field field-name:id ...) #:defaults ([(field-name 1) null])))
        (expr ...))
       
       (check-duplicate-method-names (attribute method-name))

       (define/syntax-parse (field-index ...) (range (length (attribute field-name))))
       (define/syntax-parse (method-index ...) (range (length (attribute method-name))))

       (define/syntax-parse (field-arg ...) (generate-temporaries (attribute field-name)))

       #'(let ()
           (define-syntax-parameter find-self #f)
           (syntax-parameterize ([this (make-variable-like-transformer #'find-self)])
             (letrec-syntax ([method-name (make-method-transformer #'find-self 'method-index)]
                             ...
                             [field-name (make-field-transformer #'find-self 'field-index)]
                             ...)
               (letrec ([method-table
                         (vector (lambda (self method-arg ...)
                                   (syntax-parameterize ([find-self (make-rename-transformer #'self)])
                                     method-body ...))
                                 ...)]
                        [constructor
                         (lambda (field-arg ...)
                           (let ([self (object (vector field-arg ...) cls)])
                             (syntax-parameterize ([find-self (make-rename-transformer #'self)])
                               ; void to ensure body is non-empty
                               (void)
                               expr ...)
                             self))]
                        [method-name->index
                         (make-name->index (list 'method-name ...))]
                        [cls
                         (class-info method-name->index method-table constructor)])
                 cls))))]))

  #;((listof identifier?) -> void?)
  ; If there are (symbolically) duplicate method names, error
  (define (check-duplicate-method-names names)
    (let ([duplicate (check-duplicates names #:key syntax->datum)])
      (when duplicate
        (raise-syntax-error #f "a method with same name has already been defined" duplicate))))
  
  (define (make-method-transformer this-stx method-index)
    (make-variable-like-transformer #`(send-index #,this-stx '#,method-index)))

  (define (make-field-transformer this-stx field-index)
    (make-variable-like-transformer #`(vector-ref (object-fields #,this-stx) '#,field-index)
                                    #`(lambda (v) (vector-set! (object-fields #,this-stx) '#,field-index v)))))
