#lang racket

; This file is a bindingspec style implementation of a small class system.
; It does what bindingspec does, but by hand.
; This improves over the local expand loop style by not re-evaluating syntax definitions
; However, it can potentially lead to quadratic re-expansions

(module+ test (require rackunit))
(provide (all-defined-out))

(require bindingspec
         racket/stxparam
         syntax/transformer
         (for-syntax ee-lib
                     racket/list
                     syntax/parse
                     syntax/transformer))

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

(define-class-syntax-parameters this this%)

#|
next steps:
- bindingspec-style local expansion:
  - instead of outputting define-syntax, local-expand value rhs with the def ctx that has the macros
  - when you do that,
    - [x] something like #%host-expr, compile-binder!, compile-reference. Only needed #%host-expr
    - [x] suspension and resumption
    - [x] bind surface names to transformers that ref a free id table that will end up mapping them to compiled names in the output code. Don't need it.
    - [x] initially, this lookup would fail. But running something like compile-binder! on a binder would make an entry in the table.
    - [x] references will be the surface identifiers, so they'll expand via the transformer. No real need for compile-reference I think, since the transformer will take care of it.
    - [x] scope stuff for compile-binder!: you'll find out! something with syntax-local-get-shadower on the reference.
    - [x] for #%host-expr, wrap expr positions in #%host-expr and add a stx prop containing the def ctx.
          #%host-expr will get that prop and local-expand its argument under that def ctx
    - eventually, we'll replace local-expand with syntax-local-expand-expressoin to avoid re-expansion after outputting local-expanded code


The current bindingspec-style method has quadratic re-expansions. If you have nested classes (inside of parents' expression positions),
the first class' syntax local-expands and outputs syntax that needs to be re-expanded. Then, its parent local-expands, which re-expands the first class.
Then, its parent local expands, which re-expands both classes. And so-on. You get triangular (quadratic) re-expansions.

- The syntax definitions get evaluated twice, which is inefficient and is really bad if they are effectful
- They are evaluated once during syntax-local-bind-syntaxes, and again when the emitted letrec-syntaxes expands

Eager expansion (expand rhs before compilation) wouldn't work.
I don't remember why, and I'm not convinced it doesn't
TODO try eager expansion under def ctx
Even if it does work, you'd want syntax-local-expand-expression change to avoid quadratic re-expansion

Currently, you have to choose between:
- macro transformers being evaluated twice (bind macros in pass 1 for definition-emitting macros, and re-emit them in the output syntax so
"phase 2" (expansion of emitted syntax) has access to them to expand method rhs and top-level exprs)
- quadratic re-expansion with bindingspec-style suspensions

the syntax-local-expand-expression change will allow us to create opaque suspensions with access to transformers that will only get expanded once, never local-expanded
We will get the best of both worlds.
Macro definitions won't have to be emitted, so they'll only be evaluated once when the suspension is created.
And we won't have to local-expand suspensions, they'll just expand with the transformers in context.
|#

(define-hosted-syntaxes
  (binding-class method-var #:description "method name")
  (binding-class method-arg-var #:description "method argument name")
  (binding-class field-var #:description "field name")
  (extension-class class-macro #:description "class macro")

  (two-pass-nonterminal class-form
                        #:allow-extension class-macro
                        (field name:field-var ...)
                        #:binding (export name)
                        ((~literal define) (m:method-var arg:method-arg-var ...) body:expr ...)
                        #:binding [(export m) {(bind arg) (host body)}]
                        (~literal this)
                        (~literal this%)
                        e:expr
                        #:binding (host e)))

(define-host-interface/expression
  (class e:class-form ...)
  #:binding {(recursive e)}
  (define-values (defns fields exprs) (group-class-decls #'(e ...)))
  (compile-class-body defns fields exprs))

(begin-for-syntax
  (define-symbol-table field-index-table)

  #;((listof syntax?) -> (values (listof syntax?) (listof syntax?) (listof syntax?)))
  ; accepts a list of partially expanded class-level definitions and returns them grouped into
  ; syntax definitions, value definitions, field declarations, and top-level exprs
  (define (group-class-decls exprs)
    (let loop ([exprs exprs]
               ; list of (define-values ...) exprs
               [prev-defns null]
               ; list of (field id ...) exprs
               [prev-fields null]
               [prev-exprs null])
      (syntax-parse exprs
        [(expr . rest-exprs)
         (syntax-parse #'expr
           #:literals (define field)
           [(define . _)
            (loop #'rest-exprs
                  (cons #'expr prev-defns)
                  prev-fields
                  prev-exprs)]
           [(field . _)
            (loop #'rest-exprs
                  prev-defns
                  (cons #'expr prev-fields)
                  prev-exprs)]
           [_
            (loop #'rest-exprs
                  prev-defns
                  prev-fields
                  (cons #'expr prev-exprs))])]
        [() (values (reverse prev-defns)
                    (reverse prev-fields)
                    (reverse prev-exprs))])))

  #;((listof syntax?) (listof syntax?) (listof syntax?) -> syntax?)
  ; compile the partially expanded class-level definitions into pure racket code.
  ; This is the actual class logic.
  (define (compile-class-body defns fields exprs)
    ; TODO better error messages
    (add-decl-props
     defns
     (syntax-parse (list defns fields exprs)
       #:literals (define field)
       [(; I know ~datum for lambda is bad, but I don't know how to do this correctly
         ; There are at least two distinct (by free-identifier=?) "lambda"s that could end up here
         ((define (method-name:id method-arg:id ...)  method-body:expr ...) ...)
         ; only 1 field definition allowed
         ((~optional (field field-name:id ...) #:defaults ([(field-name 1) null])))
         (expr ...))
        (check-duplicate-method-names (attribute method-name))
        (for ([field-name (attribute field-name)]
              [field-index (in-naturals)])
          (symbol-table-set! field-index-table field-name field-index))
        #'(with-reference-compilers ([method-var method-reference-compiler]
                                     [method-arg-var mutable-reference-compiler]
                                     [field-var field-reference-compiler])
            (letrec ([method-table
                      (vector (lambda (this-arg method-arg ...)
                                ; to support class-level expressions that may call methods and fields,
                                ; this will have to be done around class-level expressions too
                                (syntax-parameterize ([this (make-variable-like-transformer #'this-arg)])
                                  method-body
                                  ...))
                              ...)]
                     [constructor
                      (lambda (field-name ...)
                        (let ([this-val (object (vector field-name ...) cls)])
                          (syntax-parameterize ([this (make-variable-like-transformer #'this-val)])
                            ; I'm just putting this here to ensure that the body is non-empty
                            ; That's ok, right?
                            (void)
                            expr
                            ...)
                          this-val))]
                     [method-name->index
                      (make-name->index (list 'method-name ...))]
                     [cls
                      (class-info method-name->index method-table constructor)])
              cls))])))

  (define method-reference-compiler
    (make-variable-like-transformer (syntax-parser
                                      [name:id
                                       #'(lambda args (send this name . args))])))

  (define field-reference-compiler
    (make-variable-like-transformer (syntax-parser
                                      [name:id
                                       (let ([idx (symbol-table-ref field-index-table #'name)])
                                         #`(vector-ref (object-fields this) #,idx))])
                                    (syntax-parser
                                      [(_ name:id rhs)
                                       (let ([idx (symbol-table-ref field-index-table #'name)])
                                         #`(vector-set! (object-fields this) #,idx rhs))])))

  ; originally copied from https://github.com/racket/racket/blob/a17621bec9216edd02b44cc75a2a3ad982f030b7/racket/collects/racket/private/intdef-util.rkt
  (define (add-decl-props decls stx)
    (for/fold ([stx stx]) ([decl (in-list decls)])
      (define (copy-prop src dest stx)
        (syntax-property
         stx
         dest
         (cons (syntax-property decl src)
               (syntax-property stx dest))))
      (copy-prop
       'origin 'disappeared-use
       (copy-prop
        'disappeared-use 'disappeared-use
        (copy-prop
         'disappeared-binding 'disappeared-binding
         stx)))))

  #;((listof identifier?) -> void?)
  ; If there are (symbolically) duplicate method names, error
  (define (check-duplicate-method-names names)
    (let ([duplicate (check-duplicates names #:key syntax->datum)])
      (when duplicate
        (raise-syntax-error #f "a method with same name has already been defined" duplicate)))))

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

(module+ test)
