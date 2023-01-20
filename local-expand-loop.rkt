#lang racket

; This file is a "local-expand loop" style implementation of a small class system.
; Similar to the implementation of the 'block' macro.
; This improves over the simple implementation by allowing class-level macro uses and definitions.

(module+ test (require rackunit))
(provide (all-defined-out))

(require racket/stxparam
         syntax/transformer
         (for-syntax syntax/context
                     syntax/intdef
                     syntax/parse
                     syntax/transformer
                     racket/list))

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
  (make-expression-transformer
   (lambda (stx)
     (let ([def-ctx (syntax-local-make-definition-context)])
       ; If this was going to get more complicated, I'd do more pre-processing into appropriate structured data
       (let-values ([(stx-defns defns fields exprs) (group-class-decls (local-expand-class-body stx def-ctx))])
         (compile-class-body defns stx-defns fields exprs def-ctx))))))

(begin-for-syntax
  ; copied from https://github.com/racket/racket/blob/a17621bec9216edd02b44cc75a2a3ad982f030b7/racket/collects/racket/private/intdef-util.rkt
  (define (add-decl-props def-ctx decls stx)
    (internal-definition-context-track
     def-ctx
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
          stx))))))
  #;(syntax? definition-context? -> (listof syntax?))
  ; expand the body of the class expression using the given definition context
  ; returns a list of (partially) expanded class-level forms.
  ; expands to just field declarations and definitions (of values and syntaxes).
  ; does not expand rhs of define-values, only define-syntaxes.
  ; splices begins.
  (define (local-expand-class-body stx def-ctx)
    (let*
        ([ctx (generate-expand-context #t)]
         [stoplist (list #'begin #'define-syntaxes #'define-values #'field #'lambda #'this #'#%app)]
         [init-exprs (let ([v (syntax->list stx)])
                       (unless v (raise-syntax-error #f "bad syntax" stx))
                       (map (λ (expr) (internal-definition-context-add-scopes def-ctx expr))
                            (cdr v)))])
      (let loop ([todo init-exprs] [r '()])
        (if (null? todo)
            (reverse r)
            (let ([expr (local-expand (car todo) ctx stoplist def-ctx)]
                  [todo (cdr todo)])
              (syntax-parse expr
                #:literals (begin define-syntaxes define-values field)
                [(begin . rest)
                 ; splice the begin
                 (loop (append (syntax->list #'rest) todo) r)]
                [(define-syntaxes (id:id ...) rhs)
                 ; bind ids to transformers in the def-ctx
                 (with-syntax ([rhs (local-transformer-expand #'rhs 'expression null)])
                   (with-syntax ([(id ...) (syntax-local-bind-syntaxes (syntax->list #'(id ...))
                                                                       #'rhs
                                                                       def-ctx)])
                     (loop todo (cons (datum->syntax
                                       expr
                                       (list #'define-syntaxes #'(id ...) #'rhs)
                                       expr
                                       expr)
                                      r))))]
                [(define-values (id:id ...) rhs)
                 (with-syntax ([(id ...) (syntax-local-bind-syntaxes (syntax->list #'(id ...)) #f def-ctx)])
                   (loop todo (cons (datum->syntax
                                     expr
                                     (list #'define-values #'(id ...) #'rhs)
                                     expr
                                     expr)
                                    r)))]
                [(field id:id ...)
                 (with-syntax ([(id ...) (syntax-local-bind-syntaxes (syntax->list #'(id ...)) #f def-ctx)])
                   (loop todo (cons (datum->syntax
                                     expr
                                     ; block does this slightly differently, be careful
                                     #'(field id ...)
                                     expr
                                     expr)
                                    r)))]
                ; This is a plain top-level expression to be evaluated in the constructor
                ; Leave as-is
                [_ (loop todo (cons this-syntax r))]))))))

  #;((listof syntax?) -> (values (listof syntax?) (listof syntax?) (listof syntax?) (listof syntax?)))
  ; accepts a list of partially expanded class-level definitions and returns them grouped into
  ; syntax definitions, value definitions, field declarations, and top-level exprs
  (define (group-class-decls exprs)
    (syntax-parse exprs
      #:literals (define-values define-syntaxes field)
      [((~alt (~and defn (define-values . _))
              (~and stx-defn (define-syntaxes . _))
              (~and field-decl (field . _))
              expr)
        ...)
       (values (attribute stx-defn)
               (attribute defn)
               (attribute field-decl)
               (attribute expr))]))

  #;((listof syntax?) (listof syntax?) (listof syntax?) (listof syntax?) definition-context? -> syntax?)
  ; compile the partially expanded class-level definitions into pure racket code.
  ; This is the actual class logic.
  (define (compile-class-body defns stx-defns fields exprs def-ctx)
    (add-decl-props
     def-ctx
     (append fields stx-defns defns)
     (syntax-parse (list stx-defns defns fields exprs)
       #:literals (define-values field)
       [(((define-syntaxes (stx-name:id ...) stx-rhs:expr) ...)
         ; I know ~datum for lambda is bad, but I don't know how to do this correctly
         ; There are at least two distinct (by free-identifier=?) "lambda"s that could end up here
         ((define-values (method-name:id) ((~datum lambda) (method-arg:id ...) method-body:expr ...)) ...)
         ; only 1 field definition allowed
         ((~optional (field field-name:id ...) #:defaults ([(field-name 1) null])))
         (expr ...))
        (check-duplicate-method-names (attribute method-name))
        (define num-fields (length (attribute field-name)))
        (define/syntax-parse (field-index ...) (build-list num-fields (lambda (n) #`#,n)))
        #'(let ()
            (letrec-syntaxes ([(stx-name ...) stx-rhs]
                              ...
                              [(method-name) (make-variable-like-transformer #'(lambda args (send this method-name . args)))]
                              ...)
              (letrec ([method-table
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
                          (let ([this-val (object (vector field-name ...) cls)])
                            (let ([fields (object-fields this-val)])
                              (let-syntax ([field-name (make-vector-ref-transformer #'fields #'field-index)]
                                           ...)
                                (syntax-parameterize ([this (make-variable-like-transformer #'this-val)])
                                  ; ensure body is non-empty.
                                  (void)
                                  expr
                                  ...)))
                            this-val))]
                       [method-name->index
                        (make-name->index (list #'method-name ...))]
                       [cls
                        (class-info method-name->index method-table constructor)])
                cls)))])))
  #;((listof identifier?) -> void?)
  ; If there are (symbolically) duplicate method names, error
  (define (check-duplicate-method-names names)
    (let ([duplicate (check-duplicates names #:key syntax->datum)])
      (when duplicate
        (raise-syntax-error #f "a method with same name has already been defined" duplicate)))))

#;((listof identifier?) -> (identifier? -> natural?))
; Create a function that maps method names to their method table indices
(define (make-name->index names)
  (let ([table (make-hasheq (map (lambda (id index) (cons (syntax->datum id) index))
                                 names
                                 (build-list (length names) identity)))])
    (lambda (name)
      (hash-ref table (syntax->datum name) (lambda () (error 'send "no such method ~a" name))))))

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
     #'(send-rt obj #'method-name (list arg ...))]
    [(_ obj:expr method-name:id . args)
     #'(send-rt obj #'method-name args)]))

(define (send-rt obj method-name-stx args)
  (let* ([cls (object-class obj)]
         [index ((class-info-name->method-index cls) method-name-stx)]
         [method-table (class-info-method-table cls)]
         [method (vector-ref method-table index)])
    (apply method obj args)))

(module+ test)
