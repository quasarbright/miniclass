#lang racket

; This file is a syntax-spec style implementation of a small class system.
; It does something like what syntax-spec does, but by hand.
; This improves over the local expand loop style by not re-evaluating syntax definitions
; However, it can potentially lead to quadratic re-expansions

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
       (let-values ([(defns fields exprs) (group-class-decls (local-expand-class-body stx def-ctx))])
         (compile-class-body defns fields exprs def-ctx))))))

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
                 (syntax-local-bind-syntaxes (syntax->list #'(id ...))
                                             #'rhs
                                             def-ctx)
                 ; don't care about syntax defns after pass1
                 (loop todo r)]
                [(define-values (id:id ...) rhs)
                 (unless (= 1 (length (attribute id)))
                   (raise-syntax-error #f "each method must be defined separately" this-syntax))
                 (define/syntax-parse rhs^ (syntax-parse #'rhs
                                             [((~and their-lambda (~datum lambda)) args body ...)
                                              ; you have to expand the body separately
                                              ; so you can detect lambda later
                                              #`(their-lambda args #,(suspend-expr #'(begin body ...) def-ctx))]))
                 ; bind method ids to transformers in the def-ctx
                 (define/syntax-parse (method-name) #'(id ...))
                 (with-syntax ([(method-name) (syntax-local-bind-syntaxes (list #'method-name)
                                                                     #'(make-variable-like-transformer
                                                                        #'(lambda args (send this method-name . args)))
                                                                     def-ctx)])
                   (loop todo (cons (datum->syntax
                                     expr
                                     (list #'define-values #'(method-name) #'rhs^)
                                     expr
                                     expr)
                                    r)))]
                [(field field-name:id ...)
                 ; NOTE this only works for a single field declaration
                 (define/syntax-parse (field-index ...) (build-list (length (attribute field-name)) (λ (n) #`#,n)))
                 (with-syntax ([(field-name ...) (syntax-local-bind-syntaxes (syntax->list #'(field-name ...))
                                                                             #'(values (make-variable-like-transformer
                                                                                        #'(vector-ref (object-fields this)
                                                                                                      field-index)
                                                                                        #'(lambda (v)
                                                                                            (vector-set! (object-fields this)
                                                                                                         field-index
                                                                                                         v)))
                                                                                       ...)
                                                                             def-ctx)])
                   (loop todo (cons (datum->syntax
                                     expr
                                     #'(field field-name ...)
                                     expr
                                     expr)
                                    r)))]
                ; This is a plain top-level expression to be evaluated in the constructor
                ; Just suspend
                [_
                 (define/syntax-parse e^ (suspend-expr this-syntax def-ctx))
                 (loop todo (cons #'e^ r))]))))))

  #;(syntax? definition-context? -> syntax?)
  ; create a suspension which captures the internal definition context, which contains
  ; bindings for syntax and method transformers
  (define (suspend-expr stx def-ctx)
    ; wrap ctx in a pair because #f is valid as ctx but not as a syntax
    ; property value.
    (syntax-property #`(#%host-expression #,stx) 'miniclass-def-ctx (list def-ctx)))

  #;((listof syntax?) -> (values (listof syntax?) (listof syntax?) (listof syntax?)))
  ; accepts a list of partially expanded class-level definitions and returns them grouped into
  ; syntax definitions, value definitions, field declarations, and top-level exprs
  (define (group-class-decls exprs)
    (syntax-parse exprs
      #:literals (define-values field)
      [((~alt (~and defn (define-values . _))
              (~and field-decl (field . _))
              expr)
        ...)
       (values (attribute defn)
               (attribute field-decl)
               (attribute expr))]))

  #;((listof syntax?) (listof syntax?) (listof syntax?) internal-definition-context? -> syntax?)
  ; compile the partially expanded class-level definitions into pure racket code.
  ; This is the actual class logic.
  (define (compile-class-body defns fields exprs def-ctx)
    (add-decl-props
     def-ctx
     (append fields defns)
     (syntax-parse (list defns fields exprs)
       #:literals (define-values field)
       [(; I know ~datum for lambda is bad, but I don't know how to do this correctly
         ; There are at least two distinct (by free-identifier=?) "lambda"s that could end up here
         ((define-values (method-name:id) ((~datum lambda) (method-arg:id ...) method-body:expr ...)) ...)
         ; only 1 field definition allowed
         ((~optional (field field-name:id ...) #:defaults ([(field-name 1) null])))
         (expr ...))
        (check-duplicate-method-names (attribute method-name))
        ; If we didn't rename, we'd say `field-name` in the constructor's arguments, which would shadow the transformer binding
        ; This would make set! on a field at class-level not mutate the actual field, but rather the constructor argument.
        (define/syntax-parse (field-name-renamed ...) (generate-temporaries #'(field-name ...)))
        #'(letrec ([method-table
                  (vector (lambda (this-arg method-arg ...)
                            ; to support class-level expressions that may call methods and fields,
                            ; this will have to be done around class-level expressions too
                            (syntax-parameterize ([this (make-variable-like-transformer #'this-arg)])
                              method-body
                              ...))
                          ...)]
                 [constructor
                  (lambda (field-name-renamed ...)
                    (let ([this-val (object (vector field-name-renamed ...) cls)])
                      (syntax-parameterize ([this (make-variable-like-transformer #'this-val)])
                        ; ensure body is non-empty
                        (void)
                        expr
                        ...)
                      this-val))]
                 [method-name->index
                  (make-name->index (list #'method-name ...))]
                 [cls
                  (class-info method-name->index method-table constructor)])
          cls)])))
  #;((listof identifier?) -> void?)
  ; If there are (symbolically) duplicate method names, error
  (define (check-duplicate-method-names names)
    (let ([duplicate (check-duplicates names #:key syntax->datum)])
      (when duplicate
        (raise-syntax-error #f "a method with same name has already been defined" duplicate)))))

(define-syntax #%host-expression
  (syntax-parser
    [(_ e:expr)
     (let ([def-ctx (car (syntax-property this-syntax 'miniclass-def-ctx))])
       ; ctx needs to be empty instead of #f because we need to
       ; recursively expand subexpressions. We need to expand references of bindings
       ; defined in the def-ctx now because the bindings will disappear later.
       ; If you provide #f, local-expand doesn't expand subexpressions
       (local-expand #'e 'expression '() def-ctx))]))

#;((listof identifier?) -> (identifier? -> natural?))
; Create a function that maps method names to their method table indices
(define (make-name->index names)
  (let ([table (make-hasheq (map (lambda (id index) (cons (syntax->datum id) index))
                                 names
                                 (build-list (length names) identity)))])
    (lambda (name)
      (hash-ref table (syntax->datum name) (lambda () (error 'send "no such method ~a" name))))))

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
