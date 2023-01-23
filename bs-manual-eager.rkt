#lang racket

; This file is a syntax-spec style implementation of a small class system.
; It does something like what syntax-spec does, but by hand.
; However, rather than suspending host expressions like syntax-spec, they are eagerly expanded.
; Like the non-eager variant, this implementation risks quadratic re-expansions.

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

(begin-for-syntax
  #;(symbol? -> transformer?)
  ; creates a transformer that errors out when used outside of a class
  (define (make-literal-transformer id-sym)
    (syntax-parser
      [_ (raise-syntax-error id-sym "used outside of a class" this-syntax)])))

(define-syntax field (make-literal-transformer 'field))
(define-syntax-parameter this
  (make-expression-transformer
   (make-literal-transformer 'this)))
(define this-parameter (make-parameter #f))

(begin-for-syntax
  (define-syntax-class lambda-id
    (pattern (~or (~literal lambda) (~literal #%plain-lambda)))))

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

  #;(syntax? internal-definition-context? -> (listof syntax?))
  ; expand the body of the class expression using the given definition context
  ; returns a list of eagerly expanded class-level forms.
  ; expands to just field declarations and method definitions.
  ; also expands rhs of define-values in a second pass.
  (define (local-expand-class-body stx def-ctx)
    (let* ([stx^ (local-expand-class-body/pass-1 stx def-ctx)]
           [stx^^ (local-expand-class-body/pass-2 stx^ def-ctx)])
      stx^^))

  #;(syntax? definition-context? -> (listof syntax?))
  ; pass 1 of expansion.
  ; bind transformers for methods and local macros.
  ; expand up to define-values, define-syntaxes, and field.
  ; does not expand rhs of define-values.
  ; splices begins.
  (define (local-expand-class-body/pass-1 stx def-ctx)
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
                     ; don't care about syntax defns after pass1
                     (loop todo r)))]
                [(define-values (id:id ...) rhs)
                 (unless (= 1 (length (attribute id)))
                   (raise-syntax-error #f "each method must be defined separately" this-syntax))
                 ; bind method ids to transformers in the def-ctx
                 (define/syntax-parse (method-name) #'(id ...))
                 (with-syntax ([(id ...) (syntax-local-bind-syntaxes (syntax->list #'(id ...))
                                                                     #'(make-variable-like-transformer
                                                                        #'(lambda args (send this method-name . args)))
                                                                     def-ctx)])
                   (loop todo (cons (datum->syntax
                                     expr
                                     (list #'define-values #'(id ...) #'rhs)
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
                 ; don't need to touch e right now
                 (loop todo (cons this-syntax r))]))))))

  #;((listof syntax?) internal-definition-context? -> (listof syntax?))
  ; expand references to method names and local macros
  ; in method bodies and class-level exprs
  (define (local-expand-class-body/pass-2 exprs def-ctx)
    (for/list ([expr exprs])
      (syntax-parse expr
        #:literals (define-values field)
        ; we're guaranteed that all define-values have single ids at this point
        ; since it's checked in pass 1
        [(define-values (id:id) rhs)
         (define/syntax-parse rhs^ (local-expand-class-expression #'rhs def-ctx))
         #'(define-values (id) rhs^)]
        [(field id:id ...)
         this-syntax]
        ; This is a plain top-level expression to be evaluated in the constructor
        ; Just suspend
        [_
         (local-expand-class-expression this-syntax def-ctx)])))

  #;(syntax? internal-definition-context? -> syntax?)
  ; Fully expand syntax in an expression position inside of a class body.
  ; The definition context contains transformer bindings for methods and locally defined
  ; macros.
  (define (local-expand-class-expression stx def-ctx)
    ; this syntax-parameterize is necessary because references to the stxparams are about to be expanded away.
    (local-expand #`(syntax-parameterize ([this (make-variable-like-transformer #'(this-parameter))])
                      #,stx)
                  'expression
                  '()
                  def-ctx))

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
       [(((define-values (method-name:id) method-expr:expr) ...)
         ; only 1 field definition allowed
         ((~optional (field field-name:id ...) #:defaults ([(field-name 1) null])))
         (expr ...))
        (check-duplicate-method-names (attribute method-name))
        #'(let ()
            (letrec ([method-table
                      (vector
                       (lambda (this-arg . args)
                         (parameterize ([this-parameter this-arg])
                           (let ([method method-expr])
                             (unless (procedure? method)
                               (error 'class "definition of method ~a is not a procedure" #''method-name))
                             (apply method args))))
                       ...)]
                     [constructor
                      (lambda (field-name ...)
                        (let ([this-val (object (vector field-name ...) cls)])
                          (parameterize ([this-parameter this-val])
                            ; ensure body is non-empty
                            (void)
                            expr
                            ...)
                          this-val))]
                     [method-name->index
                      (make-name->index (list #'method-name ...))]
                     [cls
                      (class-info method-name->index method-table constructor)])
              cls))])))
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
