#lang racket

; This file is a bindingspec style implementation of a small class system.
; It does what bindingspec does, but by hand.
; This improves over the local expand loop style by not re-evaluating syntax definitions
; However, it can potentially lead to quadratic re-expansions

(module+ test (require rackunit))
(provide (all-defined-out))

(require racket/stxparam syntax/transformer (for-syntax syntax/context syntax/intdef syntax/parse syntax/transformer))

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
(define-class-syntax-parameters this this%)
(define this-parameter (make-parameter #f))
(define this%-parameter (make-parameter #f))

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

; initially copied from https://github.com/racket/racket/blob/a17621bec9216edd02b44cc75a2a3ad982f030b7/racket/collects/racket/block.rkt
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
  (define (local-expand-class-body/pass-1 stx def-ctx)
    (let*
        ([ctx (generate-expand-context #t)]
         [stoplist (list #'begin #'define-syntaxes #'define-values #'field #'lambda #'this #'this%)]
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
    (local-expand #`(syntax-parameterize ([this (make-variable-like-transformer #'(this-parameter))]
                                          [this% (make-variable-like-transformer #'(this%-parameter))])
                      #,stx)
                  'expression
                  '()
                  def-ctx))

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
           #:literals (define-values field)
           [(define-values . _)
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

  #;((listof syntax?) (listof syntax?) (listof syntax?) internal-definition-context? -> syntax?)
  ; compile the partially expanded class-level definitions into pure racket code.
  ; This is the actual class logic.
  (define (compile-class-body defns fields exprs def-ctx)
    (add-decl-props
     def-ctx
     (append defns)
     ; TODO better error messages
     (syntax-parse (list defns fields exprs)
       #:literals (define-values field)
       [(; I know ~datum for lambda is bad, but I don't know how to do this correctly
         ; There are at least two distinct (by free-identifier=?) "lambda"s that could end up here
         ((define-values (method-name:id) method-expr:expr) ...)
         ; only 1 field definition allowed
         ((~optional (field field-name:id ...) #:defaults ([(field-name 1) null])))
         (expr ...))
        (check-duplicate-method-names (attribute method-name))
        (define num-fields (length (attribute field-name)))
        (define/syntax-parse (field-index ...) (build-list num-fields (lambda (n) #`#,n)))
        #'(let ()
            (letrec ([method-table
                      (vector
                       (lambda (this-arg . args)
                         (parameterize ([this-parameter this-arg])
                           (let ([fields (object-fields this-arg)])
                             (let-syntax ([field-name (make-vector-ref-transformer #'fields #'field-index)]
                                          ...)
                               (let ([method method-expr])
                                 (unless (procedure? method)
                                   (error 'class "definition of method ~a is not a procedure" #''method-name))
                                 (apply method args))))))
                       ...)]
                     [constructor
                      (lambda (field-name ...)
                        (let ([this-val (object (vector field-name ...) cls)])
                          (let ([fields (object-fields this-val)])
                            (let-syntax ([field-name (make-vector-ref-transformer #'fields #'field-index)]
                                         ...)
                              (parameterize ([this-parameter this-val])
                                ; I'm just putting this here to ensure that the body is non-empty
                                ; That's ok, right?
                                (void)
                                expr
                                ...)))
                          this-val))]
                     [method-name->index
                      (make-name->index (list #'method-name ...))]
                     [cls
                      (class-info method-name->index method-table constructor)])
              cls))])))
  #;((listof identifier?) -> void?)
  ; If there are (symbolically) duplicate method names, error
  (define (check-duplicate-method-names names)
    (let loop ([ids names] [seen-symbols '()])
      (cond
        [(null? ids) (void)]
        [(member (syntax->datum (car ids)) seen-symbols)
         (raise-syntax-error #f "a method with same name has already been defined" (car ids))]
        [else
         (loop (cdr ids) (cons (syntax->datum (car ids)) seen-symbols))]))))

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
