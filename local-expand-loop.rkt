#lang racket

; This file is a "local-expand loop" style implementation of a small class system.
; Similar to the implementation of the 'block' macro.
; This improves over the simple implementation by allowing class-level macro uses and definitions.

(provide (all-defined-out))

(require racket/stxparam
         syntax/transformer
         "common.rkt"
         (for-syntax syntax/context
                     syntax/intdef
                     syntax/parse
                     syntax/transformer
                     racket/list))

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

(begin-for-syntax
  (define-syntax-class lambda-id
    (pattern (~or (~literal lambda) (~literal #%plain-lambda)))))

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
       #:literals (define-syntaxes define-values field)
       [(((define-syntaxes (stx-name:id ...) stx-rhs:expr) ...)
         ((define-values (method-name:id) (lam:lambda-id (method-arg:id ...) method-body:expr ...)) ...)
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
              (letrec-syntaxes ([(method-name) (make-method-transformer #'find-self 'method-index)]
                                ...
                                [(field-name) (make-field-transformer #'find-self 'field-index)]
                                ...
                                [(stx-name ...) stx-rhs]
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
                                               (void)
                                               expr
                                               ...)
                                             self))]
                                        [method-name->index
                                         (make-name->index (list 'method-name ...))]
                                        [cls
                                         (class-info method-name->index method-table constructor)])
                                 cls))))])))
  
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
