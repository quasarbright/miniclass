#lang racket

; This file is a "local-expand loop" style implementation of a small class system.
; Similar to the implementation of the 'block' macro.
; This improves over the simple implementation by allowing class-level macro uses and definitions.

(module+ test (require rackunit))
(provide (all-defined-out))

(require racket/stxparam racket/syntax syntax/id-table (for-syntax syntax/context syntax/intdef syntax/stx syntax/parse syntax/transformer))

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

#|
before matching, local expand with stop-words field and define-values, then analyze

also support define-syntaxes in the class (another stop-name)

consult block macro that michael sent you!!!
https://github.com/racket/racket/blob/a17621bec9216edd02b44cc75a2a3ad982f030b7/racket/collects/racket/block.rkt

scoping rules too

as you expand to definitions, you need to make bindings

syntax-local-bind-syntaxes

internal-definition-context-add-scopes for inside outside edge (block doens't do it)
|#

; initially copied from https://github.com/racket/racket/blob/a17621bec9216edd02b44cc75a2a3ad982f030b7/racket/collects/racket/block.rkt
(define-syntax block
  (make-expression-transformer
   (lambda (stx)
     ;; Body can have mixed exprs and defns. Wrap expressions with
     ;; `(define-values () ... (values))' as needed, and add a (void)
     ;; at the end if needed.
     (let* ([def-ctx (syntax-local-make-definition-context)]
            [ctx (generate-expand-context #t)]
            ;; [kernel-forms (kernel-form-identifier-list)]
            [stoplist (list #'begin #'define-syntaxes #'define-values)]
            [init-exprs (let ([v (syntax->list stx)])
                          (unless v (raise-syntax-error #f "bad syntax" stx))
                          (cdr v))]
            [exprs
             (let loop ([todo init-exprs] [r '()])
               (if (null? todo)
                 (reverse r)
                 (let ([expr (local-expand (car todo) ctx stoplist def-ctx)]
                       [todo (cdr todo)])
                   (syntax-case expr (begin define-syntaxes define-values)
                     [(begin . rest)
                      (loop (append (syntax->list #'rest) todo) r)]
                     [(define-syntaxes (id ...) rhs)
                      (andmap identifier? (syntax->list #'(id ...)))
                      (with-syntax ([rhs (local-transformer-expand
                                          #'rhs 'expression null)])
                        (syntax-local-bind-syntaxes
                         (syntax->list #'(id ...))
                         #'rhs def-ctx)
                        (with-syntax ([(id ...) (map syntax-local-identifier-as-binding
                                                     (syntax->list #'(id ...)))])
                          (loop todo (cons (datum->syntax
                                            expr
                                            (list #'define-syntaxes #'(id ...) #'rhs)
                                            expr
                                            expr)
                                           r))))]
                     [(define-values (id ...) rhs)
                      (andmap identifier? (syntax->list #'(id ...)))
                      (let ([ids (syntax->list #'(id ...))])
                        (syntax-local-bind-syntaxes ids #f def-ctx)
                        (with-syntax ([(id ...) (map syntax-local-identifier-as-binding
                                                       (syntax->list #'(id ...)))])
                          (loop todo (cons (datum->syntax
                                            expr
                                            (list #'define-values #'(id ...) #'rhs)
                                            expr
                                            expr)
                                           r))))]
                     [else (loop todo (cons expr r))]))))])
       (let loop ([exprs exprs]
                  [prev-stx-defns null]
                  [prev-defns null]
                  [prev-exprs null])
         (cond
           [(null? exprs)
            (add-decl-props
             def-ctx
             (append prev-stx-defns prev-defns)
             #`(letrec-syntaxes+values
                #,(map stx-cdr (reverse prev-stx-defns))
                #,(map stx-cdr (reverse prev-defns))
                #,@(if (null? prev-exprs)
                       (list #'(void))
                       (reverse prev-exprs))))]
           [(and (stx-pair? (car exprs))
                 (identifier? (stx-car (car exprs)))
                 (free-identifier=? #'define-syntaxes (stx-car (car exprs))))
            (loop (cdr exprs)
                  (cons (car exprs) prev-stx-defns)
                  prev-defns
                  prev-exprs)]
           [(and (stx-pair? (car exprs))
                 (identifier? (stx-car (car exprs)))
                 (free-identifier=? #'define-values (stx-car (car exprs))))
            (loop (cdr exprs)
                  prev-stx-defns
                  (cons (car exprs)
                        (append
                         (map (lambda (expr)
                                #`(define-values () (begin #,expr (values))))
                              prev-exprs)
                         prev-defns))
                  null)]
           [else (loop (cdr exprs)
                       prev-stx-defns
                       prev-defns
                       (cons (car exprs) prev-exprs))]))))))

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
          stx)))))))

#;
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
