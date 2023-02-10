# Miniclass
Racket's `class` DSL is an example of a sophisticated macro-extensible DSL. It is different from the other DSLs we have discussed since it re-interprets Racket definitions in a special context, leveraging Racket's existing definition macros. It is its own DSL, but borrows more from Racket than a DSL like `match` does. Inside of a class, it is possible to define methods, declare fields, use macros, and define local macros:

```racket
; represents a location in two-dimensional space using cartesian coordinates
(define posn
  (class object%
    (super-new)
    (init-field x y)
    ; defines the specified method and declares it to be public
    (define-syntax-rule 
      (define/public (method-name method-arg ...) method-body ...)
      (begin (public method-name)
             (define (method-name method-arg ...) method-body ...)))
    (define/public (magnitude)
      (sqrt (+ (sqr x) (sqr y))))))
```

The above example defines a class representing a position and defines and uses a local macro which expands to a public method definition.

In order to compare syntax-spec to current methods, we implemented a small version of Racket's `class` DSL called `miniclass` which supports mutable fields, public methods, and definition and use of macros. We implemented it twice: One implementation uses syntax-spec and the other features a hand-written DSL expander in the style of Racket's current `class` implementation.

## Manual DSL Expander

One common way to implement a macro-extensible DSL in Racket is to implement an expander for the DSL using macros which invoke Racket's low-level expander API. Racket's `class` DSL is implemented in this way.

The DSL expander must loop over language forms and invoke the expander API to partially expand them and accumulate information about bindings in the Racket expander's compile-time environment. The expander must also manipulate scopes of syntax objects and propagate syntax properties from the surface syntax to the expanded code to ensure proper scoping rules and provide IDEs with static binding information.

Implementing such an expander requires advanced knowledge of Racket's expander, scoping, and syntax models as well as the low-level APIs exposed to work with them. This required knowledge is far beyond what is necessary to implement typical macros.

Here is a code snippet from the `miniclass` expander showing the expansion of macro and method definitions:

```racket
...
(syntax-parse expr
  #:literals (begin define-syntaxes define-values field)
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
  ...)
...
```

Here, we see the expansion of a macro definition using `local-transformer-expand`, compile-time environment management using `syntax-local-bind-syntaxes`, and syntax manipulation with `datum->syntax`.

## using syntax spec

Using syntax-spec, we can declaratively describe the grammar, scoping rules, and expander without having to implement them manually.

Here is the code for the entire expander for the `miniclass` DSL in syntax-spec:

```racket
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
```

The class body should be in a mutually recursive definition context, so we use a two-pass nonterminal. We allow Racket macros to be used in the class body with `#:allow-extension racket-macro`. Field declarations and method definitions export their bound names, `begin` re-exports from its sub-expressions since they get spliced in by the compiler. We also declare `class` to be a host interface as an entry point to the language and invoke the compiler in its definition.

## comparison/analysis

The syntax-spec implementation is much shorter and more concise than the hand-written expander implementation. The syntax-spec implementation is 97 SLOC, while the hand-written expander implementation is 152 SLOC. Both of these implementations include an expander and a compiler. However, the runtime backend is shared between them and not included in these line counts.

In addition to being shorter, the syntax-spec implementation is simpler and requires much less knowledge of the Racket expander. The manual expander implementation involves working with the expander's compile-time environment and scoping mechanisms, propagating syntax properties for the IDE, low-level syntax object manipulation, and manually invoking the expander. These are all abstracted away by syntax-spec and the language implementer only needs to declaratively describe extension points, the grammar, and the binding rules. 

Another advantage that syntax-spec has over hand-writing a DSL expander is that it is much easier to avoid expansion and compilation being coupled in an undesirable way. In the style of Racket's `class` implementation, it is necessary to re-bind macros in the compiler that have already been bound in the expander. While partially expanding class-level expressions, it is necessary to bind locally defined macros since they may be used in future class-level expressions. Then, the compiler must generate code that binds those same macros so they can be used in the bodies of definitions. This also leads to macro transformer expressions being evaluated multiple times. syntax-spec avoids both of these problems by automatically handling macro binding and expansion in DSL and host expressions in a way that only binds and evaluates macro transformers once.

--throw in the number of additional API operations in local expand loop (10) (is that really informative?)
