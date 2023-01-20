miniclass
=========
This is a collection of implementations of a small version of racket's class system.

The purpose of this project is for me to understand how dsl expanders used to work,
how syntax-spec works, how local expand works, to determine if syntax-spec is expressive enough
to implement a class system, and to serve as a vanilla-racket motivating example for a change to the
expander API that will allow syntax-spec-style suspensions to avoid creating quadratic re-expansions.
It is also a good example to motivate syntax-spec, since it shows the manual way and how much simpler
it is using syntax-spec.

I iterated several times and kept around old versions as comparisons. Here is the organization:

## simple

`simple` is a simple macro. It detects surface literals for simple definitions and overrides their behavior.
It does not support macros expanding to method definitions or field declarations, and does not support class-level expressions.

## local expand loop

`local-expand-loop` is a dsl expander. This how `class` and similar dsls were implemented before syntax-spec.
I local expand each form in the class body stopping at syntax definitions,
value definitions, and field declarations. As I do this, I bind field names, method names, and macro names.
After the "first pass" of expansion, I collect the different types of definitions and declarations and compile them to plain
racket to implement the class.

This supports the following things that the previous implementation didn't support:

- Multiple field declaration forms
- Local macro definitions (at the class level)
- Macro use at the class-level (can expand to a method definition)
- Class-level expressions (evaluated at construction time)

Problems with this implementation:

- Evaluates the transformer of each syntax definition twice: once in the "first pass" for class-level usages and again
during the expansion of emitted syntax since the syntax definitions end up in the emitted syntax so class bodies have access to them.

## syntax-spec style

`bs-manual` is similar to what syntax-spec does. To avoid re-evaluation of transformers, we create suspensions that capture the definition context which
includes the bindings for the transformers. Instead of emitting syntax definitions for expansion of method bodies, we suspend them with this context such that
when they are expanded, they are local-expanded under the stored definition context which includes the transformer bindings. This reduces the size of the expanded
code and avoids re-evaluating transformers.

Problems with this implementation:

- Since method bodies get local-expanded and then re-expanded after emission, nested classes can lead to quadratic re-expansions

The problem is that the expander doesn't trust our local-expanded code and re-expands it.
Ideally, we could use `syntax-local-expand-expression`, but that function doesn't accept a definition
context. If a variable binidng was in the context, the expander could not trust that the variable would
end up being defined in the emitted code. However, if the definition context only contained transformer bindings,
their references would all expand away, and thus, the expander could safely substitute the result.
If the expander were to have this change made, we could replace the `local-expand` with a `syntax-local-expand-expression` when we resume suspensions. This would avoid the quadratic re-expansion problem.

## syntax-spec eager style

`bs-manual-eager` is like `bs-manual`, but immediately expands expression positions instead of creating suspensions.
Additionally, rather than purely using syntax parameters for `this`, dynamic parameters are used under the hood to allow eager
expansion of syntax parameter references. 
I did this just to see if it was possible. No advantages over non-eager that I can think of.

This method also has potentially quadratic re-expansions, which can be alleviated by the `syntax-local-expand-expression` change in a similar way.

## using syntax-spec

`bs-auto` uses the syntax-spec library. syntax-spec handles making a custom expander.

This method currently also has potentially quadratic re-expansions.
