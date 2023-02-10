This file compares low-level syntax api calls bewteen local expand loop and bs auto

local-expand-loop:
definition contexts:
* syntax-local-make-definition-context
* generate-expand-context
* internal-definition-context-add-scopes
* syntax-local-bind-syntaxes

syntax property propagation for IDE:
* internal-definition-context-track
* syntax-property
* origin, disappeared use, disappeared binding

low-level syntax object manipulation:
* syntax->list
* datum->syntax

local expansion:
* local-expand
* local-transformer-expand



both:
* make-expression-transformer
* make-variable-like-transformer
* make-rename-transformer
* generate-temporaries
* define-syntax-parameter, syntax-parameterize
* syntax->datum
* raise-syntax-error

bs-auto:

slocs:
bs-auto: 97
local-expand-loop: 152
