STLC Talk [![Build Status](https://travis-ci.org/jonaprieto/stlctalk.svg?branch=master)](https://travis-ci.org/jonaprieto/stlctalk)
---

We present a formalization of the syntax in Agda for the Simple Typed Lambda Calculus (STLC)
with some of its properties and a description of the type-checking for this type system.

### Contents of this talk

[Download this talk](https://github.com/jonaprieto/stlctalk/raw/master/slides/slides.pdf)

- Lambda Calculus
- Typed Lambda Calculus
- Syntax Definitions
- Decidability of Type Assignment
- Well-Scoped Lambda Expressions
- Typability
- Type-checking

### Source code

We present a refactor of the implementation by
[@gergoerdi](https://github.com/gergoerdi/stlc-agda/) for the simple lambda calculus,
specifically in the [Scopecheck](https://github.com/jonaprieto/stlctalk/blob/master/src/Scopecheck.agda)
and [Typecheck](https://github.com/jonaprieto/stlctalk/blob/master/src/Typecheck.agda) module.

- Tested with Agda v2.5.2
- Using Agda Standard Library v0.13

### Install

We can find the source code in `src` directory.

```
$ git clone https://github.com/jonaprieto/stlctalk.git
$ cd stlctalk
$ agda src/README.agda
```

You can also use
[Agda-Pkg](https://github.com/jonaprieto/agda-pkg) to install this
library. Run this command after install agda-pkg tool:

```
$ agda-pkg install
```

### References

- Barendregt, Henk, Wil Dekkers, and Richard Statman (2013). *Lambda calculus with types*. Cambridge University Press.
- Danielsson, Nils Anders. [*Normalisation for the simply typed lambda calculus*](http://www.cse.chalmers.se/~nad/listings/simply-typed/).
- Érdi, Gergő (2013). [*Simply Typed Lambda Calculus in Agda, Without Shortcuts*](https://gergo.erdi.hu/blog/2013-05-01-simply_typed_lambda_calculus_in_agda,_without_shortcuts/).
