STLC Talk
---

We present a formalization of the syntax in Agda for the Simple Typed Lambda Calculus (STLC)
with some of its properties and a description of the type-checking for this type system.

### Contents of this talk

- Lambda Calculus
- Typed Lambda Calculus
- Syntax Definitions
- Decibility of Type Assignment
- Well-Scoped Lambda Expressions
- Typability
- Type-checking

### Source code

- Tested with Agda v2.5.2
- Using Agda Standard Library v0.13

### Install

The source code is in `src` directory and there, we
can find a `README.agda` file.

```
$ git clone https://github.com/jonaprieto/stlctalk.git
$ cd stlctalk
$ agda src/README.agda
```
Be sure to install this library `stlc.agda-lib` as
[Agda demands](http://agda.readthedocs.io/en/v2.5.2/tools/package-system.html).

You can also use
[Agda-Pkg](https://github.com/jonaprieto/agda-pkg) to install this
library. Run this command after install agda-pkg tool:

```
$ agda-pkg install
```

### References

- Barendregt, Henk, Wil Dekkers, and Richard Statman (2013). *Lambda calculus with types*. Cambridge University Press.
- Danielsson, Nils Anders. *Normalisation for the simply typed lambda calculus*.
- Érdi, Gergő (2013). *Simply Typed Lambda Calculus in Agda, Without Shortcuts*.
