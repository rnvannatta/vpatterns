# vpatterns
Pattern Matching in Chicken Scheme

This is a pattern matching library similar to the functionality in Haskell or OCAML. It is an implementation of the material which [SRFI-200](https://srfi.schemers.org/srfi-200/srfi-200.html) is based off of.

Example usage is:

```
(match '(one two) (#(x y) 'vector) ((x w) (cons x w) (else (error)) ; returns (one . two)
```
