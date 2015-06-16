---
title: TIP Tools
abstract: We show our new toolbox for inductive theorem provers and benchmarks.
---

# Introduction

We have observed a new growth in interest in automated inductive theorem proving,
with support in dedicated and general theorem provers and assistants
such as Zeno, HipSpec, Hipster, CVC4, Pirate, Dafny, and the Graph Thingy.
Spurred by this we started collecting benchmarks to be able to compare and
evaluate theorem provers (in earlier work TIP). At the time of writing, we
have 351 benchmarks.

However, they don't support the same formats.
We identify a core of what the different theorem provers use and need.

Maybe some example property right here

## Contributions

* In the benchmark article the language layout was not discussed in much detail,
  so this article complements the benchmark article

* Tool chain with exciting capabilities
    (input formats (including Haskell) (add Why3 input?))
    (output formats)
    (passes)
    (can run tools: QuickSpec, HBMC, QuickCheck, FEAT, and so on)
  Should we try get a web interface up quickly?

* Our framework is general: we can support different "logic" or "semantics",

# Language design

Starting from SMT-LIB, we already have much of what is needed:

* Asserts
* Data-types (unofficial, but still widely adopted)
* Integers (all in all, UFNIA can be reached through our benchmarks)
* Function declarations

Added by others:

* polymorphic asserts

We added:

* polymorphic declarations
* higher-order functions

## Semantics

Function declarations are given the semantics as their non-computable axiomatisation.

### Semantics for partiality

We can support these semantics:

* Isabelle-style with uninterpreted function values
  (blanchettification for partial matches)

* Haskell by lifting every value to be effectively a maybe type
  (todo)

# QuickSpec

Blanchettification for uninterpreted functions (also discussed in Hipster article)

Allows theroem provers to use QuickSpec theory exploration in their tools

Not implemented: tuples to get right arity of QuickSpec functions
                 (needs a tuple constructor with size 0)

# Passes

Implemented:

* Simplification
* Removing newtypes
* Uncurrying the theory
* Negating conjecture
* Discriminators to match
* Match to discriminators
* Commuting match upwards
* Collapsing equal functions
* Removing alias functions
* Lambda lifting
* Let lifting
* Axiomatizations of lambdas
* CSE on match
* Elimination of dead code (partially implemented)
* Bool to if
* If to bool

Not yet implemented:

* Monomorphisation
* Induction
* Case lifting (could show that we can use Waldmeister)
* Axiomatizations of theories
  (example: Int with only comparisons should be come an abstract total order)
* Bottom-semantics a'la Haskell

# Future work

Future backends: Leon, Smallcheck, THF, TFF

Coinduction (reference to CVC work)

