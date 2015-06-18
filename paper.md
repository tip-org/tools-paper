---
title: TIP Tools
abstract: We show our new toolbox for inductive theorem provers and benchmarks.
---

# Introduction

We have observed a new growth in interest in automated inductive theorem proving,
with support in dedicated and general theorem provers and assistants
such as Zeno, HipSpec, Hipster, CVC4, Pirate, Dafny, and the Graphsc.
Spurred by this we started collecting benchmarks to be able to compare and
evaluate theorem provers (in earlier work TIP). At the time of writing, we
have 351 benchmarks.

However, they don't support the same formats.
We identify a core of what the different theorem provers use and need.

Furthermore, our library contains many ingredients important for inductive
theorem proving, for instance theory exploration. We show how to use
the current infrastructure to connect the induction mode in CVC4 with
QuickSpec2, in a bash script! (Add induction tactic to tip to use
a theorem prover without induction
(Z3 or with monotonox allows us to use E or vampire...)
this is the essence of HipSpec, of course)

Maybe some example property right here: side by side comparison
of format supported by CVC4 and SMTInd.

```{.tip-include }
example.smt2
```

```{.tip-include
    .TypeSkolemConjecture .Monomorphise .LambdaLift
    .AxiomatizeLambdas .Monomorphise .NegateConjecture
    .RemoveMatch .AxiomatizeFuncdefs}
example.smt2
```

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

* We show how the command-line tools can be used to boost an inductive
  theorem prover, dubbed Rudimentophocles.
  Ultimately, we can envision our tool set to be a platform for
  experimenting with induction. Developers will then not need
  to make a theorem prover from scratch, but rather plug methods
  from new insights in the existing infrastructure to be able
  to evaluate it quickly.

# The format

Side-by-side comparison of SMT-LIB and our format,
to discuss the different additions.

(with other formats)

For the different output formats:

For CVC4, we remove all non-SMT-LIB stuff:
    HOFs, assert-not, (parametric definitions) (function definitions)

For Isabelle, we replace case with left-hand-side match

For Haskell, we replace non-computable parts with uninterpreted functions
    -- Equality:
        maintain a set of functions that have an Eq constraint
        we start off by the only function being equals.
        when you look for functions that call functions that have
        an eq constraint then it gets an eq constraint added.
        then you repeat until you get a fixpoint.

`tip-spec`... `tip-qc`/`hbmc`

For TFF1, we axiomatize data types and function definitions
    (the latter can be done in two different ways)

For FOF, we use Monotonox (but what about the booleans?!)

For THF, we add induction "schema" for data types.

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

Allows theorem provers to use QuickSpec theory exploration in their tools

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

