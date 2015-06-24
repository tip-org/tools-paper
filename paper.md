---
title: TIP Tools for Inductive Theorem Provers
abstract: We show our new toolbox for inductive theorem provers and benchmarks.
---

# Introduction

We have observed a new growth in interest in automated inductive theorem
proving, with support in dedicated and general theorem provers and assistants
such as Zeno [@zeno], HipSpec [@hipspecCADE], Hipster [@hipster], CVC4 [@cvc4],
Pirate [@SPASSInduction], Dafny [@dafny], and the Graphsc [@graphsc].  Spurred
by this we started collecting benchmarks to be able to compare and evaluate
theorem provers (in earlier work [@TIP-benchmarks]). At the time of writing, we
have 351 benchmarks.

However, they don't support the same formats.
We identify a core of what the different theorem provers use and need.

This paper accompanies the test suite and is an exciting tool on its own.

In comparison to Why3 [@boogie11why3],
* not an own format: uses smtlib with small extensions
* light weight:
    * no enforced termination check on fucntion definitions
    * no module system
* low-overhead encodings to underlying theorem provers (comparisons?)
We can work in harmony together with Why3, and to that end we
have a why3 output mode to be able to tap into
the resources provided by them.
Using Why3 (WhyML?) as an input format is considered, or adding our
extension to smtlib as an output to Why3.

With this work we want to work on closing the gap on the inductive theorem
proving part that is open even in the precense of work like Why3.
Outstanding differences to Why3:
* a more light-weight monomorphisation pass
* haskell frontend
* no termination check
* quickspec support
* low-level format suitable for expressing benchmarks
* todos^[induction passes, partiality semantics]

We have boiled down our knowledge from writing HipSpec [@hipspecCADE], which
connects Haskell, our theory exploration tool QuickSpec [@quickspec] and SMT
and FO theorem provers.  With this work, we modularize it and make it
accessible for the community.

Your may have an new idea in one of these areas, for instance an amazing idea
of a new induction principle.  This tool enables you to try it out with the
existing infrastructure of a state-of-the-art inductive theorem prover.
Because, when you make an inductive theorem prover, there are lots of stuff
to take into consideration and deal with, including:

* lambdas and higher-order functions,
* polymorphism,
* a frontend to be able to type in problems,
* benchmarks,
* connecting to an underlying SMT or FO prover,
* lemma discovery,
* falsifying conjectures^[which is usually not the focus of an inductive
  prover, so you don't end up spending time on proving non-theorems
  (hbmc/quickcheck)],
* instantiating induction schemas

Our library contains many ingredients important for inductive
theorem proving, for instance theory exploration. We show how to use the
current infrastructure to connect the induction mode in CVC4 [@cvc4] with
QuickSpec2 [@quickspec], in a bash script! (Add induction tactic to tip to use
a theorem prover without induction (Z3 or with monotonox allows us to use E or
vampire...) this is the essence of HipSpec, of course)

This work has two different goals:

* To encourage people to write their own provers (based on our API or command-line tools or whatever)
* To ease interopability with existing (and future provers) that want to use their own format.

Maybe some example property right here: side by side comparison
of format supported by CVC4 and SMTInd.

## Random example

In our format

```{.tip-include }
example.smt2
```

After monomorphisation, lambda lifting, match to if-then-else and axiomatization of function
declarations:

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

## Uncurrying the theory

Our Haskell frontend makes a faithful rendition of its
curried nature: functions take one argument at a time,
returning a new function in case there are more arguments
coming. This makes partial application easy. When
translating to our logic format, it gets very inefficient
to have all the lambdas and applications around.
This can be used for other higher-order input formats.
To mitigate this, we have a pass that tries to
uncurry the top-level definitions of the theory
as much as possible.

```{.tip-include}
double-curried.smt2
```

```{.tip-include .UncurryTheory}
double-curried.smt2
```

#### Discussion
Currently, the pass tries to uncurry as many arguments
as possible, but sometimes it would seem more economical
in number of eta-expansions required to keep some
arguments curried. In the example above, if `double`
is only passed to a higher-order argument to
functions like `twice`, it can be kept curried.
Then the assertion can be expressed withot an
eta-expansion.

## Lambda lifting and axiomatization of lambdas

To enable theorem provers that have no support
for first-class functions and lambdas, we can
defunctionalise the program and axiomatize
the closures. The `twice`-`double` example
above then becomes:

```{.tip-include .UncurryTheory .LambdaLift .AxiomatizeLambdas}
double-curried.smt2
```

A new abstract sort, `fun1` has been introduced
which stands for functions taking one argument.
The function `apply1` applies an argument to a fun.

Furthermore, the theory can be monomorphised to
remove the polymorphism from `fun1`:

```{.tip-include .UncurryTheory .LambdaLift .AxiomatizeLambdas .Monomorphise}
double-curried.smt2
```

## Monomorphisation

We monomorphise the problem wrt to the types occurring
in the goals (`assert-not`).

Monomorphisation can fail in the case of polymorphically
recursive functions or datatypes. A non-regular
data types like this will not be monomorphiseable:

```.tip
(declare-datatypes (a) (irreg ((last (value a)) (more (values (irreg (irreg a))))
```

Assertions can essentially encode polymorphic properties, too.
```
example with concat and map, or a simpler one
```

Monomorphisation can be incomplete even when it succeeds.
One example is where `append` is used on `list A`,
but not on `list B`. But the proof might need a lemma
about append on `list B`!

We successfully monomorphised 350 of our 351 benchmarks;
the failing one has an irregular data type.

We could make a complete encoding of types
using ideas from Nick's paper.

## Other passes

* Simplification
* Removing newtypes
* Negating conjecture

* Discriminators to match
* Match to discriminators
  (actually we can already run Waldmeister by axiomatizing if-then-else and the discriminator functions)

* Bool to if
* If to bool

* Commuting match upwards
* Collapsing equal functions
* Removing alias functions
* Let lifting
* CSE on match
* Elimination of dead code (partially implemented)

Not yet implemented:

* Induction
* Axiomatizations of theories
  (example: Int with only comparisons should be come an abstract total order)
* Bottom-semantics a'la Haskell
* Case only on variables and unroll defaults
  (another way to make a theory UEQ)

# Future work

Future backends: Leon, Smallcheck, THF, TFF

Coinduction (reference to CVC work)

# References

