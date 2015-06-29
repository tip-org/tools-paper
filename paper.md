---
abstract: We show our new toolbox for inductive theorem provers and benchmarks. Encourage development of provers etc.
---

# Introduction

More and more people are making inductive theorem provers. New
inductive provers include Zeno [@zeno], HipSpec [@hipspecCADE],
Hipster [@hipster], Pirate [@SPASSInduction] and Graphsc [@graphsc],
while the CVC4 [@cvc4] and Dafny [@dafny] systems have gained
induction support.

Spurred on by the new interest in inductive theorem proving, we
recently introduced a suite of inductive benchmarks [@TIP-benchmarks],
which currently stands at 343 problems. The benchmarks are expressed
in our TIP format, a rich language containing inductive datatypes,
built-in integers, higher-order functions, polymorphism, recursive
function definitions and first-order logic.

#### Translating TIP to other formats

We also developed a tool to translate TIP to other formats. As very
few inductive provers support all TIP's features, the tool's main job
is to encode features that the prover does not support. For example,
if a prover does not support polymorphism, the TIP tool can
monomorphise the problem.

#### TIP as a toolbox

These provers vary widely: some support polymorphic types, some don't;
some understand higher-order functions, some don't; some reason about
programs, some about logical formulas.

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

# (the format)

Rather than developing an own format from scratch,
we use the already designed SMT-LIB format, which
is already supported by most SMT provers.

We use

* Datatypes, including match-expressions (in the 2.6 draft)
* Recursive function definitions (from 2.5).
  Although this can seem to only matter for some provers,
  this is actually more universal:
  for instance it can help in selecting the trigger
  or orienting the equation
  (typically left-to-right for function definitions).

Our own additions are:

* Polymorphic function definitions and assertions (asserts are for inclusion to CVC4)
* Higher-order function and lambda functions (our own syntax)
* Assert-not to be able to identify what the goal is.
  This corresponds to `goal` in Why3.
  In fact, the CVC4 induction mode needs to know which quantifier
  to do induction on: it cannot be skolemized by hand. So an
  `assert-not` makes sense in their work, too.

SMT-LIB is extensible through theories. Currently,
the only theory we use in the benchmarks are
Integers, but when the need arises, this can be
extended to bit vectors, arrays, sets, reals, floats, and so on,
as described by the SMT-LIB theories.

Side-by-side comparison of SMT-LIB and our format,
to discuss the different additions. (with other formats)

## Translation to other formats

* To vanilla SMT (for provers like CVC4 and Z3),
  We remove our own additions: HOFs, assert-not, (parametric definitions) (function definitions).

* To Isabelle, case is replaced with left-hand-side match

* To Haskell, we replace non-computable parts with uninterpreted functions.
  ^[We could also support translating equality by
    maintaining a set of functions that have an Eq constraint
    we start off by the only function being equals.
    when you look for functions that call functions that have
    an eq constraint then it gets an eq constraint added.
    then you repeat until you get a fixpoint.]

Sketches how to do other formats:

* to TFF1 (Typed first-order logic with rank1 types)
  Axiomatize data types and function definitions
  (the latter can be different ways: either recover pattern matching
  on left-hand-sides, or use discriminators and projections.)

* to FOF, First-order logic (unityped), we use Monotonox.
  (but what about the booleans?! one solution: FOOL)

* to THF, we use the TFF1 format, but we add induction "schema" for data types.

## (semantics)

Function declarations are given the semantics as their non-computable axiomatisation.

### Semantics for partiality

We can support these semantics:

* Isabelle-style with uninterpreted function values
  (blanchettification for partial matches)

* Haskell by lifting every value to be effectively a maybe type
  (todo)

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

```{.tip .no-check-sat}
(declare-datatypes
  (a) ((irreg (last (value a)) (more (values (irreg (irreg a)))))))
(check-sat)
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

# All the tools

## Theory exploration by QuickSpec

`tip-spec`

Blanchettification for uninterpreted functions (also discussed in Hipster article)

Allows theorem provers to use QuickSpec theory exploration in their tools

^[Not implemented: tuples to get right arity of QuickSpec functions
                 (needs a tuple constructor with size 0)]


## Counterexamples to non-theorems by QuickCheck and HBMC

`tip-qc`

`hbmc`

# Case study: Rudimentophocles

(where should this go?)

Rudimentophocles^[Named after the lesser-known Greek philosopher.] is
a basic inductive theorem prover with lemma discovery written in shell
script. It uses CVC4 to do the induction, QuickSpec to do the lemma
discovery and TIP to connect the two. It is not intended as a real
theorem prover, but rather a demonstration of what TIP can do.

# Future work

Future backends: Leon, Smallcheck, THF, TFF

Coinduction (reference to CVC work)

\printbibliography

\appendix

# Rudimentophocles

``` {.bash}
#!/bin/bash

# Run the input file through QuickSpec.
# Discovered lemmas get added as new goals.
IFS=' '
file=$(tip-spec $1 | grep -A1000000 '^;;')

# Read a problem from stdin and try to prove as many goals as possible.
# Takes a single parameter, which is the timeout to give to CVC4.
prove() {
  file=$(cat)

  progress= # Set to yes if we manage to prove some goal.
  n=0       # The index of the goal we're trying to prove now.

  while true; do
    # Check that n isn't out of bounds.
    if echo $file|tip --select-conjecture $n >& /dev/null; then
      # Make a theory where goal n is the only goal.
      goal=$(echo $file|tip --select-conjecture $n --smtlib)
      # Can we prove it without induction?
      result=$((echo '(set-logic ALL_SUPPORTED)'; echo $goal) |
               cvc4 --lang smt2.5 --tlimit=100)
      if [[ $result = unsat ]]; then
        # Proved without induction - delete the goal.
        echo -n ':D ' >&2
        file=$(echo $file|tip --delete-conjecture $n)
        progress=yes
      else
        # Can we prove the goal with induction?
        result=$((echo '(set-logic ALL_SUPPORTED)'; echo $goal) |
                 cvc4 --lang smt2.5 --tlimit=$1 --quant-ind)
        if [[ $result = unsat ]]; then
          # Proved with induction - change the goal into a lemma.
          echo -n ':) ' >&2
          file=$(echo $file|tip --proved-conjecture $n)
          progress=yes
        else
          # Failed to prove the goal - try the next one.
          echo -n ':( ' >&2
          ((n=$n+1))
        fi
      fi
    else
      # We've tried all goals - if we failed to prove any,
      # then stop, otherwise go round again.
      echo >&2
      if [[ -z $progress ]]; then break; fi
      progress=
      n=0
    fi
  done

  # Print out the final theory.
  echo $file
}

# Run the proof loop, gradually increasing the timeout.
for i in 100 400 1000; do
  file=$(echo $file | prove $i)
done

# Print the final theory out as WhyML so that it's easy to read.
echo
echo $file | tip --why
```
