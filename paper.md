---
abstract: TIP is a toolbox for users and developers of inductive provers. It consists of a large number of tools which can, for example, simplify an inductive problem, monomorphise it or find counterexamples to it. We are using TIP to help maintain a set of benchmarks for inductive theorem provers, where its main job is to encode features that are not natively supported by the respective provers. TIP makes it easier to write inductive provers, by supplying necessary tools such as lemma discovery which prover authors can simply import into their own prover.
---

# Introduction

More and more people are making inductive theorem provers. As well as
specialised provers such as Zeno [@zeno], HipSpec [@hipspecCADE],
Hipster [@hipster], Pirate [@SPASSInduction] and Graphsc [@graphsc],
some traditionally non-inductive provers such as CVC4 [@cvc4] and
Dafny [@dafny] can now do induction.

There are many ingredients to a good inductive prover:

* It needs to instantiate induction schemas, either using structural
  induction, fixpoint induction, Isabelle-style recursion induction or
  some other means.
* It needs to be good at first-order reasoning to discharge the proof
  obligations coming from induction, either using a first-order prover
  or SMT solver or its own reasoning engine.
* It needs to find the correct lemmas to prove, either by
  generalisation [@acl2], theory exploration [@theorema; @quickspec]
  or by looking at failed proof attempts
  [@jasmin-lpar; @productiveuse].

Until now, anyone writing an inductive prover has had to make or
integrate these components themselves. For example, HipSpec contains a
large amount of code to communicate with QuickSpec, instantiate
induction schemas, and translate proof obligations to TPTP [@TPTP]
or SMT-LIB [@smtlib25] formats. The contribution of this paper is

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


examples: rudimentophocles, translating benchmark problems

In this paper, we describe our tool TIP, which helps authors of
inductive theorem provers in two ways:

* blah
* blah

In this paper, we describe our TIP (tool for inductive provers) tool,
which has two aims: improving interoperability between theorem provers,
and lowering the barrier to entry for new provers.

(the TIP tool)

#### The TIP benchmark format

Spurred on by the new interest in inductive theorem proving, we
recently introduced a suite of inductive benchmarks [@TIP-benchmarks],
which currently stands at 343 problems. The benchmarks are expressed
in our TIP format, a rich language containing inductive datatypes,
built-in integers, higher-order functions, polymorphism, recursive
function definitions and first-order logic. The TIP tool originated
as a program for translating from TIP to other provers' input formats.

Inductive provers are quite varied: some require monomorphic problems,
some require first-order problems, some only reason about programs
rather than arbitrary formulas. Very few inductive provers match up
exactly with TIP's features.

#### Translating TIP to other formats

Very few inductive provers support all TIP's features, and what's more
all of them use their own input format. We have therefore developed a
tool to translate TIP to other formats. Apart from the boring job of
converting syntax, the tool has the more interesting job of encoding
any features in the input problem that the target prover doesn't support.

#### TIP as a toolbox


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
* todos^[partiality semantics, induction pass: the only difference seems to be
  that Why3 cannot do induction no the same variable many times, and that they
  do lexicographic induction]


Maybe some example property right here: side by side comparison
of format supported by CVC4 and SMTInd.

The next version of HipSpec is in fact just calls to Tip
and orchestrating the runs of theorem provers. In a way,
Tip is a reimplementation of HipSpec, but as a library
that users and developers can gain leverage from.

## Random example

In our format

```{.tip-include }
example.smt2
```

After monomorphisation, lambda lifting, match to if-then-else and axiomatization of function
declarations:

```{.tip-include
    .TypeSkolemConjecture .Monomorphise-False .LambdaLift
    .AxiomatizeLambdas .Monomorphise-False .NegateConjecture
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
  (typically left-to-right for function definitions),
  and as we will see later in the monomorphisation section^[add fwd reference],
  that it helps also there.


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

## Applying structural induction

We provide a transformation that applies structural induction over data types
in the goal. This requires a forall quantifier of the goal at the top, and does induction on
the variable at a given a position in the quantifier list. ^[TODO: the only difference seems to be
  that Why3 cannot do induction no the same variable many times, and that they
  do lexicographic induction]

This is a pass that gives a separate theory for each proof obligation yielded
by the induction pass. When using the command line tool, the theories are put
in separate files in a directory specified as a command line argument.

The pass can also do induction on several variables, or repeatedly do
induction on the same variable. There are some alternatives how strong
induction hypotheses to add. This pass does not do the strongest, it uses
HipSpec's heuristic and adds the strict subterms of the conclusion.
This is predictable, symmetric and is shown to work well in practice:
for instance, it is strong enough to prove commutativity of the normal
definition of natural number addition without any lemmas when doing induction
on both variables. Induction on both of two natural number variables,
on an abstract predicate `p` looks like this in the last of three step cases:

```{.tip .Induction-L0_1R .t3 .no-functions}
;.SkolemiseConjecture}
(declare-datatypes () ((nat (zero) (succ (pred nat)))))
(declare-fun p (nat nat) Bool)
(assert-not (forall ((x nat) (y nat)) (p x y)))
(check-sat)
```

We are adding more kinds of induction, including recursion-induction,
Leino-induction (well-founded induction on the size of data types), and fixed
point induction.

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

## Monomorphisation

Oftentimes, the natural way to express functional programs is by using
polymorphism.  And just so, the problems in the benchmark suite typically
define functions like list map and concatenation polymorphically, even if they
are only used at a few, or oftentimes, only one instance.
However, many provers do not support polymorphism,
or not even a monomorphic sorted logic.
To make problems look natural and not like an encoding,
we support rank 1 polymorphism in our tools
(all definitions can quantify over type variables, but only at the
top level).  Though there has been work on supporting polymorphism natively
in FO provers and SMT solvers, in particular Alt-Ergo [@BobotAltErgo], but also
initial work for CVC4, this is not yet standard practice.
Thus, we provide a monomorphisation pass that removes
polymorphic definitions by cloning them at different ground types.

At some problems, this procedure is not complete.
There are a few obstacles to making a complete procedure:

* Polymorphic recursion: recursive functions that call themselves at
  a bigger type, requiring infinitely many copies. Data type constructors
  can also have this quality, and if cloning of lemmas (assertions)
  is too aggressive, they can also lead to inifintely many copies.
  We outline below how we deal with this problem in practice (and in an
  incomplete way)

* As shown in [@BobotPaskevich2011frocos],
  calculating the set of reachable ground instances for a polymorphic problem is
  undecidable, and their construction carries over directly in our setting.
  To curb this, we only make simulations and check if
  the a set of copying rules terminate within some rounds.
  If it does not, we introduce fuel arguments similar to [@leinoFuel],
  guaranteeing termination (in an incomplete way).
  We show this construction later in this section.

It is possible to encode types completely, but this is heavier and the
introduced ovehead could for instance desturb trigger selection in SMT solvers.
^[An overview of type encoding for polymorphism is [@blanchette2013encoding].
TODO: Is this the right reference? ]

### The construction

We show how to flexibly express monomorphisation
as predicate horn clauses, and then obtaining the minimal model.


    Functions activate their dependencies at the same fuel:

        f(a) = ... g(a) ... h(a) ...

    gives

        f(S(n),a) -> g(S(n),a)
        f(S(n),a) -> h(S(n),a)

    For polymorphic recursion, we lower the fuel on the RHS.

    Then we want to add

        g(S(n1),a), h(S(n2),a), min(S(n1),S(n2),S(n3)) -> f(S(n3),a)

    If this rule is what causes non-termination, we drop the fuel power in the RHS:

        g(S(n1),a), h(S(n2),a), min(S(n1),S(n2),S(n3)) -> f(n3,a)

    Furthermore, we can split the preconditions here to make instantiation more
    enthusiastic:

        g(S(n),a) -> f(S(n),a)

        h(S(n),a) -> f(S(n),a)

    For the ones on this that yields non-termination, we drop the fuel in the RHS.

    For lemmas, the situation is similar, but there is no definition rule.
    So everything is really very uniform:

        * SEEDS:    Ground instances from the definition. Starts at some fuel, like
                    1, 2 or 3.

        * PRIO   I: Definitions. These only get fuels with direct
                    polymorphic recursion

        * PRIO  II: If everything that is required is active, also activate this

        * PRIO III: If enough things to cover the precondition is active,
                    also activate this (very enthusiastic)

    If a definition comes back with fuel 0, we could call the parametric
    version and keep that around.  But that's not directly going to work
    the type of arguments are a mix of instantiated and polymorphic data
    types, so we could just let this module abstract them immediately!
    (lemmas are removed, data types and functions are given abstract sorts
    or abstract signatures.)


We start with the ground seeds of the types and functions
occuring in the goal.

In case of polymorphic recursion, where a function or a constructor
makes a call to its parent with a bigger type, the polymorphism
cannot be fully removed, but we can approximate the program
by letting these definitions unroll a few times and then becoming
opaque. This section describes how to do this.


The initial ground instances, the seeds, are given by the
conjecture. To this end, we do a type-level skolemisation
of the conjecture. So if the conjecture quantifies over
the type `a` and mentions the function `f(a)`,
we introduce a new abstract sort `sk_a`: and add the rule:

    -> f(sk_a)

which states that `f(sk_a)` is always active. This now
enables other rules to fire.

For function declarations, we simply make sure that
they activate all their necessary dependencies.
If a function `h` has two type variables `a` and `b`,
and makes a call to `f` at `a` and `g` at `b` we
add this rule:

    h(a,b) -> f(a)
    h(a,b) -> g(b)

This means that we will make a copy of `h(a,b)` if
the function `f(a)` and `g(b)` are copied.

But for an inductive prover, every function definition
is valuable. As an example, the more functions you have
when you do theory exploration, the better you know
how they interact. In the general case, you need to be able
to synthesise new functions to be complete.
To this end, we would also like to instantiate functions
when they seem harmless. So in the example above, we would
also like to add this rule:

    f(a), g(b) -> h(a,b)

We give these rules a lower priority, and add rules
from higher to lower priority, checking termination
by simulating 10 parallel assignment steps. If it
does not terminate, we add _fuel arguments_:

    f(Succ(n)), g(Succ(m)), min(Succ(n),Succ(m),Succ(o)) -> h(Succ(o),a,b)

Where we just add instances for `min`. We have finitely much fuel anyway:
(Say we start at fuel 3)

    min(3,3,3)
    min(3,2,2)
    min(3,1,1)
    ...
    min(2,3,2)
    ...

The fuel for exciting rules can be throttled. 3 or 2 is a sensible default.
(In the example above, we cannot just have one of `f` or `g` on the left-hand side
as all type variables need to be mentioned. We take all minimal
sets as left-hand sides that cover all variables).

For lemmas we add one rule that says that we want a copy of it
if all function symbols of it are active. This has a high priority.
With lower priority, we do as outlined above for the function definitions:
we instantiate the lemma if there is some function active, and
as for all rules add fuels as necessary.

As an example:
Futhermore, the set is infinite for many problems due to polymorphic recursion,
either in datatype declarations or in function definitions. But assertions can
enforce polymorphic recursion, too. As an example, assume the zip-rev
conjecture above is asserted as a lemma.  Then say some ground type is used in
the program, like `(list Int)`. Then the lemma suggests that `(list (Pair Int Int))` is used too, by instantiating the lemma with the type substitution `a`
and `b` both replaced with `Int`.  Now, this yields another instatiation of
`(list (Pair Int (Pair Int Int)))`, and so on.


TODO:
* Show what to do when the fuel reaches zero.
* Add to that an example with polymorphic recursion getting cut off.

We successfully monomorphised 350 of our 351 benchmarks;
the failing one has an irregular data type.

<!--
We have five different kinds of entries in our theories:
anonymous sort declarations (could have type arguments),

```{.tip .no-check-sat}
(declare-sort M 2)
(check-sat)
```

Here, we just want to make sure to instantiate this sort if it has two arguments.
If we get $M(t1,t2)$ for ground t1 and t2 a new copy is made, say `M_t1_t2`.

```{.tip .no-check-sat .no-sorts}
(declare-sort M 2)
(declare-fun (par (a b) (f ((M a b)) (M b a))))
(check-sat)
```

If we get `f(t1,t2)` for ground t1 and t2, we make a copy of `f_t1_t2`.

The remaining types are more interesting:

* Function definitions
* Data type definitions
* Goals (negated assertions)
* Lemmas (assertions)

We have two different kinds of records: type constructors and functions.
say List(a) and append(a), reverse(a).

### Function definitions

An example, the instantiation records for `reverse`:

```{.tip .no-check-sat .no-datatypes .no-sigs}
(declare-datatypes (a) ((list (nil) (cons (head a) (tail (list a))))))
(declare-fun (par (a) (append ((list a) (list a)) (list a))))
(define-fun-rec
  (par (a)
    (reverse ((xs (list a))) (list a)
      (match xs (case nil (as nil (list a)))
                (case (cons h t) (append (reverse t) (cons h (as nil (list a)))))))))
(check-sat)
```

A function mentions types in its type signature, its local definitions,
and all functions it has active.

```
reverse(a) -> list(a)    # from type signature result and local variables xs,t
reverse(a) -> nil(a)     # pattern and constructor call
reverse(a) -> cons(a)    # pattern and constructor call
reverse(a) -> a          # from local variabe h
reverse(a) -> append(a)  # makes a call
reverse(a) -> reverse(a) # actually calls itself too. this rule can be pruned
```

When should reverse be activated (i.e. be on the rhs of the implication)?
Just as `reverse` activates `append`, other functions calling `reverse`
will make `reverse` activated.

```
mystery_length xs = length xs + length [xs]
```

    length(x), length(list(x)) -> mystery_length(x)

incorrect:

    list(x) -> mystery_length(x)

### Polymorphic recursion in functions

```.haskell
polyrec :: Nat -> (a -> Int) -> a -> Int
polyrec Zero     to_int x = x
polyrec (Succ n) to_int x = polyrec n (\ (a,b) -> to_int a + to_int b) (x+1,x-1)
```

Here, we get

    polyrec(a) -> polyrec(Pair(a,a))

Thus, instantiating `polyrec` makes an infinite number of instantiations.
We'll show later how to curb this.

### Data types

```{.tip .no-check-sat .no-datatypes .no-sigs}
(declare-datatypes (a) ((list (nil) (cons (head a) (tail (list a))))))
```

We look at the data types as signatures:

    # nil
    list(a) -> nil(a)
    nil(a) -> list(a)
    # cons
    a -> list(a) -> cons(a)
    cons(a) -> a
    cons(a) -> list(a)
    # head
    list(a) -> a -> head(a)
    head(a) -> list(a)
    head(a) -> a
    # tail
    list(a) -> tail(a)
    tail(a) -> list(a)

Additionally, `list` activates all types it needs:

    list(a) -> nil(a), cons(a), head(a), tail(a)

Data types can also be polymorphically recursive.
We can handle them with a fuel parameter.
If we instantiate an induction schema before
monomorphisation, we can still prove properties...
^[TODO: Example and implementation]

### Conjectures

Conjectures are dead simple: these are the seeds
for the monomorphisation. We just need to type-skolemise
the conjecture first.
We could introduce the same type variable for all
type variables, but we chose to introduce separate ones.

In the example below, we remove `a` and `b` and replace
them with skolems:

```{.tip-include .no-check-sat .no-functions .no-datatypes}
prop_85.smt2
```

This is with skolem types:

```{.tip-include .no-check-sat .no-functions .no-datatypes .TypeSkolemConjecture}
prop_85.smt2
```

Then we take all types and functions as initial records:

```
-> list(sk_a)
-> list(sk_b)
-> len(sk_a)
-> len(sk_b)
-> zip(sk_a,sk_b)
-> rev(sk_a)
-> rev(sk_b)
-> rev(pair(sk_a,sk_b))
```

In this example, perhaps the only surprising instantiation is `len(par(sk_a,sk_b))`,
but it is added because of the _signature trigger_ heuristic:
all the types in `len` are activated, so it is added.

### Lemmas

What triggers should we pick for lemmas (or assertions, in SMT-LIB parlance)?
One way makes many lemmas behave like polymorphically recursive definitions,
another makes them never trigger anything new.

It's now important to think as the current active records as two sets:
the type universe and the instantiated functions.
We can make it so that lemma instantiation does not grow the type universe,
but allows new functions to be instantiated.

If we consider the rev-zip-len lemma above, to say that it cannot grow the
type universe, we say that we only instantiate if all types are active.
Let's say the lemma itself has a record called L:

    a, b, list(a), list(b), list(pair(a,b)), pair(a,b) -> L(a,b)

Then, we just say that all the functions in it are also activated.

    L(a,b) -> len(a)
    L(a,b) -> len(b)
    L(a,b) -> zip(a,b)
    L(a,b) -> rev(a)
    L(a,b) -> rev(b)
    L(a,b) -> rev(pair(a,b))

QUESTION: Can this actually not trigger any new lemmas?
We have just made an approximation of the types that will become active.
Really, we should execute it as it were skolemised....
Yes, say rev makes dummy call to f on list of pairs. Then this will
be triggered again.
And then, when we look for all the types it cares about, it needs to
look through other lemmas. (right?)
Or we could assume each lemma on its own.

One can add that at least ONE of the functions needs to be active, too:

    len(a), a, b, list(a), list(b), list(pair(a,b)), pair(a,b) -> L(a,b)
    len(b), a, b, list(a), list(b), list(pair(a,b)), pair(a,b) -> L(a,b)
    zip(a,b), a, b, list(a), list(b), list(pair(a,b)), pair(a,b) -> L(a,b)
    rev(a), a, b, list(a), list(b), list(pair(a,b)), pair(a,b) -> L(a,b)
    rev(b), a, b, list(a), list(b), list(pair(a,b)), pair(a,b) -> L(a,b)
    rev(pair(a,b)), a, b, list(a), list(b), list(pair(a,b)), pair(a,b) -> L(a,b)

Or that they ALL have to be: (or two..., and so on.)

### New Text

### Old Text


Oftentimes, the natural way to express functional programs is by using
polymorphism. One example is this `zip`-`rev` property, which
is conjecture 85 obtained from the isaplanner testsuite:

```{.tip-include .no-check-sat .no-functions .no-datatypes}
prop_85.smt2
```

Here, `rev` is used both on lists of `a` and `b`, but also
on pairs of `a` and `b`.

```{.tip-include .no-check-sat .no-functions .TypeSkolemConjecture .Monomorphise-False}
prop_85.smt2
```

In this work, we show how to express monomorphisation as a
predicate horn clause problem, and how to encode things like
growing the type universe and function universe in it.
In particular, we show how to be complete when possible,
and how to use heuristics when possible.

For the benchmark suite, this has not yet posed any problems
since they don't contain any lemmas: the assumption is that
the provers will figure these out by themselves from the
function definitions. ^[FIX THIS: But even though our tool then
can claim it succeeds to monomoprhise the problem,
the proof can require a lemma oncerning
a function whose monomorphic instance
was not used. In the `zip`-`rev`-example above,
the length function `len` is not used on list of pairs,
so there will be no copy of it instantiated at that type.
If a (hypothetical) proof requires a lemma about the
`len` on pairs function, that function now needs to
be synthesised by the prover in the monomorphised problem.
    Monomorphisation can be incomplete even when it succeeds.
One example is where `append` is used on `list A`,
but not on `list B`. But the proof might need a lemma
about append on `list B`!]


We monomorphise the problem wrt to the types occurring
in the goals (`assert-not`).

* Allow instantiation as long as the type universe does not grow
  (Potential problem: the function it calls may make it grow)
* Instantiate when all functions not in the same SCC are
  available.

The cases which have some room for heuristics are instantiation
of function definitions, and lemma assertions.

By default, we should always want _careful lemma instantiation_,
which copies a lemma if all function records appearing in it
are active.

The corresponding setting exists for _careful function instantiation_,
but it does not necessarily need to be on by default. However,
we should not mention things from its own call-graph to be able
to instantiate it.

    f (x:xs) = x:g xs ; f [] = []
    g (x:xs) = f xs   ; g [] = []

There are also _enthusiastic_ versions of the above, where just
one function is active makes the lemma (or function) be active.
Now we cannot guarantee termination, so we add fuel parameters.

      concat[b] (map[list a,list b] (map[a,b] f) xs)
    = map[a,b] f (concat[a] xs)

    map[suc n,a,b] -> LEM[n,a,b]

All type variables types needs to be mentioned in the trigger, so
if we want to add some function that does not mention all type
variables, we add the function that could not have done it on their own:

    concat[suc n,a] -> concat[suc n,b] -> LEM[n,a,b]

But we might not have the fuel! So:

    concat[suc n,a] -> concat[suc m,b] -> min(suc n,suc m,suc o) -> LEM[o,a,b]


#### Discussion: A lemma trouble?
This is similar to the call graph for _careful function instantiation_:

    A, B -> L1, C
    A, C -> L2, B
    A.

Assume `B` and `C` are not dangerous to instantiate, then here we probably
want `L1` and `L2`, even though they won't be come instantiated without
fuel in our setting. Future work include figuring out when lemmas
are unproblematic to instantiate without using fuel, to catch cases
like above.
-->

#### Related work

As noted above, we could make a complete encoding of types using ideas from Nick's paper
[@blanchette2013encoding]. That article also outlines a "Finite Monomorphisation Algorithm"
(sect 7.1), with the settings in sledgehammer. By default, the type universe
is allowed to grow thrice, and at most 200 new formulae are allowed to be introduced.

We have not yet formalized our monomorphisation, but it has been done in
[@Li08trustedsource], though they don't support polymorphic recursion
or formulae. Their approach is basically the one to removing polymorphism
by cloning as in [@Oliva97fromml] in the ML setting without
polymorphic recursion. They take extra care to do monomorphisation
before defunctionalisation to be able to have simply typed closures.
Our work can be seen as an extension of their approaches in the
presence of polymorphic recursion and lemmas.

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

```{.tip-include .UncurryTheory .LambdaLift .AxiomatizeLambdas .Monomorphise-False}
double-curried.smt2
```

#### Discussion

This is closure conversion as described in [@Reynolds72Defunctionalisation].
A similar construction as in the monomorphisation section could be used to
specialize higher-order functions to cloned copies of first order functions.
How this is can be done for functional programs is described in
[@DarlingtonSpecialisation].

## Back and forth between case and if-then-else

What passes were needed to make this run smooth?
Say something about the examples from the Leon benchmark suite.

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

Rudimentophocles^[Named after the lesser-known Ancient Greek philosopher.] is
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

``` {.include .bash}
rudimentophocles
```

# Example run of Rudimentophocles

Here is an example showing the output of Rudimentophocles on a simple
theory of `append` and `reverse`. The input file has a single conjecture
that `reverse (reverse xs) = xs`:

``` {.include}
rudimentophocles-in.smt2
```

Rudimentophocles first runs QuickSpec to discover likely lemmas about
`append` and `reverse`:

``` {.include}
rudimentophocles-out-1
```

It then goes into a proof loop, taking one conjecture at a time and
trying to prove it. It prints `:(` when it failed to prove a
conjecture, `:)` when it proved a conjecture without induction, and
`:D` when it proves a conjecture with the help of induction:

``` {.include}
rudimentophocles-out-2
```

Rudimentophocles prints a newline when it has tried all conjectures, then
goes back and retries the failed ones (in case it can now prove them with
the help of lemmas). In this case it manages to prove all the discovered
conjectures, and prints out the following final theory. Notice that:
a) the property `reverse (reverse xs) = xs` is now an axiom (`assert`)
rather than a conjecture (`assert-not`), indicating that it has been proved,
and b) several other proved lemmas have been added to the theory file.

``` {.include}
rudimentophocles-out-3
```
