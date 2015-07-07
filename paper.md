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

```{.tip .Induction-L0_1R .t3 .NoFuns}
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

At some problems, this procedure is not complete.  For an inductive prover,
every function definition is valuable. As an example, the more functions you
have when you do theory exploration, the better you know how they interact. In
the general case, you need to be able to synthesise new functions to be
complete.  To this end, we would also like to instantiate functions when they
seem harmless. But, there are a few obstacles to making a complete procedure:

* Polymorphic recursion: recursive functions that call themselves at
  a bigger type, requiring infinitely many copies. Data type constructors
  can also have this quality, and if cloning of lemmas (assertions)
  is too aggressive, they can also lead to inifintely many copies.
  But we can approximate the program by letting these definitions unroll a few
  times and then becoming opaque.  We outline below how we deal with this in
  practice (and in an incomplete way).

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

We show how to flexibly express monomorphisation as predicate horn clauses, and
then obtaining the minimal model.
We introduce rules that are of the form

    forall x1..xm . LHS1, .., LHSn -> RHS

Where LHS1 is a term, using the variables `x1` .. `xn`.
All variables must present somewhere in the terms `LHS1` ... `LHSn`,
the precondition.
We will write `forall xs. LHSs -> RHS1, .., RHSn` as an
abbreviation for `forall xs. LHSs -> RHS1` up to `forall xs. LHSs -> RHSn`.
The functions in the terms will be the top-level definitions
in our program, so functions or sort declarations. The arguments
will be the types they are applied to. Later, we will
also introduce a fuel successor function and zero.
We start by looking at the goal, the `assert-not` where our seeds
are: the ground types where everything originates from.

```{.tip-include .NoDatas .NoCheckSat .NoFuns}
prop_85.smt2
```

We cannot handle a polymorphic goal now, so first you need
to skolemise the goal at the type level. Luckily, we
provide a pass that does just that. It introduces abstract
sorts and substitutes them for the type variables.

```{.tip-include .NoDatas .NoCheckSat .NoFuns .TypeSkolemConjecture}
prop_85.smt2
```

We take all the functions and types mentioned in the goal and
add them without any preconditions. Here, some of them are:

    -> list(sk_a), list(sk_b), len(sk_a), len(sk_b), zip(sk_a,sk_a),
       rev(sk_a), rev(sk_b), rev(pair(sk_a,sk_b)), ...

Now, for definitions, we make sure that everything they
need is active. So let's look at the `rev` function:

    (define-fun-rec (par (a)
      (rev ((x (list a))) (list a)
        (match x
          (case nil (as nil (list a)))
          (case (cons y xs) (append (rev xs) (cons y (as nil (list a)))))))))

We see that it calls and uses lists and its constructors, and also calls append
(and itself, but luckily not at a bigger type!)

    rev(a) -> rev(a), append(a), nil(a), cons(a), list(a), a

Similarily, for data type definitions we also add for each
entry (type constructor, data constructors, projectors) everything
it needs to be in scope.

How do we deal with lemmas? We identify two modes:

* _Safe cloning_: make a copy only if _all_ required components
  are already there.

* _Enthusiastic cloning_: make a copy if enough components are
  active to cover all type variables.

Notably, safe cloning never introduces any new copies,
and therefore is never a problem for termination.
The enthusiastic cloning can readily make more clones,
as a lemma will need to have a clone for each of its
dependencies. The critiera might be a bit confusing,
but consider a lemma `L(a,b)` with the two type variables
`a` and `b` regarding three functions `f(a)`, `g(b)` and `h(a,b)`.
We need the precondition to cover all type variables,
so the two rules created for _enthuisastic cloning_ is:

    f(a) & g(b) -> L(a,b)
    h(a,b) -> L(a,b)

For brevity, the _safe cloning_ rule requires all three in the precondition:

    f(a) & g(b) & h(a,b) -> L(a,b)

As mentioned earlier, its beneficial to do theory exploration
with many functions available. The same distinction can
also be made for function definitions. Consider this
slightly weird function:

```.haskell
mystery_length xs = length xs + length [xs]
```

It calls length on two types, one of them being bigger
than the input. For the safe rule, we want both of
them to be in scope, and the important parts is this:

    length(x), length(list(x)) -> mystery_length(x)

We can also enthusiastically instantiate this function.
One of the rules we get is this:

    length(x) -> mystery_length(x)

But if we have a record `length(A)`, this leads to `mystery_length(A)`,
which then uses `length(list(A))`, and we have infinitely many
instantiations. We simulate cloning with the rules a few rounds,
and if it does not terminate with that, we add _fuel arguments_
as outlined in the next section.

### Fuel paramaters

We can fix the rules in the sections above in the case when they do not
terminate by adding fuel arguments.  The idea is to always attach a fuel
argument as a first argument to every function, and only in  the case of
possibly non-terminating rules, decrease it on the right hand side.

Definitions activate their dependencies at the same fuel, so a function like this:

    f(a) = ... g(a) ... f(a) ...

gives these rules:

    f(S(n),a) -> g(S(n),a)
    f(S(n),a) -> f(S(n),a)

Here, `S` stand for the successor function on fuels, to make sure that
we do not fire it at zero fuel. If the function is polymorphically recursive,

    f(a) = ... g(a) ... f(list(a)) ...

, we will notice that the rule `f(S(n),a) -> f(S(n),list(a))` does not
terminate, and adjust it to:

    f(S(n),a) -> f(n,list(a))

This rule terminates, by construction.

For the _safe_ and _enthusiastic_ rules described above, we need
to take the minimum of the fuels on the right hand side. So,
one of the example rules above:

    f(a) & g(b) -> L(a,b)

Is augmented in this way with "similar" fuel and definitely decreasing fuel:

    f(S(n),a) & g(S(m),b) & min(S(n),S(m),S(o)) -> L(S(o),a,b)
    f(S(n),a) & g(S(m),b) & min(S(n),S(m),S(o)) -> L(o,a,b)

This uses a partial but sufficient axiomatisation of minimum:

    min(3,3,3)
    min(3,2,2)
    min(3,1,1)
    ...
    min(2,3,2)
    ...

(here, 3 stands for the fuel `S(S(S(Z)))`, and so on...)

To figure out which ones of the version we need (decreasing or "similar" fuel) ,
we sort the rules according how important they are. The rules are
seeds, then definitions, then safe cloning and last enthusiastic cloning.
Then we use binary search while adding more and more rules to the
set of considered rules until we find a rule that with it causes
an non-termination and without it terminates. Then we adjust this
rule with definitely decreasing fuels, and continue.

If a definition comes back with fuel 0, we make it an abstract sort
if it was a data type definiton, and just a type signature if it
was a function definition. It it is a lemma, we remove it.

### Recap

As a recap, these are the four levels:

* Seeds: Ground instances from the definition. Starts at some configurable fuel.

* Definitions: Functions and datatypes. Fuels decrease only with polymorphic recursion.

* Safe cloning: If everything that is required is active, also activate this.

* Enthusiastic cloning: If enough things to cover the precondition is active, also activate this (very enthusiastic).

We give these rules a lower priority, and add rules from higher to lower
priority, checking termination by simulating some parallel assignment steps. If it
does not terminate, we add fuel arguments.

The initial fuel can be throttled. Three or two is a sensible default,
but one fuel could used if no approximations should bedone.

We successfully monomorphised 350 of our 351 benchmarks;
the failing one has an irregular data type.

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
