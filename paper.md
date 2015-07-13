---
abstract: TIP is a toolbox for users and developers of inductive provers. It consists of a large number of tools which can, for example, simplify an inductive problem, monomorphise it or find counterexamples to it. We are using TIP to help maintain a set of benchmarks for inductive theorem provers, where its main job is to encode features that are not natively supported by the respective provers. TIP makes it easier to write inductive provers, by supplying necessary tools such as lemma discovery which prover authors can simply import into their own prover.
---

# Introduction

More and more people are making inductive theorem provers. Besides
traditional systems such as ACL2 [@acl2], new provers such as Zeno
[@zeno], HipSpec [@hipspecCADE], Hipster [@hipster], Pirate
[@SPASSInduction] and Graphsc [@graphsc] have appeared, and some
formerly non-inductive provers such as CVC4 [@cvc4] and Dafny [@dafny]
can now do induction.

To make it easier to scientifically compare these provers, we recently
compiled a benchmark suite of 343 inductive problems [@TIP-benchmarks].
We ran into a problem: all of the provers are very different.
Some expect the problem to be monomorphic, some expect it to be
first-order, some expect it to be expressed as a functional program
rather than a logic formula. If we stuck to only features supported by
all the provers, we would have very little to work with.

Instead, we designed a rich language which can express a wide variety
of problems. The TIP format (short for _Tons of Inductive Problems_) is an extension of SMT-LIB [@smtlib25] and
includes inductive datatypes, built-in integers, higher-order
functions, polymorphism, recursive function definitions and
first-order logic.

#### The TIP tools
In this paper, we demonstrate a set of tools for transforming and
processing inductive problems. The tools are based around the TIP
format, and provide a wide variety of operations that are useful to
users and developers of inductive provers. The tools can currently:

* Convert SMT-LIB and Haskell to TIP.
* Convert TIP to SMT-LIB, TPTP TFF, Haskell, WhyML or Isabelle/HOL.
* Remove features from a problem that a prover does not support,
  such as higher-order functions or polymorphism.
* Instantiate an induction schema: given a conjecture and a set
  of variables to do induction over, generate verification obligations for
  proving the conjecture by induction.
* Model check a problem, to falsify conjectures in it.
* Use theory exploration to invent new conjectures about a theory.

We describe the TIP format itself in section \ref{tip-format},
and many of the available transformations in section \ref{transforming}.
TIP improves the ecosystem of inductive provers in two ways:

* _Interoperability between provers_.
  Almost all existing inductive theorem provers are incompatible.
  They all use different input syntaxes but, more importantly,
  support entirely different sets of features. This makes it
  difficult to scientifically compare provers.
  \par
  TIP provides conversion tools which allow us to write one problem
  and try it on several provers. The conversion is not just syntactic
  but uses tools such as defunctionalisation [@defunc] and
  monomorphisation to mask the differences between provers.
  <!-- We describe many of these transformations in section \ref{transforming}. -->
  We are using TIP to convert our inductive benchmarks to various provers'
  input formats.

* _Easier to make new provers._
  There are many ingredients to a good inductive prover: it must
  instantiate induction schemas, perform first-order reasoning to
  discharge the resulting proof obligations, and discover the
  necessary lemmas to complete the proof. This makes it hard to
  experiment with new ideas.
  \par
  TIP provides many parts of an inductive prover as ready-made
  components, so that an author who has---say---an idea for a new
  induction principle can implement just that, leaving the first-order
  reasoning and lemma discovery to TIP.
  This is analogous to how someone writing an experimental first-order prover
  might use an existing clausifier instead of writing their own.
  In section \ref{rudimentophocles-main}
  we show that it is possible to stitch the TIP tools together to make
  a simple inductive prover as a shell script!

We are continually adding more tools and input and output formats to TIP.
We are working to make TIP a universal format for induction problems,
backed by a powerful toolchain which can be used by prover authors and
users alike. We describe our plans for improving TIP further in
section \ref{future}. TIP is publically available and can be downloaded
from <https://github.com/tip-org/tools>.

# The TIP format {#tip-format}

The TIP format is a variant of SMT-LIB. The following problem about
lists illustrates all of its features. We first declare the
polymorphic list datatype `(list a)`, using the widely supported
`declare-datatypes` syntax.

```
(declare-datatypes (a) ((list (nil) (cons (head a) (tail (list a))))))
```

We then define the list `map` function by pattern matching.
The `par` construct is used to introduce polymorphism.
The `match` expression provides pattern matching and is proposed for inclusion
in SMT-LIB 2.6.
To support partial functions like `head`, a `match` expression may have missing
branches, in which case its value is unspecified.
The syntax for higher-order functions is a TIP extension and we
discuss it below.

```
(define-fun-rec (par (a b)
  (map ((f (=> a b)) (xs (list a))) (list b)
    (match xs
      (case nil (as nil (list b)))
      (case (cons x xs) (cons (@ f x) (map f xs)))))))
```

Finally, we conjecture that mapping the identity function over a list
gives the same list back. Many inductive provers treat the goal
specially, so TIP uses the syntax `(assert-not p)`, which is
semantically equivalent to `(assert (not p))` but hints that `p` is a
conjecture rather than a negated axiom.

```
(assert-not (par (a)
  (forall ((xs (list a)))
     (= xs (map (lambda ((x a)) x) xs)))))
(check-sat)
```

To summarise, the TIP format consists of:

* SMT-LIB plus `declare-datatypes` (inductive datatypes), `define-funs-rec`
(recursive function definitions), `match` (pattern matching) and `par`
(polymorphism), which are all standard or proposed extensions to SMT-LIB.
* Our own TIP-specific extensions: higher-order functions, and
  `assert-not` for marking the conjecture.

Our tools also understand the SMT-LIB theory of integer arithmetic.
We intend TIP to be compatible with the standard theories of SMT-LIB.

#### First-class functions

TIP supports higher-order functions, as these often crop up in
inductive problems. So as not to make provers do unnecessary
higher-order reasoning, we use the following design, which makes
all use of higher-order functions explicit. Functions cannot be
partially applied, so if `succ` is a function from `Int` to `Int` we
cannot write `(map succ xs)`.

Instead, there is a type of _first-class functions_, \texttt{(=> a b)},
which are built using `lambda`. The syntax `(lambda ((x A)) t)`
means $\lambda (x:A).\, t$, and has type \texttt{(=> A B)} if `t` has type
`B`. To apply a first-class function we must write `(@ t u)`.

To map `succ` over a list we must therefore write
`(map (lambda ((x Int)) (succ x)) xs)`---the inner `lambda` has type
\texttt{(=> Int Int)}. In the definition of `map`, we use `(@ f x)` to apply
`f` to the list element. This design keeps higher-order reasoning
confined to the parts of the problem that use higher-order functions.

# Transforming and translating TIP {#transforming}

TIP is structured as a large number of independent transformations.
This is true even for our file format conversions. When TIP and the
target prover have different feature sets, our approach is to keep the
problem in TIP as long as possible, running many small transformations
to reduce the problem to some fragment of TIP which we can translate
directly. For example, many formats do not support pattern matching,
so we must translate it to if-then-else, or if the format does not
support that either, we can transform each function definition into a
series of axioms. This happens as a TIP-to-TIP transformation.

This approach makes TIP quite modular. It is quite easy to add a new
converter as most of the hard work is taken care of by existing
transformations. What's more, many of those transformations are
useful in their own right. In this section we illustrate many of the
available transformations; we will use as a running example the
conversion of the `map` example to SMT-LIB.

Although TIP is a variant of SMT-LIB, the two are quite different.
SMT solvers often do not support polymorphism, higher-order functions
or pattern-matching so our converter must remove those features.
Here is what our tool produces when asked to translate the `map`
example to vanilla SMT-LIB. It has monomorphised the problem, used
defunctionalisation to eliminate the `lambda` and is using
`is-cons`/`head`/`tail` instead of pattern matching.

```
(declare-sort sk_a 0)
(declare-sort fun 0)
(declare-datatypes () ((list (nil) (cons (head sk_a) (tail list)))))
(declare-const lam fun)
(declare-fun apply (fun sk_a) sk_a)
(declare-fun map (fun list) list)
(assert (forall ((x sk_a)) (= (apply lam x) x)))
(assert (forall ((f fun) (xs list))
  (= (map f xs)
    (ite (is-cons xs) (cons (apply f (head xs)) (map f (tail xs))) nil))))
(assert (not (forall ((xs list)) (= xs (map lam xs)))))
(check-sat)
```

## Defunctionalisation

To support theorem provers that have no support for first-class functions and
lambdas, a TIP problem can be defunctionalised [@defunc].
This replaces all $\lambda$-functions in the problem with axiomatised
function symbols.

In the example above, defunctionalisation has introduced the new
abstract sort `fun` which stands for functions taking one argument.
The identity function is now named `lam` and is of sort `fun`.
The `@` operator has been replaced by the function `apply`,
together with an axiom which states that `(apply lam x)` is `x`.

## Monomorphisation

Often, the natural way to express functional programs is by using
polymorphism. In the example above, map is defined polymorphically
even though it is used only once in the program.
<!--We want problems to look natural and not encoded,
so rank 1 polymorphism is supported in our tools, meaning that all definitions
can quantify over type variables, but only at the top level.-->
However, many provers do not support polymorphism.
Though there has been work on supporting polymorphism natively
in FO provers and SMT solvers, in particular Alt-Ergo [@BobotAltErgo], and also
initial work for CVC4, this is not yet standard practice.
Thus, we provide a monomorphisation transformation that removes
polymorphic definitions by cloning them at different ground types.

<!--
For an inductive prover, every function definition is valuable: the more
functions you have when you do theory exploration, the better you know how they
interact. In the general case, a prover needs to be able to synthesise _new_
functions to find some proofs. Thus, we want to to clone functions
at types which do not directly appear in the program, but
could be helpful for a proof. But, there are a few obstacles to making a
complete procedure:

* Polymorphic recursion: functions that call themselves at
  a bigger type, requiring infinitely many copies. Data type constructors
  can also have this property, and if cloning of assertions
  is too aggressive, they can also lead to infinitely many copies.

* As shown in [@BobotPaskevich2011frocos],
  calculating the set of reachable ground instances for a polymorphic problem
  is undecidable, and their construction carries over directly in our setting.

We discuss incomplete heuristics for dealing with this in the further work
section. ^[An overview of type encoding for polymorphism is [@blanchette2013encoding].
TODO: Is this the right reference? ]
-->

As calculating the required instances is undecidable
[@BobotPaskevich2011frocos], our monomorphiser is heuristic. It
generates a set of rules, in the form of first-order Horn clauses,
which say when we should generate various instances. The minimal model
of these Horn clauses then tells us which instances are required.
The reason we do this is to make it easy to adjust the behaviour of
the monomorphiser; different settings may include or omit
instantiation rules.

For a function definition, the rule is that when we instantiate the
function, we should also instantiate everything required by the
function. For `map`, some of the rules will be:

    map(a,b) -> cons(a)
    map(a,b) -> cons(b)
    map(a,b) -> map(a,b)

In the snippet above, `a` and `b` are the type arguments to `map`.
The first two lines make sure that when we instantiate `map` at types `a`
and `b` in the program, we will also instantiate the `cons` constructor at `a`
and at `b`. For data types, we have other rules that make sure that
if `cons` is needed at some type, we also instantiate `list` at that type.

The last line is present because `map` calls itself. In general, when
`f` calls `g`, we add a rule that when we instantiate `f` we must
instantiate `g`. The rule makes no difference for this example, but is
problematic for _polymorphically recursive functions_, which call
themselves at a larger type. This is an obstacle for monomorphisation
as then there is no finite set of instances. To curb this, our
procedure gives up after a predefined number of steps.

To start the procedure, we first Skolemise any type variables in the
conjecture, and then add facts to the rule set for the functions
called in the conjecture. These seed the procedure, which will either
return with a set of ground instances that cover the problem, or give up.

The transformation successfully monomorphises all but one of our benchmarks;
the failing one has a polymorphically recursive data type.

## Eliminating pattern matching

TIP provides two passes for eliminating pattern matching. The first
one is used in the translated `map` function above, and replaces
`match` with if-then-else (`ite`), discriminators (`is-nil` and
`is-cons`) and projection functions (`head` and `tail`).
For converting SMT-LIB to TIP format, we also provide a reverse
transformation which replaces discriminators and projection functions
with `match` expressions.

For some theorem provers, using if-then-else is not
an option, or not efficient. Another way to translate a function definition
using `match` is to transform it to several axioms, one for each case.
The toolbox provides this transformation as well, which
transforms the `map` function into the following two axioms, which
specify `map`'s behaviour on `nil` and `cons`:

```
(assert (forall ((f fun)) (= (map f nil) nil)))
(assert (forall ((f fun) (x sk_a) (xs list))
  (= (map f (cons x xs)) (cons (apply f x) (map f xs)))))
```

The transformation works by first lifting all `match` expressions to
the outermost level of the function definition. A function with an
outermost `match` can easily be split into several axioms.

<!--
This works when `match` expressions are only in the right hand side of an
branch or the top level of a function. To set this up, we first
run another of our transformations that commutes `match` expressions "upwards"
in function definitions. Additionally, if the problem is given using if-then-else
expressions, another transformations in the toolbox changes them into efficient
`match` expressions.
-->

## Applying structural induction

We also supply a transformation that applies structural induction to
the conjecture. It requires the conjecture to start with a
$\forall$-quantifier, and does induction on the variables quantified
there. It splits the theory into several new theories, one for each
proof obligation. When using the command line tool, the theories are
put in separate files in a directory specified as a command line
argument.

The transformation can do induction on several variables and induction
of arbitrary depth, depending on what the user chooses. There is some
choice about how strong the induction hypothesis should be: we copy
HipSpec in assuming the induction hypothesis for all strict syntactic
subterms of the conclusion. For example, if `p` is a binary predicate
on natural numbers, proving `(p x y)` by induction on `x` and `y` gives
the following proof obligation (among others):

```{.tip .Induction-L0_1R .t3 .NoFuns}
;.SkolemiseConjecture}
(declare-datatypes () ((nat (zero) (succ (pred nat)))))
(declare-fun p (nat nat) Bool)
(assert-not (forall ((x nat) (y nat)) (p x y)))
(check-sat)
```
This choice yields predictable and symmetric verification conditions and is
known to work well in practice: for instance, it is strong enough to prove
commutativity of the normal definition of natural number addition without any
lemmas by doing induction on both variables.

## Other transformations and external tools

#### Minor transformations

Included in the toolbox are also simplification passes including inlining,
dead code elimination and merging equivalent or aliased functions.
Another minor transformation removes `let`-expressions by lifting them to the top level,
and yet another transformations axiomatises data types for
provers and formats that lack builtin support for them.

#### Theory exploration by QuickSpec

TIP is integrated with the theory exploration system QuickSpec [@quickspec].
QuickSpec only accepts Haskell input, so TIP is used to translate the
theory to Haskell, and QuickSpec's conjectures are translated back
into TIP formulas. This allows theorem provers to easily use
theory exploration.

#### Counterexamples to non-theorems

QuickCheck [@quickcheck] can be run on the properties generated by the TIP to
Haskell translation.  Futhermore, the Haskell Bounded Model Checker, HBMC, has
a mode to directly read TIP files.  These tools can be useful to identify
non-theorems among conjectures.

# Rudimentophocles, a simple inductive prover {#rudimentophocles-main}

Rudimentophocles^[Named after the lesser-known Ancient Greek philosopher.]
is a rudimentary inductive theorem prover, using the E theorem prover
for first-order reasoning and QuickSpec for lemma discovery.
It is a rough caricature of HipSpec, but with the striking difference
that, while HipSpec is 6000 lines of Haskell code, Rudimentophocles is
a 100-line shell script built on top of TIP.

The source code of Rudimentophocles is found in appendix A, and an example
run in appendix B. It works as follows:

* Run QuickSpec to find conjectures about the input theory.
* Pick a conjecture, and a variable in that conjecture.
    - Generate proof obligations for proving the conjecture
      by induction on that variable.
    - Translate each obligation to TPTP and send it to
      E (with a timeout).
    - If all obligations are proved, add the conjecture
      as an axiom to the theory.
* Repeat this process until no more conjectures can be proved,
  and print out the final theory.

Each of the steps---discovering conjectures, generating proof
obligations, and translating them to TPTP---is performed by calling
TIP. Rudimentophocles is not intended as a serious inductive theorem
prover, but it demonstrates how easy it is to experiment with new
inductive tools with the help of TIP.

# Related work

Why3 [@boogie11why3]

imperative language with functional language at

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

* a more light-weight monomorphisation transformation
* haskell frontend
* no termination check
* quickspec support
* low-level format suitable for expressing benchmarks
* todos

the only difference seems to be
  that Why3 cannot do induction on the same variable many times, and that they
  do lexicographic induction



Another way to remove higher-order functions than defunctionalisation is to
specialise functions with cloned copies of first order functions
[@DarlingtonSpecialisation].

Polymorphically recursive definitions can be approximated by letting their
definitions unroll a one or a few times letting the leaves call
an opaque copy. These could still be reasoned about if the abstract version
is mentioned in an inductive hypothesis.
Similarily, assertions that require infinitely many copies to be complete could
be curbed with a limit on the number of copies. One way is use
fuel arguments [@leinoFuel] to restrict the distance from the seeds,
guaranteeing termination and predictability.

On the other hand, instead of monomorphisation, a complete encoding of types is
possible. But an encoding risks introducing overhead that
could for instance disturb trigger selection in SMT solvers.
Such encodings have been analysed in
[@blanchette2013encoding], which also outlines the "Finite Monomorphisation Algorithm"
(sect 7.1), used in Sledgehammer. <!-- By default, the type universe
is allowed to grow thrice, and at most 200 new formulae are allowed to be introduced. -->

A similar monomorphisation algorithm has been formalised in [@Li08trustedsource]
Their approach is basically the one to removing polymorphism
by cloning as in [@Oliva97fromml] in the ML setting without
polymorphic recursion. They take extra care to do monomorphisation
before defunctionalisation to be able to have simply typed closures.

# Future work and discussion and conclusion {#future}

The work on the TIP infrastructure is very much alive, we are adding more
benchmarks and more functionality to the toolbox.
These are some of the areas where TIP can be improved.

We want to add more, stronger, kinds of induction, including
recursion-induction and well-founded induction on the size of data types.  We
would also like to add inductive predicates, as well as coinductive types.

We have boiled down our knowledge from writing the
HipSpec theorem prover to the TIP modular toolbox,
with the hope of making inductive theorem proving
more accessible for the community, a sub field
of automated reasoning that we believe has a
lot of potential for continued prosperous growth beyond
the recent landwinnings.


<!-- \AtNextBibliography{\small} -->
\printbibliography

\appendix

# Rudimentophocles source code

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
a) the property `(= xs (reverse (reverse xs)))` is now an axiom (`assert`)
rather than a conjecture (`assert-not`), indicating that it has been proved,
and b) several other proved lemmas have been added to the theory file.

``` {.include}
rudimentophocles-out-3
```

<!--
# Old stuff

#### Making inductive provers interoperable

It is bad for science if all inductive provers are incompatible: how
can we compare them?

... more formats

... semantic differences, transformations etc.

#### Making it easier to write an inductive prover

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

The large number of parts makes it hard to make new inductive provers.
You may, for example, have a grand new idea for an induction
principle, but don't want to make your own lemma discovery system to
try it out. We want to provide off-the-shelf components that the
author of an inductive prover can use to build their tool-just as
someone writing an experimental first-order prover might use an
existing clausifier instead of writing their own. TIP provides
ready-made solutions to all three problems above: a transformation for applying
structural induction, pretty-printers that transform problems into
TPTP or SMT-LIB to be handled by a first-order prover, and access to
the QuickSpec theory exploration system. We demonstrate this by describing
Rudimentophocles, a simplistic inductive prover with lemma discovery,
written as a shell script which combines TIP to handle the induction
and E to do the first-order reasoning.

Until now, anyone writing an inductive prover has had to make or
integrate these components themselves. For example, HipSpec contains a
large amount of code to communicate with QuickSpec, instantiate
induction schemas, and translate proof obligations to TPTP [@TPTP]
or SMT-LIB [@smtlib25] formats. The contribution of this paper is

We have boiled down our knowledge from writing HipSpec [@hipspecCADE], which
connects Haskell, our theory exploration tool QuickSpec [@quickspec] and SMT
and FO theorem provers.  With this work, we modularise it and make it
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

#### Translating TIP to other formats


#### TIP as a toolbox


Maybe some example property right here: side by side comparison
of format supported by CVC4 and SMTInd.

The next version of HipSpec is in fact just calls to Tip
and orchestrating the runs of theorem provers. In a way,
Tip is a reimplementation of HipSpec, but as a library
that users and developers can gain leverage from.

The particular SMT-LIB extensions that TIP uses are:

* Inductive datatypes using SMT-LIB 2.5's `declare-datatypes` [@smtlib25].
* Recursive function definitions using SMT-LIB 2.5's `define-fun-rec`.
* Polymorphism, using `par` as proposed for SMT-LIB 2.6 [@smtlib26].
* Pattern matching, using `match` as proposed for SMT-LIB 2.6.

On top of that we add the syntax `(assert-not p)`, which marks `p` as
a conjecture and is semantically equivalent to `(assert (not p))`. We
use this because many inductive provers treat the goal specially.

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
    (transformations)
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
  to do induction on: it cannot be skolemised by hand. So an
  `assert-not` makes sense in their work, too.

SMT-LIB is extensible through theories. Currently,
the only theory we use in the benchmarks are
Integers, but when the need arises, this can be
extended to bit vectors, arrays, sets, reals, floats, and so on,
as described by the SMT-LIB theories.

Side-by-side comparison of SMT-LIB and our format,
to discuss the different additions. (with other formats)

## Translation to other formats

## (semantics)

Function declarations are given the semantics as their non-computable axiomatisation.

### Semantics for partiality

We can support these semantics:

* Isabelle-style with uninterpreted function values
  (blanchettification for partial matches)

* Haskell by lifting every value to be effectively a maybe type
  (todo)
-->
