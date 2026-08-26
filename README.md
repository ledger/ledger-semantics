# ledger-semantics

This repository contains a mathematical semantics for double-entry
plain-text accounting, the model of bookkeeping that the
[Ledger](https://github.com/ledger/ledger) family of programs
implements. The semantics is formalized in Lean 4 and proved against
Mathlib. From the same definitions the repository builds an
executable oracle. The oracle reads ordinary journal files, evaluates
them under the proved semantics, and prints account balances in a
small fixed format. Any implementation of the Ledger idea, in any
language, can therefore be tested against the mathematics itself. The
C++ Ledger project already does this. Its development branch replays
every positive journal in its test suite through the oracle and
requires exact agreement on every file.

The method behind the work is denotational design, as taught by Conal
Elliott ("Denotational design with type class morphisms", 2009). The
discipline has three steps. Say what a thing means. Require that
every operation preserve that meaning. Let the implementation be
whatever the equations force it to be. The sections below describe
the mathematics, the obligations it places on an implementation, the
oracle and its output protocol, the procedure for comparing another
implementation against it, and the ways to build the repository.

## The mathematics

The formalization begins with the structure of transactions and
accounts. Quantities of money enter later, through a valuation. An
account is a name. A transaction moves value among accounts, and its
meaning is indifferent to the order in which its postings are
written. The mathematical object with these properties is the free
symmetric strict monoidal category over finite multisets of accounts.
Each transaction is a generator. Its domain is the multiset of its
source accounts, and its codomain is the multiset of its
destinations. A journal is a single term, the tensor product of its
transactions. Sequencing is composition, and the symmetry
isomorphisms prove that the order of accounts carries no information.

A valuation is a functor from this category into commutative groups.
It assigns to each generator the flow of quantities that the
transaction causes, and it is required to respect composition,
tensor, and addition. The reporting function `netFlow`, which every
balance report computes, is then an additive homomorphism out of the
free model. On this view the Pacioli invariant, that debits equal
credits, is a theorem about the shape of morphisms: every morphism
has equal measure on its two ends. The theorem `pacioli_equation` in
`Ledger/Theorems.lean` establishes the invariant for the abstract
category, and `free_flow_balanced` in `Ledger/Pacioli.lean` carries
it down to the computed flows.

The theory also contains a negative result, and it explains a design
constraint that every mature accounting program exhibits. The
valuation algebra cannot support the additional laws that folklore
expects of it. The absorption law by itself forces every valuation to
zero. The theorem `zero_absorption_degenerates` in
`Ledger/Pacioli.lean` records the degeneracy argument, and the same
argument refutes the bilinearity law separately. The three laws named
above are the minimal consistent basis. For this reason pricing must
live outside the compositional core, as a lookup performed at
reporting time. A compositional pricing algebra with the expected
laws does not exist to be implemented.

A representation tower descends from the abstract meaning in proved
steps. The abstract category maps to a free model, built as a
quotient of formal morphisms. The free model maps to the Pacioli
group of finitely supported functions from accounts to rational
quantities, and this is the level at which the oracle computes. Each
step is a homomorphism. Each commuting square is checked by Lean. The
proofs depend on no axioms beyond propositional extensionality,
choice, and quotient soundness.

The modules divide along the same lines. `Basic`, `Accounts`,
`Groupoid`, `Labels`, `Hierarchy`, and `Valuation` define the objects
and their meaning. `Free` and `Pacioli` build the representation
tower. `Theorems`, `Derived`, and `Trivial` state and prove the laws.
`Prices` and `TimedPrices` treat valuation over time, and
`Derivation` is a separate rewrite layer for derived transactions.
The executable layer consists of `Parse`, `Journal`, `Oracle`,
`Register`, and `Driver`. `Gen` is a seeded generator of
property-test journals, and it never authors expected results.

## The semantics of the Ledger idea

A Ledger implementation reads plain-text journals and reports on
them. The theory fixes what any such implementation must preserve.
Value is conserved: a transaction balances exactly, per commodity, or
names the one posting that absorbs the remainder. Arithmetic is
exact: quantities are rational numbers, and the theory rounds only at
display, after all composition, so that approximation is applied once
and never compounded. The order of accounts within a transaction
carries no meaning. Reports are functions of the journal's
denotation, so two journals with the same denotation report the same
balances.

Alongside the theory, the executable layer records the observed
conventions of the C++ implementation, rule by rule. Each rule cites
the regression test or the C++ source location that forced it. The
recorded conventions cover number parsing, display precision,
automated transactions, commodity equivalences, and balancing
tolerances. A few of them depart from the exact-rounding rule in
witnessed places. One example is the rounded gain that a posting with
both a lot price and a cost books into its effective cost, and the
code marks each such place with the test that pins it. This layer is
considerably larger than the theory, which is itself instructive: the
invariants of double-entry accounting are small, while the surface
conventions of twenty years of practice are extensive. An
implementation beginning afresh is free to adopt fewer of them. The
theory identifies which parts are meaning and which parts are habit.

## The oracle

`Ledger/Driver.lean` turns the semantics into a test instrument. It
reads one or more journal files, resolves their include directives,
evaluates each journal, and prints one line for every nonzero
balance. It runs through Lake:

    lake env lean --run Ledger/Driver.lean FILE.dat ...

The output protocol is small, so that a comparator against it stays
small. Each file's section begins with `== PATH`. Each balance row
has the form `COMMODITY|AMOUNT|ACCOUNT`, with the amount in canonical
decimal form and the rows sorted. A line of the form `%% dc COMM`
declares that the named commodity learned a decimal-comma style, and
`%% dc *` names the null commodity, so that the comparator can
normalize the other side's output. A rejected file prints `!! ERROR`
with a reason and nothing else, which keeps failure visible. Flags
given before a file path apply to that file alone: `--decimal-comma`,
`--recursive-aliases`, `--now DATE`, and
`--input-date-format FORMAT`.

The driver runs under the Lean interpreter, and the build
deliberately produces no native executable, so that what executes is
a direct reading of the checked definitions.

## Bisimulation against another implementation

The oracle exists so that other ports of the Ledger idea can measure
themselves against the semantics. The procedure that brought the C++
implementation to exact agreement transfers without alteration, and
it has five parts.

First, collect a corpus. Use the implementation's own test journals,
all of them rather than a curated sample, and split each test into
its journal content and its expected command output. Classify the
files before any comparison. Tests that expect an error, files with
no journal content, and journals that embed a general-purpose
scripting language are not comparable, and each such file is assigned
to a named bin rather than quietly dropped.

Second, run both sides on the same journal and normalize both outputs
to the row format above. Normalization deserves suspicion in
proportion to its size, because it is the place where a comparison
can fail without notice. Keep it small: parse the implementation's
balance report, map displayed amounts to canonical decimals, and
apply the declared decimal-comma styles.

Third, make every non-comparison visible. A file the oracle cannot
yet read is a named skip and never a pass. The C++ harness exits with
code 77 in that case, and its test runner reports the run as skipped.
The goal is zero skips outside the inherently non-comparable bins.
The C++ suite has reached that goal. Of its 4364 test files, 3796 are
compared with zero divergence, 489 expect errors, 77 contain no
journal, and 2 embed Python in the journal itself.

Fourth, prove that the comparator can fail. Every run replays a
fixture in which one side carries a known planted defect, and the run
fails unless the detector fires. A comparator that has never been
observed to fail provides no evidence when it passes.

Fifth, record what was compared. Each result names the source
revisions of both sides, the binary, and the flags, and it states
what the comparison does not cover. This oracle compares balances. It
does not yet compare register report rows, market valuation, or lot
matching. A passing result is meaningful only together with a plain
statement of its limits.

The divergences that such a comparison surfaces are its value. Each
one either exposes a defect in the implementation under test or
exposes a convention that the semantics has not yet recorded. The
first kind is repaired in the implementation. The second kind belongs
here, as a witnessed rule.

## Building the repository

The repository builds in two ways, and both check the proofs, because
the lakefile turns warnings into errors and an unproved theorem is a
warning.

With Nix, `nix build` produces the checked oracle tree, ready for
`lake env lean --run`, and verifies every proof along the way. The
flake pins the Lean toolchain (4.30.0, in lockstep with
`lean-toolchain` and the Mathlib revision in `lake-manifest.json`)
and holds the complete dependency tree as a fixed-output derivation,
so no machine ever compiles Mathlib. `nix develop` opens a shell with
the same toolchain.

Without Nix, install Lean 4.30.0 through elan, then run
`lake exe cache get` followed by `lake build`. The first command
downloads the prebuilt Mathlib artifacts. The second compiles this
repository's modules and completes in a few minutes once the cache is
present.

## Provenance and present limits

This work was extracted from the C++ Ledger repository, where it was
developed together with the bisimulation harness that consumes it.
The development branch of that project references this repository as
a git submodule and runs the comparison in its continuous integration
and in development builds. Release builds of the C++ program require
no Lean toolchain: without the submodule the test is not registered,
and a registered test without a toolchain reports itself skipped.

The balance semantics is complete against the C++ suite as of August
2026. Register rows and time-indexed valuation are specified in the
theory and remain to be bisimulated, by the same procedure.

## License

BSD three-clause, as `LICENSE.md` states. The copyright is held by
John Wiegley.
