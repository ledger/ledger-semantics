# ledger-semantics

This repository holds a machine-checked answer to a simple question:
what does a ledger mean?

The answer is written in Lean 4 against Mathlib. It has two layers. The
first layer is a small mathematical theory of double-entry accounting,
with its central results proved. The second layer is an executable
oracle. The oracle reads journal files, applies the theory, and prints
account balances in a fixed format. Any program that claims to
implement the Ledger idea, in any language, can be tested against this
oracle. The C++ [Ledger](https://github.com/ledger/ledger) project does
exactly that: its test suite replays every positive test journal
through this oracle and requires exact agreement, file by file.

The method behind the work is denotational design, as taught by Conal
Elliott (see "Denotational design with type class morphisms", 2009).
The discipline is short to state. First say what a thing means. Then
require that every operation preserve that meaning. Let the
implementation be whatever the equations force it to be.

## The mathematics

The meaning of a journal does not begin with money. It begins with
structure.

An account is a name. A transaction moves value between accounts, and
nothing in its meaning depends on the order in which the accounts are
written. The mathematical object with exactly these properties is the
free symmetric strict monoidal category over finite multisets of
accounts. Each transaction is a generator. Its domain is the multiset
of source accounts. Its codomain is the multiset of destination
accounts. A journal is one term: the tensor product of its
transactions. Sequencing is composition. The symmetry isomorphisms say,
as a theorem rather than a convention, that account order is
irrelevant.

Money enters only through a valuation. A valuation is a functor from
this category into commutative groups. It assigns to each generator the
flow of quantities it causes, and it is required to respect
composition, tensor, and addition. The reporting function `netFlow`,
which every balance report computes, is then an additive homomorphism
out of the free model. The Pacioli invariant, that debits equal
credits, is not an axiom of the theory. It is the statement that every
morphism has equal measure on its two ends. `pacioli_equation` in
`Ledger/Theorems.lean` proves it once for the abstract category, and
`free_flow_balanced` in `Ledger/Pacioli.lean` carries it down to the
computed flows.

One negative result deserves notice. The valuation algebra cannot
carry the laws that folklore expects of it. The absorption law alone
forces every valuation to zero; `zero_absorption_degenerates` in
`Ledger/Pacioli.lean` is the short degeneracy argument, and the same
argument refutes the bilinearity law separately. The minimal
consistent basis is the three laws named above.
This explains a fact about every mature accounting program: pricing is
a report-time lookup, not a compositional algebra, because a
compositional pricing algebra with the expected laws does not exist.

The representation tower descends from this meaning in proved steps.
The abstract category maps to a free model built as a quotient of
formal morphisms. The free model maps to the Pacioli group of
finitely supported functions from accounts to rational quantities,
which is the level the oracle computes. Each step is a homomorphism,
and each commuting square is checked by Lean. The proofs close with
no axioms beyond propositional extensionality, choice, and quotient
soundness.

The modules divide as follows. `Basic`, `Accounts`, `Groupoid`,
`Labels`, `Hierarchy`, and `Valuation` define the objects and the
meaning. `Free` and `Pacioli` build the representation tower.
`Derivation` is the separate rewrite layer for derived transactions.
`Theorems`, `Derived`, and `Trivial` state and prove the laws.
`Prices` and `TimedPrices` treat valuation over time. `Parse`,
`Journal`, `Oracle`, `Register`, and `Driver` form the executable
layer. `Gen` is a seeded generator of property-test journals; it never
authors expected results.

## The semantics of the Ledger idea

A Ledger implementation reads plain text journals and reports on them.
The theory fixes what any such implementation must preserve.

Value is conserved. A transaction either balances exactly, per
commodity, or names the one posting that absorbs the remainder.
Arithmetic is exact. Quantities are rational numbers, and the theory
rounds only at display, after all composition. Account order within a
transaction has no meaning. Reports are functions of the journal's
denotation, so two journals with the same denotation report the same
balances. The recorded C++ conventions break the rounding rule in a
few witnessed places, for example the rounded gain that a lot with a
cost books into its effective cost; the code marks each such place
with the test that pins it.

The executable layer of this repository also records, rule by rule, the
observed semantics of the C++ implementation: its number parsing, its
display-precision behavior, its automated transactions, its commodity
equivalences, and its balancing tolerances. Each rule in
`Ledger/Journal.lean` and `Ledger/Parse.lean` cites the regression test
or the C++ source location that forced it. This layer is larger and
less beautiful than the theory, and that is the honest shape of the
subject: the invariants are small, and the surface conventions of
twenty years of practice are not. A new implementation is free to adopt
fewer conventions. The theory says which parts are meaning and which
parts are habit.

## The oracle

`Ledger/Driver.lean` turns the theory into a test instrument. It reads
one or more journal files, resolves includes, evaluates the journal
under the semantics, and prints one line per nonzero balance.

Run it with Lake:

    lake env lean --run Ledger/Driver.lean FILE.dat ...

The output protocol is deliberately small. Each file's block starts
with `== PATH`. Each balance row has the form
`COMMODITY|AMOUNT|ACCOUNT`, with the amount in canonical decimal form
and the rows sorted. A line `%% dc COMM` declares that the named
commodity learned a decimal-comma style, so a comparator can normalize
the other side's output; `%% dc *` names the null commodity. A
rejected file prints `!! ERROR reason` and nothing else, so failure is
visible rather than silent. Flags before a file path apply to that
file only: `--decimal-comma`, `--recursive-aliases`,
`--now DATE`, and `--input-date-format FORMAT`.

Interpretation is intentional. The driver runs under the Lean
interpreter, and the build produces no native executable, so the
oracle stays a direct reading of the checked definitions.

## Bisimulation against another implementation

The oracle exists so that other ports of the Ledger idea can measure
themselves. The procedure that reached exact agreement for the C++
implementation transfers to any other. It has five parts.

First, collect a corpus. Use your implementation's own test journals,
every one of them, not a curated sample. Split each test into its
journal and its expected command output. Classify the files before
comparison: tests that expect an error, and files with no journal
content, are not comparable and belong in named bins.

Second, run both sides on the same journal and normalize both outputs
to the row format above. Normalization is where comparisons die
quietly, so keep it small: parse your implementation's balance report,
map display amounts to canonical decimals, and apply the declared
decimal-comma styles.

Third, make every non-comparison visible. A file the oracle cannot yet
read is a named skip, never a pass. The C++ harness exits with code 77
for a skipped run so the test runner reports SKIPPED. The goal state
is zero skips outside the inherently non-comparable bins, and the
C++ suite reached it: 3792 files compared with zero divergence, and
the only skipped files are the 485 negative tests and the 52 files
with no journal content.

Fourth, prove the comparator can fail. Every run replays a fixture in
which one side is perturbed by a known defect. If the detector does
not fire, the run fails. A comparator that cannot fail measures
nothing.

Fifth, pin what was compared. Record the source revisions, the binary,
and the flags of every run in the result artifact, and state what the
comparison does not cover. This oracle compares balances. It does not
yet compare register report rows, market valuation, or lot matching.
A passing gate that hides its ceiling is advertising.

Divergences found this way are the product. Work through them one file
at a time. Each divergence either exposes a defect in your
implementation, or exposes a convention your implementation has that
the semantics does not yet record. Both outcomes are progress, and the
second kind belongs upstream here as a witnessed rule.

## Building

The repository builds in two ways.

With Nix, `nix build` produces the checked oracle tree, ready for
`lake env lean --run`, and verifies every proof on the way; the flake
pins the Lean toolchain (4.30.0) and holds
the entire Mathlib dependency tree as a fixed-output derivation, so no
machine ever compiles Mathlib. `nix develop` opens a shell with the
same toolchain.

Without Nix, install Lean 4.30.0 through elan, then run
`lake exe cache get` followed by `lake build`. The first command
downloads the prebuilt Mathlib artifacts. The second compiles this
repository's modules; because the lakefile turns warnings into errors,
an unproved theorem fails the build. A full build after the cache
download takes a few minutes.

## Provenance and status

This work was extracted from the C++ Ledger repository, where it was
developed together with the bisimulation harness that consumes it.
The development branch of the C++ project references this repository
as a submodule and runs the comparison in its continuous integration
and in development builds. Release builds of the C++ program do not
require Lean; without the submodule the test is not registered, and a
registered test without a toolchain skips visibly.

The balance semantics is complete against the C++ suite as of August
2026. Register rows and time-indexed valuation are specified in the
theory but not yet bisimulated. They are the next rungs, and the
method above is how they will be climbed.

## License

BSD three-clause, as `LICENSE.md` states. The copyright is held by
John Wiegley.
