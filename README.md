# ledger-semantics

This repository holds the mathematical semantics of double-entry
plain-text accounting, the model of bookkeeping that the
[Ledger](https://github.com/ledger/ledger) family of programs
implements. The semantics is formalized in Lean 4 and proved against
Mathlib, and from the same definitions the repository builds an
executable oracle: a program that reads ordinary journal files,
evaluates them under the proved meaning, and prints the resulting
account balances in a small fixed format. The oracle exists so that
an implementation of the Ledger idea, written in any language, can be
tested against the mathematics of the subject rather than against
the remembered behavior of an older program. The C++ Ledger project
already uses it in this way. Its development branch replays every
positive journal in its test suite through the oracle and requires
exact agreement on each file.

The work follows the discipline of denotational design as Conal
Elliott teaches it ("Denotational design with type class morphisms",
2009). One begins by saying precisely what a thing means, then
requires every operation to preserve that meaning, and finally lets
the implementation be whatever the equations force it to be. This
document takes the same order. It describes the mathematics, the
obligations that the mathematics places on any implementation, the
oracle and its output protocol, the procedure for measuring another
implementation against the oracle, and the ways in which the
repository is built.

## The mathematics

The formalization begins with the structure of transactions and
accounts, and introduces quantities of money only afterward, through
a valuation. An account, in this theory, is simply a name. A
transaction moves value among accounts, and its meaning does not
depend on the order in which its postings happen to be written down.
The mathematical object with exactly these properties is the free
symmetric strict monoidal category over finite multisets of
accounts, in which each transaction appears as a generator whose
domain is the multiset of its source accounts and whose codomain is
the multiset of its destinations. A journal is then a single term of
this category, the tensor product of its transactions, with
sequencing given by composition. The symmetry isomorphisms make
provable the familiar fact that the order of accounts carries no
information.

Money enters through a valuation, a functor from this category into
commutative groups that assigns to each generator the flow of
quantities the transaction causes, and that is required to respect
composition, tensor, and addition. The reporting function `netFlow`,
which every balance report computes, is then an additive
homomorphism out of the free model. Seen this way, the Pacioli
invariant that debits equal credits is a theorem about the shape of
morphisms, since every morphism has equal measure on its two ends.
The theorem `pacioli_equation` in `Ledger/Theorems.lean` establishes
the invariant for the abstract category, and `free_flow_balanced` in
`Ledger/Pacioli.lean` carries it down to the computed flows.

The theory also contains a negative result, one that explains a
design constraint visible in every mature accounting program. The
valuation algebra cannot support the further laws that folklore
expects of it. The absorption law by itself forces every valuation
to zero, an argument that `zero_absorption_degenerates` in
`Ledger/Pacioli.lean` records and that refutes the bilinearity law
separately as well, so the three laws named above are the minimal
consistent basis. It follows that pricing must live outside the
compositional core, as a lookup performed at reporting time, because
a compositional pricing algebra with the expected laws does not
exist.

From the abstract meaning a representation tower descends in proved
steps. The category maps first to a free model built as a quotient
of formal morphisms, and the free model maps in turn to the Pacioli
group of finitely supported functions from accounts to rational
quantities, which is the level at which the oracle computes. Each
step is a homomorphism, each commuting square is checked by Lean,
and the proofs depend on no axioms beyond propositional
extensionality, choice, and quotient soundness.

The modules divide along the same lines. The objects and their
meaning are defined in `Basic`, `Accounts`, `Groupoid`, `Labels`,
`Hierarchy`, and `Valuation`. The representation tower is built in
`Free` and `Pacioli`, the laws are stated and proved in `Theorems`,
`Derived`, and `Trivial`, and valuation over time is treated in
`Prices` and `TimedPrices`, with `Derivation` serving as a separate
rewrite layer for derived transactions. The executable layer
consists of `Parse`, `Journal`, `Oracle`, `Register`, and `Driver`,
together with `Gen`, a seeded generator of property-test journals
that never authors expected results.

## What an implementation must preserve

A Ledger implementation reads plain-text journals and reports on
them, and the theory fixes what any such program must preserve.
Value is conserved, so that a transaction either balances exactly
within each commodity or names the one posting that absorbs the
remainder. Arithmetic is exact, with quantities kept as rational
numbers and rounding performed only at display, after all
composition, so that approximation is applied once and never
compounded. The order of accounts within a transaction carries no
meaning, and reports are functions of the journal's denotation, so
that two journals with the same denotation report the same balances.

Alongside this theory, the executable layer records the observed
conventions of the C++ implementation, rule by rule, with each rule
citing the regression test or the C++ source location that forced
it. These conventions cover number parsing, display precision,
automated transactions, commodity equivalences, and balancing
tolerances, and a few of them depart from the exact-rounding rule in
witnessed places. One example is the rounded gain that a posting
carrying both a lot price and a cost books into its effective cost,
and the code marks each such departure with the test that pins it.
This layer is considerably larger than the theory, which is itself a
lesson worth having in writing: the invariants of double-entry
accounting are small, while the surface conventions of twenty years
of practice are extensive. An implementation beginning afresh is
free to adopt fewer of them, and the theory identifies which parts
are meaning and which parts are habit.

## The oracle

`Ledger/Driver.lean` turns the semantics into a test instrument
that reads one or more journal files, resolves their include
directives, evaluates each journal, and prints one line for every
nonzero balance. It runs through Lake:

    lake env lean --run Ledger/Driver.lean FILE.dat ...

The output protocol is small so that a comparator against it can
stay small. Each file's section begins with `== PATH`, and each
balance row has the form `COMMODITY|AMOUNT|ACCOUNT`, with the amount
in canonical decimal form and the rows sorted. A line of the form
`%% dc COMM` declares that the named commodity learned a
decimal-comma style, with `%% dc *` naming the null commodity, so
that a comparator can normalize the other side's output. A rejected
file prints `!! ERROR` with a reason and nothing else, which keeps
failure visible. Flags given before a file path apply to that file
alone, and four are recognized: `--decimal-comma`,
`--recursive-aliases`, `--now DATE`, and
`--input-date-format FORMAT`.

The driver runs under the Lean interpreter, and the build
deliberately produces no native executable, so that what executes
remains a direct reading of the checked definitions.

## Measuring an implementation against the oracle

The oracle exists so that other ports of the Ledger idea can measure
themselves against the semantics, and the procedure that brought the
C++ implementation to exact agreement transfers without alteration.

The procedure begins with a corpus. The implementation's own test
journals serve, taken in their entirety rather than as a curated
sample, with each test split into its journal content and its
expected command output. The files are classified before any
comparison takes place, because some are not comparable at all:
tests that expect an error, files with no journal content, and
journals that embed a general-purpose scripting language each go to
a named bin rather than being quietly dropped.

Both sides then run on the same journal, and both outputs are
normalized to the row format above. Normalization deserves suspicion
in proportion to its size, since it is the place where a comparison
can fail without notice, and it stays trustworthy by staying small.
Parsing the implementation's balance report, mapping displayed
amounts to canonical decimals, and applying the declared
decimal-comma styles is the whole of it.

Every non-comparison is made visible. A file the oracle cannot yet
read counts as a named skip and never as a pass, and the C++ harness
exits with code 77 in that case so that its test runner reports the
run as skipped. The goal is zero skips outside the inherently
non-comparable bins, and the C++ suite has reached that goal. Of its
4364 test files, 3796 are compared with zero divergence, 489 expect
errors, 77 contain no journal, and 2 embed Python in the journal
itself.

The comparator is also proved able to fail. Every run replays a
fixture in which one side carries a known planted defect, and the
run fails unless the detector fires, because a comparator that has
never been observed to fail provides no evidence when it passes.

Finally, each result records what it compared, naming the source
revisions of both sides, the binary, and the flags, and it states
what the comparison does not cover. This oracle compares balances.
It does not yet compare register report rows, market valuation, or
lot matching, and a passing result is meaningful only together with
a plain statement of such limits.

The divergences that a comparison surfaces are its value. Each one
either exposes a defect in the implementation under test or exposes
a convention that the semantics has not yet recorded. The first kind
is repaired in the implementation, and the second kind belongs here,
as a witnessed rule.

## Building the repository

The repository builds in two ways, and both check the proofs,
because the lakefile turns warnings into errors and an unproved
theorem is a warning.

With Nix, `nix build` produces the checked oracle tree, ready for
`lake env lean --run`, and verifies every proof along the way. The
flake pins the Lean toolchain at 4.30.0, in lockstep with
`lean-toolchain` and the Mathlib revision in `lake-manifest.json`,
and it holds the complete dependency tree as a fixed-output
derivation, so that no machine ever compiles Mathlib. `nix develop`
opens a shell with the same toolchain.

Without Nix, install Lean 4.30.0 through elan and run
`lake exe cache get` followed by `lake build`. The first command
downloads the prebuilt Mathlib artifacts, and the second compiles
this repository's modules, finishing in a few minutes once the
cache is present.

## Provenance and present limits

This work was extracted from the C++ Ledger repository, where it
was developed together with the bisimulation harness that consumes
it. The development branch of that project references this
repository as a git submodule and runs the comparison in its
continuous integration and in its development builds. Release
builds of the C++ program require no Lean toolchain, because
without the submodule the test is not registered, and a registered
test without a toolchain reports itself skipped.

The balance semantics is complete against the C++ suite as of
August 2026. Register rows and time-indexed valuation are specified
in the theory and remain to be bisimulated, by the same procedure.

## License

BSD three-clause, as `LICENSE.md` states. The copyright is held by
John Wiegley.
