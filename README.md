# ledger-semantics

This repository contains a mathematical semantics for double-entry
plain-text accounting — the idea at the center of the
[Ledger](https://github.com/ledger/ledger) family of programs —
formalized in Lean 4 against Mathlib, together with an executable
oracle derived from the same definitions. The formalization gives the
journal a precise meaning and proves the central theorems about it;
the oracle reads ordinary journal files, evaluates them under that
meaning, and prints account balances in a small fixed format, so that
any implementation of the Ledger idea, in any language, can be
measured against the semantics rather than against folklore. The C++
Ledger project is the first consumer: its development branch replays
every positive journal in its test suite through this oracle and
requires exact agreement, file by file.

The method followed here is denotational design, as taught by Conal
Elliott ("Denotational design with type class morphisms", 2009). Its
discipline is brief to state and demanding to practice: say first
what a thing means; require that every operation preserve that
meaning; and let the implementation be whatever the equations force
it to be. The sections that follow set out the mathematics, the
obligations it places on any implementation, the oracle and its
output protocol, the procedure for comparing an implementation
against it, and the ways in which the repository is built.

## The mathematics

The formalization begins not with money but with the structure of
transaction and account, for it is the structure that carries the
meaning; quantities enter afterward, through a valuation. An account
is a name, and a transaction moves value among accounts in a manner
indifferent to the order in which its postings are written. The
mathematical object with exactly these properties is the free
symmetric strict monoidal category over finite multisets of accounts:
each transaction is a generator whose domain is the multiset of its
source accounts and whose codomain is the multiset of its
destinations; a journal is a single term, the tensor product of its
transactions; sequencing is composition; and the symmetry
isomorphisms establish, as theorem rather than convention, that the
order of accounts is without significance.

Money enters through a valuation — a functor from this category into
commutative groups, assigning to each generator the flow of
quantities it causes and required to respect composition, tensor, and
addition. The reporting function `netFlow`, which every balance
report computes, is then an additive homomorphism out of the free
model. The Pacioli invariant, that debits equal credits, is
accordingly not an axiom of the theory but a consequence of its
shape: every morphism has equal measure on its two ends. The theorem
`pacioli_equation` in `Ledger/Theorems.lean` establishes it once for
the abstract category, and `free_flow_balanced` in
`Ledger/Pacioli.lean` carries it down to the computed flows.

One negative result deserves particular notice, because it explains a
design constraint visible in every mature accounting program. The
valuation algebra cannot carry the laws that folklore expects of it:
the absorption law alone forces every valuation to zero — the theorem
`zero_absorption_degenerates` in `Ledger/Pacioli.lean` records the
short degeneracy argument — and the same argument refutes the
bilinearity law separately. The minimal consistent basis is the three
laws named above. It follows that pricing must live outside the
compositional core, as a lookup performed at reporting time; a
compositional pricing algebra with the expected laws does not exist
to be implemented.

From this meaning a representation tower descends in proved steps.
The abstract category maps to a free model, built as a quotient of
formal morphisms; the free model maps in turn to the Pacioli group of
finitely supported functions from accounts to rational quantities,
which is the level at which the oracle computes. Each step is a
homomorphism, each commuting square is checked by Lean, and the
proofs close with no axioms beyond propositional extensionality,
choice, and quotient soundness.

The modules divide along the same lines. `Basic`, `Accounts`,
`Groupoid`, `Labels`, `Hierarchy`, and `Valuation` define the objects
and their meaning; `Free` and `Pacioli` build the representation
tower; `Theorems`, `Derived`, and `Trivial` state and prove the laws;
`Prices` and `TimedPrices` treat valuation over time; and
`Derivation` is a separate rewrite layer for derived transactions.
The executable layer comprises `Parse`, `Journal`, `Oracle`,
`Register`, and `Driver`, with `Gen` a seeded generator of
property-test journals that never authors expected results.

## The semantics of the Ledger idea

A Ledger implementation reads plain-text journals and reports upon
them; the theory fixes what any such implementation must preserve.
Value is conserved: a transaction balances exactly, per commodity, or
names the one posting that absorbs the remainder. Arithmetic is
exact: quantities are rational numbers, and the theory rounds only at
display, after all composition, so that approximation is applied once
rather than compounded. The order of accounts within a transaction
carries no meaning, and reports are functions of the journal's
denotation, so that two journals with the same denotation report the
same balances.

Alongside the theory, the executable layer records — rule by rule,
each rule citing the regression test or the C++ source location that
forced it — the observed conventions of the C++ implementation: its
number parsing, its display-precision behavior, its automated
transactions, its commodity equivalences, and its balancing
tolerances. A few of these conventions depart from the exact-rounding
rule in witnessed places; the rounded gain that a lot with a cost
books into its effective cost is one such, and the code marks each
with the test that pins it. This layer is considerably larger than
the theory, and the disproportion is instructive: the invariants of
double-entry accounting are small, while the surface conventions of
twenty years of practice are not. An implementation beginning afresh
is free to adopt fewer of them, and the theory serves precisely to
distinguish the parts that are meaning from the parts that are habit.

## The oracle

`Ledger/Driver.lean` turns the semantics into a test instrument. It
reads one or more journal files, resolves their include directives,
evaluates each journal, and prints one line for every nonzero
balance. It is run through Lake:

    lake env lean --run Ledger/Driver.lean FILE.dat ...

The output protocol is deliberately narrow, so that a comparator
against it remains small. Each file's section begins with `== PATH`;
each balance row has the form `COMMODITY|AMOUNT|ACCOUNT`, with the
amount in canonical decimal form and the rows sorted; a line
`%% dc COMM` declares that the named commodity learned a
decimal-comma style, `%% dc *` naming the null commodity, so that the
comparator can normalize the other side's output accordingly; and a
rejected file prints `!! ERROR` with a reason and nothing else, so
that failure is visible rather than silent. Flags given before a file
path apply to that file alone: `--decimal-comma`,
`--recursive-aliases`, `--now DATE`, and
`--input-date-format FORMAT`.

Interpretation is intentional. The driver runs under the Lean
interpreter, and the build produces no native executable, so that
what executes remains a direct reading of the checked definitions.

## Bisimulation against another implementation

The oracle exists so that other ports of the Ledger idea can measure
themselves against the semantics, and the procedure that brought the
C++ implementation to exact agreement transfers without alteration.
It has five parts.

First, a corpus is collected — the implementation's own test
journals, every one of them rather than a curated sample, each split
into its journal content and its expected command output. Files are
classified before any comparison: tests that expect an error, and
files with no journal content, are not comparable, and they are
assigned to named bins rather than quietly dropped.

Second, both sides run on the same journal, and both outputs are
normalized to the row format above. Normalization deserves suspicion
in proportion to its size, for it is the place where a comparison can
fail without notice; it is kept small — parse the implementation's
balance report, map displayed amounts to canonical decimals, and
apply the declared decimal-comma styles.

Third, every non-comparison is made visible. A file the oracle cannot
yet read is a named skip, never a pass; the C++ harness exits with
code 77 in that case, so that its test runner reports the run as
skipped. The goal state is zero skips outside the inherently
non-comparable bins, and the C++ suite has reached it: 3794 files
compared with zero divergence, the only skipped files being the 485
negative tests and the 52 files without journal content.

Fourth, the comparator is proved able to fail. Every run replays a
fixture in which one side carries a known planted defect, and the run
fails unless the detector fires. A comparator that has never been
observed to fail offers no evidence when it passes.

Fifth, each result records what it compared — the source revisions of
both sides, the binary, and the flags — and states what it does not
cover. This oracle compares balances; it does not yet compare
register report rows, market valuation, or lot matching. A passing
result is meaningful only beside a plain statement of its limits.

The divergences such a comparison surfaces are its value. Each one
either exposes a defect in the implementation under test or exposes a
convention the semantics has not yet recorded; the first kind is
repaired in the implementation, and the second belongs here, as a
witnessed rule.

## Building the repository

The repository is built in either of two ways, and both check the
proofs, for the lakefile turns warnings into errors and an unproved
theorem is a warning.

With Nix, `nix build` produces the checked oracle tree, ready for
`lake env lean --run`, and verifies every proof along the way. The
flake pins the Lean toolchain (4.30.0, in lockstep with
`lean-toolchain` and the Mathlib revision in `lake-manifest.json`)
and holds the complete dependency tree as a fixed-output derivation,
so that no machine ever compiles Mathlib. `nix develop` opens a shell
with the same toolchain.

Without Nix, install Lean 4.30.0 through elan, then run
`lake exe cache get` followed by `lake build`; the first command
downloads the prebuilt Mathlib artifacts, and the second compiles
this repository's modules, completing in a few minutes once the cache
is present.

## Provenance and present limits

This work was extracted from the C++ Ledger repository, where it was
developed together with the bisimulation harness that consumes it.
The development branch of that project references this repository as
a submodule and runs the comparison in its continuous integration and
in development builds; release builds of the C++ program require no
Lean toolchain, for without the submodule the test is not registered,
and a registered test without a toolchain reports itself skipped.

The balance semantics is complete against the C++ suite as of August
2026. Register rows and time-indexed valuation are specified in the
theory but not yet bisimulated; they are the natural next steps, and
the procedure above is the means by which they will be taken.

## License

BSD three-clause, as `LICENSE.md` states. The copyright is held by
John Wiegley.
