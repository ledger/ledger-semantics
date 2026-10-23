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

Money enters through valuations. A valuation is an additive real
measurement of morphisms, and there are many of them: one for each
account, each commodity, or each budget scenario. Every valuation
respects composition, tensor, and addition, in the sense that the
measurement of a composite, of a tensor product, or of an aggregate
is the sum of the measurements of its parts. The reporting function
`netFlow`, which computes the oracle's net balances, is then an
additive homomorphism out of the free model.

The double-entry principle is not a law of this structure but a
hypothesis on each entry: the postings of every transaction sum to
zero in each commodity. The principle is preserved because zero
added to zero is zero. The master theorem
`balanced_generators_balance` in `Ledger/Theorems.lean` shows that
every morphism built from balanced entries is itself balanced,
`trial_balance` states the resulting equality of debits and credits
for a finite family of account measurements whose sum vanishes on
each entry, and `balance_sheet_equation` rearranges the balance
hypothesis on three account classes as assets equal to liabilities
plus equity. For the flows the oracle computes, `free_double_entry`
and `free_trial_balance` in `Ledger/Pacioli.lean` give the same
conclusion in every commodity. Not every entry the oracle reads
satisfies the hypothesis, as the section on what an implementation
must preserve explains, and these theorems say nothing about the
entries that do not. Nor does a trial balance that sums to zero
show that each entry is correct: it shows that the entries balance
in total, and offsetting errors cancel.

The oracle also records the two sides of each entry. Each
generator's domain is the multiset of the accounts it credits and
its codomain the multiset of the accounts it debits, and for a
generator that balances in every commodity, the net debits to its
codomain equal the net credits to its domain, commodity by
commodity (`specFor_coherent` and `flowsFin_two_ends` in
`Ledger/DriverTwoSides.lean`, applying `two_ends` in
`Ledger/TwoSides.lean`). These are the positive and negative parts
of the net flow at each account, not posting-wise gross totals;
endpoint multiplicities count postings, not amounts. David Ellerman
argues that this two-sidedness is what is double in double-entry
bookkeeping ("On Double-Entry Bookkeeping: The Mathematical
Treatment", Accounting Education 23:5, 2014, p. 487). That an entry
touches two or more accounts is not what is double: every nonzero
zero-row of the signed carrier touches two accounts of one
commodity (`zeroRow_two_accounts` in `Ledger/Pacioli.lean`), and a
single-sided system of signed numbers shares the property. The
two-ends reading holds for generators and not for morphisms in
general, since a composite can carry flow at its intermediate
accounts. No nonzero valuation measures every morphism as the
difference between a measure of its codomain and a measure of its
domain (`endpoint_measure_degenerates` in `Ledger/Valuation.lean`),
and a measure of objects that is equal at the two ends of every
morphism and zero on the empty object is zero everywhere
(`conserved_measure_zero`), because the zero morphism exists
between any two objects.

The theory also contains a negative result, which explains why the
compositional core omits certain compatibility laws. Hom-set
addition aggregates transactions with the same endpoints and
respects valuations, but the additional laws considered here would
trivialize them. Each of the laws that folklore expects to relate
it to the other operations forces every valuation to zero:
absorption of zero by composition (`zero_absorption_degenerates`),
distribution of composition over addition on either side
(`left_distrib_degenerates` and `right_distrib_degenerates`), and
additivity of tensor in its first argument
(`tensor_additive_degenerates`), all in `Ledger/Pacioli.lean`.
Because the free model satisfies the remaining laws and carries
valuations that are not zero, none of these laws follows from the
laws that remain, and `comp_not_zero_absorbing`,
`comp_not_left_additive`, and `tensor_not_additive` exhibit the
failure in the free model directly. The three valuation laws are
the basis from which `V_id`, `V_zero`, and `V_inv` are derived in
`Ledger/Valuation.lean`.

None of this rules out compositional pricing. Valuation at fixed
prices is itself a lawful valuation: a price-weighted sum of
per-commodity measurements, built from `ValuationFunctor.finsetSum`
and scalar multiplication (`priceValuation` in
`Ledger/PriceVector.lean` gives the free-model form), satisfies all
three laws, and `PriceAction.constModel` in
`Ledger/TimedPrices.lean` is a model of the price action at rates
formed from arbitrary nonzero commodity prices. What no transaction
causes is the passage of the report date. In
`Ledger/HoldingGain.lean`, `holding_gain_functor` expresses the
change in value between two report dates as valuation at the
difference of the price vectors relative to the chosen numeraire,
assuming nonzero prices. The theorem
`timedConstRates_no_holding_gain` shows that the older model cannot
express this change when the numeraire is held at price 1. A report
that values holdings at the prices of a later date therefore
performs a lookup at reporting time rather than an operation on the
journal. Ellerman describes the fixed-price case, valuing each
vector of property quantities by a single price vector (2014, pp.
497-498); the treatment of dated prices and revaluation is this
repository's own.

From the abstract meaning a representation tower descends in proved
steps. The abstract structure is represented by a free model built
as a quotient of formal morphisms, and the free model maps in turn
to finitely supported functions from accounts to rational
quantities, the carrier `PacioliGroup`. The oracle computes this
denotation with plain functions, account by account, as
`netFlow_eq_flowAux` proves. Each step is a homomorphism, each
commuting square is checked by Lean, and the proofs depend on no
axioms beyond propositional extensionality, choice, and quotient
soundness.

These claims are stated in the standard vocabulary rather than in a
private one. For every lawful model, `Ledger/Groupoid.lean`
constructs genuine Mathlib instances of `Category`, `Groupoid`,
`MonoidalCategory`, and `SymmetricCategory` on the model's tagged
object type, together with the commutative-monoid structure on each
hom-set, so the sentence "a journal lives in a symmetric monoidal
groupoid" is a set of type-class instances rather than a figure of
speech. The coherence conditions are inherited from Mathlib. The one
standard structure deliberately absent is compatibility between
hom-addition and composition, which the degeneracy result above
rules out.

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

A set of leaf modules extends the specification. `TwoSides` reads
generator endpoints as the two sides of an entry and shows where
composition breaks sign coherence. `TAccount` builds Ellerman's pair
construction of the group of differences, with the debit and credit
isomorphisms onto the signed carrier in which the oracle computes.
`Decoding` presents balances by balance side and account class, and
shows that the choice of side governs presentation rather than truth.
`PriceVector` values flows by a fixed price vector, and `HoldingGain`
lets that vector change between instants, which is where holding gains
arise. `Lots` refines commodities by lot and states which market
valuations the oracle's lot-blind flows can support, `Conversion`
completes cost-balanced entries with the equity leg that Ledger's cost
syntax leaves implicit, `BasisGain` relates market value, basis, and
that leg, and `Closing` closes temporary accounts into equity.

Three join modules connect these leaves to the executable layer for
proofs only: `DriverTwoSides` proves the oracle's generators coherent
with their ends, `GrossLedger` identifies gross totals with
T-accounts, and `Market` proves that executable valuation agrees with
the price-vector valuation. The index `Ledger.lean` imports every
module except `Gen`, which defines its own `main`. No executable
module imports a leaf or a join module, so neither enters the
oracle's run path, the import closure of `Driver`.

## The relation to Ellerman's algebra

David Ellerman gives the algebra of double-entry bookkeeping as a
group of differences ("The Mathematics of Double Entry
Bookkeeping", Mathematics Magazine 58:4, 1985, 226-233). Its
elements are T-accounts `[d // c]`, pairs of an unsigned debit and
an unsigned credit, added side by side and equal when their
cross-sums agree; he calls it the Pacioli group. He extends it to
vectors of incommensurable property types, collapsed to a single
value only by a price vector ("Double-Entry Multidimensional
Accounting", Omega 14:1, 1986, 13-22), and the article cited above
presents both (2014). This repository computes in the signed,
single-sided image of that construction under his debit isomorphism
`[d // c] ↦ d - c`. The carrier `PacioliGroup` is the free vector
space over the rationals on pairs of an account name and a
commodity, the rational and finitely supported analogue of his
vector group, and it keeps only the signed difference of each
T-account. Ellerman faults treatments that pass back and forth
across the debit isomorphism without saying so, because doing so
confuses the single-sided and double-sided systems (2014, n. 14),
and the carrier is described here as his debit image for that
reason. He allows a program to store signed numbers internally
under either of his two isomorphisms (2014, p. 488). The
debit-positive choice here is inherited from the journal syntax, in
which C++ Ledger adds an amount to the account a posting names, and
it is fixed by the output protocol; under the credit isomorphism
every signed net row would change sign. The group of T-accounts
itself is built in `Ledger/TAccount.lean`: `toP_eq_toP_iff` is
Ellerman's equality by cross-sums, and `accountDebitIso` identifies
the rational, finitely supported group over accounts with the
carrier. His valuation of a vector of quantities by a price vector
is `priceDot` in `Ledger/PriceVector.lean`.

The correspondence with the tower is close. Ellerman calls the
encoding of each transaction as a zero-term, a T-account equal to
zero, the double-entry principle; here it is the hypothesis `hgen`
of `balanced_generators_balance`, which asks each generator to
balance. Posting a zero-term preserves a ledger's balance because
zero added to zero is zero (2014, p. 489), and that argument is the
proof of `balanced_generators_balance`. His two sides of an entry
are the domain and codomain of the oracle's generators, as
described above. His scheme "Beginning Ledger + Journal = Ending
Ledger" (2014, p. 496) appears without a separate beginning ledger:
opening balances can be entered as an ordinary balanced
transaction, and the journal term is built up from the identity on
the empty object (`journalTerm` in `Ledger/Driver.lean`). That is
faithful because a beginning ledger is itself a zero-account (2014,
p. 489). `balance_sheet_equation` gives his balance-sheet equation
when its three classes cover the accounts without overlap, with
revenue and expense included as temporary equity accounts, and the
flow is the whole journal up to the report date. Liabilities and
equity are read through the credit isomorphism. Decoding by balance
side, with each account assigned to one side, is `Side.decode` in
`Ledger/Decoding.lean`, and `decoded_iff_trial` shows that the side
chosen for an account changes the presentation of the equation and
not its truth. His reversal of a T-account corresponds to
`flow_inv` and `reversal_correctness`. His worked ledgers (2014,
pp. 489 and 496-498) are transcribed by hand as kernel-checked
goldens in the namespace `Ledger.Ellerman` in `Ledger/Oracle.lean`;
these check the evaluator and the transcribed arithmetic, not the
parser.

Two differences remain, and both are deliberate. The oracle's
generators need not be zero-terms, since Ledger balances an
exchange at cost and reports the postings' own quantities, where
Ellerman routes the reverse composition through equity (2014, p.
497). And where his algebra has a single operation, addition, the
free model keeps composition, tensor, and aggregation distinct.
Register reports observe the unreduced terms rather than only their
net flows. The negative results above exclude absorption and
distributive laws that would collapse every valuation; composition,
tensor and aggregation all become addition in the carrier.

Not all of Ellerman's apparatus is adopted by the executable
oracle. The default output has no debit and credit columns: the
protocol fixes it as signed rows, while the opt-in `--gross` flag
adds posting-wise debit and credit totals, as described below. The
oracle assigns no debit-balance or credit-balance labels to
accounts, since C++ accounts do not carry them, and it does not
complete exchanges with an equity leg, which would add postings
that C++ does not infer. Nor is addition the model's only
operation, which would erase the distinctions just described.
Ellerman observes that the Pacioli group is only the algebra in
which the double-entry method calculates, not the method itself,
and that the virtues of the double-sided presentation are human
rather than mathematical (2014, p. 488). This repository formalizes
the algebra and the laws that follow from it, and leaves the
presentation to the implementations it measures.

## What an implementation must preserve

A Ledger implementation reads plain-text journals and reports on
them, and the theory fixes what any such program must preserve. The
first obligation is balance, and it is weaker than conservation of
each commodity. For postings subject to balancing, the check tests
weights: a posting weighs its cost if it has one, including a
rounded lot gain where required, and otherwise its own amount. A
remaining imbalance can be settled by conversion at the rate that
C++ infers for a two-commodity implicit exchange, or by lot-price
valuation on a second pass. The weights must sum to zero in each
commodity within the recorded tolerances, or leave a remainder that
an elided posting, or, in a transaction of a single posting, the
default account named by a `bucket` directive, absorbs. The passes
and their departures from C++ are recorded in
`Ledger/Journal.lean`. Reported balances, by contrast, are sums of
the postings' own quantities. The oracle targets the check that C++
runs without `--permissive`: it rejects the conflicting balance
assignment of `test/regress/2005.test`, which C++ accepts under
`--permissive` by revising the assigned amount
(`src/xact.cc:932-953`).

The per-commodity totals of a report over all accounts, before
display rounding, therefore vanish when every transaction balances
in its own quantities, and in general they equal the sum of the
residuals that the individual transactions leave in their own
quantities. Such residuals arise from the conversions that cost and
lot-price balancing admit, the conversions that C++ infers for a
two-commodity implicit exchange, the amounts of paren-virtual
postings, which are exempt from balancing whether written or
appended by an automated transaction, timeclock entries, which are
added without a balance check, and remainders accepted within
tolerance. Residuals can cancel between transactions, so a zero
total does not show that no conversion took place.
`netFlow_trial_balance` in `Ledger/Oracle.lean` and
`netFlow_commodity_sum` in `Ledger/Register.lean` state the two
halves of this contract for the oracle's computed flows.

An unfiltered C++ `equity` report keeps nonvirtual and virtual
posting subtotals separate even within the same account. It computes
its `Equity:Opening Balances` offset as the negation of the sum of
the nonvirtual subtotals and the virtual subtotals marked for
balancing (`src/filters.cc:1673-1688` and
`src/filters.cc:1960-1961`). Nonvirtual timeclock postings contribute
despite their exemption from transaction balancing. The C++ suite
pins nonzero commodity totals and equity offsets:
`test/regress/1784.test` expects a total of 28 ABCDEF and -280.00 EUR
from a lot purchase followed by a split, and
`test/baseline/cmd-equity.test` expects `equity` to post -4 AAA and
3.80 GBP against totals of 4 AAA and -3.80 GBP. Ellerman's vector
journal records an exchange differently: it balances in each
property type because an equity account carries the reverse
composition (2014, p. 497), a leg that Ledger's cost syntax leaves
implicit.

In the compositional model, arithmetic is exact, with quantities
kept as rational numbers and rounding performed only at display,
after all composition, so that approximation is applied once and
never compounded. In the executable layer, display rounding and the
rounded test for a zero remainder follow C++ at an exact decimal
tie, through the binary expansion of `stream_out_mpq`
(`src/amount.cc:208-245`) rather than by a decimal rule. The order
of accounts within a transaction carries no meaning in the model,
and net balances are functions of the journal's denotation. Two
journals with the same denotation therefore have the same net
balances before display; their presentation still depends on the
precision and style learned from the journal.

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
failure visible. A rejection for transaction imbalance has a reason
beginning `line N: unbalanced transaction`, prefixed by
`periodic transaction: ` when the failing entry is a `~` template.
Here N is the entry's header line number in the include-spliced text.
That stem is part of the protocol, so that a comparator can check
rejections for imbalance as well as balances; other rejections name
their cause freely. Flags given before a file path apply to that file
alone, and six are recognized: `--decimal-comma`,
`--recursive-aliases`, `--now DATE`, `--input-date-format FORMAT`,
and the opt-in output flags `--gross` and `--exchange COMM`, described
below.

An output flag is opt-in. A file given without one prints exactly the
output described above, byte for byte, so that a comparator that does
not pass it needs no change. `--gross` adds, after the net rows,
sorted lines of the forms `>> dr COMMODITY|AMOUNT|ACCOUNT` and
`>> cr COMMODITY|AMOUNT|ACCOUNT`, which give as positive magnitudes
the gross debit and credit totals of each account. The totals are
summed posting by posting, as the columns of the C++ program's `--dc`
option are, and each is displayed as a net row is. Before display, an
account's debit total less its credit total is its net flow, which its
net row shows (`gross_foot` in `Ledger/Register.lean`). The totals are
worth comparing because an error in resolving the postings can leave
every net row unchanged, as a balance assignment read as a plain
amount does when a later assignment to the same account absorbs the
difference. Such an error is hidden from the net rows exactly when it
cancels in every account it touches, and the gross totals of those
accounts still move unless it also cancels within their debits and
within their credits, which is the blind spot of the gross comparison
itself. C++ can complete an elided posting with several postings of
one commodity that its lot annotations keep apart, where the oracle
completes it with a single posting of that commodity or with none,
and the columns that C++ shows for the completed account can then
depart from the oracle's gross lines in two ways. The postings of C++
can differ in sign, and both totals of the account then exceed the
oracle's. Where the oracle's single posting carries the precision of
a cost, which C++ can show for a lone posting but drops from the sum
of several in one column, a column that both sides total alike can
also show differently. A file in which the oracle finds such a
completion prints the single line `?? gross lot-annotated-completion`
in place of the gross lines. The test that decides this refuses some
files in excess and misses others, and the docstring of
`Journal.Result.lotFanout` in `Ledger/Journal.lean` records both
conditions and the known cases, each with a journal. Such a file is
not rejected: its net rows still print, and a `??` line never stands
in for `!! ERROR`.

`--exchange COMM` adds, after the net rows and any gross lines, sorted
lines of the form `>> value COMM|AMOUNT|ACCOUNT`, one for each account
whose holdings have a nonzero value in `COMM` at the prices in effect
at the report date, which is midnight at the start of the `--now`
date, as the C++ program's `-X` option values them. A commodity other
than `COMM` is priced through the only chain of recorded prices that
links it to `COMM`, at the product of the prices along the chain, and
each value is displayed in `COMM` as a net row is. The value of an
account is the sum of `netValueAt` in `Ledger/Oracle.lean` over the
account names that the report-time rewrites merge into it, and
`netValueAt_eq_valueHom` in `Ledger/Market.lean` proves `netValueAt`
equal to the value of an account name's property vector at the price
vector, Ellerman's valuation of property at prices (p. 498), over a
list of accounts without duplicates that holds every account with a
nonzero flow, as the driver's list does. Where the oracle cannot value
a file as the C++ program does, the single line `?? exchange REASON`
takes the place of the value lines, with the commodity concerned after
the reason where there is one. The reason is the first that applies of
`no-terminus`, `price-expr`, `unread-price`, `exchange-order`,
`value-expression`, `posting-date`, `fixated-lot`, `equivalence`,
`commodity-alias`, `price-precision`, `null-commodity`, `percent`,
`time-unit`, `no-price-path`, `alternative-price-path`,
`zero-inverse-price` and `rounds-to-zero`, and the comment beside each
branch of `exchangeRows` in `Ledger/Driver.lean` gives the rule of the
C++ program that forces it, or states that it marks a limitation of
the oracle. No reason covers the known departures that the value lines
inherit from the net totals, from the dated price table and from the
display precisions that the oracle learns, other than the precision
that a price directive grants, which `price-precision` refuses. The
comments beside the rules of the oracle record witnessed departures,
including shapes that the C++ program rejects and the oracle accepts,
as the provenance section explains. They are not an exhaustive account
of differences from C++. No reason covers four further
shapes either: a journal line that sets another report option or a
session option that takes effect only once the C++ program has read
the journal; a price read in a style other than the C++ program's; an
assignment in an expression that the C++ program evaluates as it reads
the journal; and such an expression that values a commodity at the
report date, which leaves in the C++ program's cache of prices a price
that a later price on its chain does not always clear. For these the
value lines can depart from the C++ program, and the docstring of
`exchangeRows` says where each is recorded. Such a file is not
rejected: its net rows still print, and a `??` line never stands in
for `!! ERROR`.

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
non-comparable bins, and the C++ suite has reached that goal. At C++
revision 76b9dc2b2, of its 4364 test files, 3796 are compared with
zero divergence, 489 expect errors, 77 contain no journal, and 2
embed Python in the journal itself.

The comparator is also proved able to fail. Every run replays a
fixture in which one side carries a known planted defect, and the
run fails unless the detector fires, because a comparator that has
never been observed to fail provides no evidence when it passes.

Finally, each result records what it compared, naming the source
revisions of both sides, the binary, and the flags, and it states
what the comparison does not cover. This oracle compares balances.
It can also print gross debit and credit totals and valuation in one
commodity for a comparator to check, but it does not compare register
report rows, unrealized gains, or lot matching, and a passing result
is meaningful only together with a plain statement of such limits.

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

The balance semantics agrees with every comparable file of the C++
suite at revision 76b9dc2b2. Known shapes that it accepts although C++
rejects them are recorded beside their rules in comments marked
`fail-open` or `fails open` in `Ledger/Journal.lean` and
`Ledger/Parse.lean`. These include the docstrings of `impliedExchange`
and `zeroTestPrec`, and the comments at the automated-transaction
check. The command `git grep -n -E 'fail-open|fails open' -- Ledger`
lists those comments together with other departures, including wrong
rows and refusals that miss a case. Agreement with this corpus is not
completeness for the journal language. Register rows, valuation at
fixed and at dated prices, lot refinement and basis gain are specified
in the theory and remain to be bisimulated by the same procedure;
lot matching is not specified.

## License

BSD three-clause, as `LICENSE.md` states. The copyright is held by
John Wiegley.
