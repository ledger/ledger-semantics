import Ledger.Basic
import Ledger.Accounts
import Ledger.Groupoid
import Ledger.Valuation
import Ledger.Labels
import Ledger.Hierarchy
import Ledger.Derivation
import Ledger.Prices
import Ledger.TimedPrices
import Ledger.Theorems
import Ledger.Derived
import Ledger.Free
import Ledger.Pacioli
import Ledger.Oracle
import Ledger.Register
import Ledger.Parse
import Ledger.Journal
import Ledger.Driver
import Ledger.Trivial
import Ledger.TwoSides
import Ledger.DriverTwoSides
import Ledger.TAccount
import Ledger.Decoding
import Ledger.PriceVector
import Ledger.HoldingGain
import Ledger.Lots
import Ledger.Conversion
import Ledger.BasisGain
import Ledger.Closing
import Ledger.GrossLedger
import Ledger.Market

/-!
# Ledger: denotational semantics of double-entry accounting

## The mathematical object (K1)

The principal mathematical object is the **free** symmetric monoidal
groupoid `𝕋`, strict over the free commutative monoid of account
multisets. Each hom-set carries a commutative-monoid structure, the
aggregation of transactions of the same shape. Decision D16 in
`Ledger.Groupoid` makes that structure compatible with valuations
only: absorption of zero by composition and either distributive law
of composition over addition collapse every valuation to zero (see
`Ledger.Pacioli`). `𝕋` is therefore not enriched over commutative
monoids in the standard sense, although each of its hom-sets is a
commutative monoid.

"Free" means that the only equations are those forced by the
structure; the fragment the theorems consume, generatedness, is
axiomatized as an induction principle (`𝕋.Generated`).
Automated-transaction rules belong to the separate derivation system
in `Ledger.Derivation`; they operate *on* the groupoid without
constraining its equality.

## The two layers

The specification layer defines meaning and proves laws. It states
the groupoid abstractly, with `Hom` an axiomatized family of types
whose theorems constrain every model, and it also builds the models
that the representation tower requires: `Free` constructs the free
model as a quotient of formal morphisms, and `Pacioli` gives its
denotation into the signed carrier of rational quantities per
account and commodity. Both are checked mathematics, not executable
conventions. The executable layer (`Parse`, `Journal`, `Oracle`,
`Register`, `Driver`, and `Gen`) reads journal text, records the
observed conventions of the C++ implementation, computes balances,
and prints them for bisimulation against other implementations;
`Gen` supplies property-test journals, never expected results. The
specification never imports the executable layer; dependency flows
one way.

## Module index

Every module under `Ledger/` is built by the lakefile's glob. This
file imports all of them except `Ledger.Gen`, which defines its own
`main` and so cannot share an environment with `Ledger.Driver`.

Specification layer:

- `Ledger.Basic`: account names, commodities, the `Account` pair
- `Ledger.Accounts`: `Object := Multiset Account`, the free
  commutative monoid
- `Ledger.Groupoid`: `𝕋`, `𝕋Laws`, `castHom` and `braiding`, `Path`,
  `Generated`
- `Ledger.Valuation`: `ValuationFunctor` (the three-law basis and
  the laws derived from it), static `Valuation`, `CommodityValuation`
- `Ledger.Labels`: metadata fibration, separate from the groupoid
- `Ledger.Hierarchy`: account forest, `ParentChain`, roll-ups
- `Ledger.Derivation`: automated-transaction derivation system and
  its soundness
- `Ledger.Prices`: price groupoid `𝓟`, its action, rate theorems
- `Ledger.Theorems`: the fundamental theorems (K3), all proved
- `Ledger.Derived`: derived operations and their laws
- `Ledger.Trivial`: the one-point model, which inhabits the structures
  of the core specification (consistency, not adequacy)
- `Ledger.TimedPrices`: time-indexed price observations
- `Ledger.Free`: L2, the free construction (reified morphisms)
- `Ledger.Pacioli`: L1, the signed carrier `PacioliGroup`, the
  denotation `flow` and its commuting squares, the degeneracy results

Executable layer:

- `Ledger.Parse`: amounts, numbers, regular expressions
- `Ledger.Journal`: the journal engine, witnessed C++ conventions
  and recorded departures
- `Ledger.Oracle`: the executable balance oracle `netFlow`, its
  agreement with `flow`, the per-commodity trial balance, `netValue`,
  and the kernel-checked Demo and Ellerman goldens
- `Ledger.Register`: register-report specification, gross debit and
  credit totals, and posting rows
- `Ledger.Gen`: seeded generator of property-test journals, never
  expected results
- `Ledger.Driver`: the bisimulation driver (IO, output protocol)

## Specification leaves

These modules extend the specification. This index imports them. No
executable module (`Parse`, `Journal`, `Gen`, `Oracle`, `Register`,
and `Driver`) imports any of them. They may import one another, as
the tables in AGENTS.md record. The oracle's run path is the import
closure of `Driver`.

- `Ledger.TwoSides`   : generator endpoints read as Ellerman's two
                        sides, sign coherence, and where composition
                        breaks it
- `Ledger.TAccount`   : Ellerman's T-accounts, the group of differences,
                        and the debit and credit isomorphisms onto
                        `PacioliGroup`
- `Ledger.Decoding`   : balance sides, the decoded balance-sheet
                        equation, five account classes
- `Ledger.PriceVector`: price-vector valuation, and the value and
                        quantity readings of `CommodityValuation`
- `Ledger.HoldingGain`: timed price vectors and the holding-gain
                        identity
- `Ledger.Lots`       : lots as property types, market vectors, and what
                        lot-blind flows support
- `Ledger.Conversion` : conversion legs and the completion projection
- `Ledger.BasisGain`  : basis gain and the forced equity leg
- `Ledger.Closing`    : the closing entry and an inhabitant of
                        `ClosesBooks` with nonzero revenue

## Join modules

Each joins the executable layer to a specification leaf. They contain
only definitions and theorems used for proofs, this index is the only
module that imports them, and none is on the oracle's run path.

- `Ledger.DriverTwoSides`: the oracle's generators are coherent with
                           their ends (`Driver`, `TwoSides`)
- `Ledger.GrossLedger`   : gross totals as T-accounts (`Register`,
                           `TAccount`)
- `Ledger.Market`        : the executable valuation agrees with the
                           price vector (`Oracle`, `PriceVector`)
-/
