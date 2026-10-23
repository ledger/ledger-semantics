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

- `Ledger.Basic`      — account names, commodities, the `Account` pair
- `Ledger.Accounts`   — `Object := Multiset Account`, the free CMon
- `Ledger.Groupoid`   — `𝕋`, `𝕋Laws`, `castHom`/`braiding`, `Path`,
                        `Generated`
- `Ledger.Valuation`  — `ValuationFunctor` (minimal law basis and the
                        derived laws), static `Valuation`,
                        `CommodityValuation`
- `Ledger.Labels`     — metadata fibration, separate from the groupoid
- `Ledger.Hierarchy`  — account forest, `ParentChain`, roll-ups
- `Ledger.Derivation` — auto-xact derivation system and its soundness
- `Ledger.Prices`     — price groupoid `𝓟`, its action, rate theorems
- `Ledger.Theorems`   — the fundamental theorems (K3), all proved
- `Ledger.Trivial`    — the one-point model: every structure is
                        inhabited (consistency, not adequacy)
- `Ledger.TimedPrices`— time-indexed price observations
- `Ledger.Free`       — L2: the free construction (reified morphisms)
- `Ledger.Pacioli`    — L1: per-account rational flows, `netFlow`,
                        the degeneracy results
- `Ledger.Derived`    — derived operations and their laws
- `Ledger.Parse`      — amounts, numbers, regular expressions
- `Ledger.Journal`    — the journal engine (C++-faithful conventions)
- `Ledger.Oracle`     — the executable balance oracle
- `Ledger.Register`   — register-report specification
- `Ledger.Gen`        — seeded journal generator for property sweeps
- `Ledger.Driver`     — the bisimulation driver (IO, output protocol)
-/
