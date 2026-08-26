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
groupoid `𝕋` enriched over `CMon` (commutative monoids), strict over
the free commutative monoid of account multisets. "Free" means the
only equations are those forced by the structure; the fragment the
theorems consume — generatedness — is axiomatized as an induction
principle (`𝕋.Generated`). Auto-xacts, assertions, and periodic
transactions form a separate derivation system that operates *on* the
groupoid without constraining its equality.

## The two layers

The specification layer is a purely mathematical, propositional
development: the groupoid morphisms (`Hom`) are an abstract,
axiomatized family of types, and the theorems constrain every model
of them. The executable layer supplies the models and the oracle:
`Free` and `Pacioli` realize the representation tower, and `Parse`,
`Journal`, `Oracle`, `Register`, and `Driver` read journal text,
evaluate it, and print balances for bisimulation against other
implementations. The specification never imports the executable
layer; dependency flows one way.

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
