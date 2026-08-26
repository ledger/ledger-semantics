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

## What this version is NOT

A **purely mathematical, propositional development**. The groupoid
morphisms (`Hom`) are an abstract, axiomatized family of types. No
computational representation is provided, and none should be inferred.
The development exists to specify correctness, not to run. The
computational oracle for C++ bisimulation is a later phase (Phase 5+).

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
-/
