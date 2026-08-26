import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Ledger.Derived

/-!
# Time-indexed prices, and a nontrivial price-action model

## 𝓟(t) (decision: fibers, no cross-time structure)

The handoff's design note: in the full theory 𝓟 is indexed by time
(`P` directives are dated; `find_price` looks up the latest
observation ≤ t). Model: a **family of fibers** — at each instant a
price groupoid and a sound action. Deliberately *no* cross-time law:
rates float freely between instants (a constraint would be headroom
lost; the domain has none — yesterday's rate does not bound today's).
Cross-time structure enters only with the observation-list
*representation* (latest-≤-t lookup), which arrives with `P`-directive
parsing (ledger-oyb follow-on) — ordering on `Time` is needed there,
not here.

## The constant-rate model (PriceAction is nontrivially inhabited)

`Trivial.lean` inhabits `PriceAction` with every rate 1. The model
here has **arbitrary nonzero rates** and captures exactly what `-V`
reports do: revaluation happens at *reporting* time — the transaction
is untouched (`revalue := id`) and the *measurement* changes. Fix a
base functional `W` and a price for each commodity; measure commodity
`c` by `(1 / price c) • W`; convert `a → b` at rate
`price a / price b`. Soundness is field arithmetic. A journal-side
revaluation (rewriting `@`-cost generators) is a different, later
model — it needs generators closed under rescaling and lands with
cost-syntax parsing.

Composing the two: `timedConstRates` — per-instant price functions
give per-fiber constant-rate actions, i.e. time-varying rates with
sound reporting at every instant.
-/

namespace Ledger

/-- Time-indexed prices: at each instant, a price groupoid and a
    sound action on 𝕋. No cross-time law, by design. -/
structure TimedPrices (Time : Type) (T : 𝕋) where
  P : Time → PriceGroupoid
  CV : Time → CommodityValuation T
  act : ∀ t : Time, PriceAction (P t) T (CV t)

namespace PriceGroupoid

/-- The constant-rate price groupoid over a nowhere-zero price
    function: one conversion per commodity pair, at rate
    `price a / price b`. -/
noncomputable def constRates (price : Commodity → ℝ)
    (hne : ∀ c, price c ≠ 0) : PriceGroupoid where
  Conversion _ _ := PUnit
  rate {a b} _ := price a / price b
  id_conv _ := .unit
  comp_conv _ _ := .unit
  inv_conv _ := .unit
  comp_assoc _ _ _ := rfl
  id_comp _ := rfl
  comp_id _ := rfl
  inv_comp _ := rfl
  comp_inv _ := rfl
  rate_id c := div_self (hne c)
  rate_comp {a b c} _ _ := by
    have hb := hne b
    field_simp
    try ring

end PriceGroupoid

namespace PriceAction

/-- The reporting-time revaluation model: transactions are untouched;
    commodity `c` is measured by `(1 / price c) • W`. Sound for the
    constant-rate groupoid — and the rates are arbitrary nonzero
    reals, so the `PriceAction` axioms have a nontrivial model
    (the inhabitation witness ledger-oyb asked for). -/
noncomputable def constModel (T : 𝕋) (W : ValuationFunctor T)
    (price : Commodity → ℝ) (hne : ∀ c, price c ≠ 0) :
    PriceAction (PriceGroupoid.constRates price hne) T
      (fun c => (1 / price c) • W) where
  revalue := fun {_a _b} _p {_A _B} f => f
  revalue_id _ := rfl
  revalue_comp := fun {_a _b _c} _q _p {_A _B} _f => rfl
  revalue_sound := fun {a b} _p {_A _B} f => by
    have ha := hne a
    have hb := hne b
    show (1 / price b) * W.V f
        = (price a / price b) * ((1 / price a) * W.V f)
    field_simp

end PriceAction

/-- Time-varying rates with sound per-instant reporting: each fiber
    is the constant-rate model at that instant's prices. -/
noncomputable def timedConstRates (Time : Type) (T : 𝕋) (W : ValuationFunctor T)
    (priceAt : Time → Commodity → ℝ)
    (hne : ∀ t c, priceAt t c ≠ 0) : TimedPrices Time T where
  P t := PriceGroupoid.constRates (priceAt t) (hne t)
  CV t := fun c => (1 / priceAt t c) • W
  act t := PriceAction.constModel T W (priceAt t) (hne t)

end Ledger
