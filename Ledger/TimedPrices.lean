import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Ledger.Derived

/-!
# Time-indexed prices, and a nontrivial price-action model

## 𝓟(t) (decision: fibers, no cross-time structure)

`TimedPrices` is a family of fibers: at each instant a price groupoid
and a sound action. There is deliberately no cross-time law. No
ordering on `Time` is needed here; choosing an observation at or
before a report date is a separate concern, not specified by this
structure.

## The constant-rate model (PriceAction is nontrivially inhabited)

`Trivial.lean` inhabits `PriceAction` with every rate 1. The model
here admits any nowhere-zero price function, with conversion rates
given by its ratios. Fix a base functional `W` and a price for each
commodity; measure commodity `c` by `(1 / price c) • W`; convert
`a → b` at rate `price a / price b`. The transaction is untouched
(`revalue := id`), and soundness is field arithmetic.
`PriceAction.constModel` therefore witnesses a price action with
rates other than 1. Valuation at fixed prices is compositional:
`ValuationFunctor.finsetSum` in `Ledger/Valuation.lean` and
`ValuationFunctor.smul` in `Ledger/Derived.lean` preserve the functor
laws, as does `GenSpec.priceValuation` in `Ledger/PriceVector.lean`.

This is not a specification of the `-V` and `-X` reports of C++
Ledger. In `timedConstRates`, one functional `W` serves every instant,
and `priceAt t b` times the `b`-measurement is always `W.V f`
(`timedConstRates_value_const`), whatever the prices are. With a
numeraire held at price 1, every morphism has the same measurement at
every instant (`timedConstRates_no_holding_gain` in
`Ledger/HoldingGain.lean`). Thus that model varies the unit of
measurement but cannot express a holding gain when the numeraire's
price is fixed. The model whose values can move is `timedPriceVector`
in `Ledger/HoldingGain.lean`: each fiber is `PriceAction.constModel`
over `GenSpec.priceValuation` at that instant's price vector, rather
than over one functional fixed for all instants.
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

/-- A conversion model at fixed prices: transactions are untouched;
    commodity `c` is measured by `(1 / price c) • W`. Sound for the
    constant-rate groupoid of any nowhere-zero price function, with
    rates given by its ratios. This witnesses that the `PriceAction`
    axioms admit rates other than 1, not that the model specifies C++
    market reports. Keeping `W` fixed across instants, as
    `timedConstRates` does, cannot express holding gains when the
    numeraire's price is fixed; see the module docstring. -/
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

/-- Time-varying rates with a sound action at each instant: each fiber
    is the constant-rate model at that instant's prices, with the same
    base functional `W` throughout. -/
noncomputable def timedConstRates (Time : Type) (T : 𝕋) (W : ValuationFunctor T)
    (priceAt : Time → Commodity → ℝ)
    (hne : ∀ t c, priceAt t c ≠ 0) : TimedPrices Time T where
  P t := PriceGroupoid.constRates (priceAt t) (hne t)
  CV t := fun c => (1 / priceAt t c) • W
  act t := PriceAction.constModel T W (priceAt t) (hne t)

/-- Value in a fixed numeraire does not move in the constant-rate
    model: at every instant, the price of `b` times the
    `b`-measurement of a transaction is its measurement under the base
    functional `W`, whatever the prices are. -/
theorem timedConstRates_value_const (Time : Type) (T : 𝕋)
    (W : ValuationFunctor T) (priceAt : Time → Commodity → ℝ)
    (hne : ∀ t c, priceAt t c ≠ 0) (t : Time) (b : Commodity)
    {A B : Object} (f : T.Hom A B) :
    priceAt t b * ((timedConstRates Time T W priceAt hne).CV t b).V f
      = W.V f := by
  have hb := hne t b
  show priceAt t b * ((1 / priceAt t b) * W.V f) = W.V f
  field_simp

end Ledger
