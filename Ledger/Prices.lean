import Ledger.Valuation

/-!
# Commodity price groupoid (P4 — separate groupoid with action)

Prices form a groupoid `𝓟` over commodities:

- **Objects**: commodities (the global `Commodity` type).
- **Morphisms**: price conversions — exchange rates.
- **Composition**: chaining through the price graph (Ledger's
  `find_price` shortest-path lookup, `src/commodity.cc:171-211`).
- **Inverses**: reciprocal rates.

Prices are NOT transactions: they have no debits and credits — they
are scalar multipliers between measurement units. Hence a separate
groupoid acting on 𝕋 rather than more structure inside 𝕋 (D8).

## Phase 2 repairs (decision D15)

Three defects of the Phase 1 module, all masked by the vacuous build:

1. `comp_comm` did not typecheck (its compositions' endpoints did not
   line up) and asserted nothing coherent. Deleted. Commutativity of
   *rates* is inherited from multiplication in ℝ; there is no
   morphism-level commutativity to state, because composition
   endpoints differ.
2. `rate_inv` was a field with an apologetic side condition ("when
   rate p ≠ 0"). Both facts are **theorems**: `rate_ne_zero` and
   `rate_inv` below follow from `rate_comp`, `rate_id`, and the
   groupoid laws. Solve, don't stipulate.
3. `PriceAction.revalue_preserves_valuation` quantified over
   *arbitrary* functions `V_c V_d`, making the structure uninhabited
   (instantiate `V_c := 0` and any nonzero `V_d`). The law now ties
   the action to one commodity-indexed family of valuation functors
   (`CommodityValuation`), which is what `-V`/`-X` reports actually
   consume.

## Time

The full theory indexes `𝓟` by time (`P` directives are dated). The
present groupoid is time-independent; time-dependence arrives with
derived operations (Phase 4), as a functor from the time poset.
-/

namespace Ledger

/-- A groupoid of price conversions over the global `Commodity` type.
    `Conversion a b` is abstract — no computational representation.
    `rate p` reads off the numerical exchange rate: "1 a = rate p b". -/
structure PriceGroupoid where
  /-- A price conversion from `a` to `b`. -/
  Conversion : Commodity → Commodity → Type
  /-- The numerical exchange rate carried by a conversion. -/
  rate : ∀ {a b : Commodity}, Conversion a b → ℝ
  /-- The identity conversion (no exchange). -/
  id_conv : (c : Commodity) → Conversion c c
  /-- Chain two conversions. -/
  comp_conv : ∀ {a b c : Commodity},
    Conversion b c → Conversion a b → Conversion a c
  /-- Reciprocal conversion. -/
  inv_conv : ∀ {a b : Commodity}, Conversion a b → Conversion b a
  /-- Groupoid laws. -/
  comp_assoc : ∀ {a b c d : Commodity}
    (h : Conversion c d) (g : Conversion b c) (f : Conversion a b),
    comp_conv h (comp_conv g f) = comp_conv (comp_conv h g) f
  id_comp : ∀ {a b : Commodity} (f : Conversion a b),
    comp_conv (id_conv b) f = f
  comp_id : ∀ {a b : Commodity} (f : Conversion a b),
    comp_conv f (id_conv a) = f
  inv_comp : ∀ {a b : Commodity} (p : Conversion a b),
    comp_conv (inv_conv p) p = id_conv a
  comp_inv : ∀ {a b : Commodity} (p : Conversion a b),
    comp_conv p (inv_conv p) = id_conv b
  /-- The rate of the identity is 1. -/
  rate_id : ∀ c : Commodity, rate (id_conv c) = 1
  /-- Rates are multiplicative along composition. -/
  rate_comp : ∀ {a b c : Commodity}
    (g : Conversion b c) (f : Conversion a b),
    rate (comp_conv g f) = rate g * rate f

namespace PriceGroupoid

variable (P : PriceGroupoid)

/-- No conversion has rate zero — derived, not stipulated: a zero rate
    would make `rate p⁻¹ · rate p = rate (id) = 1` impossible. -/
theorem rate_ne_zero {a b : Commodity} (p : P.Conversion a b) :
    P.rate p ≠ 0 := by
  intro h0
  have h : P.rate (P.comp_conv (P.inv_conv p) p) = P.rate (P.id_conv a) := by
    rw [P.inv_comp]
  rw [P.rate_comp, P.rate_id, h0, mul_zero] at h
  exact zero_ne_one h

/-- The reciprocal conversion carries the reciprocal rate — derived
    from `rate_comp` and `rate_id`, replacing the Phase 1 field. -/
theorem rate_inv {a b : Commodity} (p : P.Conversion a b) :
    P.rate (P.inv_conv p) = 1 / P.rate p := by
  have h : P.rate (P.inv_conv p) * P.rate p = 1 := by
    rw [← P.rate_comp, P.inv_comp, P.rate_id]
  exact (eq_div_iff (P.rate_ne_zero p)).mpr h

end PriceGroupoid

/-- The action of the price groupoid on the transaction groupoid,
    sound for a commodity-indexed family of valuations `CV`:
    revaluing by `p : a → b` rescales the `b`-denominated measurement
    by `rate p` from the `a`-denominated one.

    This is a specification, not a computation; it is what makes
    `-V`/`-X` reports correct. -/
structure PriceAction (P : PriceGroupoid) (T : 𝕋)
    (CV : CommodityValuation T) where
  /-- Revalue a morphism's postings from commodity `a` to `b`. The
      revalued morphism has the same accounts and directions, hence
      the same endpoints. -/
  revalue : ∀ {a b : Commodity} (_ : P.Conversion a b)
    {A B : Object} (_ : T.Hom A B), T.Hom A B
  /-- The identity conversion revalues nothing. -/
  revalue_id : ∀ (c : Commodity) {A : Object},
    revalue (P.id_conv c) (T.id A) = T.id A
  /-- Revaluation is compatible with composition of conversions. -/
  revalue_comp : ∀ {a b c : Commodity}
    (q : P.Conversion b c) (p : P.Conversion a b)
    {A B : Object} (f : T.Hom A B),
    revalue q (revalue p f) = revalue (P.comp_conv q p) f
  /-- **Soundness** (worksheet P1): the `b`-valuation of the revalued
      transaction is the rate times the `a`-valuation. -/
  revalue_sound : ∀ {a b : Commodity} (p : P.Conversion a b)
    {A B : Object} (f : T.Hom A B),
    (CV b).V (revalue p f) = P.rate p * (CV a).V f

namespace PriceAction

variable {P : PriceGroupoid} {T : 𝕋} {CV : CommodityValuation T}
variable (act : PriceAction P T CV)

/-- Chained conversions rescale by the product of the rates —
    the composite of `revalue_sound` with `rate_comp`. -/
theorem revalue_sound_comp {a b c : Commodity}
    (q : P.Conversion b c) (p : P.Conversion a b)
    {A B : Object} (f : T.Hom A B) :
    (CV c).V (act.revalue q (act.revalue p f))
      = P.rate q * P.rate p * (CV a).V f := by
  rw [act.revalue_comp, act.revalue_sound, P.rate_comp]

/-- Round-tripping a revaluation restores the measurement exactly
    (in ℝ — the L3 representation will weaken this to bounded error
    at the floating-point seam). -/
theorem revalue_roundtrip {a b : Commodity} (p : P.Conversion a b)
    {A B : Object} (f : T.Hom A B) :
    (CV a).V (act.revalue (P.inv_conv p) (act.revalue p f))
      = (CV a).V f := by
    rw [act.revalue_comp, act.revalue_sound, P.inv_comp, P.rate_id, one_mul]

end PriceAction

end Ledger
