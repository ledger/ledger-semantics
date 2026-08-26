import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Ledger.Groupoid

/-!
# Valuation functors and the balancing condition

A valuation functor `W : 𝕋 → (ℝ, +, 0)` assigns to every morphism
(transaction) a net flow, additively in every dimension the groupoid
composes in. That every transaction balances is the statement that the
per-account valuations sum to a functor that annihilates the
generators — see `Theorems.lean`.

## Extraction (decision D12)

Phase 1 baked a single `V_obj`/`V_hom` pair into the `𝕋` structure.
That made multi-commodity impossible: the old `CommodityValuation`
carried `respects_V_hom : V_hom_c f = T.V_hom f`, forcing every
commodity's valuation to equal the global one — an uninhabitable
specification for any journal with two commodities. The repair is to
make valuation a *separate structure over* `𝕋`, of which there are
many: one per commodity, one per budget scenario, one per account
(the per-account family is what reports consume).

`V_obj` is deleted: the object part of a valuation is derived from a
static account assignment (`Valuation.ofObject` below), and no law
connected `V_obj` to `V_hom` — nor should one: hom-valuations measure
*flow*, account assignments measure *state at rest*.

## The minimal law basis (solved, not verified)

Only three laws are structure: `V_comp`, `V_tensor`, `V_add`. The
remaining Phase 1 laws are **derived**:

- `V_id`   — from `V_comp` at `id ∘ id = id`;
- `V_zero` — from `V_add` at `0 + 0 = 0`;
- `V_inv`  — from `V_comp` and `V_id` at `f ∘ f⁻¹ = id`.

This is the method's "laws already paid for": the smaller the law
table, the smaller the obligation every representation must discharge.
-/

namespace Ledger

/-- A valuation functor on `T`: an additive measurement of morphisms.
    The functor laws are the mathematical content of double-entry
    bookkeeping (worksheet T13, T14, T16). -/
structure ValuationFunctor (T : 𝕋) where
  /-- The net flow measured for each morphism. -/
  V : ∀ {A B : Object}, T.Hom A B → ℝ
  /-- T13 — the flow of a chain is the sum of the flows. -/
  V_comp : ∀ {A B C : Object} (g : T.Hom B C) (f : T.Hom A B),
    V (T.comp g f) = V g + V f
  /-- T14 — parallel flows sum. -/
  V_tensor : ∀ {A B C D : Object} (f : T.Hom A B) (g : T.Hom C D),
    V (T.tensor f g) = V f + V g
  /-- T16 — aggregation of flows sums. -/
  V_add : ∀ {A B : Object} (f g : T.Hom A B), V (f + g) = V f + V g

namespace ValuationFunctor

variable {T : 𝕋} (W : ValuationFunctor T)

/-- T12 (derived) — the identity transaction is balanced. -/
theorem V_id (L : 𝕋Laws T) (A : Object) : W.V (T.id A) = 0 := by
  have h : W.V (T.id A) = W.V (T.id A) + W.V (T.id A) := by
    conv_lhs => rw [← L.id_comp (T.id A)]
    exact W.V_comp (T.id A) (T.id A)
  have h2 : W.V (T.id A) + 0 = W.V (T.id A) + W.V (T.id A) := by
    rw [add_zero]; exact h
  exact (add_left_cancel h2).symm

/-- Derived — the zero transaction is balanced. -/
theorem V_zero (A B : Object) : W.V (0 : T.Hom A B) = 0 := by
  have h : W.V (0 : T.Hom A B) = W.V (0 : T.Hom A B) + W.V (0 : T.Hom A B) := by
    conv_lhs => rw [← add_zero (0 : T.Hom A B)]
    exact W.V_add 0 0
  have h2 : W.V (0 : T.Hom A B) + 0
      = W.V (0 : T.Hom A B) + W.V (0 : T.Hom A B) := by
    rw [add_zero]; exact h
  exact (add_left_cancel h2).symm

/-- T15 (derived) — reversal negates the flow. -/
theorem V_inv (L : 𝕋Laws T) {A B : Object} (f : T.Hom A B) :
    W.V (T.inv f) = -W.V f := by
  have h : W.V f + W.V (T.inv f) = 0 := by
    rw [← W.V_comp f (T.inv f), L.comp_inv, W.V_id L]
  exact eq_neg_of_add_eq_zero_right h

/-- Transport does not change the measured flow. -/
theorem V_castHom {A A' B B' : Object} (hA : A = A') (hB : B = B')
    (f : T.Hom A B) : W.V (T.castHom hA hB f) = W.V f := by
  subst hA; subst hB; rfl

/-- The braiding is balanced: permuting accounts moves nothing. -/
theorem V_braiding (L : 𝕋Laws T) (A B : Object) :
    W.V (T.braiding A B) = 0 := by
  unfold 𝕋.braiding
  rw [W.V_castHom, W.V_id L]

/-- Pointwise sum of valuation functors (e.g. summing per-account
    measurements into a trial balance). -/
def add (W₁ W₂ : ValuationFunctor T) : ValuationFunctor T where
  V f := W₁.V f + W₂.V f
  V_comp g f := by rw [W₁.V_comp, W₂.V_comp, add_add_add_comm]
  V_tensor f g := by rw [W₁.V_tensor, W₂.V_tensor, add_add_add_comm]
  V_add f g := by rw [W₁.V_add, W₂.V_add, add_add_add_comm]

instance : Add (ValuationFunctor T) := ⟨add⟩

@[simp] theorem add_V (W₁ W₂ : ValuationFunctor T) {A B : Object}
    (f : T.Hom A B) : (W₁ + W₂).V f = W₁.V f + W₂.V f := rfl

/-- Sum of a finite family of valuation functors — the vehicle for
    "sum over all accounts" statements (trial balance, Pacioli). -/
def finsetSum {ι : Type*} (s : Finset ι) (Ws : ι → ValuationFunctor T) :
    ValuationFunctor T where
  V f := ∑ i ∈ s, (Ws i).V f
  V_comp g f := by
    have h : ∀ i : ι, (Ws i).V (T.comp g f) = (Ws i).V g + (Ws i).V f :=
      fun i => (Ws i).V_comp g f
    simp only [h, Finset.sum_add_distrib]
  V_tensor f g := by
    have h : ∀ i : ι, (Ws i).V (T.tensor f g) = (Ws i).V f + (Ws i).V g :=
      fun i => (Ws i).V_tensor f g
    simp only [h, Finset.sum_add_distrib]
  V_add f g := by
    have h : ∀ i : ι, (Ws i).V (f + g) = (Ws i).V f + (Ws i).V g :=
      fun i => (Ws i).V_add f g
    simp only [h, Finset.sum_add_distrib]

@[simp] theorem finsetSum_V {ι : Type*} (s : Finset ι)
    (Ws : ι → ValuationFunctor T) {A B : Object} (f : T.Hom A B) :
    (finsetSum s Ws).V f = ∑ i ∈ s, (Ws i).V f := rfl

end ValuationFunctor

/-- A static valuation: each account×commodity pair is assigned a
    quantity at rest. This is the *object-level* companion of a
    valuation functor (opening balances, price tables). The pointwise
    `AddCommMonoid` structure on `Account → ℝ` is Mathlib's Pi
    instance — nothing bespoke. -/
abbrev Valuation : Type := Account → ℝ

namespace Valuation

/-- Extend a static valuation from atomic accounts to objects — the
    unique commutative-monoid homomorphism from the free CMon. -/
def ofObject (v : Valuation) (obj : Object) : ℝ :=
  (obj.map v).sum

/-- The empty object has zero value. -/
@[simp] theorem ofObject_zero (v : Valuation) : ofObject v 0 = 0 := by
  simp [ofObject]

/-- Tensor (multiset sum) is additive under valuation: the object part
    of the monoidal functor condition. -/
@[simp] theorem ofObject_add (v : Valuation) (A B : Object) :
    ofObject v (A + B) = ofObject v A + ofObject v B := by
  simp [ofObject]

end Valuation

/-- Multi-commodity valuation: one valuation functor per commodity.
    `CV c` measures net flow denominated in commodity `c`. The price
    groupoid (`Prices.lean`) relates the members of the family. -/
abbrev CommodityValuation (T : 𝕋) : Type := Commodity → ValuationFunctor T

end Ledger
