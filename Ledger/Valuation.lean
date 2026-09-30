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

`V_obj` is deleted. The object part of a valuation is derived from a
static account assignment (`Valuation.ofObject` below), and no law
connects it to the measure of morphisms, nor should one:
hom-valuations measure *flow*, account assignments measure *state at
rest*. The endpoint theorems below make this precise. A valuation
that equals the change of an object measure across every morphism
vanishes (`ValuationFunctor.endpoint_measure_degenerates`); an object
measure equal at the two ends of every morphism is constant
(`conserved_measure_const`); a static valuation whose extension to
objects is equal at the two ends of every morphism is zero
(`Valuation.ofObject_ends_equal_degenerates`). Each follows because
the zero morphism `0 : Hom A B` exists for every pair of objects.
These refute only the object-measure readings of a morphism's two
ends. The free model has a nonzero valuation, which shows that the
difference-form refutation is not vacuous
(`GenSpec.endpoint_law_refuted` in `Pacioli.lean`).

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

/-- An object measure whose difference across every morphism is the
    valuation is constant: compare the ends of `0 : T.Hom A B`. -/
theorem endpoint_measure_const (φ : Object → ℝ)
    (hφ : ∀ {A B : Object} (f : T.Hom A B), W.V f = φ B - φ A)
    (A B : Object) : φ A = φ B := by
  have h := hφ (0 : T.Hom A B)
  rw [W.V_zero] at h
  exact (sub_eq_zero.mp h.symm).symm

/-- **Only the zero valuation is a difference of endpoint measures**:
    if `W.V f = φ B - φ A` for every `f : T.Hom A B`, then `W`
    vanishes identically. No `𝕋Laws` are needed. -/
theorem endpoint_measure_degenerates (φ : Object → ℝ)
    (hφ : ∀ {A B : Object} (f : T.Hom A B), W.V f = φ B - φ A)
    {A B : Object} (f : T.Hom A B) : W.V f = 0 := by
  rw [hφ f, W.endpoint_measure_const φ hφ A B, sub_self]

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

/-- An object measure equal at the two ends of every morphism of `T`
    is constant: the conservation reading of "equal measure on its
    two ends" holds of no measure that distinguishes objects. -/
theorem conserved_measure_const {T : 𝕋} (φ : Object → ℝ)
    (hφ : ∀ {A B : Object} (_ : T.Hom A B), φ A = φ B)
    (A B : Object) : φ A = φ B :=
  hφ (0 : T.Hom A B)

/-- An object measure that is zero on the empty object and equal at
    the two ends of every morphism is identically zero. -/
theorem conserved_measure_zero {T : 𝕋} (φ : Object → ℝ) (h0 : φ 0 = 0)
    (hφ : ∀ {A B : Object} (_ : T.Hom A B), φ A = φ B)
    (A : Object) : φ A = 0 := by
  rw [conserved_measure_const φ hφ A 0, h0]

/-- A static valuation: a quantity at rest for each account, given as
    a real number, where an account is a name paired with a commodity.
    It is the *object-level* companion of a valuation functor,
    measuring state rather than flow, and it represents neither
    opening balances nor price tables. Opening balances are excluded
    for two reasons. First, in Ellerman's treatment the T-accounts of
    a beginning ledger add up to the zero-account, as those of each
    transaction do (p. 489), so a beginning ledger can be recorded as
    one entry posted to the empty ledger rather than as a state; the
    oracle has no construct for opening balances and records an
    opening entry as a generator like any other. Second, an
    unconstrained function on accounts is not confined to ledgers
    that add up to the zero-account, since nothing requires its values
    to sum to zero within each commodity, whereas the signed form of
    Ellerman's beginning ledger does so within each property type (a
    zero-row, p. 492, and a zero-row of vectors, p. 498). The second
    reason rests on Ellerman's model and does not carry over to C++
    Ledger, which accepts opening entries that do not sum to zero
    within each commodity, since a posting with a lot price or a cost
    is balanced at that price or cost rather than at its own amount
    (the balancing convention recorded in the `Ledger/Journal.lean`
    module docstring); for C++ journals the first reason stands
    alone. Prices are rates between commodities, carried by
    `PriceGroupoid` in `Prices.lean` and, when dated, by
    `TimedPrices` in `TimedPrices.lean`, not quantities held by
    accounts. The pointwise additive structure on `Account → ℝ` is
    Mathlib's Pi instance. -/
abbrev Valuation : Type := Account → ℝ

namespace Valuation

/-- Extend a static valuation from accounts to objects by summing
    over the multiset. As a map `Object →+ ℝ` this is `ofObjectHom`
    (`ofObjectHom_apply`), the unique additive map that agrees with
    `v` on singletons (`ofObjectHom_unique`). -/
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

/-- A one-account object has the value of its account. -/
@[simp] theorem ofObject_singleton (v : Valuation) (a : Account) :
    ofObject v {a} = v a := by
  simp [ofObject]

/-- `ofObject` as an additive map on the free commutative monoid of
    accounts. -/
def ofObjectHom (v : Valuation) : Object →+ ℝ :=
  Multiset.sumAddMonoidHom.comp (Multiset.mapAddMonoidHom v)

/-- The additive map computes `ofObject`, by definition. -/
@[simp] theorem ofObjectHom_apply (v : Valuation) (obj : Object) :
    ofObjectHom v obj = ofObject v obj := rfl

/-- The extension is unique: an additive map on objects that agrees
    with `v` on every singleton is `ofObjectHom v`. -/
theorem ofObjectHom_unique (v : Valuation) (F : Object →+ ℝ)
    (h : ∀ a, F {a} = v a) : F = ofObjectHom v :=
  Multiset.addHom_ext fun a => by simp [h]

/-- **Equal-ends form.** If every morphism of `T` has the same static
    value at both ends, the static valuation is zero on every account:
    compare `{a}` with the empty object along `0`. -/
theorem ofObject_ends_equal_degenerates {T : 𝕋} (v : Valuation)
    (hv : ∀ {A B : Object} (_ : T.Hom A B), ofObject v A = ofObject v B) :
    v = 0 := by
  funext a
  have h := hv (0 : T.Hom 0 {a})
  simpa using h.symm

/-- **Difference form, at a static valuation.** If some valuation
    functor measures every morphism as the change of a static
    valuation between its ends, the static valuation is zero on every
    account, and by `ValuationFunctor.endpoint_measure_degenerates` so
    is the functor. -/
theorem ofObject_endpoint_degenerates {T : 𝕋} (W : ValuationFunctor T)
    (v : Valuation)
    (hv : ∀ {A B : Object} (f : T.Hom A B),
      W.V f = ofObject v B - ofObject v A) :
    v = 0 :=
  ofObject_ends_equal_degenerates (T := T) v
    (fun {A B} _ => W.endpoint_measure_const (ofObject v) hv A B)

end Valuation

/-- Multi-commodity valuation: one valuation functor per commodity.

    The type admits two readings, and the specification uses both.
    Under the quantity reading, `CV c` measures the net quantity of
    commodity `c` that a morphism moves, summed over accounts
    (`GenSpec.quantityValuation` in `Ledger/PriceVector.lean`); it
    vanishes identically on a journal whose entries balance per
    commodity. Under the value reading, `CV c` measures value expressed
    in the numeraire `c` at a fixed, nowhere-zero price vector `p`, the
    family `fun c => (1 / (p c : ℝ)) • GenSpec.priceValuation flows p`
    over which `PriceAction.constModel` is sound. The price groupoid
    (`Prices.lean`) relates the members of a family under the value
    reading. On a journal that moves only commodity `c`, the readings
    agree at the member `c` (`GenSpec.valueIn_eq_quantity_of_single`);
    they differ in general. -/
abbrev CommodityValuation (T : 𝕋) : Type := Commodity → ValuationFunctor T

end Ledger
