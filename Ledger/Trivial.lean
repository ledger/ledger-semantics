import Mathlib.Algebra.Group.PUnit
import Ledger.Labels
import Ledger.Theorems

/-!
# The one-point model: the core specification is inhabited

Phase 1 shipped two uninhabitable specifications, `LabeledGroupoid`
(its `label_inv` law contradicted `inv_inv`) and `PriceAction` (its
soundness law quantified over arbitrary valuation pairs), and the
vacuous build hid both. A specification no model can satisfy specifies
nothing; its theorems are true for free and mean nothing.

This module is a guard against that defect class. The **one-point
model**, where every hom-set is `PUnit`, the valuation is `0`, and
every rate is `1`, inhabits the following structures of the core
specification: the transaction groupoid and its laws, generation,
valuation functors, the labels fibration, the price groupoid and its
action, and the account forest with its roll-up. Some structures
introduced by later modules have inhabitants of their own;
`ClosesBooks` (`Ledger/Derived.lean`), for example, is inhabited with
nonzero revenue by `ClosingDemo.demo_closesBooks` in
`Ledger/Closing.lean`. For the listed structures, these inhabitants
establish satisfiability only. Adequacy, a model faithful to actual
journals, is the work of the free construction at L2.

Nothing here is kernel: these definitions are evidence about the
kernel, not part of it.
-/

namespace Ledger

namespace Trivial

/-- The one-point transaction groupoid: a single morphism everywhere.
    Every equation below holds by `rfl` — `PUnit` has definitional
    eta, so any two of its inhabitants are definitionally equal. -/
def model : 𝕋 where
  Hom _ _ := PUnit
  homAddCommMonoid _ _ := inferInstance
  id _ := .unit
  comp _ _ := .unit
  inv _ := .unit
  tensor _ _ := .unit

/-- All laws hold in the one-point model. -/
def modelLaws : 𝕋Laws model where
  comp_assoc _ _ _ := rfl
  id_comp _ := rfl
  comp_id _ := rfl
  inv_comp _ := rfl
  comp_inv _ := rfl
  tensor_id _ _ := rfl
  tensor_comp _ _ _ _ := rfl
  tensor_assoc _ _ _ := HEq.rfl
  tensor_comm _ _ := HEq.rfl
  tensor_unit _ := HEq.rfl

/-- The one-point model is generated — by everything. -/
def generated : 𝕋.Generated model where
  IsGen _ := True
  induction := fun _P hgen _hid _hzero _hcomp _hinv _htensor _hadd {_A _B} f =>
    hgen f trivial

/-- The zero valuation functor. -/
def valuation : ValuationFunctor model where
  V _ := 0
  V_comp _ _ := by simp
  V_tensor _ _ := by simp
  V_add _ _ := by simp

/-- The labels fibration is inhabited (everything labeled empty). -/
def labeled : LabeledGroupoid :=
  ⟨model, modelLaws, fun _ => Label.empty, fun _ => rfl⟩

/-- The one-point price groupoid: every conversion at rate 1. -/
def prices : PriceGroupoid where
  Conversion _ _ := PUnit
  rate _ := 1
  id_conv _ := .unit
  comp_conv _ _ := .unit
  inv_conv _ := .unit
  comp_assoc _ _ _ := rfl
  id_comp _ := rfl
  comp_id _ := rfl
  inv_comp _ := rfl
  comp_inv _ := rfl
  rate_id _ := rfl
  rate_comp _ _ := (one_mul 1).symm

/-- The repaired `PriceAction` is inhabited — the Phase 1 version was
    not (for any price groupoid with a conversion and any 𝕋 with a
    morphism). -/
def priceAction : PriceAction prices model (fun _ => valuation) where
  revalue := fun {_a _b} _p {_A _B} f => f
  revalue_id _ := rfl
  revalue_comp := fun {_a _b _c} _q _p {_A _B} _f => rfl
  revalue_sound _ _ := by simp [valuation, prices]

/-- A one-account forest with no parent edges. -/
def forest : AccountForest where
  Account := PUnit
  parent _ := none
  wellFounded := ⟨fun a => Acc.intro a fun _ hy => nomatch hy⟩

/-- Roll-up data over the one-account forest — `RollupFunctor` is
    inhabited. -/
def rollup : RollupFunctor forest model where
  embed _ := 0
  rollup _ _ _ := .unit

end Trivial

end Ledger
