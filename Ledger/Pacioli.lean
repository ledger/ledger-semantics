import Mathlib.Data.Finsupp.Basic
import Mathlib.Tactic.Abel
import Ledger.Free

/-!
# L1: the Pacioli skeleton, and the denotation L2 → L1

Ellerman's Pacioli group, per commodity and account: the free abelian
group of per-account flows, carried by finitely-supported functions
`Account →₀ ℚ` (D2: exact rationals below L0). The **denotation** of a
reified morphism is its net per-account flow:

    ⟦gen t⟧ = flows t     ⟦id⟧ = ⟦0⟧ = 0      ⟦g ∘ f⟧ = ⟦g⟧ + ⟦f⟧
    ⟦f⁻¹⟧ = −⟦f⟧          ⟦f ⊗ g⟧ = ⟦f⟧ + ⟦g⟧   ⟦f + g⟧ = ⟦f⟧ + ⟦g⟧

`flowAux_respects` — the Phase 8 obligation — checks this assignment
against every `Rel` equation, so it descends to the quotient
(`flow`), and the commuting squares (`flow_comp` etc.) then hold by
construction. As the worksheet records, the skeleton deliberately
loses morphism identity: adequate for *balance* queries, not for
*register* queries.

## The finding this module forced (decision D16)

Writing `flowAux_respects` against the Phase 1–3 law set **failed**
at `f ∘ 0 = 0`: the flow of the left side is `⟦f⟧`, of the right `0`.
Unwinding: `comp_zero` together with `V_comp` forces `V f = 0` for
*every* morphism — the Phase 1 axioms admitted only the identically
zero valuation, so every valuation theorem was true of a degenerate
subject. The same argument refutes bilinearity (`(g+g') ∘ f =
g∘f + g'∘f` double-counts `V f`). The repair: hom-set `+` is
compatible with valuations (`V_add`) and with nothing else — the
four bilinearity/absorption laws are gone from `𝕋Laws`, and this
module's model is the standing proof of non-degeneracy. The formal
witnesses are at the bottom of this file:

- `zero_absorption_degenerates` — adding the absorption law back
  collapses every valuation to zero (three lines);
- `comp_not_zero_absorbing`, `tensor_not_additive` — the free model
  refutes the removed laws, so they are not derivable from `𝕋Laws`.
-/

namespace Ledger

/-- L1 carrier: per-account rational net flows — the Pacioli group. -/
abbrev PacioliGroup : Type := Account →₀ ℚ

namespace GenSpec

variable {S : GenSpec}

noncomputable section

/-- The flow denotation on terms. -/
def flowAux (flows : S.Gen → PacioliGroup) :
    {A B : Object} → S.FreeMor A B → PacioliGroup
  | _, _, .gen t => flows t
  | _, _, .id _ => 0
  | _, _, .zero _ _ => 0
  | _, _, .comp g f => flowAux flows g + flowAux flows f
  | _, _, .inv f => -flowAux flows f
  | _, _, .tensor f g => flowAux flows f + flowAux flows g
  | _, _, .add f g => flowAux flows f + flowAux flows g

@[simp] theorem flowAux_cast (flows : S.Gen → PacioliGroup)
    {A A' B B' : Object} (hA : A = A') (hB : B = B') (f : S.FreeMor A B) :
    flowAux flows (f.cast hA hB) = flowAux flows f := by
  subst hA; subst hB; rfl

/-- The flow denotation respects every equation of the free model —
    the L2 → L1 leg of the commuting squares, checked constructor by
    constructor. This induction is where a wrong law refuses to
    close; see the module docstring. -/
theorem flowAux_respects (flows : S.Gen → PacioliGroup)
    {A B : Object} {f g : S.FreeMor A B} (h : Rel f g) :
    flowAux flows f = flowAux flows g := by
  induction h with
  | refl f => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | comp_congr _ _ ihg ihf => simp only [flowAux, ihg, ihf]
  | inv_congr _ ih => simp only [flowAux, ih]
  | tensor_congr _ _ ihf ihg => simp only [flowAux, ihf, ihg]
  | add_congr _ _ ihf ihg => simp only [flowAux, ihf, ihg]
  | comp_assoc h g f => simp only [flowAux]; abel
  | id_comp f => simp only [flowAux]; abel
  | comp_id f => simp only [flowAux]; abel
  | inv_comp f => simp only [flowAux]; abel
  | comp_inv f => simp only [flowAux]; abel
  | tensor_id A B => simp only [flowAux]; abel
  | tensor_comp g f g' f' => simp only [flowAux]; abel
  | tensor_assoc f g h => simp only [flowAux_cast, flowAux]; abel
  | tensor_comm f g => simp only [flowAux_cast, flowAux]; abel
  | tensor_unit f => simp only [flowAux_cast, flowAux]; abel
  | add_comm f g => simp only [flowAux]; abel
  | add_assoc f g h => simp only [flowAux]; abel
  | add_zero f => simp only [flowAux]; abel

/-- The denotation of an L2 morphism: its per-account net flow. -/
def flow (flows : S.Gen → PacioliGroup) {A B : Object} :
    FreeHom S A B → PacioliGroup :=
  Quotient.lift (flowAux flows) fun _ _ h => flowAux_respects flows h

/-! ### The commuting squares (Phase 8)

Each fundamental operation of the free model commutes with the
denotation into the Pacioli group. The proofs are induction to
representatives plus the defining clauses of `flowAux` — the solved
forms *are* the definition, which is what "solve, don't verify"
buys. -/

@[simp] theorem flow_mk (flows : S.Gen → PacioliGroup)
    {A B : Object} (f : S.FreeMor A B) :
    flow flows (⟦f⟧ : FreeHom S A B) = flowAux flows f := rfl

@[simp] theorem flow_gen (flows : S.Gen → PacioliGroup) (t : S.Gen) :
    flow flows (⟦.gen t⟧ : FreeHom S _ _) = flows t := by
  show flowAux flows (.gen t) = flows t
  simp [flowAux]

@[simp] theorem flow_id (flows : S.Gen → PacioliGroup) (A : Object) :
    flow flows ((freeT S).id A) = 0 := by
  show flowAux flows (.id A) = 0
  simp [flowAux]

@[simp] theorem flow_zero (flows : S.Gen → PacioliGroup) (A B : Object) :
    flow flows (0 : (freeT S).Hom A B) = 0 := by
  show flowAux flows (.zero A B) = 0
  simp [flowAux]

@[simp] theorem flow_comp (flows : S.Gen → PacioliGroup)
    {A B C : Object} (g : (freeT S).Hom B C) (f : (freeT S).Hom A B) :
    flow flows ((freeT S).comp g f) = flow flows g + flow flows f :=
  Quotient.inductionOn₂ g f fun x y => by
    show flowAux flows (.comp x y) = flowAux flows x + flowAux flows y
    simp [flowAux]

@[simp] theorem flow_inv (flows : S.Gen → PacioliGroup)
    {A B : Object} (f : (freeT S).Hom A B) :
    flow flows ((freeT S).inv f) = -flow flows f :=
  Quotient.inductionOn f fun x => by
    show flowAux flows (.inv x) = -flowAux flows x
    simp [flowAux]

@[simp] theorem flow_tensor (flows : S.Gen → PacioliGroup)
    {A B C D : Object} (f : (freeT S).Hom A B) (g : (freeT S).Hom C D) :
    flow flows ((freeT S).tensor f g) = flow flows f + flow flows g :=
  Quotient.inductionOn₂ f g fun x y => by
    show flowAux flows (.tensor x y) = flowAux flows x + flowAux flows y
    simp [flowAux]

@[simp] theorem flow_add (flows : S.Gen → PacioliGroup)
    {A B : Object} (f g : (freeT S).Hom A B) :
    flow flows (f + g) = flow flows f + flow flows g :=
  Quotient.inductionOn₂ f g fun x y => by
    show flowAux flows (.add x y) = flowAux flows x + flowAux flows y
    simp [flowAux]

/-- The per-account ℝ-valued valuation functors of the free model:
    project the flow at one account and embed ℚ ↪ ℝ (the L1 → L0
    leg). This ties the concrete tower to the abstract kernel — every
    Phase 3 theorem now speaks about the free model with no further
    proof. -/
def accountValuation (flows : S.Gen → PacioliGroup) (a : Account) :
    ValuationFunctor (freeT S) where
  V f := ((flow flows f) a : ℝ)
  V_comp g f := by rw [flow_comp, Finsupp.add_apply, Rat.cast_add]
  V_tensor f g := by rw [flow_tensor, Finsupp.add_apply, Rat.cast_add]
  V_add f g := by rw [flow_add, Finsupp.add_apply, Rat.cast_add]

/-- **The free model's double-entry theorem**, by instantiating the
    abstract master theorem at the per-account valuations: balanced
    journal entries make every derived flow vanish, account by
    account. The kernel and the tower meet here. -/
theorem free_flow_balanced (flows : S.Gen → PacioliGroup)
    (hbal : ∀ t : S.Gen, flows t = 0)
    {A B : Object} (f : FreeHom S A B) :
    flow flows f = 0 := by
  ext a
  have h := balanced_generators_balance (freeT S) (freeGenerated S)
    (accountValuation flows a) (freeLaws S)
    (fun {A B} g hg => by
      obtain ⟨t, hA, hB, rfl⟩ := hg
      rw [(accountValuation flows a).V_castHom]
      show ((flow flows (⟦.gen t⟧ : FreeHom S _ _)) a : ℝ) = 0
      rw [flow_gen, hbal t]
      simp) f
  have hq : (flow flows f) a = 0 := Rat.cast_eq_zero.mp h
  simpa using hq

/-! ### Formal witnesses of the D16 finding -/

/-- Putting the zero-absorption law back degenerates the theory:
    every valuation of every morphism would be zero. This is the
    three-line argument that exposed the Phase 1 axiom set. -/
theorem zero_absorption_degenerates (T : 𝕋) (W : ValuationFunctor T)
    (habs : ∀ {A B C : Object} (f : T.Hom B C),
      T.comp f (0 : T.Hom A B) = (0 : T.Hom A C))
    {A B : Object} (f : T.Hom A B) : W.V f = 0 := by
  have h1 := W.V_comp f (0 : T.Hom A A)
  rw [habs, W.V_zero, W.V_zero] at h1
  linarith

/-- A one-generator specification: a single atomic transaction on the
    empty endpoints. -/
def unitSpec : GenSpec := ⟨PUnit, fun _ => 0, fun _ => 0⟩

/-- The account the counterexamples flow through. -/
def someAccount : Account := ⟨"Assets:Cash", "USD"⟩

def oneFlow : unitSpec.Gen → PacioliGroup :=
  fun _ => Finsupp.single someAccount 1

/-- The free model refutes zero-absorption: `f ∘ 0 ≠ 0` when `f`
    carries flow. Hence the removed law is not derivable from
    `𝕋Laws` — the removal (D16) is forced, not merely prudent. -/
theorem comp_not_zero_absorbing :
    ¬ (∀ (T : 𝕋) (_ : 𝕋Laws T) {A B C : Object} (f : T.Hom B C),
        T.comp f (0 : T.Hom A B) = (0 : T.Hom A C)) := by
  intro hlaw
  have h := hlaw (freeT unitSpec) (freeLaws unitSpec)
    (A := 0) (⟦.gen PUnit.unit⟧)
  have hrel := Quotient.exact h
  have hfl := flowAux_respects oneFlow hrel
  simp only [flowAux, oneFlow, add_zero] at hfl
  rw [Finsupp.single_eq_zero] at hfl
  exact one_ne_zero hfl

/-- The free model refutes tensor-additivity: `(f + f') ⊗ g` and
    `f ⊗ g + f' ⊗ g` measure `g`'s flow once and twice
    respectively. -/
theorem tensor_not_additive :
    ¬ (∀ (T : 𝕋) (_ : 𝕋Laws T) {A B C D : Object}
        (f f' : T.Hom A B) (g : T.Hom C D),
        T.tensor (f + f') g = T.tensor f g + T.tensor f' g) := by
  intro hlaw
  have h := hlaw (freeT unitSpec) (freeLaws unitSpec)
    (⟦.id 0⟧ : FreeHom unitSpec 0 0) (⟦.id 0⟧) (⟦.gen PUnit.unit⟧)
  have hrel := Quotient.exact h
  have hfl := flowAux_respects oneFlow hrel
  simp only [flowAux, oneFlow, add_zero, zero_add] at hfl
  have happ := congrArg (fun v : PacioliGroup => v someAccount) hfl
  simp only [Finsupp.add_apply, Finsupp.single_eq_same] at happ
  norm_num at happ

end

end GenSpec

end Ledger
