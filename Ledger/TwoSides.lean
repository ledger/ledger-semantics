import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.PosPart
import Ledger.Pacioli

/-!
# Generator endpoints as Ellerman's two sides

Ellerman locates what is double in double-entry bookkeeping in the
two-sidedness of the T-accounts, and not in the number of accounts a
transaction touches (D. Ellerman, "On Double-Entry Bookkeeping: The
Mathematical Treatment", Accounting Education 23:5 (2014) 483-501,
p. 487). `zeroRow_two_accounts` in `Pacioli.lean` records the second
half of that argument. This module gives the first half a checked
form at the level of generators.

`EndsCoherent A B v` says that every account with a positive (debit)
entry in `v` lies in the codomain `B`, and every account with a
negative (credit) entry lies in the domain `A`. A generator
specification is `SignCoherent` when the flow of each generator is
coherent with its own endpoints. For such a generator whose flow is a
zero-row, `two_ends` proves that, commodity by commodity, the debits
over the codomain equal the credits over the domain: Ellerman's equal
debits and credits (p. 496), located on the two ends. Coherent in this
module means coherent in sign: the positive part of a flow is
supported in the codomain and the negative part in the domain. The
word is unrelated to the monoidal coherence of `Groupoid.lean`.

Coherence of an L2 morphism (`GenSpec.IsCoherent`) is defined through
its flow and its endpoints, both invariant under `Rel`. It holds for
the generators of a coherent specification and for `id` and `0`, and
it is closed under `inv`, `tensor` and `+`. It fails under
composition (`GenSpec.comp_breaks_coherence`), because a composite
can carry flow at intermediate accounts that lie in neither of its
ends. The statement in which the domain matters is
`GenSpec.flow_eq_zero_of_isCoherent`: a coherent morphism out of the
empty object whose flow is a zero-row has zero flow. This is the
precise form of the intuition that an opening balance with no offset
moves nothing. In Ellerman's notation, `[x // 0]` is a zero-term only
when `x = 0`, which follows from the cross-sum equality of his
Table 1 (p. 485).

Two limits of scope. Endpoint multiplicities do not record amounts,
so the pair of ends is not an element of Ellerman's group of
T-accounts. In the oracle's construction (`Driver.specFor`) they count
postings: the domain is the multiset of credited postings, which
contains the support of the negative part of the flow and may also
contain accounts whose net is zero or positive (postings of `+10` and
`-5` to one account give Ellerman's unreduced `[10 // 5]`). And the
theorems concern generators whose flow is a zero-row;
`free_trial_balance` in `Pacioli.lean` names the kinds of generator
that are not. The abstract theory leaves endpoints unconstrained by
flows, and the counterexample model of `Pacioli.lean` is deliberately
incoherent (`GenSpec.unitSpec_not_signCoherent`).

`DriverTwoSides.lean` proves that the oracle's generators are
coherent (`Driver.specFor_coherent`), so the theorems of this module
apply to them.

The endpoint theorems of `Valuation.lean` refute a different reading,
in which one object measure is compared across every morphism, and do
not bear on this one.
-/

namespace Ledger

/-! ## Coherence of a flow with a pair of ends -/

/-- Ellerman's two sides, read at the level of supports: every account
    with a positive (debit) entry lies in the codomain `B`, every
    account with a negative (credit) entry lies in the domain `A`.
    Stated over plain functions, so that it applies to the oracle's
    flows directly and to `PacioliGroup` flows by coercion. -/
def EndsCoherent (A B : Object) (v : Account → ℚ) : Prop :=
  ∀ a, (0 < v a → a ∈ B) ∧ (v a < 0 → a ∈ A)

namespace EndsCoherent

theorem zero (A B : Object) : EndsCoherent A B (fun _ => 0) := fun _ =>
  ⟨fun h => absurd h (lt_irrefl 0), fun h => absurd h (lt_irrefl 0)⟩

/-- Exchanging the ends and negating the flow preserves coherence. -/
theorem neg {A B : Object} {v : Account → ℚ} (h : EndsCoherent A B v) :
    EndsCoherent B A (fun a => -v a) := fun a =>
  ⟨fun hp => (h a).2 (by linarith), fun hn => (h a).1 (by linarith)⟩

theorem tensor {A B C D : Object} {v w : Account → ℚ}
    (hv : EndsCoherent A B v) (hw : EndsCoherent C D w) :
    EndsCoherent (A + C) (B + D) (fun a => v a + w a) := fun a => by
  constructor
  · intro hp
    rw [Multiset.mem_add]
    by_cases h : 0 < v a
    · exact Or.inl ((hv a).1 h)
    · exact Or.inr ((hw a).1 (by linarith))
  · intro hn
    rw [Multiset.mem_add]
    by_cases h : v a < 0
    · exact Or.inl ((hv a).2 h)
    · exact Or.inr ((hw a).2 (by linarith))

theorem add {A B : Object} {v w : Account → ℚ}
    (hv : EndsCoherent A B v) (hw : EndsCoherent A B w) :
    EndsCoherent A B (fun a => v a + w a) := fun a => by
  constructor
  · intro hp
    by_cases h : 0 < v a
    · exact (hv a).1 h
    · exact (hw a).1 (by linarith)
  · intro hn
    by_cases h : v a < 0
    · exact (hv a).2 h
    · exact (hw a).2 (by linarith)

end EndsCoherent

/-- A zero-row sums to zero over the accounts of each commodity that
    it touches. -/
theorem sum_commodity_eq_zero {v : PacioliGroup} (hbal : v ∈ zeroRows)
    (c : Commodity) : ∑ a ∈ v.support with a.commodity = c, v a = 0 := by
  rw [← trialBalance_apply, mem_zeroRows.mp hbal]
  rfl

/-- **The `[x // 0]` case**: a coherent flow with empty domain that is
    a zero-row is zero. Every entry is nonnegative, and nonnegative
    entries summing to zero in each commodity all vanish. -/
theorem eq_zero_of_endsCoherent_zero {B : Object} {v : PacioliGroup}
    (hcoh : EndsCoherent 0 B v) (hbal : v ∈ zeroRows) : v = 0 := by
  have hnn : ∀ a, 0 ≤ v a := fun a => by
    by_contra h
    have := (hcoh a).2 (not_le.mp h)
    simp at this
  ext a
  simp only [Finsupp.coe_zero, Pi.zero_apply]
  have hz := sum_commodity_eq_zero hbal a.commodity
  by_cases ha : a ∈ v.support
  · exact (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => hnn b)).mp hz a
      (Finset.mem_filter.mpr ⟨ha, rfl⟩)
  · exact Finsupp.notMem_support_iff.mp ha

/-- The `[x // 0]` case with the empty domain given as a hypothesis,
    for domains that are empty only propositionally. -/
theorem eq_zero_of_endsCoherent_dom_eq_zero {A B : Object} {v : PacioliGroup}
    (hA : A = 0) (hcoh : EndsCoherent A B v) (hbal : v ∈ zeroRows) : v = 0 := by
  subst hA
  exact eq_zero_of_endsCoherent_zero hcoh hbal

/-- **Equal debits and credits, located on the two ends** (Ellerman
    p. 496): for a coherent zero-row, in each commodity the positive
    parts over the codomain sum to the negative parts over the
    domain. -/
theorem two_ends {A B : Object} {v : PacioliGroup}
    (hcoh : EndsCoherent A B v) (hbal : v ∈ zeroRows) (c : Commodity) :
    ∑ a ∈ B.toFinset with a.commodity = c, (v a)⁺
      = ∑ a ∈ A.toFinset with a.commodity = c, (v a)⁻ := by
  set U : Finset Account :=
    (A.toFinset ∪ B.toFinset ∪ v.support).filter (fun a => a.commodity = c) with hU
  have hB : ∑ a ∈ B.toFinset with a.commodity = c, (v a)⁺ = ∑ a ∈ U, (v a)⁺ := by
    apply Finset.sum_subset
    · intro a ha
      rw [Finset.mem_filter] at ha ⊢
      exact ⟨Finset.mem_union_left _ (Finset.mem_union_right _ ha.1), ha.2⟩
    · intro a haU haB
      rw [posPart_eq_zero]
      by_contra hpos
      exact haB (Finset.mem_filter.mpr
        ⟨Multiset.mem_toFinset.mpr ((hcoh a).1 (not_le.mp hpos)),
          (Finset.mem_filter.mp haU).2⟩)
  have hA : ∑ a ∈ A.toFinset with a.commodity = c, (v a)⁻ = ∑ a ∈ U, (v a)⁻ := by
    apply Finset.sum_subset
    · intro a ha
      rw [Finset.mem_filter] at ha ⊢
      exact ⟨Finset.mem_union_left _ (Finset.mem_union_left _ ha.1), ha.2⟩
    · intro a haU haA
      rw [negPart_eq_zero]
      by_contra hneg
      exact haA (Finset.mem_filter.mpr
        ⟨Multiset.mem_toFinset.mpr ((hcoh a).2 (not_le.mp hneg)),
          (Finset.mem_filter.mp haU).2⟩)
  have hS : ∑ a ∈ U, v a = 0 := by
    rw [← sum_commodity_eq_zero hbal c]
    symm
    apply Finset.sum_subset
    · intro a ha
      rw [Finset.mem_filter] at ha ⊢
      exact ⟨Finset.mem_union_right _ ha.1, ha.2⟩
    · intro a haU hav
      by_contra hne
      exact hav (Finset.mem_filter.mpr
        ⟨Finsupp.mem_support_iff.mpr hne, (Finset.mem_filter.mp haU).2⟩)
  rw [hB, hA, ← sub_eq_zero, ← Finset.sum_sub_distrib]
  simpa [posPart_sub_negPart] using hS

namespace GenSpec

/-! ## Coherence of specifications and of free morphisms -/

/-- Generator-wise coherence of a specification: each generator's
    flow is coherent with its own domain and codomain. -/
def SignCoherent (S : GenSpec) (flows : S.Gen → Account → ℚ) : Prop :=
  ∀ t, EndsCoherent (S.dom t) (S.cod t) (flows t)

variable {S : GenSpec}

/-- Coherence of an L2 morphism: its flow is coherent with its ends.
    Both are invariant under `Rel`, so this is a property of the
    morphism and not of a representative. -/
def IsCoherent (flows : S.Gen → PacioliGroup) {A B : Object}
    (f : FreeHom S A B) : Prop :=
  EndsCoherent A B (flow flows f)

theorem isCoherent_gen {flows : S.Gen → PacioliGroup}
    (hS : S.SignCoherent (fun t => flows t)) (t : S.Gen) :
    IsCoherent flows (⟦.gen t⟧ : FreeHom S (S.dom t) (S.cod t)) := by
  intro a
  rw [flow_gen]
  exact hS t a

theorem isCoherent_id (flows : S.Gen → PacioliGroup) (A : Object) :
    IsCoherent flows ((freeT S).id A) := by
  intro a; simp [flow_id]

theorem isCoherent_zero (flows : S.Gen → PacioliGroup) (A B : Object) :
    IsCoherent flows (0 : (freeT S).Hom A B) := by
  intro a; simp [flow_zero]

theorem IsCoherent.inv {flows : S.Gen → PacioliGroup} {A B : Object}
    {f : FreeHom S A B} (h : IsCoherent flows f) :
    IsCoherent flows ((freeT S).inv f) := by
  intro a
  have := EndsCoherent.neg h a
  simpa [flow_inv] using this

theorem IsCoherent.tensor {flows : S.Gen → PacioliGroup} {A B C D : Object}
    {f : FreeHom S A B} {g : FreeHom S C D}
    (hf : IsCoherent flows f) (hg : IsCoherent flows g) :
    IsCoherent flows ((freeT S).tensor f g) := by
  intro a
  have := EndsCoherent.tensor hf hg a
  simpa [flow_tensor] using this

theorem IsCoherent.add {flows : S.Gen → PacioliGroup} {A B : Object}
    {f g : FreeHom S A B}
    (hf : IsCoherent flows f) (hg : IsCoherent flows g) :
    IsCoherent flows (f + g) := by
  have e : flow flows (f + g) = flow flows f + flow flows g := flow_add flows f g
  intro a
  have := EndsCoherent.add hf hg a
  rw [e]
  simpa using this

/-- **An opening balance with no offset moves nothing**, in the form
    in which the domain does work: a coherent morphism out of the
    empty object whose flow is a zero-row has zero flow. Compare
    `double_entry_invariant`, whose proof never reads the domain. -/
theorem flow_eq_zero_of_isCoherent {flows : S.Gen → PacioliGroup} {A : Object}
    {f : FreeHom S 0 A} (hcoh : IsCoherent flows f)
    (hbal : flow flows f ∈ zeroRows) : flow flows f = 0 :=
  eq_zero_of_endsCoherent_zero hcoh hbal

/-- Terms built without composition. The oracle's journal term is one
    (a tensor of generators). -/
def FreeMor.CompFree : {A B : Object} → S.FreeMor A B → Prop
  | _, _, .gen _ => True
  | _, _, .id _ => True
  | _, _, .zero _ _ => True
  | _, _, .comp _ _ => False
  | _, _, .inv f => FreeMor.CompFree f
  | _, _, .tensor f g => FreeMor.CompFree f ∧ FreeMor.CompFree g
  | _, _, .add f g => FreeMor.CompFree f ∧ FreeMor.CompFree g

/-- Composition-free terms over a coherent specification have coherent
    flows. -/
theorem endsCoherent_flowAux {flows : S.Gen → PacioliGroup}
    (hS : S.SignCoherent (fun t => flows t)) {A B : Object}
    (f : S.FreeMor A B) (hf : f.CompFree) :
    EndsCoherent A B ⇑(flowAux flows f) := by
  induction f with
  | gen t => intro a; simpa [flowAux] using hS t a
  | id A => intro a; simp [flowAux]
  | zero A B => intro a; simp [flowAux]
  | comp g f _ _ => exact absurd hf (by simp [FreeMor.CompFree])
  | inv f ih =>
      intro a
      have := EndsCoherent.neg (ih hf) a
      simpa [flowAux] using this
  | tensor f g ihf ihg =>
      obtain ⟨hf1, hf2⟩ := hf
      intro a
      have := EndsCoherent.tensor (ihf hf1) (ihg hf2) a
      simpa [flowAux] using this
  | add f g ihf ihg =>
      obtain ⟨hf1, hf2⟩ := hf
      intro a
      have := EndsCoherent.add (ihf hf1) (ihg hf2) a
      simpa [flowAux] using this

/-- A composition-free representative gives a coherent morphism. -/
theorem isCoherent_mk {flows : S.Gen → PacioliGroup}
    (hS : S.SignCoherent (fun t => flows t)) {A B : Object}
    (f : S.FreeMor A B) (hf : f.CompFree) :
    IsCoherent flows (⟦f⟧ : FreeHom S A B) :=
  endsCoherent_flowAux hS f hf

/-! ## Witnesses -/

/-- The D16 counterexample model is deliberately incoherent: its one
    generator has empty ends and yet carries flow at `Assets:Cash`. -/
theorem unitSpec_not_signCoherent :
    ¬ unitSpec.SignCoherent (fun t => oneFlow t) := by
  intro h
  have := (h PUnit.unit someAccount).1
  simp [oneFlow, unitSpec] at this

/-- The account the composition counterexample moves a dollar into. -/
def foodAccount : Account := ⟨"Expenses:Food", "USD"⟩

/-- Two generators and their ends: `true : 0 → {cash}` and
    `false : {cash} → {food}`. Their flows are `chainFlows`. -/
def chainSpec : GenSpec where
  Gen := Bool
  dom | true => 0 | false => {someAccount}
  cod | true => {someAccount} | false => {foodAccount}

/-- The flows of `chainSpec`: `true` has zero flow, and `false` moves
    one dollar from cash to food. -/
noncomputable def chainFlows : chainSpec.Gen → PacioliGroup
  | true => 0
  | false => Finsupp.single foodAccount 1 - Finsupp.single someAccount 1

/-- **Coherence fails under composition.** Both generators are
    coherent zero-rows, yet their composite `0 → {food}` has a flow
    that is a nonzero zero-row and is not coherent: it credits
    `Assets:Cash`, which lies in neither end. Read account by account,
    "a morphism out of the empty object moves nothing" is therefore
    false for composites. -/
theorem comp_breaks_coherence :
    chainSpec.SignCoherent (fun t => chainFlows t) ∧
    (∀ t, chainFlows t ∈ zeroRows) ∧
    let hk := (freeT chainSpec).comp
      (⟦FreeMor.gen (S := chainSpec) false⟧ : FreeHom chainSpec {someAccount} {foodAccount})
      (⟦FreeMor.gen (S := chainSpec) true⟧ : FreeHom chainSpec 0 {someAccount})
    flow chainFlows hk ∈ zeroRows ∧ flow chainFlows hk ≠ 0 ∧
      ¬ IsCoherent chainFlows hk := by
  have hne : someAccount ≠ foodAccount := by decide
  refine ⟨?_, ?_, ?_⟩
  · intro t a
    cases t
    · by_cases h1 : a = foodAccount
      · subst h1
        simp [chainFlows, chainSpec, hne]
      · by_cases h2 : a = someAccount
        · subst h2
          simp [chainFlows, chainSpec, hne]
        · simp [chainFlows, chainSpec, Ne.symm h1, Ne.symm h2]
    · simp [chainFlows]
  · intro t
    cases t
    · show trialBalance _ = 0
      simp [chainFlows, trialBalance_single, someAccount, foodAccount]
    · show trialBalance _ = 0
      simp [chainFlows]
  · have hflow : flow chainFlows ((freeT chainSpec).comp
        (⟦FreeMor.gen (S := chainSpec) false⟧ : FreeHom chainSpec {someAccount} {foodAccount})
        (⟦FreeMor.gen (S := chainSpec) true⟧ : FreeHom chainSpec 0 {someAccount}))
        = Finsupp.single foodAccount 1 - Finsupp.single someAccount 1 := by
      rw [flow_comp]
      simp [flowAux, chainFlows]
    refine ⟨?_, ?_, ?_⟩
    · rw [hflow]
      show trialBalance _ = 0
      simp [trialBalance_single, someAccount, foodAccount]
    · rw [hflow]
      intro h0
      have := congrArg (fun v : PacioliGroup => v someAccount) h0
      simp [hne] at this
    · intro hc
      have := (hc someAccount).2
      rw [hflow] at this
      simp [hne] at this

end GenSpec

end Ledger
