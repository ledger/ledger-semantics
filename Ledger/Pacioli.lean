import Mathlib.Data.Finsupp.Basic
import Mathlib.Algebra.Group.Subgroup.Ker
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

/-! ### The per-commodity trial balance -/

/-- Ellerman's vector trial balance (pp. 494, 496): collapse each
    account to its commodity and sum, one column per property type. -/
noncomputable def trialBalance : PacioliGroup →+ (Commodity →₀ ℚ) :=
  Finsupp.mapDomain.addMonoidHom Account.commodity

/-- The trial-balance column of one commodity. Taken over every
    account, it vanishes on each derived flow of a journal whose
    entries balance in that commodity (`free_trial_balance`), as they
    do when they are zero-rows. It is therefore a check and not a
    report; a report measures selected accounts, as
    `accountValuation` measures one. -/
noncomputable def commodityTotal (c : Commodity) : PacioliGroup →+ ℚ :=
  (Finsupp.applyAddHom c).comp trialBalance

/-- Zero-rows: the flows whose amounts sum to zero over the accounts
    of each commodity. Ellerman's name for a signed row that sums to
    zero (p. 492), which in the vector case is a row of vectors that
    adds to zero (p. 498); on the T-account side of his debit
    isomorphism the corresponding rows of T-accounts are transaction
    zero-terms (pp. 488-489). -/
noncomputable def zeroRows : AddSubgroup PacioliGroup := trialBalance.ker

theorem mem_zeroRows {v : PacioliGroup} : v ∈ zeroRows ↔ trialBalance v = 0 :=
  AddMonoidHom.mem_ker

@[simp] theorem trialBalance_single (a : Account) (q : ℚ) :
    trialBalance (Finsupp.single a q) = Finsupp.single a.commodity q :=
  Finsupp.mapDomain_single

/-- A column of the trial balance is the sum of the flow over the
    accounts of that commodity that it touches. -/
theorem trialBalance_apply (x : PacioliGroup) (c : Commodity) :
    trialBalance x c = ∑ a ∈ x.support with a.commodity = c, x a := by
  rw [Finset.sum_filter]
  simp only [trialBalance, Finsupp.mapDomain.addMonoidHom_apply,
    Finsupp.mapDomain, Finsupp.sum, Finsupp.finsetSum_apply, Finsupp.single_apply]

@[simp] theorem commodityTotal_apply (c : Commodity) (v : PacioliGroup) :
    commodityTotal c v = trialBalance v c := rfl

namespace GenSpec

variable {S : GenSpec}

noncomputable section

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H]

/-- The flow denotation on terms, into any additive commutative
    group. The L1 denotation `flow` is valued in `PacioliGroup`; the
    generality is what makes `map_flowAux` (naturality) statable,
    because its right-hand side is a denotation into another group,
    which `trialBalance_flowAux` takes to be `Commodity →₀ ℚ`.
    `flowAux_mem` (subgroup preservation) is stated at the same
    generality. -/
def flowAux (flows : S.Gen → G) :
    {A B : Object} → S.FreeMor A B → G
  | _, _, .gen t => flows t
  | _, _, .id _ => 0
  | _, _, .zero _ _ => 0
  | _, _, .comp g f => flowAux flows g + flowAux flows f
  | _, _, .inv f => -flowAux flows f
  | _, _, .tensor f g => flowAux flows f + flowAux flows g
  | _, _, .add f g => flowAux flows f + flowAux flows g

@[simp] theorem flowAux_cast (flows : S.Gen → G)
    {A A' B B' : Object} (hA : A = A') (hB : B = B') (f : S.FreeMor A B) :
    flowAux flows (f.cast hA hB) = flowAux flows f := by
  subst hA; subst hB; rfl

/-- The flow denotation respects every equation of the free model —
    the L2 → L1 leg of the commuting squares, checked constructor by
    constructor. This induction is where a wrong law refuses to
    close; see the module docstring. -/
theorem flowAux_respects (flows : S.Gen → G)
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

/-! ### Naturality, and the bridge to the abstract kernel -/

/-- Naturality: an additive map commutes with the denotation. -/
theorem map_flowAux (φ : G →+ H) (flows : S.Gen → G)
    {A B : Object} (f : S.FreeMor A B) :
    φ (flowAux flows f) = flowAux (φ ∘ flows) f := by
  induction f with
  | gen t => rfl
  | id A => simp [flowAux]
  | zero A B => simp [flowAux]
  | comp g f ihg ihf => simp [flowAux, ihg, ihf]
  | inv f ih => simp [flowAux, ih]
  | tensor f g ihf ihg => simp [flowAux, ihf, ihg]
  | add f g ihf ihg => simp [flowAux, ihf, ihg]

/-- Subgroup preservation: a subgroup that contains every
    generator's flow contains the flow of every term. -/
theorem flowAux_mem (flows : S.Gen → G) (K : AddSubgroup G)
    (h : ∀ t, flows t ∈ K) {A B : Object} (f : S.FreeMor A B) :
    flowAux flows f ∈ K := by
  induction f with
  | gen t => exact h t
  | id A => exact K.zero_mem
  | zero A B => exact K.zero_mem
  | comp g f ihg ihf => exact K.add_mem ihg ihf
  | inv f ih => exact K.neg_mem ih
  | tensor f g ihf ihg => exact K.add_mem ihf ihg
  | add f g ihf ihg => exact K.add_mem ihf ihg

/-- Subgroup preservation for the denotation of L2 morphisms. -/
theorem flow_mem (flows : S.Gen → PacioliGroup) (K : AddSubgroup PacioliGroup)
    (h : ∀ t, flows t ∈ K) {A B : Object} (f : FreeHom S A B) :
    flow flows f ∈ K :=
  Quotient.inductionOn f fun x => flowAux_mem flows K h x

/-- **Residual formula**: the trial balance of any term's flow is the
    denotation of the generators' own trial balances. When entries
    fail to be zero-rows, the per-commodity totals of a journal are
    the sum of the per-entry residuals, which may cancel. -/
theorem trialBalance_flowAux (flows : S.Gen → PacioliGroup)
    {A B : Object} (f : S.FreeMor A B) :
    trialBalance (flowAux flows f) = flowAux (trialBalance ∘ flows) f :=
  map_flowAux trialBalance flows f

/-- Every additive functional of L1 flows is a valuation functor of
    the free model, measured in ℝ through ℚ ↪ ℝ: the bridge from L1 to
    the abstract kernel. `accountValuation` is its instance at
    evaluation at one account. -/
def ofFlowHom (flows : S.Gen → PacioliGroup) (φ : PacioliGroup →+ ℚ) :
    ValuationFunctor (freeT S) where
  V f := ((φ (flow flows f) : ℚ) : ℝ)
  V_comp g f := by rw [flow_comp, map_add, Rat.cast_add]
  V_tensor f g := by rw [flow_tensor, map_add, Rat.cast_add]
  V_add f g := by rw [flow_add, map_add, Rat.cast_add]

@[simp] theorem ofFlowHom_V (flows : S.Gen → PacioliGroup) (φ : PacioliGroup →+ ℚ)
    {A B : Object} (f : FreeHom S A B) :
    (ofFlowHom flows φ).V f = ((φ (flow flows f) : ℚ) : ℝ) := rfl

example (flows : S.Gen → PacioliGroup) (a : Account) {A B : Object}
    (f : FreeHom S A B) :
    (accountValuation flows a).V f = (ofFlowHom flows (Finsupp.applyAddHom a)).V f :=
  rfl

/-- The master theorem at any additive functional: a functional of
    flows that vanishes on every generator vanishes on every derived
    flow. This instantiates `balanced_generators_balance` at
    `ofFlowHom`, so the abstract kernel and the tower meet here. -/
theorem free_hom_balanced (flows : S.Gen → PacioliGroup) (φ : PacioliGroup →+ ℚ)
    (hbal : ∀ t, φ (flows t) = 0) {A B : Object} (f : FreeHom S A B) :
    φ (flow flows f) = 0 := by
  have h := balanced_generators_balance (freeT S) (freeGenerated S)
    (ofFlowHom flows φ) (freeLaws S)
    (fun {A B} g hg => by
      obtain ⟨t, hA, hB, rfl⟩ := hg
      rw [(ofFlowHom flows φ).V_castHom]
      show ((φ (flow flows (⟦.gen t⟧ : FreeHom S _ _)) : ℚ) : ℝ) = 0
      rw [flow_gen, hbal t]; simp) f
  exact Rat.cast_eq_zero.mp h

/-- The kernel form, for an additive map into any additive
    commutative group: a map that vanishes on every generator's flow
    vanishes on every derived flow. -/
theorem free_ker_balanced (flows : S.Gen → PacioliGroup) (ψ : PacioliGroup →+ H)
    (hbal : ∀ t, ψ (flows t) = 0) {A B : Object} (f : FreeHom S A B) :
    ψ (flow flows f) = 0 :=
  AddMonoidHom.mem_ker.mp
    (flow_mem flows ψ.ker (fun t => AddMonoidHom.mem_ker.mpr (hbal t)) f)

/-- **Per-commodity double entry** (Ellerman pp. 493-496): if every
    journal entry balances in commodity `c`, so does every derived
    flow.

    The hypothesis is a condition on the entries, and not every
    generator the oracle emits meets it. `Ledger/Journal.lean`
    balances each transaction on weights, valuing a posting at its lot
    price or cost where it carries one, but records the posting's own
    amount, so a priced exchange leaves a nonzero column in each of
    its commodities. A residual accepted as an implicit exchange or
    within the balancing tolerance, a paren-virtual posting (exempt
    from balancing, whether written in the transaction or appended by
    an automated transaction), and a timeclock entry (added without a
    balance check) can each do the same. `Ledger/Journal.lean` records
    each of these conventions in its module docstring or beside the
    rule that implements it. -/
theorem free_trial_balance (flows : S.Gen → PacioliGroup) (c : Commodity)
    (hbal : ∀ t, commodityTotal c (flows t) = 0) {A B : Object}
    (f : FreeHom S A B) :
    commodityTotal c (flow flows f) = 0 :=
  free_hom_balanced flows (commodityTotal c) hbal f

/-- **The free model's double-entry theorem**, Ellerman's vector
    trial balance (p. 496): if every journal entry is a zero-row,
    every derived flow is a zero-row. Proved column by column from
    `free_trial_balance`; the scope of the hypothesis is stated
    there. -/
theorem free_double_entry (flows : S.Gen → PacioliGroup)
    (hbal : ∀ t, flows t ∈ zeroRows) {A B : Object} (f : FreeHom S A B) :
    trialBalance (flow flows f) = 0 := by
  ext c
  have h := free_trial_balance flows c
    (fun t => by rw [commodityTotal_apply, mem_zeroRows.mp (hbal t)]; rfl) f
  simpa using h

/-- The degenerate case `ψ = id` of `free_ker_balanced`: if every
    entry moves nothing, every derived flow is zero. Only a journal
    whose entries move nothing satisfies the hypothesis, so this
    theorem does not carry double entry down to computed flows;
    `free_double_entry` does, under the zero-row hypothesis. -/
theorem free_flow_balanced (flows : S.Gen → PacioliGroup)
    (hbal : ∀ t : S.Gen, flows t = 0)
    {A B : Object} (f : FreeHom S A B) :
    flow flows f = 0 :=
  free_ker_balanced flows (AddMonoidHom.id _) hbal f

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
