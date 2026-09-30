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

/-! ### What a zero-row touches (Ellerman pp. 486-487, 492) -/

/-- **Ellerman pp. 486-487.** An equation `∑ j ∈ s, f j = r` cannot
    survive a change to exactly one term: if `g` agrees with `f` on
    `s` except possibly at `i`, and satisfies the same equation, then
    it agrees at `i` as well. The total `r` is held fixed. Ellerman's
    two-sided equation `x + ... + y = w + ... + z` is the case in
    which `r` is the sum of the right side; a change confined to the
    right side is the same statement with the sides exchanged.
    Nothing about double entry is used, only cancellation in an
    `AddCancelCommMonoid`, which is Ellerman's point that the property
    belongs to the transaction and not to the method of recording it
    (p. 487). -/
theorem one_term_change {ι M : Type*} [AddCancelCommMonoid M]
    (s : Finset ι) (f g : ι → M) {r : M} {i : ι} (hi : i ∈ s)
    (hrest : ∀ j ∈ s, j ≠ i → f j = g j)
    (hf : ∑ j ∈ s, f j = r) (hg : ∑ j ∈ s, g j = r) : f i = g i := by
  classical
  have hrest' : ∑ j ∈ s.erase i, f j = ∑ j ∈ s.erase i, g j :=
    Finset.sum_congr rfl fun j hj =>
      hrest j (Finset.mem_of_mem_erase hj) (Finset.ne_of_mem_erase hj)
  rw [← Finset.add_sum_erase s f hi] at hf
  rw [← Finset.add_sum_erase s g hi, ← hrest'] at hg
  exact add_right_cancel (hf.trans hg.symm)

/-- **Ellerman p. 492, in the signed carrier.** A nonzero zero-row
    touches at least two accounts of one commodity.

    `PacioliGroup` holds signed numbers in single-sided accounts. It
    is Ellerman's single-sided system: the image of his group of
    T-accounts under the debit isomorphism, and not that group itself.
    This is therefore his observation that the single-sided system
    shares the property of each transaction affecting two or more
    accounts, so that the property cannot be what is double in
    double-entry bookkeeping; what is double is the two-sidedness of
    the T-accounts (p. 487). An `Account` pairs a name with a
    commodity, so the two accounts, sharing a commodity, differ in
    name; they are two accounts also in Ellerman's vector sense, in
    which one account may hold several property types. The statement
    concerns zero-rows only and says nothing about entries accepted
    outside `zeroRows`, such as an implicit exchange
    (`implicit_exchange_not_mem_zeroRows`).

    Proof: pick an account `a` that the row touches and compare the
    row with the zero flow in the column of the commodity of `a`. Both
    satisfy the column equation `∑ = 0`, so by `one_term_change` they
    cannot differ at `a` alone, and the row touches a second account
    of that commodity. -/
theorem zeroRow_two_accounts {x : PacioliGroup} (hx : x ∈ zeroRows)
    (h0 : x ≠ 0) :
    ∃ a b : Account, a ≠ b ∧ a.commodity = b.commodity ∧ x a ≠ 0 ∧ x b ≠ 0 := by
  obtain ⟨a, ha⟩ : ∃ a, x a ≠ 0 := by
    by_contra h
    push Not at h
    exact h0 (Finsupp.ext h)
  by_contra hno
  push Not at hno
  have hs : a ∈ x.support.filter (fun b => b.commodity = a.commodity) :=
    Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr ha, rfl⟩
  have hcol : ∑ b ∈ x.support.filter (fun b => b.commodity = a.commodity), x b = 0 := by
    rw [← trialBalance_apply, mem_zeroRows.mp hx, Finsupp.zero_apply]
  refine ha (one_term_change _ (⇑x) (fun _ => (0 : ℚ)) hs ?_ hcol (by simp))
  intro b hb hba
  exact hno a b (Ne.symm hba) (Finset.mem_filter.mp hb).2.symm ha

/-- The same fact read as Ellerman's "change": two distinct zero-rows
    differ in at least two accounts of one commodity. -/
theorem zeroRows_change_two_accounts {x y : PacioliGroup}
    (hx : x ∈ zeroRows) (hy : y ∈ zeroRows) (hne : x ≠ y) :
    ∃ a b : Account, a ≠ b ∧ a.commodity = b.commodity ∧ x a ≠ y a ∧ x b ≠ y b := by
  obtain ⟨a, b, hab, hc, ha, hb⟩ :=
    zeroRow_two_accounts (zeroRows.sub_mem hx hy) (sub_ne_zero.mpr hne)
  refine ⟨a, b, hab, hc, fun h => ha ?_, fun h => hb ?_⟩ <;> simp [h]

/-- A lone posting is a zero-row only when it moves nothing. -/
theorem single_mem_zeroRows_iff (a : Account) (q : ℚ) :
    Finsupp.single a q ∈ zeroRows ↔ q = 0 := by
  rw [mem_zeroRows, trialBalance_single, Finsupp.single_eq_zero]

/-- A two-commodity exchange with no stated price, `10 EUR` against
    `-11 USD`, touches two accounts but not two of one commodity, and
    is not a zero-row. C++ Ledger and the oracle both accept this
    transaction as an implicit exchange (the two-commodity residual
    convention recorded in the `Ledger/Journal.lean` module
    docstring), so an accepted transaction need not be a zero-row. -/
theorem implicit_exchange_not_mem_zeroRows :
    Finsupp.single (⟨"Assets:EUR", "EUR"⟩ : Account) 10
      + Finsupp.single (⟨"Assets:USD", "USD"⟩ : Account) (-11) ∉ zeroRows := by
  rw [mem_zeroRows, map_add, trialBalance_single, trialBalance_single]
  intro h
  have := congrArg (fun v : Commodity →₀ ℚ => v "EUR") h
  simp at this

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

/-- **The free-model form of Ellerman p. 492**: if every journal entry
    is a zero-row, every nonzero derived flow touches two accounts of
    one commodity. The hypothesis is that of `free_double_entry`;
    under the hypothesis of `free_flow_balanced` every flow is zero,
    and the statement would hold vacuously. -/
theorem free_flow_two_accounts (flows : S.Gen → PacioliGroup)
    (hbal : ∀ t, flows t ∈ zeroRows) {A B : Object} (f : FreeHom S A B)
    (h0 : flow flows f ≠ 0) :
    ∃ a b : Account, a ≠ b ∧ a.commodity = b.commodity ∧
      flow flows f a ≠ 0 ∧ flow flows f b ≠ 0 :=
  zeroRow_two_accounts (flow_mem flows zeroRows hbal f) h0

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

/-- The hypotheses of `free_flow_two_accounts` are jointly
    satisfiable: one generator moving a dollar from cash to food.
    This is not a witness of the D16 finding; it stands in this
    section only because it uses `unitSpec` and `someAccount`. -/
example : ∃ flows : unitSpec.Gen → PacioliGroup, (∀ t, flows t ∈ zeroRows) ∧
    flow flows (⟦.gen PUnit.unit⟧ : FreeHom unitSpec _ _) ≠ 0 := by
  refine ⟨fun _ => Finsupp.single (⟨"Expenses:Food", "USD"⟩ : Account) 1
      - Finsupp.single someAccount 1, fun _ => ?_, ?_⟩
  · rw [mem_zeroRows, map_sub, trialBalance_single, trialBalance_single]
    simp [someAccount]
  · rw [flow_gen]
    intro h
    have := congrArg (fun v : PacioliGroup => v someAccount) h
    simp [someAccount] at this

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

/-- The valuation of `oneFlow` at `someAccount` measures the generator
    of `unitSpec` as `1`. The generator is a morphism `0 ⟶ 0`, so its
    two ends are the same object and carry no information about its
    flow. -/
theorem oneFlow_gen_measure :
    (accountValuation oneFlow someAccount).V
      (⟦.gen PUnit.unit⟧ : FreeHom unitSpec 0 0) = 1 := by
  show ((flow oneFlow (⟦.gen PUnit.unit⟧ : FreeHom unitSpec _ _))
    someAccount : ℝ) = 1
  rw [flow_gen]
  simp [oneFlow]

/-- **The endpoint law is refuted**: it is not the case that every
    valuation of every lawful model is the difference of an object
    measure across each morphism. The witness is the generator of
    `unitSpec`, a morphism from the empty object to itself that the
    valuation measures as `1` (`oneFlow_gen_measure`), so the
    difference form fails on the generator itself and the zero
    morphism plays no part. What the theorem adds to
    `ValuationFunctor.endpoint_measure_degenerates` is a lawful model
    with a nonzero valuation: the degeneracy theorem excludes a
    valuation that exists, not merely a hypothetical one. -/
theorem endpoint_law_refuted :
    ¬ (∀ (T : 𝕋) (_ : 𝕋Laws T) (W : ValuationFunctor T),
        ∃ φ : Object → ℝ,
          ∀ {A B : Object} (f : T.Hom A B), W.V f = φ B - φ A) := by
  intro hlaw
  obtain ⟨φ, hφ⟩ := hlaw (freeT unitSpec) (freeLaws unitSpec)
    (accountValuation oneFlow someAccount)
  have h := (accountValuation oneFlow someAccount).endpoint_measure_degenerates
    φ hφ (⟦.gen PUnit.unit⟧ : FreeHom unitSpec 0 0)
  rw [oneFlow_gen_measure] at h
  exact one_ne_zero h

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
