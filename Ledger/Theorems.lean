import Mathlib.Tactic.Linarith
import Ledger.Valuation
import Ledger.Derivation
import Ledger.Hierarchy
import Ledger.Prices

/-!
# Fundamental theorems (K3)

The laws with downstream force from the design worksheet §3, stated
over the abstract `𝕋` and proved from `𝕋Laws`, the valuation-functor
laws, and — where the theorem is genuinely about *journals* rather
than arbitrary models — the `Generated` induction principle.

## The shape of the double-entry results

Phase 1 stated `double_entry_invariant` for a bare `𝕋` and could not
prove it: nothing in `𝕋Laws` prevents a model with an unbalanced
generator. The missing hypothesis is the one every accountant states
first: **the journal's atomic entries balance**. Formally: `T` is
generated (`𝕋.Generated`) and each generator is annihilated by the
valuation. The master theorem `balanced_generators_balance` then
propagates balance through every operation — that propagation is
exactly what the valuation functor laws are *for* — and the named
invariants (double-entry, trial balance, Pacioli, roll-up
preservation) are corollaries.

Every Phase 1 `sorry` and every `True`-stub is gone; each theorem
below is a real statement with a checked proof.
-/

namespace Ledger

open ValuationFunctor

section DoubleEntry

variable (T : 𝕋) (G : 𝕋.Generated T) (W : ValuationFunctor T)

/-- **The master balance theorem**: if every atomic generator is
    balanced, every morphism of the generated groupoid is balanced.
    Induction over `Generated`; the functor laws discharge every
    constructor. This is "you cannot build an unbalanced flow out of
    balanced entries" — the soundness of double-entry bookkeeping. -/
theorem balanced_generators_balance (L : 𝕋Laws T)
    (hgen : ∀ {A B : Object} (f : T.Hom A B), G.IsGen f → W.V f = 0)
    {A B : Object} (f : T.Hom A B) : W.V f = 0 := by
  refine G.induction (fun {A B} f => W.V f = 0) hgen
    (fun A => W.V_id L A)
    (fun A B => W.V_zero A B)
    (fun g f hg hf => ?_)
    (fun f hf => ?_)
    (fun f g hf hg => ?_)
    (fun f g hf hg => ?_)
    f
  · simp only [W.V_comp, hg, hf, add_zero]
  · simp only [W.V_inv L, hf, neg_zero]
  · simp only [W.V_tensor, hf, hg, add_zero]
  · simp only [W.V_add, hf, hg, add_zero]

/-- **The double-entry invariant** (worksheet §1, identity test): a
    transaction out of the empty account multiset — an "opening
    balance with no offset" — moves nothing. The Phase 1 statement,
    now a corollary of the master theorem. -/
theorem double_entry_invariant (L : 𝕋Laws T)
    (hgen : ∀ {A B : Object} (f : T.Hom A B), G.IsGen f → W.V f = 0)
    {A : Object} (f : T.Hom 0 A) : W.V f = 0 :=
  balanced_generators_balance T G W L hgen f

end DoubleEntry

section TrialBalance

variable (T : 𝕋) (G : 𝕋.Generated T)

/-- **Trial balance**: measure each account with its own valuation
    functor; if every journal entry's postings sum to zero across
    accounts (the definition of a balanced entry), then so do the
    per-account totals of every derived flow. -/
theorem trial_balance (L : 𝕋Laws T) {ι : Type*} (s : Finset ι)
    (Ws : ι → ValuationFunctor T)
    (hgen : ∀ {A B : Object} (f : T.Hom A B), G.IsGen f →
      ∑ i ∈ s, (Ws i).V f = 0)
    {A B : Object} (f : T.Hom A B) :
    ∑ i ∈ s, (Ws i).V f = 0 := by
  have h := balanced_generators_balance T G (finsetSum s Ws) L
    (fun f hf => by simpa using hgen f hf) f
  simpa using h

/-- **The Pacioli equation**: Assets = Liabilities + Equity.

    Accounts are split into three classes; per-account flows are
    measured debit-positive. Liabilities and equity are reported
    credit-positive (the negations on the right). Given balanced
    journal entries, the equation holds for every derived flow —
    it is the trial balance, rearranged. -/
theorem pacioli_equation (L : 𝕋Laws T) {ι : Type*}
    (assets liabs eqs : Finset ι) (Ws : ι → ValuationFunctor T)
    (hgen : ∀ {A B : Object} (f : T.Hom A B), G.IsGen f →
      (∑ i ∈ assets, (Ws i).V f) + (∑ i ∈ liabs, (Ws i).V f)
        + (∑ i ∈ eqs, (Ws i).V f) = 0)
    {A B : Object} (f : T.Hom A B) :
    ∑ i ∈ assets, (Ws i).V f
      = (∑ i ∈ liabs, -(Ws i).V f) + (∑ i ∈ eqs, -(Ws i).V f) := by
  have h := balanced_generators_balance T G
    (finsetSum assets Ws + finsetSum liabs Ws + finsetSum eqs Ws) L
    (fun f hf => by simpa using hgen f hf) f
  simp only [add_V, finsetSum_V] at h
  rw [Finset.sum_neg_distrib, Finset.sum_neg_distrib]
  linarith

end TrialBalance

section CompositionOrder

variable {T : 𝕋}

/-- The aggregate valuation of a composition chain, entry by entry. -/
def 𝕋.Path.valuationSum (W : ValuationFunctor T) :
    {A B : Object} → T.Path A B → ℝ
  | _, _, .nil _ => 0
  | _, _, .cons g rest => W.V g + rest.valuationSum W

/-- The flow of a composed chain is the entry-by-entry sum. -/
theorem 𝕋.Path.V_compose (L : 𝕋Laws T) (W : ValuationFunctor T) :
    ∀ {A B : Object} (p : T.Path A B), W.V p.compose = p.valuationSum W := by
  intro A B p
  induction p with
  | nil => simp [𝕋.Path.valuationSum, W.V_id L]
  | cons g rest ih =>
      simp [𝕋.Path.valuationSum, W.V_comp, ih]

/-- **Balance-sheet independence of composition order** (worksheet
    §3): any two ways of assembling the same total flow from
    individual transactions report the same aggregate valuation.
    Without this, `balance` over a date range would depend on how the
    journal file groups entries. -/
theorem balance_sheet_independent_of_composition_order
    (L : 𝕋Laws T) (W : ValuationFunctor T) {A B : Object}
    (p q : T.Path A B) (h : p.compose = q.compose) :
    p.valuationSum W = q.valuationSum W := by
  rw [← p.V_compose L W, ← q.V_compose L W, h]

end CompositionOrder

section Reversal

variable (T : 𝕋) (W : ValuationFunctor T)

/-- **Reversal correctness**: composing a transaction with its
    reversal yields the identity flow — zero. -/
theorem reversal_correctness (L : 𝕋Laws T) {A B : Object} (f : T.Hom A B) :
    W.V (T.comp f (T.inv f)) = 0 := by
  rw [L.comp_inv, W.V_id L]

/-- **Aggregation correctness** (T16): the flow of an aggregate is the
    sum of the flows — the valuation-functor law, re-exported under
    its worksheet name. -/
theorem aggregation_correctness {A B : Object} (f g : T.Hom A B) :
    W.V (f + g) = W.V f + W.V g :=
  W.V_add f g

end Reversal

section Hierarchy

variable (T : 𝕋) (W : ValuationFunctor T)
variable {F : AccountForest} (R : RollupFunctor F T)

/-- **Roll-up preservation** (H1, edge-local form): if each parent-edge
    roll-up is balanced, rolling up along any ancestor chain is
    balanced — moving a child's balance into its parent, transitively,
    neither creates nor destroys value. This is what makes the balance
    sheet (the colimit over the forest) well-defined: roll up then
    sum, or sum directly — same answer. -/
theorem rollup_chain_preserves_valuation (L : 𝕋Laws T)
    (hedges : ∀ (a b : F.Account) (h : F.parent a = some b),
      W.V (R.rollup a b h) = 0)
    {a c : F.Account} (ch : F.ParentChain a c) :
    W.V (R.rollupChain ch) = 0 := by
  induction ch with
  | refl a => exact W.V_id L _
  | step h rest ih =>
      rw [R.rollupChain_step, W.V_comp, ih, hedges, add_zero]

/-- Roll-up preservation for a single edge, as a corollary of the
    master theorem: in a generated groupoid with balanced generators,
    roll-up morphisms — like every morphism — are balanced. -/
theorem rollup_preserves_valuation (L : 𝕋Laws T) (G : 𝕋.Generated T)
    (hgen : ∀ {A B : Object} (f : T.Hom A B), G.IsGen f → W.V f = 0)
    (a b : F.Account) (h : F.parent a = some b) :
    W.V (R.rollup a b h) = 0 :=
  balanced_generators_balance T G W L hgen _

end Hierarchy

section Derivation

variable (T : 𝕋) (W : ValuationFunctor T)

/-- **Derivation soundness** (D1): applying auto-xact rules with
    balanced templates never changes the measured flow — auto-xacts
    reclassify value, they do not create or destroy it. -/
theorem derivation_soundness (rules : List (DerivationRule T))
    (templates_balance : ∀ r ∈ rules, W.V r.template = 0)
    {A B A' B' : Object} {f : T.Hom A B} {f' : T.Hom A' B'}
    (h : Derives T rules f f') :
    W.V f' = W.V f :=
  derivation_preserves_valuation T W rules h templates_balance

end Derivation

section Prices

/-- **Price soundness** (P1): revaluing a transaction through a
    conversion `p : a → b` scales its `b`-denominated measurement by
    `rate p` from its `a`-denominated one — the correctness of `-V`
    and `-X` reports. Re-exported from the action's soundness law;
    see also `PriceAction.revalue_sound_comp` (chained conversions
    multiply) and `PriceAction.revalue_roundtrip`. -/
theorem price_soundness (P : PriceGroupoid) (T : 𝕋)
    (CV : CommodityValuation T) (act : PriceAction P T CV)
    {a b : Commodity} (p : P.Conversion a b)
    {A B : Object} (f : T.Hom A B) :
    (CV b).V (act.revalue p f) = P.rate p * (CV a).V f :=
  act.revalue_sound p f

end Prices

end Ledger
