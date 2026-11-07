import Ledger.Conversion

/-!
# Closing the books as an ordinary zero-row

Ellerman, "On Double-Entry Bookkeeping: The Mathematical Treatment",
Accounting Education 23:5 (2014), note 11 (pp. 499-500): one adds "a
credit-balance revenue account and a debit-balance expenses account",
and "another transaction or two at the end of the period would 'close
the income statement into the balance sheet' by making the changes to
equity and resetting the zero balance in the revenue and expense
accounts". Page 493 records that in Ijiri's system "the temporary or
nominal accounts could not be closed". That nothing other than
temporary and equity accounts changes is a formalization of the note,
not a quotation.

`ClosesBooks` (`Ledger/Derived.lean`) is unchanged, since its docstring
is accurate. It is weak, because it constrains a closing only through
three views (`ClosesBooks.of_invisible` shows how weak). The exclusivity
that this module reads into the note is stated at L1 instead: the
closing entry of a ledger state reverses every temporary balance and
adds that reversal's equity leg, which posts the negation of its
per-commodity residual to one equity account per commodity. It is the
completion (`Ledger/Conversion.lean`) of the reversed temporary
balances, so it is a zero-row (`closingEntry_mem_zeroRows`) and it
touches only temporary and equity accounts (`closingEntry_support`);
when no equity account is itself temporary, it resets every temporary
account (`closingEntry_resets`) and moves into equity exactly each
commodity's column of the temporary balances (`closingEntry_equity`).
`GenSpec.closesBooks_of_closingEntry` bridges it to `ClosesBooks` in the
free model, and `ClosingDemo` applies that bridge to a period whose
revenue is nonzero.
-/

namespace Ledger

noncomputable section

/-! ## The abstract notion is weak -/

section Abstract

variable {T : 𝕋}

/-- Documentary: `ClosesBooks` constrains a closing only through its
    three views, so any morphism those views cannot see closes the empty
    period. -/
theorem ClosesBooks.of_invisible (L : 𝕋Laws T)
    {Wrev Wexp Weq : ValuationFunctor T} {A C : Object} (c : T.Hom A C)
    (hr : Wrev.V c = 0) (he : Wexp.V c = 0) (hq : Weq.V c = 0) :
    ClosesBooks Wrev Wexp Weq (T.id A) c where
  rev_zeroed := by rw [Wrev.V_comp, hr, Wrev.V_id L, add_zero]
  exp_zeroed := by rw [Wexp.V_comp, he, Wexp.V_id L, add_zero]
  balanced := by rw [hr, he, hq, add_zero, add_zero]

end Abstract

/-! ## The closing entry at L1 -/

section ClosingEntry

variable (temp : Account → Prop) [DecidablePred temp] (eq : AccountName)

/-- The closing entry of a ledger state `x`: reverse every temporary
    balance and complete the reversal into the equity accounts
    `⟨eq, c⟩`, one per commodity. -/
def closingEntry (x : PacioliGroup) : PacioliGroup :=
  completion eq (-(x.filter temp))

variable {temp eq}

theorem closingEntry_apply (x : PacioliGroup) :
    closingEntry temp eq x
      = -(x.filter temp) + conversionLeg eq (trialBalance (x.filter temp)) := by
  rw [closingEntry, completion_apply, map_neg, map_neg, sub_neg_eq_add]

/-- **Closing is a zero-row**: the trial balance is preserved in every
    commodity. -/
theorem closingEntry_mem_zeroRows (x : PacioliGroup) :
    closingEntry temp eq x ∈ zeroRows :=
  completion_mem_zeroRows eq _

theorem conversionLeg_apply_of_name_ne (r : Commodity →₀ ℚ) {a : Account}
    (ha : a.name ≠ eq) : conversionLeg eq r a = 0 := by
  have hr : a ∉ Set.range fun c => (⟨eq, c⟩ : Account) := by
    rintro ⟨c, rfl⟩
    exact ha rfl
  exact Finsupp.mapDomain_notin_range _ _ hr

theorem closingEntry_apply_of_temp (he : ∀ c, ¬ temp ⟨eq, c⟩)
    (x : PacioliGroup) {a : Account} (ha : temp a) :
    closingEntry temp eq x a = -x a := by
  have hn : a.name ≠ eq := fun h => he a.commodity (by rw [← h]; exact ha)
  rw [closingEntry_apply, Finsupp.add_apply, Finsupp.neg_apply,
    Finsupp.filter_apply_pos _ _ ha, conversionLeg_apply_of_name_ne _ hn, add_zero]

theorem closingEntry_apply_of_not (x : PacioliGroup) {a : Account}
    (ht : ¬ temp a) (hn : a.name ≠ eq) :
    closingEntry temp eq x a = 0 := by
  rw [closingEntry_apply, Finsupp.add_apply, Finsupp.neg_apply,
    Finsupp.filter_apply_neg _ _ ht, conversionLeg_apply_of_name_ne _ hn,
    neg_zero, add_zero]

/-- **The closing resets every temporary account to zero.** -/
theorem closingEntry_resets (he : ∀ c, ¬ temp ⟨eq, c⟩)
    (x : PacioliGroup) {a : Account} (ha : temp a) :
    (x + closingEntry temp eq x) a = 0 := by
  rw [Finsupp.add_apply, closingEntry_apply_of_temp he x ha, add_neg_cancel]

/-- **Only temporary and equity accounts change.** -/
theorem closingEntry_support (x : PacioliGroup) :
    ((closingEntry temp eq x).support : Set Account)
      ⊆ {a | temp a} ∪ {a | a.name = eq} := by
  intro a ha
  by_contra h
  rw [Set.mem_union, Set.mem_setOf_eq, Set.mem_setOf_eq, not_or] at h
  rw [Finset.mem_coe, Finsupp.mem_support_iff] at ha
  exact ha (closingEntry_apply_of_not x h.1 h.2)

/-- **The changes to equity**: each commodity's equity account receives
    that commodity's column of the temporary balances. -/
theorem closingEntry_equity (he : ∀ c, ¬ temp ⟨eq, c⟩) (x : PacioliGroup)
    (c : Commodity) :
    closingEntry temp eq x ⟨eq, c⟩ = trialBalance (x.filter temp) c := by
  have hinj : Function.Injective fun c : Commodity => (⟨eq, c⟩ : Account) :=
    fun c d h => congrArg Account.commodity h
  rw [closingEntry_apply, Finsupp.add_apply, Finsupp.neg_apply,
    Finsupp.filter_apply_neg _ _ (he c), neg_zero, zero_add, conversionLeg,
    Finsupp.mapDomain.addMonoidHom_apply, Finsupp.mapDomain_apply hinj]

/-- A trial-balance column, computed over any finite set of accounts
    that covers the support and lies in that commodity. -/
theorem trialBalance_apply_eq_sum (x : PacioliGroup) (s : Finset Account)
    (hs : x.support ⊆ s) (k : Commodity) (hk : ∀ a ∈ s, a.commodity = k) :
    trialBalance x k = ∑ a ∈ s, x a := by
  rw [trialBalance, Finsupp.mapDomain.addMonoidHom_apply, Finsupp.mapDomain,
    Finsupp.sum_apply, Finsupp.sum_of_support_subset x hs]
  · refine Finset.sum_congr rfl fun a ha => ?_
    rw [hk a ha, Finsupp.single_eq_same]
  · intro a _
    rw [Finsupp.single_zero, Finsupp.coe_zero, Pi.zero_apply]

end ClosingEntry

/-! ## The bridge: an L1 closing entry closes the books in the free model -/

namespace GenSpec

variable {S : GenSpec} (flows : S.Gen → PacioliGroup)

open ValuationFunctor in
/-- A morphism whose flow is the L1 closing entry of the period's flow
    satisfies `ClosesBooks` for the revenue, expense and equity views of
    one commodity. The closing flow is a hypothesis, which avoids
    defining a generator's flow from the period's own flow. -/
theorem closesBooks_of_closingEntry (rev exp : Finset Account)
    (hdisj : Disjoint rev exp) (k : Commodity)
    (hk : ∀ a ∈ rev ∪ exp, a.commodity = k) (eq : AccountName)
    (hek : (⟨eq, k⟩ : Account) ∉ rev ∪ exp)
    {A B C : Object} (f : (freeT S).Hom A B) (c : (freeT S).Hom B C)
    (hc : flow flows c = closingEntry (· ∈ rev ∪ exp) eq (flow flows f)) :
    ClosesBooks (finsetSum rev (accountValuation flows))
      (finsetSum exp (accountValuation flows))
      (accountValuation flows ⟨eq, k⟩) f c := by
  have he : ∀ c', ¬ ((⟨eq, c'⟩ : Account) ∈ rev ∪ exp) := by
    intro c' h
    have h' := hk _ h
    subst h'
    exact hek h
  set x := flow flows f
  have hsupp : (x.filter (· ∈ rev ∪ exp)).support ⊆ rev ∪ exp := by
    intro a ha
    rw [Finsupp.support_filter, Finset.mem_filter] at ha
    exact ha.2
  refine ⟨?_, ?_, ?_⟩
  · show ∑ a ∈ rev, ((flow flows ((freeT S).comp c f) a : ℚ) : ℝ) = 0
    refine Finset.sum_eq_zero fun a ha => ?_
    rw [flow_comp, hc, Finsupp.add_apply,
      closingEntry_apply_of_temp he x (Finset.mem_union_left _ ha),
      neg_add_cancel, Rat.cast_zero]
  · show ∑ a ∈ exp, ((flow flows ((freeT S).comp c f) a : ℚ) : ℝ) = 0
    refine Finset.sum_eq_zero fun a ha => ?_
    rw [flow_comp, hc, Finsupp.add_apply,
      closingEntry_apply_of_temp he x (Finset.mem_union_right _ ha),
      neg_add_cancel, Rat.cast_zero]
  · show ∑ a ∈ rev, ((flow flows c a : ℚ) : ℝ) + ∑ a ∈ exp, ((flow flows c a : ℚ) : ℝ)
        + ((flow flows c ⟨eq, k⟩ : ℚ) : ℝ) = 0
    rw [hc]
    have hrev : ∑ a ∈ rev, closingEntry (· ∈ rev ∪ exp) eq x a = -∑ a ∈ rev, x a := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun a ha =>
        closingEntry_apply_of_temp he x (Finset.mem_union_left _ ha)
    have hexp : ∑ a ∈ exp, closingEntry (· ∈ rev ∪ exp) eq x a = -∑ a ∈ exp, x a := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun a ha =>
        closingEntry_apply_of_temp he x (Finset.mem_union_right _ ha)
    have hfil : ∑ a ∈ rev ∪ exp, (x.filter (· ∈ rev ∪ exp)) a = ∑ a ∈ rev ∪ exp, x a :=
      Finset.sum_congr rfl fun a ha => Finsupp.filter_apply_pos _ _ ha
    have heq : closingEntry (· ∈ rev ∪ exp) eq x ⟨eq, k⟩
        = ∑ a ∈ rev, x a + ∑ a ∈ exp, x a := by
      rw [closingEntry_equity he, trialBalance_apply_eq_sum _ _ hsupp k hk, hfil,
        Finset.sum_union hdisj]
    have key : ∑ a ∈ rev, closingEntry (· ∈ rev ∪ exp) eq x a
        + ∑ a ∈ exp, closingEntry (· ∈ rev ∪ exp) eq x a
        + closingEntry (· ∈ rev ∪ exp) eq x ⟨eq, k⟩ = 0 := by
      rw [hrev, hexp, heq]
      abel
    exact_mod_cast key

end GenSpec

/-! ## A non-degenerate inhabitant in the free model -/

namespace ClosingDemo

open GenSpec

def cash : Account := ⟨"Assets:Checking", "$"⟩
def revenue : Account := ⟨"Income:Sales", "$"⟩
def expense : Account := ⟨"Expenses:Wages", "$"⟩
/-- The retained-earnings account name; one account per commodity. -/
def retained : AccountName := "Equity:Retained"

inductive Entry where
  | sale
  | wage
  | close
  deriving DecidableEq

/-- The closing generator's domain is the period's codomain. -/
def spec : GenSpec where
  Gen := Entry
  dom
    | .sale => {revenue}
    | .wage => {cash}
    | .close => {cash} + {expense}
  cod
    | .sale => {cash}
    | .wage => {expense}
    | .close => {⟨retained, "$"⟩}

/-- Debit-positive flows: a sale of 100 and wages of 30 in the period,
    then the closing entry, which zeroes revenue and expense and credits
    equity with the net income of 70. -/
def flows : Entry → PacioliGroup
  | .sale => Finsupp.single cash 100 + Finsupp.single revenue (-100)
  | .wage => Finsupp.single expense 30 + Finsupp.single cash (-30)
  | .close => Finsupp.single revenue 100 + Finsupp.single expense (-30)
      + Finsupp.single ⟨retained, "$"⟩ (-70)

def period : (freeT spec).Hom ({revenue} + {cash}) ({cash} + {expense}) :=
  (freeT spec).tensor (genHom (S := spec) Entry.sale) (genHom (S := spec) Entry.wage)

def closing : (freeT spec).Hom ({cash} + {expense}) {⟨retained, "$"⟩} :=
  genHom (S := spec) Entry.close

abbrev temps : Finset Account := {revenue} ∪ {expense}

theorem period_flow : flow flows period = flows .sale + flows .wage := rfl

theorem closing_flow : flow flows closing = flows .close := rfl

theorem revenue_mem : revenue ∈ temps := by
  rw [Finset.mem_union, Finset.mem_singleton, Finset.mem_singleton]
  exact Or.inl rfl

theorem expense_mem : expense ∈ temps := by
  rw [Finset.mem_union, Finset.mem_singleton, Finset.mem_singleton]
  exact Or.inr rfl

theorem cash_not_mem : cash ∉ temps := by
  rw [Finset.mem_union, Finset.mem_singleton, Finset.mem_singleton]
  decide

theorem retained_not_mem : (⟨retained, "$"⟩ : Account) ∉ temps := by
  rw [Finset.mem_union, Finset.mem_singleton, Finset.mem_singleton]
  decide

theorem cash_name_ne : cash.name ≠ retained := by decide

/-- The closing generator's flow is exactly the L1 closing entry of the
    period's flow. -/
theorem closing_is_closingEntry :
    flow flows closing = closingEntry (· ∈ temps) retained (flow flows period) := by
  rw [closing_flow, period_flow, closingEntry_apply]
  simp only [flows, Finsupp.filter_add, Finsupp.filter_single_of_pos _ revenue_mem,
    Finsupp.filter_single_of_pos _ expense_mem, Finsupp.filter_single_of_neg _ cash_not_mem,
    zero_add, add_zero, map_add, trialBalance_single, conversionLeg_single]
  have hr : revenue.commodity = "$" := rfl
  have he : expense.commodity = "$" := rfl
  rw [hr, he, neg_add, ← Finsupp.single_neg, ← Finsupp.single_neg, neg_neg,
    ← Finsupp.single_add]
  norm_num

theorem rev_ne_cash : revenue ≠ cash := by decide
theorem rev_ne_exp : revenue ≠ expense := by decide
theorem exp_ne_cash : expense ≠ cash := by decide
theorem exp_ne_rev : expense ≠ revenue := by decide
theorem ret_ne_cash : (⟨retained, "$"⟩ : Account) ≠ cash := by decide
theorem ret_ne_rev : (⟨retained, "$"⟩ : Account) ≠ revenue := by decide
theorem ret_ne_exp : (⟨retained, "$"⟩ : Account) ≠ expense := by decide

theorem temps_disjoint : Disjoint ({revenue} : Finset Account) {expense} :=
  Finset.disjoint_singleton.mpr rev_ne_exp

theorem temps_commodity : ∀ a ∈ temps, a.commodity = "$" := by
  intro a ha
  rw [Finset.mem_union, Finset.mem_singleton, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl <;> rfl

/-- The revenue view: the sum over the one revenue account, in `$`. -/
abbrev Wrev : ValuationFunctor (freeT spec) :=
  ValuationFunctor.finsetSum {revenue} (accountValuation flows)
/-- The expense view: the sum over the one expense account, in `$`. -/
abbrev Wexp : ValuationFunctor (freeT spec) :=
  ValuationFunctor.finsetSum {expense} (accountValuation flows)
/-- The equity view: the retained-earnings account in `$`. -/
abbrev Weq : ValuationFunctor (freeT spec) := accountValuation flows ⟨retained, "$"⟩

/-- **The inhabitant**: the closing generator closes the period's
    books. -/
theorem demo_closesBooks : ClosesBooks Wrev Wexp Weq period closing := by
  -- Stated as a term, this proof times out in `whnf` at the default
  -- heartbeat limit; elaborating it inside a tactic block avoids that.
  have h := closesBooks_of_closingEntry flows {revenue} {expense} temps_disjoint "$"
    temps_commodity retained retained_not_mem period closing closing_is_closingEntry
  exact h

/-- The period has nonzero revenue, so the witness is not the
    degenerate empty-period closing of `ClosesBooks.of_invisible`. -/
theorem period_revenue : Wrev.V period = -100 := by
  show ∑ a ∈ ({revenue} : Finset Account), ((flow flows period a : ℚ) : ℝ) = -100
  rw [Finset.sum_singleton, period_flow]
  simp only [flows, Finsupp.add_apply, Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne rev_ne_cash, Finsupp.single_eq_of_ne rev_ne_exp]
  norm_num

theorem period_expense : Wexp.V period = 30 := by
  show ∑ a ∈ ({expense} : Finset Account), ((flow flows period a : ℚ) : ℝ) = 30
  rw [Finset.sum_singleton, period_flow]
  simp only [flows, Finsupp.add_apply, Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne exp_ne_cash, Finsupp.single_eq_of_ne exp_ne_rev]
  norm_num

theorem period_equity : Weq.V period = 0 := by
  show ((flow flows period ⟨retained, "$"⟩ : ℚ) : ℝ) = 0
  rw [period_flow]
  simp only [flows, Finsupp.add_apply, Finsupp.single_eq_of_ne ret_ne_cash,
    Finsupp.single_eq_of_ne ret_ne_rev, Finsupp.single_eq_of_ne ret_ne_exp]
  norm_num

theorem revenue_nonzero : Wrev.V period ≠ 0 := by
  rw [period_revenue]
  norm_num

/-- `closing_transfers_net_income` at a satisfiable, non-degenerate
    hypothesis: equity absorbs the net income of 70, a credit, hence
    negative in the debit-positive convention. -/
theorem demo_net_income_closed :
    Weq.V ((freeT spec).comp closing period) = -70 := by
  rw [closing_transfers_net_income demo_closesBooks, period_equity, period_revenue,
    period_expense]
  norm_num

/-- Cash reads the same after the closing as before it. -/
theorem demo_cash_preserved :
    (accountValuation flows cash).V ((freeT spec).comp closing period)
      = (accountValuation flows cash).V period := by
  show ((flow flows ((freeT spec).comp closing period) cash : ℚ) : ℝ)
    = ((flow flows period cash : ℚ) : ℝ)
  rw [flow_comp, Finsupp.add_apply, closing_is_closingEntry,
    closingEntry_apply_of_not _ cash_not_mem cash_name_ne, zero_add]

/-- The closing generator touches only the temporary accounts and the
    equity accounts (`closingEntry_support`, read on the demo). -/
theorem demo_closing_support :
    ((flow flows closing).support : Set Account)
      ⊆ {a | a ∈ temps} ∪ {a | a.name = retained} := by
  rw [closing_is_closingEntry]
  exact closingEntry_support _

end ClosingDemo

end

end Ledger
