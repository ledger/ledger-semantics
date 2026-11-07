import Mathlib.Tactic.DeriveFintype
import Ledger.Derived

/-!
# Decoding by balance side

Ellerman, "On Double-Entry Bookkeeping: The Mathematical Treatment",
Accounting Education 23:5 (2014). On p. 486 each T-account is labeled
debit-balance or credit-balance; on p. 496 the accounts of the final
zero-account equation are partitioned by the side of the initial
equation from which they were encoded; note 11 (pp. 499-500, an aside)
adds a credit-balance revenue account and a debit-balance expense
account.

Prose here says "balance side" rather than "label", because
`Ledger/Labels.lean` already uses "label" for transaction metadata.
Measurements in this project are debit-positive (the debit isomorphism
applied to every account), so `Side.decode .credit` is the change from
the debit isomorphism to the credit isomorphism; that is the
definition of "reported credit-positive" that `balance_sheet_equation`
leaves to its docstring.

For every side function the decoded equation is equivalent to the
trial balance (`decoded_iff_trial`), so it holds for every side
function once the journal entries balance (`decoded_balance_sheet`):
the side chooses presentation, not truth, which is Ellerman's point
about the two isomorphisms. The side-based form follows from
`balance_sheet_equation` (`decoded_of_balance_sheet`), and conversely
`balance_sheet_equation` for pairwise disjoint classes follows from the
side-based form (`balance_sheet_of_decoded`), so the new content is a
definition with disjointness and coverage built in, not a stronger
theorem. The five-class form through `AccountClass`, the
per-commodity `ChartOfAccounts`, and the closing bridge follow.

This is specification only. C++ Ledger has no account types, so
nothing here is bisimulated, and nothing about sides may reach the
executable layer without a witness. It lives in its own leaf rather
than in `Basic`, which the executable layer imports.
-/

namespace Ledger

/-! ## Balance sides and decoding -/

/-- Ellerman's balance side: the side of the initial equation from
    which an account comes (p. 496). A fixed attribute of an account,
    not the sign of its balance. -/
inductive Side
  | debit
  | credit
  deriving DecidableEq, Repr, Inhabited

namespace Side

/-- Decoding by balance side. Measurements in this project are already
    debit-positive (the debit isomorphism applied to every account), so
    `decode .credit` is the change from the debit isomorphism to the
    credit isomorphism, not the decoding of a T-account. This is the
    definition of "reported credit-positive". -/
def decode {α : Type*} [Neg α] : Side → α → α
  | .debit, x => x
  | .credit, x => -x

@[simp] theorem decode_debit {α : Type*} [Neg α] (x : α) :
    Side.debit.decode x = x := rfl

@[simp] theorem decode_credit {α : Type*} [Neg α] (x : α) :
    Side.credit.decode x = -x := rfl

/-- Decoding commutes with finite sums. -/
theorem decode_sum {ι M : Type*} [AddCommGroup M] (d : Side)
    (s : Finset ι) (x : ι → M) :
    d.decode (∑ i ∈ s, x i) = ∑ i ∈ s, d.decode (x i) := by
  cases d <;> simp [Finset.sum_neg_distrib]

/-- Every side is debit or credit; used to identify the complement of
    the debit filter with the credit filter. -/
theorem ne_debit_iff (d : Side) : d ≠ .debit ↔ d = .credit := by
  cases d <;> simp

end Side

/-! ## The decoded equation is the trial balance -/

section Decoded

variable {ι M : Type*} [AddCommGroup M]

/-- A side function partitions any finite set of accounts into its
    debit-side and credit-side parts: coverage and disjointness hold by
    construction. -/
theorem sum_debit_add_sum_credit (s : Finset ι) (side : ι → Side)
    (x : ι → M) :
    (∑ i ∈ s with side i = .debit, x i)
      + (∑ i ∈ s with side i = .credit, x i) = ∑ i ∈ s, x i := by
  rw [← Finset.sum_filter_add_sum_filter_not s (fun i => side i = .debit) x]
  congr 1
  exact Finset.sum_congr
    (Finset.filter_congr (fun i _ => (Side.ne_debit_iff (side i)).symm))
    (fun _ _ => rfl)

theorem sum_decode_debit (s : Finset ι) (side : ι → Side) (x : ι → M) :
    ∑ i ∈ s with side i = .debit, (side i).decode (x i)
      = ∑ i ∈ s with side i = .debit, x i :=
  Finset.sum_congr rfl fun i hi => by
    rw [(Finset.mem_filter.mp hi).2]; rfl

theorem sum_decode_credit (s : Finset ι) (side : ι → Side) (x : ι → M) :
    ∑ i ∈ s with side i = .credit, (side i).decode (x i)
      = -∑ i ∈ s with side i = .credit, x i := by
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i hi => by
    rw [(Finset.mem_filter.mp hi).2]; rfl

/-- **The decoded equation is the trial balance.** For every side
    function, debit-side accounts reported debit-positive equal
    credit-side accounts reported credit-positive exactly when the
    debit-positive measurements sum to zero. Since the right side does
    not mention `side`, the side chooses presentation, not truth. -/
theorem decoded_iff_trial (s : Finset ι) (side : ι → Side) (x : ι → M) :
    (∑ i ∈ s with side i = .debit, (side i).decode (x i)
      = ∑ i ∈ s with side i = .credit, (side i).decode (x i))
    ↔ ∑ i ∈ s, x i = 0 := by
  rw [sum_decode_debit, sum_decode_credit, ← sum_debit_add_sum_credit s side x]
  exact eq_neg_iff_add_eq_zero

end Decoded

/-! ## The decoded balance sheet over the groupoid -/

section BalanceSheet

variable (T : 𝕋) (G : 𝕋.Generated T)

/-- **The decoded balance-sheet equation.** Given balanced journal
    entries, every derived flow satisfies the decoded equation for every
    side function. The side is quantified before the flow `f`: it is a
    fixed attribute of the account. -/
theorem decoded_balance_sheet (L : 𝕋Laws T) {ι : Type*} (s : Finset ι)
    (side : ι → Side) (Ws : ι → ValuationFunctor T)
    (hgen : ∀ {A B : Object} (f : T.Hom A B), G.IsGen f →
      ∑ i ∈ s, (Ws i).V f = 0)
    {A B : Object} (f : T.Hom A B) :
    ∑ i ∈ s with side i = .debit, (side i).decode ((Ws i).V f)
      = ∑ i ∈ s with side i = .credit, (side i).decode ((Ws i).V f) :=
  (decoded_iff_trial s side (fun i => (Ws i).V f)).mpr
    (trial_balance T G L s Ws hgen f)

/-- The side-based form follows from `balance_sheet_equation` itself
    (assets := debit part, liabilities := credit part, equity := ∅), so
    the new content is the definition of "credit-positive", not a
    stronger theorem. The statement coincides with that of
    `decoded_balance_sheet`; only the proof differs, going through
    `balance_sheet_equation` rather than `trial_balance`, so the
    dependency shows in the proof term and not in the type. -/
theorem decoded_of_balance_sheet (L : 𝕋Laws T) {ι : Type*} (s : Finset ι)
    (side : ι → Side) (Ws : ι → ValuationFunctor T)
    (hgen : ∀ {A B : Object} (f : T.Hom A B), G.IsGen f →
      ∑ i ∈ s, (Ws i).V f = 0)
    {A B : Object} (f : T.Hom A B) :
    ∑ i ∈ s with side i = .debit, (side i).decode ((Ws i).V f)
      = ∑ i ∈ s with side i = .credit, (side i).decode ((Ws i).V f) := by
  have h := balance_sheet_equation T G L (s.filter (side · = .debit))
    (s.filter (side · = .credit)) ∅ Ws
    (fun f hf => by
      rw [Finset.sum_empty, add_zero, sum_debit_add_sum_credit]
      exact hgen f hf) f
  rw [Finset.sum_empty, add_zero] at h
  rw [sum_decode_debit, sum_decode_credit, h, Finset.sum_neg_distrib]

/-- **The balance-sheet equation recovered from the side-based form**
    under pairwise disjointness, with the hypothesis being the trial
    balance over `assets ∪ liabs ∪ eqs`. The side function is
    membership in `assets`. `balance_sheet_equation` itself is
    unchanged and needs no disjointness. -/
theorem balance_sheet_of_decoded (L : 𝕋Laws T) {ι : Type*} [DecidableEq ι]
    (assets liabs eqs : Finset ι)
    (hal : Disjoint assets liabs) (hae : Disjoint assets eqs)
    (hle : Disjoint liabs eqs)
    (Ws : ι → ValuationFunctor T)
    (hgen : ∀ {A B : Object} (f : T.Hom A B), G.IsGen f →
      ∑ i ∈ assets ∪ liabs ∪ eqs, (Ws i).V f = 0)
    {A B : Object} (f : T.Hom A B) :
    ∑ i ∈ assets, (Ws i).V f
      = (∑ i ∈ liabs, -(Ws i).V f) + (∑ i ∈ eqs, -(Ws i).V f) := by
  classical
  let side : ι → Side := fun i => if i ∈ assets then .debit else .credit
  have h := decoded_balance_sheet T G L (assets ∪ liabs ∪ eqs) side Ws hgen f
  have hdeb : (assets ∪ liabs ∪ eqs).filter (side · = .debit) = assets := by
    ext i
    by_cases hi : i ∈ assets <;> simp [side, hi]
  have hcred : (assets ∪ liabs ∪ eqs).filter (side · = .credit) = liabs ∪ eqs := by
    ext i
    by_cases hi : i ∈ assets
    · have hl : i ∉ liabs := Finset.disjoint_left.mp hal hi
      have he : i ∉ eqs := Finset.disjoint_left.mp hae hi
      simp [side, hi, hl, he]
    · simp [side, hi]
  rw [sum_decode_debit, sum_decode_credit, hdeb, hcred,
    Finset.sum_union hle] at h
  rw [h, Finset.sum_neg_distrib, Finset.sum_neg_distrib, neg_add]

end BalanceSheet

/-! ## Five account classes -/

/-- The five classes of the extended accounting equation. Revenue and
    expense are Ellerman's n. 11 aside (pp. 499-500). -/
inductive AccountClass
  | asset
  | liability
  | equity
  | revenue
  | expense
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- The normal balance side of each class: asset and expense are
    debit-balance, the rest credit-balance. -/
def AccountClass.side : AccountClass → Side
  | .asset => .debit
  | .expense => .debit
  | .liability => .credit
  | .equity => .credit
  | .revenue => .credit

section FiveClass

variable {T : 𝕋}

/-- The decoded balance of one class: the class fiber's debit-positive
    total, decoded by the class's normal side. -/
noncomputable def classBalance {ι : Type*} (s : Finset ι)
    (cls : ι → AccountClass) (Ws : ι → ValuationFunctor T)
    (c : AccountClass) {A B : Object} (f : T.Hom A B) : ℝ :=
  c.side.decode (∑ i ∈ s with cls i = c, (Ws i).V f)

/-- The valuation functor of one class: the sum over its fiber. -/
noncomputable def classValuation {ι : Type*} (s : Finset ι) (cls : ι → AccountClass)
    (Ws : ι → ValuationFunctor T) (c : AccountClass) : ValuationFunctor T :=
  ValuationFunctor.finsetSum (s.filter (cls · = c)) Ws

theorem univ_accountClass :
    (Finset.univ : Finset AccountClass)
      = {.asset, .liability, .equity, .revenue, .expense} := by
  decide

variable (T) (G : 𝕋.Generated T)

/-- **The five-class equation** A + X = L + E + R, for balanced
    generators and every derived flow. Proved from `trial_balance` by a
    fiberwise split over the five classes; in content it is the
    per-account form at `side := AccountClass.side ∘ cls` with each side
    regrouped by class. The per-account form stays primary because it
    also covers contra accounts, whose side differs from their class's
    normal side. -/
theorem five_class_equation (L : 𝕋Laws T) {ι : Type*} (s : Finset ι)
    (cls : ι → AccountClass) (Ws : ι → ValuationFunctor T)
    (hgen : ∀ {A B : Object} (f : T.Hom A B), G.IsGen f →
      ∑ i ∈ s, (Ws i).V f = 0)
    {A B : Object} (f : T.Hom A B) :
    classBalance s cls Ws .asset f + classBalance s cls Ws .expense f
      = classBalance s cls Ws .liability f + classBalance s cls Ws .equity f
        + classBalance s cls Ws .revenue f := by
  have h := trial_balance T G L s Ws hgen f
  rw [← Finset.sum_fiberwise s cls, univ_accountClass] at h
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
    reduceCtorEq, or_self, not_false_eq_true, Finset.sum_singleton] at h
  simp only [classBalance, AccountClass.side, Side.decode_debit,
    Side.decode_credit]
  linarith

variable {T}

/-! ## Closing the books, decoded -/

/-- **Closing, decoded (abstract form).** After a lawful closing entry,
    equity reported credit-positive grows by revenue reported
    credit-positive minus expense reported debit-positive. -/
theorem closing_decoded
    {Wrev Wexp Weq : ValuationFunctor T} {A B C : Object}
    {f : T.Hom A B} {c : T.Hom B C}
    (h : ClosesBooks Wrev Wexp Weq f c) :
    AccountClass.equity.side.decode (Weq.V (T.comp c f))
      = AccountClass.equity.side.decode (Weq.V f)
        + (AccountClass.revenue.side.decode (Wrev.V f)
            - AccountClass.expense.side.decode (Wexp.V f)) := by
  have := closing_transfers_net_income h
  simp only [AccountClass.side, Side.decode_debit, Side.decode_credit]
  rw [this]
  linarith

/-- **Closing, decoded, bridged to class balances.** With the three
    `ClosesBooks` views taken as the revenue, expense, and equity class
    fibers of a chart, equity's class balance grows by net income
    `R - X`. -/
theorem closing_classBalance {ι : Type*} (s : Finset ι)
    (cls : ι → AccountClass) (Ws : ι → ValuationFunctor T)
    {A B C : Object} {f : T.Hom A B} {c : T.Hom B C}
    (h : ClosesBooks (classValuation s cls Ws .revenue) (classValuation s cls Ws .expense)
      (classValuation s cls Ws .equity) f c) :
    classBalance s cls Ws .equity (T.comp c f)
      = classBalance s cls Ws .equity f
        + (classBalance s cls Ws .revenue f - classBalance s cls Ws .expense f) :=
  closing_decoded h

end FiveClass

/-! ## Chart of accounts: the side belongs to the name -/

/-- A chart of accounts assigns a balance side to each account name.
    An account×commodity pair takes its side from its name, so every
    commodity of one account decodes alike. -/
abbrev ChartOfAccounts : Type := AccountName → Side

/-- The side of an account×commodity pair, read from its name. -/
def ChartOfAccounts.sideOf (chart : ChartOfAccounts) (a : Account) : Side :=
  chart a.name

theorem ChartOfAccounts.sideOf_commodity_indep (chart : ChartOfAccounts)
    (n : AccountName) (k k' : Commodity) :
    chart.sideOf ⟨n, k⟩ = chart.sideOf ⟨n, k'⟩ := rfl

/-- **The decoded balance sheet for one commodity.** Ledger reports
    balances per commodity, and for quantity measurements an ℝ sum
    across commodities has no meaning, so the account set is restricted
    to commodity `k`, with the per-commodity trial balance of generators
    as hypothesis. -/
theorem chart_decoded_balance_sheet (T : 𝕋) (G : 𝕋.Generated T)
    (L : 𝕋Laws T) (chart : ChartOfAccounts) (s : Finset Account)
    (k : Commodity) (Ws : Account → ValuationFunctor T)
    (hgen : ∀ {A B : Object} (f : T.Hom A B), G.IsGen f →
      ∑ a ∈ s with a.commodity = k, (Ws a).V f = 0)
    {A B : Object} (f : T.Hom A B) :
    ∑ a ∈ s.filter (·.commodity = k) with chart.sideOf a = .debit,
        (chart.sideOf a).decode ((Ws a).V f)
      = ∑ a ∈ s.filter (·.commodity = k) with chart.sideOf a = .credit,
        (chart.sideOf a).decode ((Ws a).V f) :=
  decoded_balance_sheet T G L _ chart.sideOf Ws hgen f

end Ledger
