import Mathlib.Tactic.Linarith
import Ledger.Theorems

/-!
# Derived operations and theorems (Phase 4, K4)

Everything here is *derived*: definitions and theorems over the
Phase 1–3 kernel, adding no new axioms. The worksheet's "Reach" list
(§1) is cashed out:

- **Reports as colimits**: per-account flows grouped by `rootOf`
  agree with the ungrouped total (`balance_sheet_at_roots`) — the
  finite form of "the balance sheet is the colimit of V over the
  forest" — and the grouped report of a balanced journal is zero
  (`root_report_balances`).
- **Budgeting**: a second valuation functor and `variance` — the
  pointwise difference, which is again nothing more than the
  `ValuationFunctor` algebra (`neg`, `sub`, `smul`) defined here.
- **Multi-currency**: the price action's soundness law *is* a natural
  transformation statement: measuring the revalued transaction in the
  target commodity equals measuring in the source commodity rescaled
  (`PriceAction.revalue_sound_smul`).
- **Closing the books**: `ClosesBooks` specifies a closing morphism;
  `closing_transfers_net_income` proves equity absorbs exactly the
  net income.
- **Periodic transactions** (`~ period`, handoff open question 5):
  `PeriodicRule` + `PeriodicFires` — scheduled generators; firing any
  number of balanced templates preserves every valuation.
- **Balance assignments** (handoff open question 6): `CompletionRule`
  — an assignment *computes* the adjoined posting so that a target
  measurement holds; `completion_value_determined` shows the computed
  amount is forced by the homomorphism equation. (Assertion-style
  rules remain `DerivationRule`.)
-/

namespace Ledger

/-! ## The valuation-functor algebra -/

namespace ValuationFunctor

variable {T : 𝕋}

/-- Pointwise negation (e.g. flip a measurement's sign convention). -/
def neg (W : ValuationFunctor T) : ValuationFunctor T where
  V f := -W.V f
  V_comp g f := by rw [W.V_comp, neg_add]
  V_tensor f g := by rw [W.V_tensor, neg_add]
  V_add f g := by rw [W.V_add, neg_add]

instance : Neg (ValuationFunctor T) := ⟨neg⟩

@[simp] theorem neg_V (W : ValuationFunctor T) {A B : Object}
    (f : T.Hom A B) : (-W).V f = -W.V f := rfl

/-- Pointwise difference of measurements. -/
instance : Sub (ValuationFunctor T) := ⟨fun W₁ W₂ => W₁ + -W₂⟩

@[simp] theorem sub_V (W₁ W₂ : ValuationFunctor T) {A B : Object}
    (f : T.Hom A B) : (W₁ - W₂).V f = W₁.V f - W₂.V f :=
  sub_eq_add_neg (W₁.V f) (W₂.V f) ▸ rfl

/-- Rescale a measurement (unit conversion, percentage reporting). -/
def smul (r : ℝ) (W : ValuationFunctor T) : ValuationFunctor T where
  V f := r * W.V f
  V_comp g f := by rw [W.V_comp, mul_add]
  V_tensor f g := by rw [W.V_tensor, mul_add]
  V_add f g := by rw [W.V_add, mul_add]

instance : SMul ℝ (ValuationFunctor T) := ⟨smul⟩

@[simp] theorem smul_V (r : ℝ) (W : ValuationFunctor T) {A B : Object}
    (f : T.Hom A B) : (r • W).V f = r * W.V f := rfl

/-- **Budget variance**: actual minus planned, as a valuation functor
    — variance reports inherit every functor law (they sum over
    composition, tensor, and aggregation like any measurement). -/
abbrev variance (actual budget : ValuationFunctor T) : ValuationFunctor T :=
  actual - budget

end ValuationFunctor

/-! ## Multi-currency as a natural transformation -/

/-- The worksheet's "multi-currency support is a natural
    transformation between valuation functors", made precise: along a
    conversion `p : a → b`, measuring the revalued transaction in `b`
    *is* the `a`-measurement rescaled by the rate. -/
theorem PriceAction.revalue_sound_smul {P : PriceGroupoid} {T : 𝕋}
    {CV : CommodityValuation T} (act : PriceAction P T CV)
    {a b : Commodity} (p : P.Conversion a b) {A B : Object}
    (f : T.Hom A B) :
    (CV b).V (act.revalue p f) = (P.rate p • CV a).V f :=
  act.revalue_sound p f

/-! ## Reports as colimits over the forest -/

section Reports

variable {T : 𝕋} {F : AccountForest}

/-- **Balance sheet at the roots**: group per-account measurements by
    root account and sum — the total agrees with summing directly.
    This is the finite content of "reports are colimits over the
    forest": rolling attribution up to the roots loses no value. -/
theorem balance_sheet_at_roots [DecidableEq F.Account]
    (s roots : Finset F.Account)
    (hmap : ∀ a ∈ s, F.rootOf a ∈ roots)
    (Ws : F.Account → ValuationFunctor T) {A B : Object} (f : T.Hom A B) :
    ∑ r ∈ roots, ∑ a ∈ s with F.rootOf a = r, (Ws a).V f
      = ∑ a ∈ s, (Ws a).V f :=
  Finset.sum_fiberwise_of_maps_to hmap _

/-- The grouped-by-root report of a balanced journal is zero: the
    balance sheet balances, however the accounts roll up. -/
theorem root_report_balances [DecidableEq F.Account]
    (L : 𝕋Laws T) (G : 𝕋.Generated T)
    (s roots : Finset F.Account)
    (hmap : ∀ a ∈ s, F.rootOf a ∈ roots)
    (Ws : F.Account → ValuationFunctor T)
    (hgen : ∀ {A B : Object} (f : T.Hom A B), G.IsGen f →
      ∑ a ∈ s, (Ws a).V f = 0)
    {A B : Object} (f : T.Hom A B) :
    ∑ r ∈ roots, ∑ a ∈ s with F.rootOf a = r, (Ws a).V f = 0 := by
  rw [balance_sheet_at_roots s roots hmap]
  exact trial_balance T G L s Ws hgen f

end Reports

/-! ## Closing the books -/

section Closing

variable {T : 𝕋}

/-- A closing entry for the period recorded by `f`: composed after
    `f`, it zeroes the revenue and expense measurements, and it is
    balanced across the three views. -/
structure ClosesBooks (Wrev Wexp Weq : ValuationFunctor T)
    {A B C : Object} (f : T.Hom A B) (c : T.Hom B C) : Prop where
  rev_zeroed : Wrev.V (T.comp c f) = 0
  exp_zeroed : Wexp.V (T.comp c f) = 0
  balanced : Wrev.V c + Wexp.V c + Weq.V c = 0

/-- **Closing transfers exactly the net income into equity**: after
    the closing entry, the equity measurement has grown by precisely
    revenue + expense (net income, sign convention debit-positive).
    Forced by the functor laws — there is no other amount a lawful
    closing could transfer. -/
theorem closing_transfers_net_income
    {Wrev Wexp Weq : ValuationFunctor T} {A B C : Object}
    {f : T.Hom A B} {c : T.Hom B C}
    (h : ClosesBooks Wrev Wexp Weq f c) :
    Weq.V (T.comp c f) = Weq.V f + (Wrev.V f + Wexp.V f) := by
  have hrev : Wrev.V c + Wrev.V f = 0 := by
    rw [← Wrev.V_comp]; exact h.rev_zeroed
  have hexp : Wexp.V c + Wexp.V f = 0 := by
    rw [← Wexp.V_comp]; exact h.exp_zeroed
  have hbal := h.balanced
  rw [Weq.V_comp]
  linarith

end Closing

/-! ## Periodic transactions (open question 5) -/

section Periodic

variable {T : 𝕋}

/-- A periodic rule (`~ period`): a scheduled generator that adjoins a
    fixed template every `period` ticks. Dates are labels (metadata),
    so the schedule is modeled on abstract ticks. -/
structure PeriodicRule (T : 𝕋) where
  name : Option String
  /-- The period, in ticks (days, in Ledger's realization). -/
  period : ℕ
  period_pos : 0 < period
  templateDom : Object
  templateCod : Object
  template : T.Hom templateDom templateCod

/-- The rule fires on ticks divisible by the period. -/
def PeriodicRule.firesAt (r : PeriodicRule T) (n : ℕ) : Prop :=
  n % r.period = 0

/-- `PeriodicFires T r k f f'`: adjoining `k` firings of the rule's
    template to `f` yields `f'`. -/
inductive PeriodicFires (T : 𝕋) (r : PeriodicRule T) :
    ℕ → ∀ {A B : Object}, T.Hom A B →
    ∀ {A' B' : Object}, T.Hom A' B' → Prop where
  | zero {A B : Object} (f : T.Hom A B) : PeriodicFires T r 0 f f
  | succ {k : ℕ} {A B A' B' : Object} {f : T.Hom A B} {f' : T.Hom A' B'} :
      PeriodicFires T r k (T.tensor f r.template) f' →
      PeriodicFires T r (k + 1) f f'

/-- Any number of firings of a balanced periodic template preserves
    every measurement — recurring transactions reclassify, never
    create, value. -/
theorem periodic_preserves_valuation (W : ValuationFunctor T)
    {r : PeriodicRule T} (hbal : W.V r.template = 0)
    {k : ℕ} {A B A' B' : Object} {f : T.Hom A B} {f' : T.Hom A' B'}
    (h : PeriodicFires T r k f f') : W.V f' = W.V f := by
  induction h with
  | zero f => rfl
  | succ _ ih => rw [ih, W.V_tensor, hbal, add_zero]

end Periodic

/-! ## Balance assignments as completions (open question 6) -/

section Completion

variable {T : 𝕋}

/-- A completion rule (balance *assignment*, `= AMOUNT` with no
    posting amount): where an assertion-style `DerivationRule` checks
    a predicate and adjoins a fixed template, a completion **computes**
    the adjoined posting so that a target measurement holds
    afterwards. -/
structure CompletionRule (T : 𝕋) (W : ValuationFunctor T) where
  name : Option String
  /-- When does this rule apply? -/
  predicate : ∀ {A B : Object}, T.Hom A B → Prop
  /-- The target measurement the completed transaction must satisfy
      (the asserted balance). -/
  target : ℝ
  /-- Endpoints of the computed posting (may depend on the matched
      transaction). -/
  completionDom : ∀ {A B : Object}, T.Hom A B → Object
  completionCod : ∀ {A B : Object}, T.Hom A B → Object
  /-- The computed posting itself. -/
  completion : ∀ {A B : Object} (f : T.Hom A B), predicate f →
    T.Hom (completionDom f) (completionCod f)
  /-- The defining property: after adjoining the completion, the
      measurement hits the target. -/
  completes : ∀ {A B : Object} (f : T.Hom A B) (h : predicate f),
    W.V (T.tensor f (completion f h)) = target

/-- **The computed amount is forced**: any lawful completion adjoins
    exactly `target - W.V f`. Assignments do not choose the amount —
    the homomorphism equation does. This is the design-method story
    in miniature: state the specification (`completes`), solve for
    the implementation. -/
theorem completion_value_determined {W : ValuationFunctor T}
    (r : CompletionRule T W) {A B : Object} (f : T.Hom A B)
    (h : r.predicate f) :
    W.V (r.completion f h) = r.target - W.V f := by
  have hc := r.completes f h
  rw [W.V_tensor] at hc
  linarith

end Completion

end Ledger
