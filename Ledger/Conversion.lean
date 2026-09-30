import Ledger.PriceVector

/-!
# Conversion legs: completing cost-balanced entries with equity

Ellerman, "On Double-Entry Bookkeeping: The Mathematical Treatment",
Accounting Education 23:5 (2014), p. 497: transaction 2b posts Assets
`[(2000,0,0)//(0,20,0)]` together with Equity `[(0,20,0)//(2000,0,0)]`,
so the whole entry is a zero-term in every property type. Every
transaction of that example except the loan payment, transaction 3,
posts against Equity, since the article deals "for simplicity,
directly with equity rather than using 'income statement' or
property-flow accounts" (p. 497). The equity leg of 2b is therefore the
same counterpart that transactions 1 and 2a carry, not a construct
reserved for exchanges. Ledger's `@` syntax writes only the Assets leg;
the part of Ellerman's Equity leg that crosses commodities is left
implicit, and the entry's per-commodity residual is nonzero.

`conversionLeg conv` places a per-commodity residual on the accounts
`⟨conv, c⟩`, and the conversion leg of a posting vector is its residual
so placed; `equityConversion e` is the equity leg, the negation of the
conversion leg, which cancels the vector's residual. `completion conv`
is the idempotent projection `id - conversionLeg conv ∘ trialBalance`:
it subtracts the conversion leg, and so adds the equity leg; its range
is `zeroRows` (`completion_range`) and its kernel is the conversion
legs themselves (`completion_ker`). The completed journal balances per
commodity for **every** flows assignment (`withConversion_balanced`,
`completed_trialBalance`): these are facts about the projection, not
accounting facts. The accounting content lies elsewhere:

- an entry that balances in value at its own positive transaction
  prices has a conversion leg worth zero at those prices and worth the
  revaluation at any other (`conversionLeg_value_zero_at_cost`,
  `conversionLeg_value_revaluation`), so the equity leg that completion
  posts is worth minus the revaluation, which is what a fresh
  conversion account records (`conversion_account_value_gen`); and if
  the entry is not a zero-row it gives up one commodity and receives
  another (`residual_exchange`);
- any leg assignment that completes a journal is worth minus the
  journal at every price vector (`conversion_value`), and the
  completed journal needs no revaluation entry
  (`completed_revalues_free`);
- a conversion account that no entry already posts to records minus
  the journal's value (`conversion_account_value`).

C++ witness: an unfiltered `equity` report under default options books
the negation of the journal's per-commodity totals to
`Equity:Opening Balances`, which is the equity leg of the whole
journal's flow (`test/baseline/cmd-equity.test`, first `test equity`
block, replayed as `CmdEquity.opening_leg`). At C++ revision
`76b9dc2b2`, posts_as_equity::report_subtotal sums the per-account
balances, leaving out those accumulated from virtual postings that need
not balance (filters.cc:1610-1611), and books one posting per commodity
of that total (filters.cc:1619-1624), its amount negated
(filters.cc:1534-1535), to the account that filters.h:1096-1097
creates. Two options change the booking. `--invert` negates each
account's balance before the total is formed (filters.cc:1564 and
1571-1572), so the leg then equals the totals rather than their
negation; and a lot option such as `--lot-prices` keeps the lot
annotations that the report otherwise strips (filters.cc:1568), so the
totals are then taken per annotated commodity, as the
`test equity --lot-prices` block of the same file shows. Nothing here
reaches the executable layer, which books exactly what C++ books.
-/

namespace Ledger

noncomputable section

/-! ## The conversion leg -/

/-- Place a per-commodity residual on the accounts `⟨conv, c⟩`. -/
def conversionLeg (conv : AccountName) : (Commodity →₀ ℚ) →+ PacioliGroup :=
  Finsupp.mapDomain.addMonoidHom fun c => (⟨conv, c⟩ : Account)

@[simp] theorem conversionLeg_single (conv : AccountName) (c : Commodity) (q : ℚ) :
    conversionLeg conv (Finsupp.single c q) = Finsupp.single ⟨conv, c⟩ q := by
  simp [conversionLeg, Finsupp.mapDomain_single]

@[simp] theorem trialBalance_conversionLeg (conv : AccountName) (r : Commodity →₀ ℚ) :
    trialBalance (conversionLeg conv r) = r := by
  simp only [trialBalance, conversionLeg, Finsupp.mapDomain.addMonoidHom_apply]
  rw [← Finsupp.mapDomain_comp]
  exact Finsupp.mapDomain_id

/-- The leg of `x`'s residual has the value of `x` at every price
    vector. -/
@[simp] theorem priceDot_conversionLeg (conv : AccountName) (p : Commodity → ℚ)
    (x : PacioliGroup) :
    priceDot p (conversionLeg conv (trialBalance x)) = priceDot p x := by
  simp only [priceDot, AddMonoidHom.coe_comp, Function.comp_apply,
    trialBalance_conversionLeg]

/-- The canonical equity leg of a posting vector `x`: minus its
    per-commodity residual, posted to account name `e`. -/
def equityConversion (e : AccountName) : PacioliGroup →+ PacioliGroup :=
  -((conversionLeg e).comp trialBalance)

@[simp] theorem equityConversion_single (e : AccountName) (a : Account) (q : ℚ) :
    equityConversion e (Finsupp.single a q) = -Finsupp.single ⟨e, a.commodity⟩ q := by
  simp [equityConversion]

theorem trialBalance_equityConversion (e : AccountName) (x : PacioliGroup) :
    trialBalance (equityConversion e x) = -trialBalance x := by
  simp [equityConversion]

/-- Completing with the equity leg yields a zero-row, the shape of
    Ellerman's 2b. -/
theorem add_equityConversion_mem_zeroRows (e : AccountName) (x : PacioliGroup) :
    x + equityConversion e x ∈ zeroRows := by
  rw [mem_zeroRows, map_add, trialBalance_equityConversion, add_neg_cancel]

/-- The equity leg posts to account name `e` only. -/
theorem equityConversion_support (e : AccountName) (x : PacioliGroup) :
    ∀ a ∈ (equityConversion e x).support, a.name = e := by
  intro a ha
  simp only [equityConversion, AddMonoidHom.neg_apply, Finsupp.support_neg,
    AddMonoidHom.coe_comp, Function.comp_apply, conversionLeg,
    Finsupp.mapDomain.addMonoidHom_apply] at ha
  have h := Finsupp.mapDomain_support ha
  simp only [Finset.mem_image] at h
  obtain ⟨c, _, rfl⟩ := h
  rfl

/-! ## The completion projection -/

/-- `π = id - leg ∘ trialBalance`: subtract the residual, placed on the
    conversion accounts. -/
def completion (conv : AccountName) : PacioliGroup →+ PacioliGroup :=
  AddMonoidHom.id _ - (conversionLeg conv).comp trialBalance

theorem completion_apply (conv : AccountName) (x : PacioliGroup) :
    completion conv x = x - conversionLeg conv (trialBalance x) := rfl

/-- The completion adds the equity leg. -/
theorem completion_eq_add_equityConversion (conv : AccountName) (x : PacioliGroup) :
    completion conv x = x + equityConversion conv x := by
  rw [completion_apply, sub_eq_add_neg]
  rfl

theorem completion_mem_zeroRows (conv : AccountName) (x : PacioliGroup) :
    completion conv x ∈ zeroRows := by
  rw [mem_zeroRows, completion_apply, map_sub, trialBalance_conversionLeg, sub_self]

/-- On elements that already balance per commodity the completion is
    the identity. -/
theorem completion_of_mem (conv : AccountName) {x : PacioliGroup}
    (hx : x ∈ zeroRows) : completion conv x = x := by
  rw [completion_apply, mem_zeroRows.mp hx, map_zero, sub_zero]

theorem completion_idem (conv : AccountName) (x : PacioliGroup) :
    completion conv (completion conv x) = completion conv x :=
  completion_of_mem conv (completion_mem_zeroRows conv x)

theorem completion_range (conv : AccountName) :
    (completion conv).range = zeroRows := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact completion_mem_zeroRows conv y
  · intro hx
    exact ⟨x, completion_of_mem conv hx⟩

/-- The completion annihilates exactly the elements that live wholly on
    the conversion accounts. An entry that already posts to them can
    therefore be erased (`completion_erases_stale`), which is why
    `conversion_account_value` assumes freshness. -/
theorem completion_ker (conv : AccountName) :
    (completion conv).ker = (conversionLeg conv).range := by
  ext x
  constructor
  · intro hx
    have h : x - conversionLeg conv (trialBalance x) = 0 := hx
    exact ⟨trialBalance x, (sub_eq_zero.mp h).symm⟩
  · rintro ⟨r, rfl⟩
    show completion conv (conversionLeg conv r) = 0
    rw [completion_apply, trialBalance_conversionLeg, sub_self]

/-- An entry that already posts to the conversion account can be erased
    by completion: one posting of 1 USD to `⟨"Equity", "USD"⟩` is
    nonzero and completes to zero. This is why
    `conversion_account_value` assumes freshness. -/
theorem completion_erases_stale : ∃ x : PacioliGroup, x ≠ 0 ∧ completion "Equity" x = 0 := by
  refine ⟨Finsupp.single ⟨"Equity", "USD"⟩ 1, by simp, ?_⟩
  have : Finsupp.single (⟨"Equity", "USD"⟩ : Account) (1 : ℚ)
      ∈ (conversionLeg "Equity").range := ⟨Finsupp.single "USD" 1, by simp⟩
  rw [← completion_ker] at this
  exact this

/-! ## The completed journal -/

namespace GenSpec

variable {S : GenSpec}

/-- Each generator's flow with its conversion leg subtracted. The
    endpoints are unchanged; the theory never links flows to
    endpoints. -/
def withConversion (conv : AccountName) (flows : S.Gen → PacioliGroup) :
    S.Gen → PacioliGroup :=
  fun t => completion conv (flows t)

/-- Every completed entry is a zero-row. This holds for every flows
    assignment, including unbalanced ones: it is a fact about the
    projection, not about the journal. -/
theorem withConversion_balanced (conv : AccountName) (flows : S.Gen → PacioliGroup)
    (t : S.Gen) : withConversion conv flows t ∈ zeroRows :=
  completion_mem_zeroRows conv (flows t)

/-- On a journal that already balances per commodity, completion
    changes nothing. -/
theorem withConversion_of_balanced (conv : AccountName) (flows : S.Gen → PacioliGroup)
    (h : ∀ t, flows t ∈ zeroRows) : withConversion conv flows = flows :=
  funext fun t => completion_of_mem conv (h t)

/-- Completion commutes with the flow denotation (`flow_map` at the
    projection). -/
theorem flow_withConversion (conv : AccountName) (flows : S.Gen → PacioliGroup)
    {A B : Object} (f : FreeHom S A B) :
    flow (withConversion conv flows) f
      = flow flows f - conversionLeg conv (trialBalance (flow flows f)) :=
  flow_map (completion conv) flows f

/-- The completed journal satisfies the per-commodity double-entry
    theorem for every morphism and every flows assignment; equally
    unconditional, hence equally empty as an accounting statement. -/
theorem completed_trialBalance (conv : AccountName) (flows : S.Gen → PacioliGroup)
    {A B : Object} (f : FreeHom S A B) :
    trialBalance (flow (withConversion conv flows) f) = 0 :=
  free_double_entry _ (withConversion_balanced conv flows) f

/-! ## The value of conversion legs -/

/-- The completed vector journal needs no revaluation entry: at every
    price vector its value is zero. Every transaction of Ellerman's
    vector journal is a zero-term (p. 497), so the same holds there by
    linearity. The article does not discuss revaluation, so this
    reading is the module's and not a claim of the article. -/
theorem completed_revalues_free (flows conv : S.Gen → PacioliGroup)
    (hconv : ∀ t, flows t + conv t ∈ zeroRows) (q : Commodity → ℚ)
    {A B : Object} (f : FreeHom S A B) :
    (priceValuation (fun t => flows t + conv t) q).V f = 0 :=
  priceValuation_balanced _ hconv q f

/-- **Any completing leg is forced in value**: if `conv` completes
    `flows` to zero-rows, its value at every price vector is minus the
    journal's value. -/
theorem conversion_value (flows conv : S.Gen → PacioliGroup)
    (hconv : ∀ t, flows t + conv t ∈ zeroRows) (q : Commodity → ℚ)
    {A B : Object} (f : FreeHom S A B) :
    (priceValuation conv q).V f = -(priceValuation flows q).V f := by
  have h := completed_revalues_free flows conv hconv q f
  rw [priceValuation, ofFlowHom_add_flows] at h
  rw [priceValuation, priceValuation]
  linarith

/-- Per-entry transaction prices, positive on every commodity: the unit
    values at which each entry's own exchange is struck. Positivity is
    what makes "balances at its own prices" a constraint; the zero
    price vector would satisfy it for every entry. C++ rejects a
    negative cost (textual_xacts.cc:696-697 at `76b9dc2b2`) but accepts
    a zero one, so this field narrows what C++ admits. -/
structure EntryPrices (S : GenSpec) where
  /-- The price vector of each entry. -/
  price : S.Gen → Commodity → ℚ
  /-- Every price is positive. -/
  pos : ∀ t c, 0 < price t c

/-- Each entry balances in value at its own prices. This models the
    balance check C++ performs on an `@` exchange, which values each
    costed amount at its cost (xact.cc:325 at `76b9dc2b2`), when the
    entry's per-unit costs fit one price vector that gives the cost
    commodity the price 1. -/
def CostBalanced (flows : S.Gen → PacioliGroup) (P : EntryPrices S) : Prop :=
  ∀ t, priceDot (P.price t) (flows t) = 0

/-- **The leg adds no value at cost.** An entry that balances at its
    own prices has a conversion leg worth zero at those prices: the
    completion adds only the property counterpart. -/
theorem conversionLeg_value_zero_at_cost (conv : AccountName)
    (flows : S.Gen → PacioliGroup) (P : EntryPrices S) (h : CostBalanced flows P)
    (t : S.Gen) :
    priceDot (P.price t) (conversionLeg conv (trialBalance (flows t))) = 0 := by
  rw [priceDot_conversionLeg, h t]

/-- At any other price vector the conversion leg, the residual that
    completion subtracts, is worth the revaluation of the entry: its
    value at `p` minus its value at its own prices. The equity leg that
    completion posts is its negation and is worth minus the revaluation,
    which is what a fresh conversion account records
    (`conversion_account_value_gen`). -/
theorem conversionLeg_value_revaluation (conv : AccountName)
    (flows : S.Gen → PacioliGroup) (P : EntryPrices S) (h : CostBalanced flows P)
    (t : S.Gen) (p : Commodity → ℚ) :
    priceDot p (conversionLeg conv (trialBalance (flows t)))
      = priceDot p (flows t) - priceDot (P.price t) (flows t) := by
  rw [priceDot_conversionLeg, h t, sub_zero]

/-- **A cost-balanced entry that is not a zero-row is an exchange**: at
    positive prices its residual has a positive and a negative
    coordinate, so it gives up one commodity and receives another, as
    2b does. A nonzero residual whose coordinates share a sign stays
    nonzero in value at every positive price vector. -/
theorem residual_exchange (flows : S.Gen → PacioliGroup) (P : EntryPrices S)
    (h : CostBalanced flows P) (t : S.Gen) (hne : flows t ∉ zeroRows) :
    ∃ c d : Commodity, 0 < trialBalance (flows t) c ∧ trialBalance (flows t) d < 0 := by
  set r := trialBalance (flows t) with hr
  have hr0 : r ≠ 0 := fun h0 => hne (mem_zeroRows.mpr h0)
  have hdot : ∑ c ∈ r.support, r c * P.price t c = 0 := by
    have h1 := h t
    simp only [priceDot, AddMonoidHom.coe_comp, Function.comp_apply,
      LinearMap.toAddMonoidHom_coe, Finsupp.linearCombination_apply, smul_eq_mul,
      Finsupp.sum] at h1
    exact h1
  obtain ⟨c0, hc0⟩ : ∃ c, r c ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hr0 (Finsupp.ext hall)
  have hc0s : c0 ∈ r.support := Finsupp.mem_support_iff.mpr hc0
  by_contra hno
  push Not at hno
  rcases lt_or_gt_of_ne hc0 with hneg | hpos
  · have hnp : ∀ d, r d ≤ 0 := fun d => by
      by_contra hd
      push Not at hd
      exact absurd (hno d c0 hd) (not_le.mpr hneg)
    have : 0 < ∑ c ∈ r.support, -(r c * P.price t c) :=
      Finset.sum_pos' (fun c _ => neg_nonneg.mpr (mul_nonpos_of_nonpos_of_nonneg
          (hnp c) (P.pos t c).le))
        ⟨c0, hc0s, neg_pos.mpr (mul_neg_of_neg_of_pos hneg (P.pos t c0))⟩
    rw [Finset.sum_neg_distrib, hdot, neg_zero] at this
    exact lt_irrefl 0 this
  · have hnn : ∀ d, 0 ≤ r d := fun d => hno c0 d hpos
    have : 0 < ∑ c ∈ r.support, r c * P.price t c :=
      Finset.sum_pos' (fun c _ => mul_nonneg (hnn c) (P.pos t c).le)
        ⟨c0, hc0s, mul_pos hpos (P.pos t c0)⟩
    rw [hdot] at this
    exact lt_irrefl 0 this

end GenSpec

/-! ## The conversion account's value, under freshness -/

/-- Elements that post nothing to any account named `conv`. -/
def freshFor (conv : AccountName) : AddSubgroup PacioliGroup where
  carrier := {x | ∀ c, x ⟨conv, c⟩ = 0}
  zero_mem' := fun _ => rfl
  add_mem' := fun {x y} hx hy c => by
    simp only [Set.mem_setOf_eq] at hx hy
    rw [Finsupp.add_apply, hx c, hy c, add_zero]
  neg_mem' := fun {x} hx c => by
    simp only [Set.mem_setOf_eq] at hx
    rw [Finsupp.neg_apply, hx c, neg_zero]

theorem valueHom_of_fresh (p : Commodity → ℚ) (conv : AccountName)
    {x : PacioliGroup} (hx : x ∈ freshFor conv) : valueHom p conv x = 0 := by
  rw [valueHom, Finsupp.liftAddHom_apply]
  refine Finset.sum_eq_zero fun a ha => ?_
  by_cases hn : a.name = conv
  · exfalso
    have h0 : x a = 0 := by
      have := hx a.commodity
      rw [← hn] at this
      exact this
    exact (Finsupp.mem_support_iff.mp ha) h0
  · simp [hn]

theorem valueHom_conversionLeg (p : Commodity → ℚ) (conv : AccountName)
    (x : PacioliGroup) :
    valueHom p conv (conversionLeg conv (trialBalance x)) = priceDot p x := by
  rw [← priceDot_conversionLeg conv p x]
  generalize trialBalance x = r
  induction r using Finsupp.induction_linear with
  | zero => simp
  | add r₁ r₂ h₁ h₂ => rw [map_add, map_add, map_add, h₁, h₂]
  | single c q => simp

namespace GenSpec

variable {S : GenSpec}

/-- **The conversion account's value.** If no entry already posts to
    the conversion account, then in the completed journal that
    account's value at a common price vector `p` is minus the value of
    the uncompleted flow. -/
theorem conversion_account_value (conv : AccountName) (flows : S.Gen → PacioliGroup)
    (hfresh : ∀ t, flows t ∈ freshFor conv) (p : Commodity → ℚ)
    {A B : Object} (f : FreeHom S A B) :
    valueHom p conv (flow (withConversion conv flows) f) = -priceDot p (flow flows f) := by
  rw [flow_withConversion, map_sub, valueHom_of_fresh p conv (flow_mem flows _ hfresh f),
    valueHom_conversionLeg, zero_sub]

/-- Per entry, for cost-balanced entries: the conversion account records
    the entry's value at its own prices minus its value at `p`, which
    is zero at the entry's own prices. -/
theorem conversion_account_value_gen (conv : AccountName) (flows : S.Gen → PacioliGroup)
    (hfresh : ∀ t, flows t ∈ freshFor conv) (P : EntryPrices S)
    (hcost : CostBalanced flows P) (p : Commodity → ℚ) (t : S.Gen) :
    valueHom p conv (withConversion conv flows t)
      = priceDot (P.price t) (flows t) - priceDot p (flows t) := by
  have h := conversion_account_value conv flows hfresh p (genHom t)
  rw [flow_genHom, flow_genHom] at h
  rw [h, hcost t, zero_sub]

end GenSpec

/-! ## Ellerman's transaction 2b (p. 497) and note 20 -/

namespace EllermanWidgets

/-- A cost valuation of widgets at the price of their inputs, two
    half-widgets at 40 each (the recipe of p. 497), with no other cost
    of production: the usual practice, valuing output at cost until it
    is sold, that note 20 sets aside. -/
def costPrice : Commodity → ℚ := fun c =>
  if c = "$" then 1 else if c = "WIDGET" then 80 else if c = "HALF" then 40 else 0

/-- **2b recovered**: completing the Assets-only swap with the equity
    leg yields exactly the transaction journaled on p. 497. -/
theorem txn2b_completion : completion "Equity" txn2bAssets = txn2b := by
  rw [completion_eq_add_equityConversion, txn2bAssets, txn2b, map_sub,
    equityConversion_single, equityConversion_single]
  abel

/-- Note 20: at the selling prices `(1, 100, 40)` the Equity leg that
    completion adds to the Assets swap
    (`EllermanWidgets.txn2b_completion`) is worth zero. -/
theorem txn2b_leg_value_zero :
    priceDot price (equityConversion "Equity" txn2bAssets) = 0 := by
  rw [equityConversion, AddMonoidHom.neg_apply, map_neg, AddMonoidHom.comp_apply,
    priceDot_conversionLeg, txn2bAssets_value_neutral_not_zeroRow.2, neg_zero]

/-- At cost the Equity account is credited 400: the realized gain,
    debit-positive value `-400`. -/
theorem txn2b_equity_at_cost :
    valueHom costPrice "Equity" (completion "Equity" txn2bAssets) = -400 := by
  have hfresh : txn2bAssets ∈ freshFor "Equity" := by
    intro c
    simp [txn2bAssets]
  rw [completion_apply, map_sub, valueHom_of_fresh _ _ hfresh,
    valueHom_conversionLeg]
  have hWD : ("WIDGET" : String) ≠ "$" := by decide
  simp [txn2bAssets, costPrice, hWD]
  norm_num

end EllermanWidgets

/-! ## The C++ `equity` report books the completion leg -/

namespace CmdEquity

/-- The journal of `test/baseline/cmd-equity.test`: two purchases of
    2 AAA, at 0.90 GBP and 1.00 GBP, paid from `Assets:Bank`. Its
    flow is 4 AAA on `Assets:Broker` and -3.80 GBP on `Assets:Bank`,
    the balances the oracle reports for that journal. -/
def journalFlow : PacioliGroup :=
  Finsupp.single ⟨"Assets:Broker", "AAA"⟩ 4 + Finsupp.single ⟨"Assets:Bank", "GBP"⟩ (-19 / 5)

/-- The first `test equity` block of `cmd-equity.test` books `-4 AAA`
    and `3.80 GBP` to `Equity:Opening Balances`: exactly the equity leg
    of the journal's flow. -/
theorem opening_leg :
    equityConversion "Equity:Opening Balances" journalFlow
      = Finsupp.single ⟨"Equity:Opening Balances", "AAA"⟩ (-4)
        + Finsupp.single ⟨"Equity:Opening Balances", "GBP"⟩ (19 / 5) := by
  simp only [journalFlow, map_add, equityConversion_single, Finsupp.single_neg]
  norm_num

end CmdEquity

end

end Ledger
