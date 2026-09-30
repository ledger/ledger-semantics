import Ledger.Lots
import Ledger.Conversion

/-!
# Basis gain and the forced equity leg

Ellerman, "On Double-Entry Bookkeeping: The Mathematical Treatment",
Accounting Education 23:5 (2014), p. 496: the one valid operation on
equations encoded as zero-accounts is to "add on a zero-account or
zero-term"; p. 497: in transaction 2b Equity carries the reverse
composition of Assets, so the entry is a zero-term in every property
type. Every transaction of the article's vector journal is a
zero-term, so by linearity the journal is worth zero at every price
vector and revaluing it calls for no entry; for completed journals
this is `GenSpec.completed_revalues_free`. The article does not
discuss revaluation, so this reading, and everything below, is the
repository's and not a claim of the article.

In Ledger revaluation does call for an entry, because an exchange
balances at basis and not per commodity. Under any price vector a
journal's value is exactly minus the value of the equity leg that
would complete it (`GenSpec.conversion_value`). This module names
market value minus basis value the **basis gain**, which is the whole
market value of a journal that balances at basis
(`market_eq_basisGain`), and states it over the lot refinement of
`Ledger/Lots.lean`, in which fixated lots and valuation expressions do
not float.

- `market_eq_basisGain`, `conversion_leg_forced` and
  `equityConversion_entry` hold for any market vector.
- `basisGain_change_refined` is the law of price motion over refined
  flows, with no hypothesis on the refinement. The market-vector
  difference it reads vanishes on every commodity that does not float,
  the valuation expressions held fixed
  (`LotRefinement.marketVector_sub_of_not_floating`).
- The coarse forms `basisGain_change`, `entry_change` and
  `market_eq_coarse` read lot-blind flows and assume that every
  commodity floats, and
  `BasisGainExamples.basisGain_change_needs_floating` shows that
  `basisGain_change` fails without that hypothesis. Every commodity
  floats when the journal has no fixated lot and no valuation
  expression, which is also the hypothesis under which
  `LotRefinement.market_of_lotBlind` computes market value from the
  lot-blind flows the oracle has.

`LotRefinement.basisVector` values every lot at its lot price and every
unannotated commodity at 1, and so adds amounts denominated in
different commodities as though they were one unit. The hypothesis
`hbasis` is that every generator is worth zero under `basisVector`. A
generator that balances at basis in each commodity separately
satisfies it. The converse holds whenever, within the generator, every
lot price is denominated in one commodity and no other commodity
appears unannotated, and it can fail otherwise, because a surplus in
one commodity may cancel a deficit in another
(`BasisGainExamples.hbasis_weaker`). The theorems below assume only
`hbasis`. For the whole journal the condition is the regime the
docstring of `basisVector` names: every lot price in one commodity
(`LotRefinement.LotsIn`), which is the only unannotated one.

The basis gain is not the unrealized gain: across mismatched automatic
lots it also contains realized gain that was never booked
(`BasisGainExamples.sale_basis_gain_price_independent`). C++'s own
`test/baseline/opt-unrealized-gains.test`, at revision `76b9dc2b2`,
expects the unfiltered report `bal -V --unrealized --unrealized-gains
G` to total zero on a journal that buys 10 AAPL for $200 and then
prices AAPL at $30: Assets report $100 and the gains account `G`
reports $-100. Read with the posting to `G` as the journal's equity
leg valued at market, that zero total is `market_eq_basisGain`
together with `equityConversion_entry`: the journal is worth its basis
gain, $100, and the equity leg is worth minus that
(`OptUnrealizedGains.total_zero`).
-/

namespace Ledger

noncomputable section

namespace GenSpec

variable {S : GenSpec}

/-- Basis gain at a market vector `m`: market value minus basis value. -/
def basisGain (flows : S.Gen → PacioliGroup) (R : LotRefinement)
    (m : Commodity → ℚ) : ValuationFunctor (freeT S) :=
  priceValuation flows m - priceValuation flows R.basisVector

/-- On a journal that balances at basis, market value is the basis
    gain. -/
theorem market_eq_basisGain (flows : S.Gen → PacioliGroup) (R : LotRefinement)
    (m : Commodity → ℚ) (hbasis : ∀ t, priceDot R.basisVector (flows t) = 0)
    {A B : Object} (f : FreeHom S A B) :
    (priceValuation flows m).V f = (basisGain flows R m).V f := by
  have h0 : (priceValuation flows R.basisVector).V f = 0 := by
    rw [priceValuation_V, free_hom_balanced flows _ hbasis f, Rat.cast_zero]
  rw [basisGain, ValuationFunctor.sub_V, h0, sub_zero]

/-- The coarse reading, when every commodity floats: market value at
    the market vector is the value at `p` of the lot-blind flows the
    oracle computes. -/
theorem market_eq_coarse (flows : S.Gen → PacioliGroup) (R : LotRefinement)
    (hfl : ∀ k, R.Floating k) (p e : Commodity → ℚ) {A B : Object} (f : FreeHom S A B) :
    (priceValuation flows (R.marketVector p e)).V f
      = (priceValuation (fun t => R.forget (flows t)) p).V f := by
  rw [priceValuation_V, priceValuation_V, R.market_of_lotBlind flows p e hfl]

/-- **Price motion, in general**: when the price table moves from `p`
    to `p'` with the valuation expressions `e` held fixed, the change in
    basis gain is the refined flows valued at the market-vector
    difference, which vanishes on commodities that do not float. -/
theorem basisGain_change_refined (flows : S.Gen → PacioliGroup) (R : LotRefinement)
    (p p' e : Commodity → ℚ) {A B : Object} (f : FreeHom S A B) :
    (basisGain flows R (R.marketVector p' e)).V f - (basisGain flows R (R.marketVector p e)).V f
      = (priceValuation flows (R.marketVector p' e - R.marketVector p e)).V f := by
  simp only [basisGain, ValuationFunctor.sub_V]
  rw [priceValuation_sub_prices]
  ring

/-- Price motion through lot-blind flows, when every commodity
    floats. -/
theorem basisGain_change (flows : S.Gen → PacioliGroup) (R : LotRefinement)
    (hfl : ∀ k, R.Floating k) (p p' e : Commodity → ℚ) {A B : Object} (f : FreeHom S A B) :
    (basisGain flows R (R.marketVector p' e)).V f - (basisGain flows R (R.marketVector p e)).V f
      = (priceValuation (fun t => R.forget (flows t)) (p' - p)).V f := by
  have hsub : R.marketVector p' e - R.marketVector p e = R.marketVector (p' - p) e := by
    funext k
    rw [R.marketVector_sub_of_floating p p' e k (hfl k), R.marketVector_of_floating _ e hfl]
    rfl
  rw [basisGain_change_refined, hsub, market_eq_coarse flows R hfl]

/-- **The completing leg is forced**: any leg assignment that completes
    a journal balancing at basis is worth minus its basis gain. -/
theorem conversion_leg_forced (flows conv : S.Gen → PacioliGroup) (R : LotRefinement)
    (m : Commodity → ℚ) (hconv : ∀ t, flows t + conv t ∈ zeroRows)
    (hbasis : ∀ t, priceDot R.basisVector (flows t) = 0)
    {A B : Object} (f : FreeHom S A B) :
    (priceValuation conv m).V f = -(basisGain flows R m).V f := by
  rw [conversion_value flows conv hconv, market_eq_basisGain flows R m hbasis f]

/-- The canonical equity leg is that forced entry. -/
theorem equityConversion_entry (flows : S.Gen → PacioliGroup) (R : LotRefinement)
    (m : Commodity → ℚ) (e : AccountName)
    (hbasis : ∀ t, priceDot R.basisVector (flows t) = 0)
    {A B : Object} (f : FreeHom S A B) :
    (priceValuation (fun t => equityConversion e (flows t)) m).V f
      = -(basisGain flows R m).V f :=
  conversion_leg_forced flows _ R m (fun _ => add_equityConversion_mem_zeroRows e _)
    hbasis f

/-- Change in a completing leg under price motion, through lot-blind
    flows, when every commodity floats. The journal need not balance
    at basis: by `conversion_value` the leg moves by minus the change
    in the journal's value, and the basis value cancels. -/
theorem entry_change (flows conv : S.Gen → PacioliGroup) (R : LotRefinement)
    (hfl : ∀ k, R.Floating k) (p p' e : Commodity → ℚ)
    (hconv : ∀ t, flows t + conv t ∈ zeroRows)
    {A B : Object} (f : FreeHom S A B) :
    (priceValuation conv (R.marketVector p' e)).V f
        - (priceValuation conv (R.marketVector p e)).V f
      = -(priceValuation (fun t => R.forget (flows t)) (p' - p)).V f := by
  rw [conversion_value flows conv hconv, conversion_value flows conv hconv,
    ← basisGain_change flows R hfl p p' e f]
  simp only [basisGain, ValuationFunctor.sub_V]
  ring

end GenSpec

/-! ## Witnesses -/

namespace BasisGainExamples

/-- Lots of AAPL at $150, $160 and $170, all floating. Every other
    commodity carries no lot and is its own base, so the dollar has
    basis 1. -/
def lots : LotRefinement where
  base c :=
    if c = "AAPL{150}" then "AAPL" else if c = "AAPL{160}" then "AAPL"
    else if c = "AAPL{170}" then "AAPL" else c
  lot c :=
    if c = "AAPL{150}" then some ⟨"$", 150, false⟩
    else if c = "AAPL{160}" then some ⟨"$", 160, false⟩
    else if c = "AAPL{170}" then some ⟨"$", 170, false⟩ else none
  valueExpr _ := false

/-- A report price table: the dollar at 1, AAPL at `aapl`, and every
    other commodity at 0. -/
def quote (aapl : ℚ) : Commodity → ℚ := fun c =>
  if c = "$" then 1 else if c = "AAPL" then aapl else 0

def buy150 : PacioliGroup :=
  Finsupp.single ⟨"Assets:Brokerage", "AAPL{150}"⟩ 10
    + Finsupp.single ⟨"Assets:Cash", "$"⟩ (-1500)

def buy160 : PacioliGroup :=
  Finsupp.single ⟨"Assets:Brokerage", "AAPL{160}"⟩ 10
    + Finsupp.single ⟨"Assets:Cash", "$"⟩ (-1600)

/-- A sale of 10 AAPL at $170 with no lot selection. At C++ revision
    `76b9dc2b2` the default lot policy is `none` (journal.h:161-162),
    under which no lot is matched (xact.cc:528). The exchange at
    xact.cc:688-690 annotates the sold amount with its own per-unit
    cost as lot price and the posting's date (pool.cc:508-522), and,
    since the posting's amount carried no lot price (xact.cc:692),
    xact.cc:803-811 books the annotated amount. C++ therefore books a
    new automatic lot of -10 AAPL at $170, written `AAPL{170}` here
    without its lot date, and does not reduce the lot at $150. -/
def sell170 : PacioliGroup :=
  Finsupp.single ⟨"Assets:Brokerage", "AAPL{170}"⟩ (-10)
    + Finsupp.single ⟨"Assets:Cash", "$"⟩ 1700

def bareBuy150 : PacioliGroup :=
  Finsupp.single ⟨"Assets:Brokerage", "AAPL"⟩ 10
    + Finsupp.single ⟨"Assets:Cash", "$"⟩ (-1500)

def bareBuy160 : PacioliGroup :=
  Finsupp.single ⟨"Assets:Brokerage", "AAPL"⟩ 10
    + Finsupp.single ⟨"Assets:Cash", "$"⟩ (-1600)

/-- The bare purchases are the lot-blind flows of the refined ones. -/
theorem bareBuys_eq_forget :
    lots.forget buy150 = bareBuy150 ∧ lots.forget buy160 = bareBuy160 := by
  have h1 : ("AAPL{160}" : String) ≠ "AAPL{150}" := by decide
  have h2 : ("$" : String) ≠ "AAPL{150}" := by decide
  have h3 : ("$" : String) ≠ "AAPL{160}" := by decide
  have h4 : ("$" : String) ≠ "AAPL{170}" := by decide
  refine ⟨?_, ?_⟩ <;>
    simp [buy150, buy160, bareBuy150, bareBuy160, LotRefinement.forgetAccount, lots,
      h1, h2, h3, h4]

theorem lots_floating : ∀ k, lots.Floating k := by
  intro k
  refine ⟨fun l hl => ?_, rfl⟩
  simp only [lots] at hl
  split_ifs at hl <;> cases hl <;> rfl

theorem buys_balance_at_basis :
    priceDot lots.basisVector buy150 = 0 ∧ priceDot lots.basisVector buy160 = 0 := by
  have h1 : ("$" : String) ≠ "AAPL{150}" := by decide
  have h2 : ("$" : String) ≠ "AAPL{160}" := by decide
  have h3 : ("$" : String) ≠ "AAPL{170}" := by decide
  have h4 : ("AAPL{160}" : String) ≠ "AAPL{150}" := by decide
  refine ⟨?_, ?_⟩ <;>
    simp [buy150, buy160, lots, LotRefinement.basisVector, h1, h2, h3, h4] <;> norm_num

/-- `hbasis` is weaker than a balance at basis: a generator that moves
    $5 into one account and 5 EUR out of another balances in neither
    commodity, yet it is worth zero under `basisVector`. -/
theorem hbasis_weaker :
    priceDot lots.basisVector
      (Finsupp.single ⟨"Assets:A", "$"⟩ 5 + Finsupp.single ⟨"Assets:B", "EUR"⟩ (-5)) = 0 := by
  have h1 : ("$" : String) ≠ "AAPL{150}" := by decide
  have h2 : ("$" : String) ≠ "AAPL{160}" := by decide
  have h3 : ("$" : String) ≠ "AAPL{170}" := by decide
  have h5 : ("EUR" : String) ≠ "AAPL{150}" := by decide
  have h6 : ("EUR" : String) ≠ "AAPL{160}" := by decide
  have h7 : ("EUR" : String) ≠ "AAPL{170}" := by decide
  simp [lots, LotRefinement.basisVector, h1, h2, h3, h5, h6, h7]

/-- **A basis needs lots**: a basis vector over bare commodities that
    balances both purchases must price the dollar at zero, so over the
    lot-blind flows of these two purchases
    (`BasisGainExamples.bareBuys_eq_forget`) no basis that balances
    them values the dollar. -/
theorem bare_basis_degenerate (b : Commodity → ℚ)
    (h1 : priceDot b bareBuy150 = 0) (h2 : priceDot b bareBuy160 = 0) :
    b "$" = 0 := by
  simp [bareBuy150, bareBuy160] at h1 h2
  linarith

/-- Purchases at $150 and $160, then AAPL at $170: the basis gain is
    $300, so the forced entry is -$300. -/
theorem two_purchases_basis_gain :
    priceDot (lots.marketVector (quote 170) (fun _ => 0)) (buy150 + buy160)
      - priceDot lots.basisVector (buy150 + buy160) = 300 := by
  rw [lots.marketVector_of_floating _ _ lots_floating]
  have h1 : ("$" : String) ≠ "AAPL{150}" := by decide
  have h2 : ("$" : String) ≠ "AAPL{160}" := by decide
  have h3 : ("$" : String) ≠ "AAPL{170}" := by decide
  have h4 : ("AAPL{160}" : String) ≠ "AAPL{150}" := by decide
  have h5 : ("AAPL" : String) ≠ "$" := by decide
  simp [buy150, buy160, lots, quote, LotRefinement.basisVector, h1, h2, h3, h4, h5]
  norm_num

/-- **The basis gain is not the unrealized gain**: buy at $150 and sell
    at $170 with no lot selection. The basis gain is $200 at every AAPL
    quote, so none of it comes from a price change; it is realized gain
    across mismatched automatic lots that was never booked. -/
theorem sale_basis_gain_price_independent (aapl : ℚ) :
    priceDot (lots.marketVector (quote aapl) (fun _ => 0)) (buy150 + sell170)
      - priceDot lots.basisVector (buy150 + sell170) = 200 := by
  rw [lots.marketVector_of_floating _ _ lots_floating]
  have h1 : ("$" : String) ≠ "AAPL{150}" := by decide
  have h2 : ("$" : String) ≠ "AAPL{160}" := by decide
  have h3 : ("$" : String) ≠ "AAPL{170}" := by decide
  have h4 : ("AAPL{170}" : String) ≠ "AAPL{150}" := by decide
  have h6 : ("AAPL{170}" : String) ≠ "AAPL{160}" := by decide
  have h5 : ("AAPL" : String) ≠ "$" := by decide
  simp [buy150, sell170, lots, quote, LotRefinement.basisVector, h1, h2, h3, h4, h5, h6]
  ring

/-- Two atomic transactions on empty endpoints. -/
def twoBuys : GenSpec := ⟨Bool, fun _ => 0, fun _ => 0⟩

def twoBuysFlows : twoBuys.Gen → PacioliGroup := fun (b : Bool) => cond b buy150 buy160

theorem twoBuys_balance_at_basis : ∀ t, priceDot lots.basisVector (twoBuysFlows t) = 0 :=
  fun (t : Bool) => by
    cases t
    · exact buys_balance_at_basis.2
    · exact buys_balance_at_basis.1

/-- Both purchases, recorded in parallel. -/
def bothBuys : (GenSpec.freeT twoBuys).Hom (twoBuys.dom true + twoBuys.dom false)
    (twoBuys.cod true + twoBuys.cod false) :=
  (GenSpec.freeT twoBuys).tensor (GenSpec.genHom (S := twoBuys) true)
    (GenSpec.genHom (S := twoBuys) false)

/-- On the free model, the equity leg the two purchases leave out is
    worth -$300 at AAPL $170. -/
theorem twoBuys_forced_entry :
    (GenSpec.priceValuation (fun t => equityConversion "Equity" (twoBuysFlows t))
        (lots.marketVector (quote 170) (fun _ => 0))).V bothBuys = -300 := by
  rw [GenSpec.equityConversion_entry twoBuysFlows lots _ "Equity"
    twoBuys_balance_at_basis]
  have h := two_purchases_basis_gain
  rw [map_add, map_add] at h
  have h' : ((priceDot (lots.marketVector (quote 170) (fun _ => 0)) buy150
      + priceDot (lots.marketVector (quote 170) (fun _ => 0)) buy160
      - (priceDot lots.basisVector buy150 + priceDot lots.basisVector buy160) : ℚ) : ℝ)
        = 300 := by
    rw [h]; norm_num
  push_cast at h'
  rw [GenSpec.basisGain, ValuationFunctor.sub_V, bothBuys, ValuationFunctor.V_tensor,
    ValuationFunctor.V_tensor, GenSpec.priceValuation_gen, GenSpec.priceValuation_gen,
    GenSpec.priceValuation_gen, GenSpec.priceValuation_gen]
  show -(((priceDot (lots.marketVector (quote 170) (fun _ => 0)) buy150 : ℚ) : ℝ)
      + ((priceDot (lots.marketVector (quote 170) (fun _ => 0)) buy160 : ℚ) : ℝ)
      - (((priceDot lots.basisVector buy150 : ℚ) : ℝ)
        + ((priceDot lots.basisVector buy160 : ℚ) : ℝ)))
    = -300
  linarith

/-- On one fixated lot, with prices read in USD as the widget `W` moves
    from 10 to 15, the market-vector difference is zero, while the
    coarse reading moves by 5. -/
theorem fixated_price_motion_not_coarse :
    priceDot (LotExamples.widgetLots.marketVector
          (fun c => if c = "W" then 15 else 1) (fun _ => 0)
        - LotExamples.widgetLots.marketVector
          (fun c => if c = "W" then 10 else 1) (fun _ => 0))
        (LotExamples.oneLot "W {=10 USD}")
      ≠ priceDot ((fun c => if c = "W" then (15 : ℚ) else 1)
          - fun c => if c = "W" then 10 else 1)
        (LotExamples.widgetLots.forget (LotExamples.oneLot "W {=10 USD}")) := by
  have h₁ : ("W {=10 USD}" : String) ≠ "W {10 USD}" := by decide
  have h₂ : ("W {=10 USD}" : String) ≠ "W {12 USD}" := by decide
  norm_num [LotExamples.oneLot, LotRefinement.marketVector, LotRefinement.unfixedPrice,
    LotRefinement.forgetAccount, LotExamples.widgetLots, h₁, h₂]

/-- **The Floating hypothesis is necessary**: the unconditional coarse
    law of price motion is false. On one fixated lot the basis gain does
    not move, while the coarse right-hand side does. -/
theorem basisGain_change_needs_floating :
    ¬ (∀ (R : LotRefinement) (flows : GenSpec.unitSpec.Gen → PacioliGroup)
        (p p' e : Commodity → ℚ),
        (GenSpec.basisGain flows R (R.marketVector p' e)).V
            (GenSpec.genHom (S := GenSpec.unitSpec) PUnit.unit)
          - (GenSpec.basisGain flows R (R.marketVector p e)).V
            (GenSpec.genHom (S := GenSpec.unitSpec) PUnit.unit)
        = (GenSpec.priceValuation (fun t => R.forget (flows t)) (p' - p)).V
            (GenSpec.genHom (S := GenSpec.unitSpec) PUnit.unit)) := by
  intro h
  have h' := h LotExamples.widgetLots (fun _ => LotExamples.oneLot "W {=10 USD}")
    (fun c => if c = "W" then 10 else 1) (fun c => if c = "W" then 15 else 1)
    (fun _ => 0)
  rw [GenSpec.basisGain_change_refined, GenSpec.priceValuation_gen,
    GenSpec.priceValuation_gen] at h'
  exact fixated_price_motion_not_coarse (Rat.cast_injective h')

end BasisGainExamples

/-! ## The C++ unrealized-gains report -/

namespace OptUnrealizedGains

/-- The lot C++ books for the purchase in
    `test/baseline/opt-unrealized-gains.test`, 10 AAPL against
    $-200.00. At revision `76b9dc2b2` the transaction has two
    commodities and no null posting, so xact.cc:380 and 454-463 give
    the AAPL posting the computed cost $200.00, and the exchange at
    xact.cc:688-690 annotates the amount with the per-unit cost $20.00
    and the posting's date (pool.cc:508-522). The lot is written
    `AAPL{20}` here without its date, and it floats. -/
def lots : LotRefinement where
  base c := if c = "AAPL{20}" then "AAPL" else c
  lot c := if c = "AAPL{20}" then some ⟨"$", 20, false⟩ else none
  valueExpr _ := false

/-- The test's one transaction, refined by that lot, as the single
    generator of `GenSpec.unitSpec`. -/
def flows : GenSpec.unitSpec.Gen → PacioliGroup := fun _ =>
  Finsupp.single ⟨"Assets:Brokerage", "AAPL{20}"⟩ 10
    + Finsupp.single ⟨"Assets:Checking", "$"⟩ (-200)

/-- The report's market vector after the test's price directive of
    2008/10/20, AAPL at $30.00. -/
def market : Commodity → ℚ := lots.marketVector (BasisGainExamples.quote 30) (fun _ => 0)

theorem lots_floating : ∀ k, lots.Floating k := by
  intro k
  refine ⟨fun l hl => ?_, rfl⟩
  simp only [lots] at hl
  split_ifs at hl
  cases hl
  rfl

theorem balances_at_basis : ∀ t, priceDot lots.basisVector (flows t) = 0 := by
  intro _
  have h1 : ("$" : String) ≠ "AAPL{20}" := by decide
  simp [flows, lots, LotRefinement.basisVector, h1]
  norm_num

/-- The report's `Assets` row, $100.00, is the journal's basis gain. -/
theorem basisGain_value :
    (GenSpec.basisGain flows lots market).V (GenSpec.genHom (S := GenSpec.unitSpec) PUnit.unit)
      = 100 := by
  rw [← GenSpec.market_eq_basisGain _ _ _ balances_at_basis, GenSpec.priceValuation_gen,
    market, lots.marketVector_of_floating _ _ lots_floating]
  have h1 : ("$" : String) ≠ "AAPL{20}" := by decide
  have h2 : ("AAPL" : String) ≠ "$" := by decide
  simp [flows, lots, BasisGainExamples.quote, h1, h2]
  norm_num

/-- The report's `G` row, $-100.00, is the equity leg, worth minus the
    basis gain. -/
theorem gains_leg :
    (GenSpec.priceValuation (fun t => equityConversion "G" (flows t)) market).V
        (GenSpec.genHom (S := GenSpec.unitSpec) PUnit.unit) = -100 := by
  rw [GenSpec.equityConversion_entry _ lots _ "G" balances_at_basis, basisGain_value]

/-- The report's total, 0: the journal and its equity leg. -/
theorem total_zero :
    (GenSpec.priceValuation flows market).V (GenSpec.genHom (S := GenSpec.unitSpec) PUnit.unit)
      + (GenSpec.priceValuation (fun t => equityConversion "G" (flows t)) market).V
        (GenSpec.genHom (S := GenSpec.unitSpec) PUnit.unit) = 0 := by
  rw [gains_leg, GenSpec.market_eq_basisGain _ _ _ balances_at_basis, basisGain_value]
  norm_num

end OptUnrealizedGains

end

end Ledger
