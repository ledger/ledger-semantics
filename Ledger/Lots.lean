import Ledger.PriceVector

/-!
# Lots as distinct property types

Ellerman, "On Double-Entry Bookkeeping: The Mathematical Treatment",
Accounting Education 23:5 (2014), note 20 (text on p. 500, marker on
p. 498): valuing produced goods at cost "could be accommodated in
property accounting at the cost of treating 'Produced Widgets' as a
different form of property from 'Sold Widgets' (so each type of
property has a single unit value)". Ellerman proposes the refinement
for a different valuation basis and sets it aside; treating Ledger's
lots the same way is an extension by analogy, not the article's claim.
Note 18 warns that tagging an amount with database fields is not
vector accounting. A lot here is not such a tag: it is a property type
in its own right, an annotated commodity string, so refined flows
still live in `Account →₀ ℚ` and add freely. Forgetting lots is a
group homomorphism (`LotRefinement.forget`), and the flow denotation
commutes with it (`LotRefinement.flow_forget`), which is the relation
between refined flows and the lot-blind flows the oracle computes
(the oracle's generators record bare-commodity amounts; see the
`flows` binding of `finalizeXact` in `Ledger/Journal.lean`).

This module specifies lot identity and valuation. It does not specify
lot matching. The theorems prove linear algebra only; each
correspondence to a C++ report is an observed C++ behavior, cited
beside the definition that models it together with the conditions
under which it holds, with C++ source locations at revision
`76b9dc2b2`. `market_of_lotBlind` scopes what lot-blind flows
support: market value under `-X` when every commodity floats (no
fixated lot and no valuation expression) and prices are read in the
target, whose own price is then 1. `-B`, fixated lots under `-X`, and
plain `-V` need refined flows
(`basis_not_factor`, `fixated_not_factor`, `plainV_not_factor`).
-/

namespace Ledger

noncomputable section

/-- A lot price annotation on a commodity, with its own commodity.

`fixated` is set by every fixation syntax: `{=P}` and `{{=T}}`
(annotate.cc:169), and the fixated costs `@ =P` and `@@ =T`, which C++
turns into a fixated annotation at xact.cc:816-819 (textual_xacts.cc:713
sets `POST_COST_FIXATED`; the oracle parses them in the `@ =` and
`@@ =` branches of `annotLoop` in `Ledger/Journal.lean`, witness
`test/regress/1794.test`). -/
structure LotPrice where
  /-- The commodity the lot price is denominated in. -/
  comm : Commodity
  /-- The per-unit lot price (a `{{T}}` total is divided by the quantity). -/
  perUnit : ℚ
  /-- Whether the price is fixated. -/
  fixated : Bool

/-- A refinement of the commodity alphabet by lots. Commodities are
abstract annotated strings; the structure reads off each one's base
commodity, its lot price if it has one, and whether a valuation
expression applies to it. A refinement describes the commodities of
one journal: `lot` and `valueExpr` are read off that journal's
commodities and are `none` and `false` on every other string, so a
hypothesis quantified over all commodities, such as
`∀ k, R.Floating k`, constrains only the commodities the journal
uses. -/
structure LotRefinement where
  /-- The commodity a lot annotates (C++ `referent()`). -/
  base : Commodity → Commodity
  /-- The lot price, if the commodity carries one. -/
  lot : Commodity → Option LotPrice
  /-- Whether a valuation expression applies to the commodity: a
      `((expr))` annotation (annotate.cc:417-418), or an expression
      that C++ writes into the annotation of a posting's commodity
      after balancing, taken from a `Value` tag, from a `value`
      directive of the account, of the commodity or of the whole
      journal, or from the matching session options
      (post.cc:1056-1106, run for each posting at journal.cc:585).
      `commodity_t::find_price` also applies a `value` directive of
      the base commodity (commodity.cc:206-207). -/
  valueExpr : Commodity → Bool

namespace LotRefinement

variable (R : LotRefinement)

/-- Forget the lot on one account-commodity pair. -/
def forgetAccount (a : Account) : Account := ⟨a.name, R.base a.commodity⟩

/-- Forgetting lots: the group homomorphism from refined flows to the
    lot-blind flows the oracle computes. -/
def forget : PacioliGroup →+ PacioliGroup :=
  Finsupp.mapDomain.addMonoidHom R.forgetAccount

@[simp] theorem forget_single (a : Account) (q : ℚ) :
    R.forget (Finsupp.single a q) = Finsupp.single (R.forgetAccount a) q := by
  simp [forget, Finsupp.mapDomain_single]

/-- **Pricing through forgetting.** A price vector that reads only a
    unit's base commodity values refined flows as the plain price
    vector values the forgotten flows. -/
theorem priceDot_forget (p : Commodity → ℚ) (x : PacioliGroup) :
    priceDot p (R.forget x) = priceDot (p ∘ R.base) x := by
  have h : (priceDot p).comp R.forget = priceDot (p ∘ R.base) := by
    refine Finsupp.addHom_ext fun a q => ?_
    simp [forgetAccount]
  exact DFunLike.congr_fun h x

/-- The tie to the tower: the flow denotation commutes with
    forgetting lots. The lot-blind flow of every morphism is the
    forgetting of its refined flow. -/
theorem flow_forget {S : GenSpec} (flows : S.Gen → PacioliGroup)
    {A B : Object} (f : GenSpec.FreeHom S A B) :
    GenSpec.flow (fun t => R.forget (flows t)) f
      = R.forget (GenSpec.flow flows f) :=
  GenSpec.flow_map R.forget flows f

/-! ## Market valuation of one unit -/

/-- The price of one unit of `k` when no fixation applies: a
    valuation expression wins (annotate.cc:417-418,
    commodity.cc:206-207), otherwise the base commodity's price, since
    `commodity_t::find_price` searches the price graph of the
    referent. `p` and `e` are total here. In C++ a missing price
    leaves the amount unconverted, except that under `-X tgt` a single
    annotated amount whose lot price is in `tgt` is valued at its lot
    price times its quantity (report.cc:957-970), so a total `p` is an
    idealization. -/
def unfixedPrice (p e : Commodity → ℚ) (k : Commodity) : ℚ :=
  if R.valueExpr k then e k else p (R.base k)

/-- The per-unit market value of `k`: a fixated lot's value is its lot
    price, whatever the market says (annotate.cc:403-405,
    amount.cc:1270-1272). The commodity the value lands in is
    `xTarget` or `vTarget` below. -/
def marketVector (p e : Commodity → ℚ) (k : Commodity) : ℚ :=
  match R.lot k with
  | some l => if l.fixated then l.perUnit else R.unfixedPrice p e k
  | none => R.unfixedPrice p e k

/-- A commodity whose market value follows its base's price: no
    fixation by any syntax, and no valuation expression. -/
def Floating (k : Commodity) : Prop :=
  (∀ l, R.lot k = some l → l.fixated = false) ∧ R.valueExpr k = false

theorem marketVector_of_floating (p e : Commodity → ℚ)
    (h : ∀ k, R.Floating k) : R.marketVector p e = p ∘ R.base := by
  funext k
  obtain ⟨hfix, hve⟩ := h k
  unfold marketVector unfixedPrice
  cases hl : R.lot k with
  | none => simp [hve]
  | some l => simp [hfix l hl, hve]

/-- When every commodity floats, the market valuation of refined flows
    factors through forgetting lots. -/
theorem market_factors_of_floating (p e : Commodity → ℚ)
    (h : ∀ k, R.Floating k) (x : PacioliGroup) :
    priceDot (R.marketVector p e) x = priceDot p (R.forget x) := by
  rw [R.marketVector_of_floating p e h, R.priceDot_forget]

/-- **The scoping theorem.** The same statement on the tower: under
    `-X` over journals whose commodities all float, the market value
    of any morphism's refined flow is computable from its lot-blind
    flow, which is what the oracle already has. That C++ `-X tgt`
    reports `marketX` when `p` gives prices in `tgt`, so that
    `p tgt = 1`, is a C++-observed fact (commodity.cc `find_price`
    uses `referent()`; amount.cc:927 `in_place_round` leaves the
    rational untouched, so valuation is exactly linear), not a
    theorem here; floating commodities meet the other conditions
    stated for `marketX`, and that `marketX` then places this value
    in `tgt` is `marketX_of_floating`. -/
theorem market_of_lotBlind {S : GenSpec} (flows : S.Gen → PacioliGroup)
    (p e : Commodity → ℚ) (h : ∀ k, R.Floating k)
    {A B : Object} (f : GenSpec.FreeHom S A B) :
    priceDot (R.marketVector p e) (GenSpec.flow flows f)
      = priceDot p (GenSpec.flow (fun t => R.forget (flows t)) f) := by
  rw [R.flow_forget, R.market_factors_of_floating p e h]

/-! ## Units: where the market value lands -/

/-- Where the model places a unit's value under `-X tgt`: a fixated
    lot's value stays in its lot price's commodity
    (amount.cc:1270-1272), and every other unit's value lands in
    `tgt`. -/
def xTarget (tgt : Commodity) (k : Commodity) : Commodity :=
  match R.lot k with
  | some l => if l.fixated then l.comm else tgt
  | none => tgt

/-- `-X tgt`, vector-valued. It models C++ where C++ finds every
    price it needs in `tgt` (the idealization stated for
    `unfixedPrice`), and then under three conditions, which the
    definitions do not enforce. First, `p` gives prices in `tgt`, so
    `p tgt = 1`: C++ returns an amount whose base commodity is `tgt`
    in `tgt`, unconverted (amount.cc:1279-1280). Second, every
    commodity whose base is `tgt` floats, because that return comes
    before a fixated lot price or a valuation expression is used, so
    C++ reports such a unit's quantity where the model reports its lot
    price or its expression's value. Third, every valuation expression
    evaluates to an amount in `tgt`, because C++ places the value in
    the commodity of the result, after repricing a result in several
    commodities into `tgt` (commodity.cc:144-154,
    amount.cc:1323-1327). -/
def marketX (tgt : Commodity) (p e : Commodity → ℚ) :
    PacioliGroup →+ (Commodity →₀ ℚ) :=
  Finsupp.liftAddHom fun a =>
    (Finsupp.singleAddHom (R.xTarget tgt a.commodity)).comp
      (AddMonoidHom.mulRight (R.marketVector p e a.commodity))

/-- The single-unit hypothesis: every lot price is denominated in
    the valuation target. -/
def LotsIn (tgt : Commodity) : Prop :=
  ∀ k l, R.lot k = some l → l.comm = tgt

theorem xTarget_of_lotsIn {tgt : Commodity} (hU : R.LotsIn tgt)
    (k : Commodity) : R.xTarget tgt k = tgt := by
  unfold xTarget
  cases hl : R.lot k with
  | none => rfl
  | some l => simp [hU k l hl]

/-- Under the single-unit hypothesis the vector-valued `-X` report is
    the scalar `priceDot` of the market vector, placed in `tgt`.
    Without it the scalar reading can fail: a fixated lot priced
    outside `tgt` keeps its value in its own commodity. The reading
    also holds when every commodity floats (`marketX_of_floating`). -/
theorem marketX_of_lotsIn {tgt : Commodity} (hU : R.LotsIn tgt)
    (p e : Commodity → ℚ) (x : PacioliGroup) :
    R.marketX tgt p e x
      = Finsupp.single tgt (priceDot (R.marketVector p e) x) := by
  have h : R.marketX tgt p e
      = (Finsupp.singleAddHom tgt).comp (priceDot (R.marketVector p e)) := by
    refine Finsupp.addHom_ext fun a q => ?_
    simp [marketX, R.xTarget_of_lotsIn hU]
  exact DFunLike.congr_fun h x

/-- When every commodity floats, every unit lands in the target, since
    only a fixated lot keeps its own commodity. -/
theorem xTarget_of_floating {tgt : Commodity} (h : ∀ k, R.Floating k)
    (k : Commodity) : R.xTarget tgt k = tgt := by
  unfold xTarget
  cases hl : R.lot k with
  | none => rfl
  | some l => simp [(h k).1 l hl]

/-- When every commodity floats, the vector-valued `-X` report is the
    scalar `priceDot` of the market vector, placed in `tgt`, whatever
    the commodities of the lot prices. With `market_of_lotBlind` this
    makes `-X` over a journal whose commodities all float a function
    of its lot-blind flows. -/
theorem marketX_of_floating {tgt : Commodity} (h : ∀ k, R.Floating k)
    (p e : Commodity → ℚ) (x : PacioliGroup) :
    R.marketX tgt p e x
      = Finsupp.single tgt (priceDot (R.marketVector p e) x) := by
  have hx : R.marketX tgt p e
      = (Finsupp.singleAddHom tgt).comp (priceDot (R.marketVector p e)) := by
    refine Finsupp.addHom_ext fun a q => ?_
    simp [marketX, R.xTarget_of_floating h]
  exact DFunLike.congr_fun hx x

/-- Under plain `-V` (no `-X`), a floating lot is valued in its lot
    price's commodity (annotate.cc:406-409, amount.cc:1274-1275); an
    unannotated commodity goes wherever the price graph sends it,
    modeled by `dflt`. A valuation expression's value lands instead
    in the commodity of the expression's result (amount.cc:1323-1327),
    so `marketV` models it only where that is the commodity named
    here. -/
def vTarget (dflt : Commodity → Commodity) (k : Commodity) : Commodity :=
  (R.lot k).elim (dflt k) LotPrice.comm

/-- Plain `-V`, vector-valued. `pv c b` is the price of one `b` in
    `c`. -/
def marketV (pv : Commodity → Commodity → ℚ) (e : Commodity → ℚ)
    (dflt : Commodity → Commodity) : PacioliGroup →+ (Commodity →₀ ℚ) :=
  Finsupp.liftAddHom fun a =>
    (Finsupp.singleAddHom (R.vTarget dflt a.commodity)).comp
      (AddMonoidHom.mulRight
        (R.marketVector (pv (R.vTarget dflt a.commodity)) e a.commodity))

/-! ## Basis and gain -/

/-- The per-unit basis (`-B`): the lot price, or 1 for an unannotated
    commodity, which is its own basis. C++ `-B` reports
    `rounded(cost)` (report.h:607-610), which `get_cost`
    (post.cc:400-418) reads as the booked cost when the posting has
    one, so the two agree where the booked cost equals the lot price
    times the quantity, the condition `gainG_of_basis_cost` assumes.
    The scalar reading is sound when every lot price is in the target
    (`LotsIn`) and every unannotated holding is the target itself. -/
def basisVector (k : Commodity) : ℚ := (R.lot k).elim 1 LotPrice.perUnit

/-- Market minus basis, per unit. -/
def gainVector (p e : Commodity → ℚ) : Commodity → ℚ :=
  R.marketVector p e - R.basisVector

/-- The model's per-unit gain on every fixated lot is zero:
    `marketVector` values the lot at its lot price
    (annotate.cc:403-405), which is its basis. C++ differs under `-X`
    of the lot's base commodity, outside the conditions of `marketX`:
    it reports the lot's quantity in that commodity
    (amount.cc:1279-1280), so its `-G` is that quantity minus the
    booked cost. -/
theorem gain_fixated_zero (p e : Commodity → ℚ) {k : Commodity}
    {l : LotPrice} (hl : R.lot k = some l) (hf : l.fixated = true) :
    R.gainVector p e k = 0 := by
  simp [gainVector, marketVector, basisVector, hl, hf]

/-- `-G` as C++ computes it when `-X tgt` precedes `-G` on the command
    line, under the conditions stated for `marketX`: the market value,
    placed as `marketX` places it, minus the posting's own booked cost
    component, a separate input that is not revalued (report.h:925-956).
    Each display expression is a `merged_expr_t` whose pieces apply in
    option order (report.h:853-861, expr.cc:333-349), and the piece
    that `-G` adds reads `total_expr` rather than the display total, so
    it replaces the `market` piece that `-X` added before it. Two other
    invocations differ from this model. Plain `-G` has no exchange
    commodity, so `market` falls back to `value(moment)`
    (report.cc:947-951) and places the market leg as `vTarget` does.
    Under `-G -X tgt`, the `market` piece that `-X` turns on through
    `-V` (report.h:903-909, 1034-1040) applies last, so C++ also
    revalues a booked cost in another commodity into `tgt`. The
    booked cost is not determined by the refined flow: xact.cc:696-729
    folds the gain, rounded at commodity precision plus the amount's
    precision, into `post->cost`, `pool.cc` `exchange` rounds per-unit
    prices, and `post.cc:400-418` (`get_cost`) reads the result. -/
def gainG (tgt : Commodity) (p e : Commodity → ℚ) (x : PacioliGroup)
    (cost : Commodity →₀ ℚ) : Commodity →₀ ℚ :=
  R.marketX tgt p e x - cost

/-- `gainG` is the scalar gain functional on refined flows under two
    explicit hypotheses: every lot price is in the target, and the
    booked cost equals the basis value in `tgt`. The second holds for
    a lot whose posting cost after the rounded fold equals its lot
    price times its quantity, and for a posting of `tgt` itself
    without a lot or a cost, whose cost `get_cost` reads as the
    amount (post.cc:400-418). It fails for an acquisition booked in a
    commodity other than the lot price's, where xact.cc:693 skips the
    fold and the cost stays in that commodity; `basisVector` states
    the condition on unannotated holdings. The result then lies in
    `tgt`, where revaluing into `tgt` changes nothing, so
    `-G -X tgt` agrees with `-X tgt -G` in this regime. -/
theorem gainG_of_basis_cost {tgt : Commodity} (hU : R.LotsIn tgt)
    (p e : Commodity → ℚ) (x : PacioliGroup) (cost : Commodity →₀ ℚ)
    (hcost : cost = Finsupp.single tgt (priceDot R.basisVector x)) :
    R.gainG tgt p e x cost
      = Finsupp.single tgt (priceDot (R.gainVector p e) x) := by
  rw [gainG, R.marketX_of_lotsIn hU, hcost, ← Finsupp.single_sub, gainVector,
    priceDot_sub_prices]

/-- Motion of the price table `p`, with the valuation expressions `e`
    held fixed, is invisible on every non-floating commodity. Holding
    `e` fixed is a modeling choice: C++ evaluates a valuation
    expression in the default scope and reprices a basket result at
    market (commodity.cc:116-155), so such a value can move with
    prices. -/
theorem marketVector_sub_of_not_floating (p p' e : Commodity → ℚ) (k : Commodity)
    (hk : ¬ R.Floating k) :
    (R.marketVector p' e - R.marketVector p e) k = 0 := by
  unfold Floating at hk
  simp only [Pi.sub_apply, marketVector, unfixedPrice]
  cases hl : R.lot k with
  | none =>
    have hv : R.valueExpr k = true := by
      by_contra hv
      apply hk
      refine ⟨fun l h => by simp [hl] at h, ?_⟩
      simpa using hv
    simp [hv]
  | some l =>
    cases hf : l.fixated with
    | true => simp [hf]
    | false =>
      have hv : R.valueExpr k = true := by
        by_contra hv
        apply hk
        refine ⟨fun l' h => ?_, by simpa using hv⟩
        rw [hl] at h
        cases h
        exact hf
      simp [hv]

theorem marketVector_sub_of_floating (p p' e : Commodity → ℚ) (k : Commodity)
    (hk : R.Floating k) :
    (R.marketVector p' e - R.marketVector p e) k = (p' - p) (R.base k) := by
  obtain ⟨hfix, hve⟩ := hk
  simp only [Pi.sub_apply, marketVector, unfixedPrice]
  cases hl : R.lot k with
  | none => simp [hve]
  | some l => simp [hfix l hl, hve]

end LotRefinement

/-! ## Counterexamples: what lot-blind flows cannot support -/

namespace LotExamples

/-- Four lots of one widget `W`: floating at 10 USD and 12 USD, fixated
    at 10 USD, and floating at 10 EUR. Every commodity has base `W`,
    those outside the four lots included, which is why
    `widgetLots_forget` holds for any two commodities; the
    counterexamples apply it only to two lots of `W`, so none of them
    depends on the base of another commodity. -/
def widgetLots : LotRefinement where
  base _ := "W"
  lot k :=
    if k = "W {10 USD}" then some ⟨"USD", 10, false⟩
    else if k = "W {12 USD}" then some ⟨"USD", 12, false⟩
    else if k = "W {=10 USD}" then some ⟨"USD", 10, true⟩
    else if k = "W {10 EUR}" then some ⟨"EUR", 10, false⟩
    else none
  valueExpr _ := false

/-- One unit of a widget lot in the broker account. -/
def oneLot (k : Commodity) : PacioliGroup :=
  Finsupp.single ⟨"Assets:Broker", k⟩ 1

theorem widgetLots_forget (k k' : Commodity) :
    widgetLots.forget (oneLot k) = widgetLots.forget (oneLot k') := by
  simp [oneLot, LotRefinement.forgetAccount, widgetLots]

/-- **`-B` needs refined flows.** Two floating lots of one base at
    different lot prices have equal forgotten flows and different
    basis values. -/
theorem basis_not_factor : ∃ (R : LotRefinement) (x y : PacioliGroup),
    R.forget x = R.forget y
      ∧ priceDot R.basisVector x ≠ priceDot R.basisVector y := by
  refine ⟨widgetLots, oneLot "W {10 USD}", oneLot "W {12 USD}",
    widgetLots_forget _ _, ?_⟩
  have h : ("W {12 USD}" : String) ≠ "W {10 USD}" := by decide
  norm_num [oneLot, LotRefinement.basisVector, widgetLots, h]

/-- **Fixated lots need refined flows under `-X`.** A fixated and a
    floating lot of one base, with equal forgotten flows, differ in
    market value once the market moves off the lot price. The witness
    reads prices in USD, pricing `W` at 15 and USD itself at 1, so the
    example sits within the conditions stated for `marketX` with
    target USD. -/
theorem fixated_not_factor : ∃ (R : LotRefinement) (p e : Commodity → ℚ)
    (x y : PacioliGroup), R.forget x = R.forget y
      ∧ priceDot (R.marketVector p e) x ≠ priceDot (R.marketVector p e) y := by
  refine ⟨widgetLots, fun c => if c = "W" then 15 else 1, fun _ => 0,
    oneLot "W {=10 USD}", oneLot "W {10 USD}", widgetLots_forget _ _, ?_⟩
  have h₁ : ("W {=10 USD}" : String) ≠ "W {10 USD}" := by decide
  have h₂ : ("W {=10 USD}" : String) ≠ "W {12 USD}" := by decide
  norm_num [oneLot, LotRefinement.marketVector, LotRefinement.unfixedPrice,
    widgetLots, h₁, h₂]

/-- **Plain `-V` needs refined flows.** Two floating lots of one base
    whose lot prices are in different commodities have equal forgotten
    flows, and their `-V` values land in different commodities. -/
theorem plainV_not_factor : ∃ (R : LotRefinement)
    (pv : Commodity → Commodity → ℚ) (e : Commodity → ℚ)
    (dflt : Commodity → Commodity) (x y : PacioliGroup),
    R.forget x = R.forget y ∧ R.marketV pv e dflt x ≠ R.marketV pv e dflt y := by
  refine ⟨widgetLots, fun _ _ => 1, fun _ => 0, id, oneLot "W {10 USD}",
    oneLot "W {10 EUR}", widgetLots_forget _ _, ?_⟩
  intro h
  have h' := congrArg (fun v : Commodity →₀ ℚ => v "USD") h
  simp [oneLot, LotRefinement.marketV, LotRefinement.vTarget,
    LotRefinement.marketVector, LotRefinement.unfixedPrice, widgetLots] at h'

end LotExamples

end

end Ledger
