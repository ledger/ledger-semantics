import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Ledger.Pacioli
import Ledger.TimedPrices

/-!
# Price-vector valuation over the free model

Ellerman, "On Double-Entry Bookkeeping: The Mathematical Treatment",
Accounting Education 23:5 (2014) 483-501, pp. 497-498: given a price
vector, "the vector accounts of property accounting collapse to the
scalar accounts of value accounting", and "Scalar equation = price
vector times vector equation". This module defines that dot product
on the carrier `PacioliGroup` and the valuation functors it induces
on the free model, each an instance of `GenSpec.ofFlowHom`.

Prices are rational inside the carrier `PacioliGroup` (`priceDot`),
and the cast to ℝ happens at the `ValuationFunctor` boundary, as for
`accountValuation`.

`CommodityValuation` admits two readings, and this module states
both. The quantity reading `GenSpec.quantityValuation` is the net
quantity of one commodity moved, and it vanishes on journals that
balance per commodity. The value reading is value in the numeraire
`c`, the family
`fun c => (1 / (p c : ℝ)) • GenSpec.priceValuation flows p`, which is
what a price action relates; it has no definition of its own and
appears in `GenSpec.valueIn_eq_quantity_of_single` and, over
`priceVectorValuation`, in `exchangeReport`. The latter presents
`-X b` as `constModel` over the price-vector functional; that is an
idealization, not a bisimulated claim, because it needs a total,
nowhere-zero price table and ignores fixated lot prices. That
cost-basis reports need lots as commodities is an extrapolation from
Ellerman's note 20, not his claim.

`priceDot`, `valueHom` and the free-model functors built on them are
noncomputable, so an executable market valuation needs a computable
twin with an agreement theorem.
-/

namespace Ledger

noncomputable section

/-! ## The dot product (p. 498) -/

/-- Ellerman's scalar product `p · x` of a price vector with the
    ledger-wide property vector: `linearCombination p ∘ trialBalance`. -/
def priceDot (p : Commodity → ℚ) : PacioliGroup →+ ℚ :=
  (Finsupp.linearCombination ℚ p).toAddMonoidHom.comp trialBalance

theorem priceDot_apply (p : Commodity → ℚ) (x : PacioliGroup) :
    priceDot p x = x.sum fun a q => q * p a.commodity := by
  simp only [priceDot, trialBalance, AddMonoidHom.coe_comp, Function.comp_apply,
    LinearMap.toAddMonoidHom_coe, Finsupp.linearCombination_apply,
    Finsupp.mapDomain.addMonoidHom_apply, smul_eq_mul]
  rw [Finsupp.sum_mapDomain_index (by simp) (by intros; ring)]

@[simp] theorem priceDot_single (p : Commodity → ℚ) (a : Account) (q : ℚ) :
    priceDot p (Finsupp.single a q) = q * p a.commodity := by
  rw [priceDot_apply, Finsupp.sum_single_index (by simp)]

/-- The dot product is linear in the price vector: difference. -/
theorem priceDot_sub_prices (p q : Commodity → ℚ) (x : PacioliGroup) :
    priceDot (p - q) x = priceDot p x - priceDot q x := by
  simp only [priceDot_apply, Finsupp.sum, Pi.sub_apply, mul_sub,
    Finset.sum_sub_distrib]

/-- The dot product is linear in the price vector: scaling. -/
theorem priceDot_smul_prices (k : ℚ) (p : Commodity → ℚ) (x : PacioliGroup) :
    priceDot (k • p) x = k * priceDot p x := by
  simp only [priceDot_apply, Pi.smul_apply, smul_eq_mul, Finsupp.mul_sum]
  refine Finsupp.sum_congr fun a _ => ?_
  ring

/-- Property-balanced implies value-balanced, at every price vector. -/
theorem priceDot_of_mem_zeroRows (p : Commodity → ℚ) {x : PacioliGroup}
    (hx : x ∈ zeroRows) : priceDot p x = 0 := by
  have h : trialBalance x = 0 := mem_zeroRows.mp hx
  simp [priceDot, h]

/-- The converse fails at **every** price vector: since at least two
    commodities exist, the functional `p ·` on property vectors has a
    nonzero kernel, and `trialBalance` is onto, so value-neutral does
    not imply zero-row. The statement quantifies over every `p`
    because a bare existential would be satisfied by the zero price
    vector. This is a consequence of the linear algebra, not a claim
    of the article. -/
theorem value_neutral_not_zeroRow (p : Commodity → ℚ) :
    ∃ x : PacioliGroup, x ∉ zeroRows ∧ priceDot p x = 0 := by
  by_cases h : p "W" = 0
  · refine ⟨Finsupp.single ⟨"A", "W"⟩ 1, ?_, ?_⟩
    · intro hx
      rw [mem_zeroRows, trialBalance_single] at hx
      simp at hx
    · simp [h]
  · refine ⟨Finsupp.single ⟨"A", "USD"⟩ (p "W") - Finsupp.single ⟨"A", "W"⟩ (p "USD"),
      ?_, ?_⟩
    · intro hx
      rw [mem_zeroRows, map_sub, trialBalance_single, trialBalance_single] at hx
      have h2 := congrArg (fun v : Commodity →₀ ℚ => v "USD") hx
      simp at h2
      exact h h2
    · simp [mul_comm]

/-! ## Per-account value -/

/-- The value, at prices `p`, of account name `n`'s property vector: a
    per-account report line. -/
def valueHom (p : Commodity → ℚ) (n : AccountName) : PacioliGroup →+ ℚ :=
  Finsupp.liftAddHom fun a =>
    if a.name = n then AddMonoidHom.mulLeft (p a.commodity) else 0

theorem valueHom_apply (p : Commodity → ℚ) (n : AccountName) (x : PacioliGroup) :
    valueHom p n x = x.sum fun a q => if a.name = n then q * p a.commodity else 0 := by
  rw [valueHom, Finsupp.liftAddHom_apply]
  refine Finsupp.sum_congr fun a _ => ?_
  split_ifs <;> simp [mul_comm]

@[simp] theorem valueHom_single (p : Commodity → ℚ) (n : AccountName)
    (a : Account) (q : ℚ) :
    valueHom p n (Finsupp.single a q) = if a.name = n then q * p a.commodity else 0 := by
  rw [valueHom_apply, Finsupp.sum_single_index (by simp)]

/-- Per-account value is linear in the price vector: difference. -/
theorem valueHom_sub_prices (p q : Commodity → ℚ) (n : AccountName) :
    valueHom (p - q) n = valueHom p n - valueHom q n := by
  refine AddMonoidHom.ext fun x => ?_
  rw [AddMonoidHom.sub_apply, valueHom_apply, valueHom_apply, valueHom_apply,
    ← Finsupp.sum_sub]
  refine Finsupp.sum_congr fun a _ => ?_
  split_ifs <;> simp [mul_sub]

/-- **Attribution**: the ledger-wide value is the sum of the
    per-account-name values, over any set of names covering the
    support. -/
theorem priceDot_eq_sum_valueHom (p : Commodity → ℚ) (x : PacioliGroup)
    (ns : Finset AccountName) (hns : ∀ a ∈ x.support, a.name ∈ ns) :
    priceDot p x = ∑ n ∈ ns, valueHom p n x := by
  simp only [priceDot_apply, valueHom_apply, Finsupp.sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [Finset.sum_ite_eq, if_pos (hns a ha)]

/-! ## The free model: total value, per-account value and the quantity reading -/

namespace GenSpec

variable {S : GenSpec}

/-- Total value: the net value moved at prices `p`, summed over
    accounts, in the unit in which `p` is quoted. This functor is not
    itself the value reading: that reading's member `c` is
    `(1 / (p c : ℝ)) •` this functor, and it takes the same values as
    this functor when `p c = 1`. -/
def priceValuation (flows : S.Gen → PacioliGroup) (p : Commodity → ℚ) :
    ValuationFunctor (freeT S) := ofFlowHom flows (priceDot p)

/-- Per-account-name value at prices `p`. -/
def accountValue (flows : S.Gen → PacioliGroup) (p : Commodity → ℚ)
    (n : AccountName) : ValuationFunctor (freeT S) := ofFlowHom flows (valueHom p n)

/-- The **quantity reading** of `CommodityValuation`: `CV c` is the net
    quantity of commodity `c` moved, summed over accounts. It vanishes
    on every journal whose entries balance per commodity
    (`quantityValuation_vanishes`), so it is not a report-grade
    measurement; `accountValue` is, per account name. -/
def quantityValuation (flows : S.Gen → PacioliGroup) : CommodityValuation (freeT S) :=
  fun c => ofFlowHom flows (commodityTotal c)

theorem priceValuation_V (flows : S.Gen → PacioliGroup) (p : Commodity → ℚ)
    {A B : Object} (f : FreeHom S A B) :
    (priceValuation flows p).V f = ((priceDot p (flow flows f) : ℚ) : ℝ) := rfl

@[simp] theorem priceValuation_gen (flows : S.Gen → PacioliGroup) (p : Commodity → ℚ)
    (t : S.Gen) :
    (priceValuation flows p).V (genHom t) = ((priceDot p (flows t) : ℚ) : ℝ) :=
  ofFlowHom_gen flows _ t

theorem quantityValuation_V (flows : S.Gen → PacioliGroup) (c : Commodity)
    {A B : Object} (f : FreeHom S A B) :
    (quantityValuation flows c).V f = ((trialBalance (flow flows f) c : ℚ) : ℝ) := rfl

/-- Total value is linear in the price vector: difference. -/
theorem priceValuation_sub_prices (flows : S.Gen → PacioliGroup) (p q : Commodity → ℚ)
    {A B : Object} (f : FreeHom S A B) :
    (priceValuation flows (p - q)).V f
      = (priceValuation flows p).V f - (priceValuation flows q).V f := by
  rw [priceValuation_V, priceValuation_V, priceValuation_V, priceDot_sub_prices,
    Rat.cast_sub]

/-- Property-balanced journals balance in value at every price vector:
    p. 498 read as a theorem, valuation preserves zero-rows. -/
theorem priceValuation_balanced (flows : S.Gen → PacioliGroup)
    (hbal : ∀ t, flows t ∈ zeroRows) (p : Commodity → ℚ)
    {A B : Object} (f : FreeHom S A B) : (priceValuation flows p).V f = 0 := by
  rw [priceValuation_V,
    free_hom_balanced flows _ (fun t => priceDot_of_mem_zeroRows p (hbal t)) f,
    Rat.cast_zero]

/-- The quantity reading vanishes on journals that balance per
    commodity. -/
theorem quantityValuation_vanishes (flows : S.Gen → PacioliGroup)
    (hbal : ∀ t, flows t ∈ zeroRows) (c : Commodity) {A B : Object}
    (f : FreeHom S A B) : (quantityValuation flows c).V f = 0 := by
  rw [quantityValuation_V, free_double_entry flows hbal f]
  simp

/-- Per-account values sum to total value for every derived morphism,
    provided the names `ns` cover every generator's postings. -/
theorem priceValuation_eq_sum_accountValue (flows : S.Gen → PacioliGroup)
    (p : Commodity → ℚ) (ns : Finset AccountName)
    (hns : ∀ t, ∀ a ∈ (flows t).support, a.name ∈ ns)
    {A B : Object} (f : FreeHom S A B) :
    (priceValuation flows p).V f = ∑ n ∈ ns, (accountValue flows p n).V f :=
  free_valuation_ext (priceValuation flows p)
    (ValuationFunctor.finsetSum ns (accountValue flows p)) (fun t => by
      rw [ValuationFunctor.finsetSum_V, priceValuation_gen]
      simp only [accountValue, ofFlowHom_gen]
      rw [priceDot_eq_sum_valueHom p (flows t) ns (hns t), Rat.cast_sum]) f

end GenSpec

/-! ## The abstract price-vector valuation -/

/-- Price-weighted sum of any quantity family over a finite commodity
    set: the abstract "price vector times quantity vector". -/
def priceVectorValuation {T : 𝕋} (Q : CommodityValuation T)
    (cs : Finset Commodity) (price : Commodity → ℝ) : ValuationFunctor T :=
  ValuationFunctor.finsetSum cs (fun c => price c • Q c)

/-- If each commodity balances separately on generators, so does the
    price-weighted sum. The hypothesis is stronger than Ledger journals
    satisfy, since `@`-cost exchanges do not balance per commodity. -/
theorem priceVectorValuation_balanced {T : 𝕋} (G : 𝕋.Generated T) (L : 𝕋Laws T)
    (Q : CommodityValuation T) (cs : Finset Commodity) (price : Commodity → ℝ)
    (hgen : ∀ c ∈ cs, ∀ {A B : Object} (f : T.Hom A B), G.IsGen f → (Q c).V f = 0)
    {A B : Object} (f : T.Hom A B) : (priceVectorValuation Q cs price).V f = 0 :=
  balanced_generators_balance T G _ L
    (fun f hf => by
      simp only [priceVectorValuation, ValuationFunctor.finsetSum_V,
        ValuationFunctor.smul_V]
      exact Finset.sum_eq_zero fun c hc => by rw [hgen c hc f hf, mul_zero]) f

namespace GenSpec

variable {S : GenSpec}

/-- **Bridge**: on the free model, total value `priceValuation` is the
    abstract price-vector valuation over the quantity reading, whenever
    `cs` covers every generator's commodities. The sum runs over a
    fixed `cs`, not over a support that depends on the morphism. -/
theorem priceValuation_eq_priceVector (flows : S.Gen → PacioliGroup)
    (p : Commodity → ℚ) (cs : Finset Commodity)
    (hcs : ∀ t, ∀ a ∈ (flows t).support, a.commodity ∈ cs)
    {A B : Object} (f : FreeHom S A B) :
    (priceValuation flows p).V f
      = (priceVectorValuation (quantityValuation flows) cs (fun c => (p c : ℝ))).V f :=
  free_valuation_ext _ _ (fun t => by
    simp only [priceValuation_gen, priceVectorValuation, ValuationFunctor.finsetSum_V,
      ValuationFunctor.smul_V, quantityValuation, ofFlowHom_gen, commodityTotal_apply]
    have hsupp : (trialBalance (flows t)).support ⊆ cs := by
      intro c hc
      have hc' := Finsupp.mapDomain_support hc
      simp only [Finset.mem_image] at hc'
      obtain ⟨a, ha, rfl⟩ := hc'
      exact hcs t a ha
    simp only [priceDot, AddMonoidHom.coe_comp, Function.comp_apply,
      LinearMap.toAddMonoidHom_coe, Finsupp.linearCombination_apply, smul_eq_mul]
    rw [Finsupp.sum_of_support_subset _ hsupp _ (by simp)]
    push_cast
    exact Finset.sum_congr rfl fun c _ => mul_comm _ _) f

/-- On a journal whose generators move only commodity `b`, at a price
    vector with `p b ≠ 0`, the two readings agree at the member `b`:
    value in the numeraire `b` equals the quantity of `b` moved. The
    statement concerns that one member, not the two families as a
    whole. -/
theorem valueIn_eq_quantity_of_single (flows : S.Gen → PacioliGroup)
    (p : Commodity → ℚ) (b : Commodity) (hb : p b ≠ 0)
    (honly : ∀ t, ∀ a ∈ (flows t).support, a.commodity = b)
    {A B : Object} (f : FreeHom S A B) :
    ((1 / (p b : ℝ)) • priceValuation flows p).V f = (quantityValuation flows b).V f := by
  have hbR : (p b : ℝ) ≠ 0 := Rat.cast_ne_zero.mpr hb
  rw [ValuationFunctor.smul_V,
    priceValuation_eq_priceVector flows p {b} (fun t a ha => by
      rw [Finset.mem_singleton]; exact honly t a ha) f]
  simp only [priceVectorValuation, ValuationFunctor.finsetSum_V, Finset.sum_singleton,
    ValuationFunctor.smul_V]
  field_simp

/-- On the one-generator model `unitSpec` with `oneFlow` (one unit
    into `Assets:Cash` in USD), the quantity reading admits no sound
    price action converting USD to EUR. Together with
    `PriceAction.constModel`, which is sound for the value reading on
    the same model, this is a narrow witness that the readings differ.
    It is not a claim that such an action is impossible in general. -/
theorem quantity_priceAction_uninhabited (P : PriceGroupoid)
    (p : P.Conversion "USD" "EUR")
    (act : PriceAction P (freeT unitSpec) (quantityValuation oneFlow)) : False := by
  have hEUR : ∀ {A B : Object} (f : FreeHom unitSpec A B),
      (quantityValuation oneFlow "EUR").V f = 0 := fun f => by
    rw [quantityValuation_V, ← commodityTotal_apply,
      free_trial_balance oneFlow "EUR" (fun _ => by simp [oneFlow, someAccount]) f]
    simp
  have hs := act.revalue_sound p (⟦.gen PUnit.unit⟧ : FreeHom unitSpec _ _)
  rw [hEUR] at hs
  have hUSD : (quantityValuation oneFlow "USD").V
      (⟦.gen PUnit.unit⟧ : FreeHom unitSpec _ _) = 1 := by
    rw [quantityValuation_V, flow_gen]
    simp [oneFlow, someAccount]
  rw [hUSD, mul_one] at hs
  exact P.rate_ne_zero p hs.symm

end GenSpec

/-- `-X b` at a fixed, total, nowhere-zero price table: the
    reporting-time model whose commodity-`b` member is value in
    numeraire `b` of the price-vector functional. An idealization, not
    bisimulated: `hne` quantifies over every commodity, so it cannot
    express C++'s partial price tables, and fixated lot prices are
    outside it. -/
def exchangeReport {T : 𝕋} (Q : CommodityValuation T) (cs : Finset Commodity)
    (price : Commodity → ℝ) (hne : ∀ c, price c ≠ 0) :
    PriceAction (PriceGroupoid.constRates price hne) T
      (fun b => (1 / price b) • priceVectorValuation Q cs price) :=
  PriceAction.constModel T (priceVectorValuation Q cs price) price hne

/-! ## Ellerman's worked example (pp. 496-498), debit-positive

Ellerman's three types of property, "cash, outputs (widgets), and
inputs (half-widgets)" (p. 496), listed in that order in each vector,
are the commodities `$`, `WIDGET` and `HALF`. The prices are those of
p. 498, `(1, 100, 40)`. -/

namespace EllermanWidgets

/-- Ellerman's price vector `(1, 100, 40)`. -/
def price : Commodity → ℚ := fun c =>
  if c = "$" then 1 else if c = "WIDGET" then 100 else if c = "HALF" then 40 else 0

/-- A three-component property vector held by one account name. -/
def vec3 (n : AccountName) (cash widget half : ℚ) : PacioliGroup :=
  Finsupp.single ⟨n, "$"⟩ cash + Finsupp.single ⟨n, "WIDGET"⟩ widget
    + Finsupp.single ⟨n, "HALF"⟩ half

/-- Transaction 2b as journaled on p. 497: Assets
    `[(2000,0,0)//(0,20,0)]` with Equity `[(0,20,0)//(2000,0,0)]`. -/
def txn2b : PacioliGroup :=
  (Finsupp.single ⟨"Assets", "$"⟩ 2000 - Finsupp.single ⟨"Assets", "WIDGET"⟩ 20)
    + (Finsupp.single ⟨"Equity", "WIDGET"⟩ 20 - Finsupp.single ⟨"Equity", "$"⟩ 2000)

/-- The Assets leg of 2b alone: the shape of an `@`-cost exchange as
    the oracle emits it. -/
def txn2bAssets : PacioliGroup :=
  Finsupp.single ⟨"Assets", "$"⟩ 2000 - Finsupp.single ⟨"Assets", "WIDGET"⟩ 20

/-- Transaction 2b as journaled is itself a zero-row. -/
theorem txn2b_mem_zeroRows : txn2b ∈ zeroRows := by
  rw [mem_zeroRows, txn2b]
  simp only [map_add, map_sub, trialBalance_single]
  abel

/-- Its Assets leg is value-neutral at `(1, 100, 40)` but not a
    zero-row: the article's own numbers witness non-injectivity. -/
theorem txn2bAssets_value_neutral_not_zeroRow :
    txn2bAssets ∉ zeroRows ∧ priceDot price txn2bAssets = 0 := by
  refine ⟨fun hx => ?_, ?_⟩
  · rw [mem_zeroRows, txn2bAssets, map_sub, trialBalance_single,
      trialBalance_single] at hx
    have h2 := congrArg (fun v : Commodity →₀ ℚ => v "$") hx
    simp at h2
  · simp [txn2bAssets, price]; norm_num

/-- p. 498: `(1,100,40) · (10200,35,20) = 14500`. This evaluates the
    ending vector as the article gives it; it does not derive that
    vector by posting. -/
theorem assets_value : priceDot price (vec3 "Assets" 10200 35 20) = 14500 := by
  simp [vec3, price]; norm_num

/-- p. 498, "Scalar equation = price vector times vector equation":
    the ending vector ledger evaluates, account by account, to
    `14500 = 9200 + 5300`. -/
theorem scalar_equation :
    let L := vec3 "Assets" 10200 35 20 + vec3 "Liabilities" (-9200) 0 0
      + vec3 "Equity" (-1000) (-35) (-20)
    valueHom price "Assets" L = 14500
      ∧ valueHom price "Liabilities" L = -9200
      ∧ valueHom price "Equity" L = -5300
      ∧ priceDot price L = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [vec3, price] <;> norm_num

end EllermanWidgets

end

end Ledger
