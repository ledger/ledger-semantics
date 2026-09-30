import Ledger.PriceVector

/-!
# Timed price vectors and the holding-gain identity

`timedConstRates` (`Ledger/TimedPrices.lean`) fixes one functional for
all instants and measures commodity `c` by `(1 / priceAt t c) • W`, so
a holding's value in a numeraire of constant price never changes
(`timedConstRates_value_const`; at price 1 this is
`timedConstRates_no_holding_gain`): that model varies the unit of
measurement, not the value of a holding. This module adds the timed
model whose values move, `timedPriceVector`, each fiber of which is
the existing `constModel` over the price-vector functional
`priceValuation flows (priceAt t)` of `Ledger/PriceVector.lean`, so
per-instant soundness is inherited unchanged.

The holding gain between two instants is itself a valuation functor,
the price-vector valuation at the change in numeraire-relative prices
(`holding_gain_functor`), with the constant-numeraire forms as
corollaries and the per-account form `accountValue_sub`. On journals
that balance per commodity the whole-flow gain vanishes
(`holding_gain_balanced`); the content lies in the per-account form
(`HoldingGainExample.balanced_account_holding_gain`) and in Ledger's
cost-balanced `@` journals, whose generators do not balance per
commodity (`HoldingGainExample.cost_exchange_holding_gain`).

For every flow, the scalar accounts at new prices are those at old
prices plus the revaluation (`scalarize_sub_prices`). On a flow that
balances per commodity the revaluation is a scalar zero-row
(`revaluation_mem_zeroRows`), the signed form, under the debit
isomorphism, of Ellerman's "add on a zero-account or zero-term"
(p. 496). On a cost-balanced flow it need not be one: its trial
balance is the value of the flow at the price change, booked in the
numeraire (`trialBalance_scalarize`), which with the numeraire held at
price 1 is the holding gain (`holding_gain`).

Every price must be nonzero, because `constRates` divides by it. An
unpriced commodity other than the numeraire takes a placeholder price,
which changes levels but leaves differences unchanged when the
placeholder does not move relative to the numeraire; a placeholder `k`
for the numeraire itself, held at both instants, divides every gain by
`k` (`holding_gain_const`). The fiber measurement is at best `-X c`
under direct, path-consistent prices; it is not C++ `-V`, which
chooses its target commodity per amount. The article applies one
price vector once, so the revaluation identity goes beyond it.
-/

namespace Ledger

noncomputable section

/-- **The blind spot of `timedConstRates`**: with a numeraire held at
    price 1, the value of every morphism is the same at every instant.
    The model varies only the unit of measurement. -/
theorem timedConstRates_no_holding_gain (Time : Type) (T : 𝕋)
    (W : ValuationFunctor T) (priceAt : Time → Commodity → ℝ)
    (hne : ∀ t c, priceAt t c ≠ 0) (c : Commodity) (hc : ∀ t, priceAt t c = 1)
    (t t' : Time) {A B : Object} (f : T.Hom A B) :
    ((timedConstRates Time T W priceAt hne).CV t c).V f
      = ((timedConstRates Time T W priceAt hne).CV t' c).V f := by
  have h := timedConstRates_value_const Time T W priceAt hne t c f
  have h' := timedConstRates_value_const Time T W priceAt hne t' c f
  rw [hc t, one_mul] at h
  rw [hc t', one_mul] at h'
  rw [h, h']

namespace GenSpec

variable {S : GenSpec}

/-- Flow valuations subtract as their functionals do. -/
theorem ofFlowHom_sub (flows : S.Gen → PacioliGroup) (φ ψ : PacioliGroup →+ ℚ) :
    ofFlowHom flows φ - ofFlowHom flows ψ = ofFlowHom flows (φ - ψ) :=
  ValuationFunctor.ext_V fun f => by
    rw [ValuationFunctor.sub_V, ofFlowHom_V, ofFlowHom_V, ofFlowHom_V,
      AddMonoidHom.sub_apply, Rat.cast_sub]

end GenSpec

/-- The timed model whose values move: at instant `t`, commodity `c`
    measures the whole flow at the price vector `priceAt t`, expressed
    in units of `c`. Each fiber is `constModel` over `priceValuation`,
    so soundness is inherited. `priceAt` must be nowhere zero. -/
def timedPriceVector (Time : Type) {S : GenSpec}
    (flows : S.Gen → PacioliGroup) (priceAt : Time → Commodity → ℚ)
    (hne : ∀ t c, priceAt t c ≠ 0) : TimedPrices Time (GenSpec.freeT S) where
  P t := PriceGroupoid.constRates (fun c => (priceAt t c : ℝ))
           (fun c => Rat.cast_ne_zero.mpr (hne t c))
  CV t := fun c => (1 / (priceAt t c : ℝ)) • GenSpec.priceValuation flows (priceAt t)
  act t := PriceAction.constModel (GenSpec.freeT S)
             (GenSpec.priceValuation flows (priceAt t)) _ _

/-- The fiber measurement as a sum over accounts: a candidate property
    for a future `-X c` comparison, not a claim about C++. -/
theorem timedPriceVector_CV (Time : Type) {S : GenSpec}
    (flows : S.Gen → PacioliGroup) (priceAt : Time → Commodity → ℚ)
    (hne : ∀ t c, priceAt t c ≠ 0) (t : Time) (c : Commodity)
    {A B : Object} (f : GenSpec.FreeHom S A B) :
    ((timedPriceVector Time flows priceAt hne).CV t c).V f
      = (((GenSpec.flow flows f).sum fun a q =>
            (priceAt t a.commodity / priceAt t c) * q : ℚ) : ℝ) := by
  show (1 / (priceAt t c : ℝ)) * ((priceDot (priceAt t) (GenSpec.flow flows f) : ℚ) : ℝ) = _
  rw [priceDot_apply]
  have hc := hne t c
  simp only [Finsupp.sum, Rat.cast_sum, Finset.mul_sum, Rat.cast_mul, Rat.cast_div]
  refine Finset.sum_congr rfl fun a _ => ?_
  field_simp

/-- The fiber measurement is itself a price-vector valuation, at the
    numeraire-relative prices `priceAt t d / priceAt t c`. -/
theorem timedPriceVector_CV_eq (Time : Type) {S : GenSpec}
    (flows : S.Gen → PacioliGroup) (priceAt : Time → Commodity → ℚ)
    (hne : ∀ t c, priceAt t c ≠ 0) (t : Time) (c : Commodity) :
    (timedPriceVector Time flows priceAt hne).CV t c
      = GenSpec.priceValuation flows (fun d => priceAt t d / priceAt t c) :=
  ValuationFunctor.ext_V fun f => by
    show (1 / (priceAt t c : ℝ)) * ((priceDot (priceAt t) (GenSpec.flow flows f) : ℚ) : ℝ)
        = ((priceDot (fun d => priceAt t d / priceAt t c) (GenSpec.flow flows f) : ℚ) : ℝ)
    have hfun : (fun d => priceAt t d / priceAt t c) = (priceAt t c)⁻¹ • priceAt t := by
      funext d
      simp [div_eq_mul_inv, mul_comm]
    rw [hfun, priceDot_smul_prices, Rat.cast_mul, Rat.cast_inv, one_div]

/-- **Holding gain, numeraire-relative.** Between two instants, the
    change in measured value is the price-vector valuation at the
    change in numeraire-relative prices. No hypothesis on the
    numeraire's own price. -/
theorem holding_gain_functor (Time : Type) {S : GenSpec}
    (flows : S.Gen → PacioliGroup) (priceAt : Time → Commodity → ℚ)
    (hne : ∀ t c, priceAt t c ≠ 0) (c : Commodity) (t t' : Time) :
    (timedPriceVector Time flows priceAt hne).CV t' c
        - (timedPriceVector Time flows priceAt hne).CV t c
      = GenSpec.priceValuation flows
          ((fun d => priceAt t' d / priceAt t' c) - (fun d => priceAt t d / priceAt t c)) := by
  rw [timedPriceVector_CV_eq, timedPriceVector_CV_eq, GenSpec.priceValuation,
    GenSpec.priceValuation, GenSpec.priceValuation, GenSpec.ofFlowHom_sub]
  congr 1
  refine AddMonoidHom.ext fun x => ?_
  rw [AddMonoidHom.sub_apply, priceDot_sub_prices]

/-- **Holding gain**, numeraire held at price 1: the change in value is
    the price change applied to the trial balance of the flow. -/
theorem holding_gain (Time : Type) {S : GenSpec} (flows : S.Gen → PacioliGroup)
    (priceAt : Time → Commodity → ℚ) (hne : ∀ t c, priceAt t c ≠ 0)
    (c : Commodity) (hc : ∀ t, priceAt t c = 1) (t t' : Time)
    {A B : Object} (f : GenSpec.FreeHom S A B) :
    ((timedPriceVector Time flows priceAt hne).CV t' c).V f
      - ((timedPriceVector Time flows priceAt hne).CV t c).V f
      = ((Finsupp.linearCombination ℚ (priceAt t' - priceAt t)
            (trialBalance (GenSpec.flow flows f)) : ℚ) : ℝ) := by
  rw [← ValuationFunctor.sub_V, holding_gain_functor]
  have h1 : ∀ s, (fun d => priceAt s d / priceAt s c) = priceAt s := by
    intro s; funext d; rw [hc s, div_one]
  rw [h1 t, h1 t']
  rfl

/-- **Holding gain**, numeraire held at a constant price `k`: the same
    identity scaled by `1 / k`. -/
theorem holding_gain_const (Time : Type) {S : GenSpec} (flows : S.Gen → PacioliGroup)
    (priceAt : Time → Commodity → ℚ) (hne : ∀ t c, priceAt t c ≠ 0)
    (c : Commodity) (k : ℚ) (hc : ∀ t, priceAt t c = k) (t t' : Time)
    {A B : Object} (f : GenSpec.FreeHom S A B) :
    ((timedPriceVector Time flows priceAt hne).CV t' c).V f
      - ((timedPriceVector Time flows priceAt hne).CV t c).V f
      = (1 / (k : ℝ)) * ((Finsupp.linearCombination ℚ (priceAt t' - priceAt t)
            (trialBalance (GenSpec.flow flows f)) : ℚ) : ℝ) := by
  rw [← ValuationFunctor.sub_V, holding_gain_functor]
  have hfun : ((fun d => priceAt t' d / priceAt t' c) - (fun d => priceAt t d / priceAt t c))
      = k⁻¹ • (priceAt t' - priceAt t) := by
    funext d
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hc]
    ring
  rw [hfun]
  show ((priceDot (k⁻¹ • (priceAt t' - priceAt t)) (GenSpec.flow flows f) : ℚ) : ℝ) = _
  rw [priceDot_smul_prices, Rat.cast_mul, Rat.cast_inv, one_div]
  rfl

/-- **Per-account revaluation**, as an equality of valuation functors:
    `V_{p'} - V_p = V_{p' - p}`, account by account. -/
theorem accountValue_sub {S : GenSpec} (flows : S.Gen → PacioliGroup)
    (p p' : Commodity → ℚ) (n : AccountName) :
    GenSpec.accountValue flows p' n - GenSpec.accountValue flows p n
      = GenSpec.accountValue flows (p' - p) n := by
  rw [GenSpec.accountValue, GenSpec.accountValue, GenSpec.accountValue,
    GenSpec.ofFlowHom_sub, valueHom_sub_prices]

/-- The whole-flow holding gain vanishes on journals that balance per
    commodity, the setting of Ellerman's worked examples. Indeed each
    side is zero at every instant (`timedPriceVector_CV_eq` with
    `GenSpec.priceValuation_balanced`), so on such journals the
    whole-flow measurement carries no information. -/
theorem holding_gain_balanced (Time : Type) {S : GenSpec} (flows : S.Gen → PacioliGroup)
    (hbal : ∀ g, flows g ∈ zeroRows)
    (priceAt : Time → Commodity → ℚ) (hne : ∀ t c, priceAt t c ≠ 0)
    (c : Commodity) (t t' : Time)
    {A B : Object} (f : GenSpec.FreeHom S A B) :
    ((timedPriceVector Time flows priceAt hne).CV t' c).V f
      = ((timedPriceVector Time flows priceAt hne).CV t c).V f := by
  rw [← sub_eq_zero, ← ValuationFunctor.sub_V, holding_gain_functor]
  exact GenSpec.priceValuation_balanced flows hbal _ f

/-! ## Revaluation, and when it is a scalar zero-row -/

/-- The scalar (value) accounts of a vector flow at prices `p`, in
    signed form, all in the numeraire `c`: account `a` carries
    `p a.commodity * q` in `⟨a.name, c⟩`. -/
def scalarize (p : Commodity → ℚ) (c : Commodity) : PacioliGroup →+ PacioliGroup :=
  Finsupp.liftAddHom fun a =>
    (Finsupp.singleAddHom (⟨a.name, c⟩ : Account)).comp (AddMonoidHom.mulLeft (p a.commodity))

/-- The scalar account of name `n` holds exactly `valueHom p n`. -/
theorem scalarize_apply (p : Commodity → ℚ) (c : Commodity) (n : AccountName)
    (x : PacioliGroup) : scalarize p c x ⟨n, c⟩ = valueHom p n x := by
  have h : (Finsupp.applyAddHom (⟨n, c⟩ : Account)).comp (scalarize p c) = valueHom p n := by
    refine Finsupp.addHom_ext fun a q => ?_
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, scalarize, valueHom,
      Finsupp.liftAddHom_apply_single, Finsupp.applyAddHom_apply,
      Finsupp.singleAddHom_apply, AddMonoidHom.coe_mulLeft, Finsupp.single_apply,
      Account.mk.injEq, and_true]
    split_ifs <;> simp
  exact DFunLike.congr_fun h x

/-- The trial balance of the scalar accounts is the whole-flow value,
    booked in the numeraire. -/
theorem trialBalance_scalarize (p : Commodity → ℚ) (c : Commodity) (x : PacioliGroup) :
    trialBalance (scalarize p c x) = Finsupp.single c (priceDot p x) := by
  have h : trialBalance.comp (scalarize p c)
      = (Finsupp.singleAddHom c).comp (priceDot p) := by
    refine Finsupp.addHom_ext fun a q => ?_
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, scalarize,
      Finsupp.liftAddHom_apply_single, Finsupp.singleAddHom_apply,
      AddMonoidHom.coe_mulLeft, trialBalance_single, priceDot_single]
    rw [mul_comm]
  exact DFunLike.congr_fun h x

/-- Scalarization at new prices is scalarization at old prices plus
    scalarization at the price change. -/
theorem scalarize_sub_prices (p p' : Commodity → ℚ) (c : Commodity) (x : PacioliGroup) :
    scalarize p' c x = scalarize p c x + scalarize (p' - p) c x := by
  have h : scalarize p' c = scalarize p c + scalarize (p' - p) c := by
    refine Finsupp.addHom_ext fun a q => ?_
    simp only [scalarize, AddMonoidHom.add_apply, Finsupp.liftAddHom_apply_single,
      AddMonoidHom.coe_comp, Function.comp_apply, Finsupp.singleAddHom_apply,
      AddMonoidHom.coe_mulLeft, Pi.sub_apply, ← Finsupp.single_add]
    congr 1
    ring
  rw [h, AddMonoidHom.add_apply]

/-- **On a flow that balances per commodity, revaluation is adding a
    zero-row**, the signed form, under the debit isomorphism, of
    Ellerman's "add on a zero-account or zero-term" (p. 496), which the
    article does not apply to revaluation. For every vector flow the
    scalar accounts at new prices are those at old prices plus the
    per-account revaluation (`scalarize_sub_prices`); when the flow is
    a zero-row, that revaluation is itself a scalar zero-row. -/
theorem revaluation_mem_zeroRows (p p' : Commodity → ℚ) (c : Commodity)
    {x : PacioliGroup} (hx : x ∈ zeroRows) :
    scalarize p' c x = scalarize p c x + scalarize (p' - p) c x
      ∧ scalarize (p' - p) c x ∈ zeroRows := by
  refine ⟨scalarize_sub_prices p p' c x, ?_⟩
  rw [mem_zeroRows, trialBalance_scalarize, priceDot_of_mem_zeroRows _ hx,
    Finsupp.single_zero]

/-- The same, for every derived morphism of a journal that balances per
    commodity. -/
theorem revaluation_mem_zeroRows_flow {S : GenSpec} (flows : S.Gen → PacioliGroup)
    (hbal : ∀ g, flows g ∈ zeroRows) (p p' : Commodity → ℚ) (c : Commodity)
    {A B : Object} (f : GenSpec.FreeHom S A B) :
    scalarize (p' - p) c (GenSpec.flow flows f) ∈ zeroRows :=
  (revaluation_mem_zeroRows p p' c (GenSpec.flow_mem flows zeroRows hbal f)).2

/-! ## Non-vacuity: nonzero holding gains in both settings

Ledger's `@` exchanges balance at cost, not per commodity. One
generator buys 1 AAPL for 100 USD; AAPL moves from 100 to 120 with USD
as the numeraire at price 1. The holding gain is 20. On a journal that
does balance per commodity the whole-flow gain vanishes, yet the same
price change raises the value booked in the receiving account by 20,
and the revaluation zero-row is not zero. -/

namespace HoldingGainExample

/-- The purchase, on the one-generator specification `GenSpec.unitSpec`. -/
def costFlow : GenSpec.unitSpec.Gen → PacioliGroup := fun _ =>
  Finsupp.single ⟨"Assets:Broker", "AAPL"⟩ 1 + Finsupp.single ⟨"Assets:Cash", "USD"⟩ (-100)

/-- AAPL at 100 (`false`) and at 120 (`true`); every other commodity at 1. -/
def examplePrice : Bool → Commodity → ℚ := fun t d =>
  if d = "AAPL" then (if t then 120 else 100) else 1

/-- Every example price is nonzero. -/
theorem examplePrice_ne : ∀ t d, examplePrice t d ≠ 0 := by
  intro t d
  unfold examplePrice
  split_ifs <;> norm_num

/-- **The cost exchange carries a holding gain.** Buying 1 AAPL for
    100 USD, then AAPL moving from 100 to 120 with USD at price 1,
    gives a gain of 20 USD (`holding_gain`). -/
theorem cost_exchange_holding_gain :
    ((timedPriceVector Bool costFlow examplePrice examplePrice_ne).CV true "USD").V
        (GenSpec.genHom (S := GenSpec.unitSpec) PUnit.unit)
      - ((timedPriceVector Bool costFlow examplePrice examplePrice_ne).CV false "USD").V
        (GenSpec.genHom (S := GenSpec.unitSpec) PUnit.unit)
      = 20 := by
  rw [holding_gain Bool costFlow examplePrice examplePrice_ne "USD"
    (by intro t; simp [examplePrice]) false true, GenSpec.flow_genHom]
  show ((priceDot (examplePrice true - examplePrice false) (costFlow PUnit.unit) : ℚ) : ℝ) = 20
  have hUA : ("USD" : String) ≠ "AAPL" := by decide
  simp only [costFlow, map_add, priceDot_single]
  norm_num [examplePrice, hUA]

/-- A transfer of 1 AAPL from `Equity` to `Assets:Broker`, balanced per
    commodity, on the same one-generator specification. -/
def balancedFlow : GenSpec.unitSpec.Gen → PacioliGroup := fun _ =>
  Finsupp.single ⟨"Assets:Broker", "AAPL"⟩ 1 - Finsupp.single ⟨"Equity", "AAPL"⟩ 1

/-- The transfer is a zero-row. -/
theorem balancedFlow_mem_zeroRows : ∀ g, balancedFlow g ∈ zeroRows := fun _ => by
  rw [mem_zeroRows, balancedFlow, map_sub, trialBalance_single, trialBalance_single, sub_self]

/-- **The per-account form is not vacuous.** The whole-flow gain of the
    transfer is zero (`holding_gain_balanced`), but as AAPL moves from
    100 to 120, the value that the transfer books in `Assets:Broker`
    rises by 20 (`accountValue_sub`). -/
theorem balanced_account_holding_gain :
    (GenSpec.accountValue balancedFlow (examplePrice true) "Assets:Broker").V
        (GenSpec.genHom (S := GenSpec.unitSpec) PUnit.unit)
      - (GenSpec.accountValue balancedFlow (examplePrice false) "Assets:Broker").V
        (GenSpec.genHom (S := GenSpec.unitSpec) PUnit.unit)
      = 20 := by
  rw [← ValuationFunctor.sub_V, accountValue_sub, GenSpec.accountValue, GenSpec.ofFlowHom_V,
    GenSpec.flow_genHom]
  have hEB : ("Equity" : String) ≠ "Assets:Broker" := by decide
  simp only [balancedFlow, map_sub, valueHom_single]
  norm_num [examplePrice, hEB]

/-- **The revaluation is not vacuous.** The revaluation of the transfer,
    a zero-row by `revaluation_mem_zeroRows`, books 20 USD in
    `Assets:Broker`. -/
theorem balanced_revaluation_apply :
    scalarize (examplePrice true - examplePrice false) "USD" (balancedFlow PUnit.unit)
      ⟨"Assets:Broker", "USD"⟩ = 20 := by
  rw [scalarize_apply]
  have hEB : ("Equity" : String) ≠ "Assets:Broker" := by decide
  simp only [balancedFlow, map_sub, valueHom_single]
  norm_num [examplePrice, hEB]

end HoldingGainExample

end

end Ledger
