import Ledger.Labels
import Ledger.Oracle

/-!
# Register observables (the L2-term level), and their footing theorem

The Pacioli skeleton deliberately conflates chaining, parallelism, and
aggregation (worksheet §7): adequate for `balance`, blind to
`register`. This module says precisely where register lives — and
where it cannot.

**Register is presentation-level.** The observable is a *fold over
terms* (`FreeMor`), not over the quotient: `f⁻¹ ∘ f` is `Rel`-equal to
`id`, but its register shows two rows where `id` shows none (witness
below). That is not a defect — it is the C++ semantics: `register`
reports the journal *as written*, entry by entry; algebraic identity
of the composite flow is exactly what it does not quotient by. So:

  - `balance` observables live on `FreeHom` (the quotient) via `flow`;
  - `register` observables live on `FreeMor` (the term) via
    `registerRows`;
  - the two meet in the **footing theorem** `register_foots`: summing
    a term's register deltas per account is its net flow — the
    invariant a C++ register-vs-balance comparison can rely on, and
    the flow-observable half of acceptance card 3.

Label fidelity (dates, payees, order) is fibration data
(`LabeledGenSpec`); comparing it against the C++ `register` output is
card 3's separate, label-scoped rung.

**Posting granularity.** `registerRows` has one row per generator
occurrence, while the C++ `register` command prints one row for each
posting that it displays. The definitions below therefore take, for
each generator, the list of postings it records. `postingFlows` sums
that list per account by the same filter and fold as `flowsFor` in
`Ledger/Driver.lean`, which sums the postings that the engine emits
for one transaction; `termPostings` lists the postings of a term in
presentation order, each amount negated under an odd number of
reversals; and `postingRows` gives one row per posting with a running
total per commodity. The running total follows
`calc_posts::operator()` in src/filters.cc, which sets the running
total of each posting to that of the posting before it plus the
posting's own value; test/baseline/cmd-register.test shows that total
commodity by commodity, and `LabeledGenSpec.postingRows_total` states
it as a prefix sum. C++ departs from this rule under `--average`
without `--collapse` or `--depth`, as the docstring of `postingRows`
records with its sources: there a posting that C++ generates, such as
an automated posting, a further posting that completes an elided
posting, or a posting of an interval report, starts from the total
that the last generated posting to its account reached, or from zero.
Under `--average`, with or without those options, the total that C++
displays is moreover that running total divided by the posting count
that `calc_posts::operator()` keeps, and `--empty` is turned on
(src/report.h:583-586 at 76b9dc2b2). Line numbers of C++ sources in
this module are those of revision 76b9dc2b2.

Register rows are not bisimulated: the oracle prints balances and no
register, so these rows are specified and proved here, and no C++
output is compared with them mechanically; the example at the end of
this module transcribes by hand the running totals of one C++ test.
Rows computed over the postings that the engine emits can differ from
the rows that C++ prints in their order within a transaction, in their
number and in their amounts, and the instances below are not a
complete list. C++ prints the postings of a transaction in the order
written, giving an elided posting one of the amounts that complete it
in its place, and then the postings that it adds, among them a
posting for each further amount that completes the elided posting
(src/xact.cc:233-246, applied at 832-835 and 851-854) and the
automated postings. The engine lists the real postings first, then
the bracket-virtual and then the paren-virtual ones
(`realDone.posts ++ virtDone.posts ++ exempt` in `finalizeXact`,
`Ledger/Journal.lean`), in each balancing pool the postings written
with an amount before those that complete its elided posting, and the
automated postings last (`cand.toList ++ extra` in `applyAutos`). So
C++ prints the paren-virtual posting of the transaction Virtual move
of test/regress/3211.test first, and the elided Assets:Cash of the
transaction KFC - Rebate of test/baseline/opt-dc.test first, where the
engine lists each of them last. C++ also leaves out a posting whose
amount displays as zero unless `--empty` is given
(src/filters.cc:843-848 and 902), while the engine keeps a posting
written with a zero amount and emits none for an elided posting that
completes to zero. By default C++ inserts a row for the account
`<Adjustment>` where rounding for display would leave the running
total inconsistent with the amounts displayed
(`display_filter_posts::output_rounding`, src/filters.cc:859-887), and
no posting that the engine emits matches that row. Where C++ splits
the completion of an elided posting by lot annotation, as the
paragraph on gross totals records, its rows differ from the engine's
in their number and in their amounts.

**Gross totals.** `grossTotals` sums, at one account, the positive
amounts and the magnitudes of the negative amounts posted to it,
posting by posting. These are the quantities of the debit and credit
columns that `bal --dc --flat` prints for the account, the option
`--dc` (src/report.h:751-754 at 76b9dc2b2) splitting the amount of
each posting into its positive and its negative part; without
`--flat`, the row of a parent account also counts the postings to its
subaccounts. The definition is named `grossTotals` because `dc`
already names the decimal-comma declaration of the oracle's output
protocol. In test/baseline/opt-dc.test, Expenses:Food shows $40 of
debits and $10 of credits, two postings to it in one transaction being
counted separately; netting each transaction at the account first, as
Ellerman's unreduced ledger adds the T-terms `[x⁺ // x⁻]` of whole
transactions (pp. 489 and 494), gives $35 and $5 (`txnDebitTotal`,
`txnCreditTotal`). Both granularities foot, debits less credits being
the net flow (`gross_foot`, `txn_gross_foot`), and a reversal swaps
the two columns (`grossTotals_inv`). Summed over the accounts of one
commodity, gross debits and gross credits are equal when every entry
balances in that commodity (`gross_trial_balance`, which states this
sufficient condition and no converse); otherwise the debits less the
credits are the sum of the residuals that the term's entries leave in
the commodity (by `gross_foot` and `netFlow_commodity_sum`), and
residuals can cancel. Gross totals are nonnegative, and they are not
invariant under `Rel`: an entry followed by its reversal is
`Rel`-equal to the identity, yet its gross totals are not zero when it
posts a nonzero amount (an example below). By
`nonneg_valuation_trivial` a valuation functor on a lawful `𝕋` with
nonnegative values is zero, so gross totals, which are nonnegative and
not always zero, are computed by no valuation functor on a lawful
`𝕋`; they are folds over terms, as register rows are. The
correspondence with `bal --dc --flat` holds for the postings that C++
records, which the postings that the engine emits do not always match.
When the amounts that complete an elided posting include several of
one commodity that C++ keeps apart by their lot annotations, C++ posts
each of them (src/xact.cc:233-246, applied at 832-835 and 851-854),
so that the completed account can receive amounts of both signs; the
engine posts their sum, or nothing when the sum is zero, so that at
that account the gross totals over its postings can be smaller than
the columns of `bal --dc`. Valuation under `-B`, `-V` and `-X` lies
outside these definitions, and so does the choice of the accounts
that `bal --dc` displays, among them an account whose balance is
zero, which `bal` hides.
-/

namespace Ledger

namespace GenSpec

variable {S : GenSpec}

/-- Generator occurrences of a term, in presentation order, with
    reversal parity (`true` = appears under an odd number of `inv`). -/
def occurrences : {A B : Object} → S.FreeMor A B → List (S.Gen × Bool)
  | _, _, .gen t => [(t, false)]
  | _, _, .id _ => []
  | _, _, .zero _ _ => []
  | _, _, .comp g f => occurrences g ++ occurrences f
  | _, _, .inv f => (occurrences f).map fun ts => (ts.1, !ts.2)
  | _, _, .tensor f g => occurrences f ++ occurrences g
  | _, _, .add f g => occurrences f ++ occurrences g

/-- The signed flow of one occurrence. -/
def occValue (flows : S.Gen → Account → ℚ) (a : Account)
    (ts : S.Gen × Bool) : ℚ :=
  if ts.2 then -flows ts.1 a else flows ts.1 a

private theorem sum_map_neg {α : Type _} (l : List α) (v : α → ℚ) :
    (l.map fun x => -(v x)).sum = -(l.map v).sum := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [ih, add_comm]

/-- **The footing theorem**: a term's register foots to its balance —
    summing the signed occurrence flows at an account is exactly the
    oracle's net flow there. -/
theorem occurrences_foot (flows : S.Gen → Account → ℚ)
    {A B : Object} (f : S.FreeMor A B) (a : Account) :
    ((occurrences f).map (occValue flows a)).sum = netFlow flows f a := by
  induction f with
  | gen t => simp [occurrences, occValue, netFlow]
  | id A => simp [occurrences, netFlow]
  | zero A B => simp [occurrences, netFlow]
  | comp g f ihg ihf =>
      simp [occurrences, netFlow, List.map_append, List.sum_append, ihg, ihf]
  | inv f ih =>
      have h : ((occurrences f).map fun ts => (ts.1, !ts.2)).map
          (occValue flows a)
          = (occurrences f).map fun ts => -(occValue flows a ts) := by
        simp only [List.map_map]
        refine List.map_congr_left fun ts _ => ?_
        by_cases hb : ts.2 <;> simp [occValue, hb]
      simp [occurrences, netFlow, h, sum_map_neg, ih]
  | tensor f g ihf ihg =>
      simp [occurrences, netFlow, List.map_append, List.sum_append, ihf, ihg]
  | add f g ihf ihg =>
      simp [occurrences, netFlow, List.map_append, List.sum_append, ihf, ihg]

/-- **The per-commodity sum, unconditional form.** Summed over the
    commodity-`c` accounts of a finite set `s`, a term's net flow is
    the sum, over its generator occurrences in presentation order, of
    each occurrence's signed flows over the same accounts. The
    statement has no hypothesis on the generators, so it holds
    whatever residuals they leave: for an `s` that holds every account
    the term's generators touch, the residual of a term in `c` is the
    signed sum of the residuals of its occurrences. Residuals of
    distinct occurrences can cancel, as those of a purchase and a sale
    of the same quantity at one price do (the example below), so a
    zero sum does not show that each generator balances.
    `trialBalance_flowAux` in `Ledger/Pacioli.lean` is the same
    residual formula for the free model, and `netFlow_trial_balance`
    in `Ledger/Oracle.lean` states the case in which every generator's
    sum is zero. -/
theorem netFlow_commodity_sum (flows : S.Gen → Account → ℚ)
    (s : Finset Account) (c : Commodity) {A B : Object} (f : S.FreeMor A B) :
    ∑ a ∈ s.filter (·.commodity = c), netFlow flows f a
      = ((occurrences f).map fun ts =>
          ∑ a ∈ s.filter (·.commodity = c), occValue flows a ts).sum := by
  simp_rw [← occurrences_foot]
  induction occurrences f with
  | nil => simp
  | cons x xs ih => simp [Finset.sum_add_distrib, ih]

/-- Two generators for the cancellation example: `true` is a purchase
    of 10 AAPL for 50 dollars and `false` a sale of the same 10 AAPL
    for the same 50 dollars. Endpoints play no part in `netFlow`. -/
private def tradeSpec : GenSpec := ⟨Bool, fun _ => 0, fun _ => 0⟩

/-- The two accounts the example posts to. -/
private def tradeAccounts : Finset Account :=
  {⟨"Assets:Broker", "AAPL"⟩, ⟨"Assets:Cash", "$"⟩}

/-- Each trade recorded as its postings, a priced exchange that leaves
    a nonzero column in each of its two commodities. -/
private def tradeFlows (b : Bool) (a : Account) : ℚ :=
  (if b then 1 else -1) *
    (if a = ⟨"Assets:Broker", "AAPL"⟩ then 10
     else if a = ⟨"Assets:Cash", "$"⟩ then -50 else 0)

/-- **Residuals can cancel**, as the docstring of
    `netFlow_commodity_sum` says: each trade leaves a nonzero residual
    in AAPL, yet the residuals of the two occurrences in their tensor
    sum to zero, so the zero total does not show that either trade
    balances. -/
example :
    (∀ b, ∑ a ∈ tradeAccounts.filter (·.commodity = "AAPL"), tradeFlows b a ≠ 0) ∧
    ∑ a ∈ tradeAccounts.filter (·.commodity = "AAPL"),
      netFlow (S := tradeSpec) tradeFlows (.tensor (.gen true) (.gen false)) a = 0 := by
  refine ⟨by decide +kernel, ?_⟩
  rw [netFlow_commodity_sum]
  decide +kernel

/-- **Register is not `Rel`-invariant** (and must not be): `f⁻¹ ∘ f`
    and `id` are the same morphism of the quotient, but their
    registers differ — the register observes the presentation. -/
example :
    GenSpec.Rel (S := unitSpec)
      (.comp (.inv (.gen PUnit.unit)) (.gen PUnit.unit)) (.id 0) :=
  Rel.inv_comp _

example :
    occurrences (S := unitSpec)
        (.comp (.inv (.gen PUnit.unit)) (.gen PUnit.unit))
      ≠ occurrences (S := unitSpec) (.id 0) := by
  simp [occurrences]

/-! ## Postings and gross totals -/

private theorem foldl_add_snd (l : List (Account × ℚ)) (z : ℚ) :
    l.foldl (fun s p => s + p.2) z = z + (l.map Prod.snd).sum := by
  induction l generalizing z with
  | nil => simp
  | cons x xs ih => simp [ih, add_assoc]

private theorem sum_map_flatMap {α β : Type} (l : List α) (g : α → List β)
    (v : β → ℚ) :
    ((l.flatMap g).map v).sum = (l.map fun x => ((g x).map v).sum).sum := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [List.flatMap_cons, ih]

private theorem sum_map_sub {α : Type} (l : List α) (u v : α → ℚ) :
    (l.map fun x => u x - v x).sum = (l.map u).sum - (l.map v).sum := by
  induction l with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih]; abel

private theorem sum_map_nonneg {α : Type} (l : List α) (v : α → ℚ)
    (h : ∀ x, 0 ≤ v x) : 0 ≤ (l.map v).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      exact add_nonneg (h x) ih

/-- The flows of a generator that records its postings as a list: the
    flow at an account is the sum of the amounts posted to it, by the
    same filter and fold as `flowsFor` in `Ledger/Driver.lean`. -/
def postingFlows (posts : S.Gen → List (Account × ℚ)) (t : S.Gen)
    (a : Account) : ℚ :=
  ((posts t).filter fun p => p.1 = a).foldl (fun s p => s + p.2) 0

/-- The postings of a term in presentation order: the postings of each
    generator occurrence, in the order of its list, each amount negated
    when the occurrence is reversed. -/
def termPostings (posts : S.Gen → List (Account × ℚ))
    {A B : Object} (f : S.FreeMor A B) : List (Account × ℚ) :=
  (occurrences f).flatMap fun ts =>
    (posts ts.1).map fun p => (p.1, if ts.2 then -p.2 else p.2)

/-- The signed amounts that a term posts to one account, in
    presentation order. -/
def postingValues (posts : S.Gen → List (Account × ℚ))
    {A B : Object} (f : S.FreeMor A B) (a : Account) : List ℚ :=
  ((termPostings posts f).filter fun p => p.1 = a).map Prod.snd

/-- The debit total of an account: the sum of the positive parts of
    the amounts posted to it, posting by posting. -/
def debitTotal (posts : S.Gen → List (Account × ℚ))
    {A B : Object} (f : S.FreeMor A B) (a : Account) : ℚ :=
  ((postingValues posts f a).map fun q => q⁺).sum

/-- The credit total of an account: the sum of the negative parts of
    the amounts posted to it, posting by posting, the negative part of
    an amount being its magnitude when it is negative and zero
    otherwise. -/
def creditTotal (posts : S.Gen → List (Account × ℚ))
    {A B : Object} (f : S.FreeMor A B) (a : Account) : ℚ :=
  ((postingValues posts f a).map fun q => q⁻).sum

/-- The gross totals of an account, debit total first: for the
    postings given, the quantities of the debit and credit columns that
    `bal --dc --flat` prints for the account (src/report.h:751-754 at
    76b9dc2b2; test/baseline/opt-dc.test); without `--flat`, the row of
    a parent account also counts the postings to its subaccounts. -/
def grossTotals (posts : S.Gen → List (Account × ℚ))
    {A B : Object} (f : S.FreeMor A B) (a : Account) : ℚ × ℚ :=
  (debitTotal posts f a, creditTotal posts f a)

private theorem occ_postings_sum (posts : S.Gen → List (Account × ℚ))
    (a : Account) (ts : S.Gen × Bool) :
    ((((posts ts.1).map fun p => (p.1, if ts.2 then -p.2 else p.2)).filter
        fun p => p.1 = a).map Prod.snd).sum
      = occValue (postingFlows posts) a ts := by
  obtain ⟨t, b⟩ := ts
  cases b <;>
    simp [occValue, postingFlows, foldl_add_snd, List.filter_map, Function.comp_def,
      sum_map_neg]

/-- **The footing law of postings**: the amounts that a term posts to
    an account sum to its net flow there, the flows of each generator
    being the sums of its postings. -/
theorem termPostings_foot (posts : S.Gen → List (Account × ℚ))
    {A B : Object} (f : S.FreeMor A B) (a : Account) :
    (postingValues posts f a).sum = netFlow (postingFlows posts) f a := by
  rw [← occurrences_foot, postingValues, termPostings, List.filter_flatMap,
    sum_map_flatMap]
  exact congrArg List.sum (List.map_congr_left fun ts _ => occ_postings_sum posts a ts)

/-- **The gross footing law**: debit total less credit total is the net
    flow, for every term and with no condition on its generators. -/
theorem gross_foot (posts : S.Gen → List (Account × ℚ))
    {A B : Object} (f : S.FreeMor A B) (a : Account) :
    debitTotal posts f a - creditTotal posts f a
      = netFlow (postingFlows posts) f a := by
  rw [debitTotal, creditTotal, ← sum_map_sub, ← termPostings_foot]
  simp [posPart_sub_negPart]

/-- A debit total is a sum of positive parts, so it is nonnegative. -/
theorem debitTotal_nonneg (posts : S.Gen → List (Account × ℚ))
    {A B : Object} (f : S.FreeMor A B) (a : Account) :
    0 ≤ debitTotal posts f a :=
  sum_map_nonneg _ _ posPart_nonneg

/-- A credit total is a sum of negative parts, so it is nonnegative. -/
theorem creditTotal_nonneg (posts : S.Gen → List (Account × ℚ))
    {A B : Object} (f : S.FreeMor A B) (a : Account) :
    0 ≤ creditTotal posts f a :=
  sum_map_nonneg _ _ negPart_nonneg

private theorem termPostings_inv (posts : S.Gen → List (Account × ℚ))
    {A B : Object} (f : S.FreeMor A B) :
    termPostings posts (.inv f)
      = (termPostings posts f).map fun p => (p.1, -p.2) := by
  simp only [termPostings, occurrences, List.flatMap_map, List.map_flatMap]
  refine List.flatMap_congr fun ts _ => ?_
  obtain ⟨t, b⟩ := ts
  cases b <;> simp [Function.comp_def]

private theorem postingValues_inv (posts : S.Gen → List (Account × ℚ))
    {A B : Object} (f : S.FreeMor A B) (a : Account) :
    postingValues posts (.inv f) a = (postingValues posts f a).map Neg.neg := by
  simp [postingValues, termPostings_inv, List.filter_map, Function.comp_def]

/-- **A reversal swaps the gross totals**: the debits of a reversed
    term are the credits of the term, and its credits are the debits. -/
theorem grossTotals_inv (posts : S.Gen → List (Account × ℚ))
    {A B : Object} (f : S.FreeMor A B) (a : Account) :
    grossTotals posts (.inv f) a = (creditTotal posts f a, debitTotal posts f a) := by
  simp [grossTotals, debitTotal, creditTotal, postingValues_inv, Function.comp_def,
    posPart_neg, negPart_neg]

/-- **The gross trial balance, sufficient direction.** If every
    generator's flows sum to zero over the commodity-`c` accounts of a
    finite set `s`, then for every term the debit totals and the credit
    totals summed over the same accounts are equal. For a single term
    the converse fails: its debits less its credits are the summed
    residuals of its occurrences (the example below), and residuals of
    distinct occurrences can cancel (the example after
    `netFlow_commodity_sum`), so equal totals do not show that every
    entry balances. -/
theorem gross_trial_balance (posts : S.Gen → List (Account × ℚ))
    (s : Finset Account) (c : Commodity)
    (hgen : ∀ t, ∑ a ∈ s.filter (·.commodity = c), postingFlows posts t a = 0)
    {A B : Object} (f : S.FreeMor A B) :
    ∑ a ∈ s.filter (·.commodity = c), debitTotal posts f a
      = ∑ a ∈ s.filter (·.commodity = c), creditTotal posts f a := by
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib]
  simp_rw [gross_foot]
  exact netFlow_trial_balance _ s c hgen f

/-- **The debits less the credits are the summed residuals.** Summed
    over the commodity-`c` accounts of `s` and with no hypothesis on
    the generators, the debit totals less the credit totals of a term
    are the sum, over its occurrences in presentation order, of each
    occurrence's signed flows over the same accounts (`gross_foot` and
    `netFlow_commodity_sum`). -/
example (posts : S.Gen → List (Account × ℚ)) (s : Finset Account) (c : Commodity)
    {A B : Object} (f : S.FreeMor A B) :
    ∑ a ∈ s.filter (·.commodity = c), debitTotal posts f a
        - ∑ a ∈ s.filter (·.commodity = c), creditTotal posts f a
      = ((occurrences f).map fun ts =>
          ∑ a ∈ s.filter (·.commodity = c), occValue (postingFlows posts) a ts).sum := by
  rw [← Finset.sum_sub_distrib]
  simp_rw [gross_foot]
  exact netFlow_commodity_sum _ s c f

/-- The debit total of an account at transaction granularity: the flow
    of each generator occurrence is netted at the account first, and
    its positive part is summed, as Ellerman's unreduced ledger adds the
    T-terms `[x⁺ // x⁻]` of whole transactions (pp. 489 and 494). -/
def txnDebitTotal (flows : S.Gen → Account → ℚ)
    {A B : Object} (f : S.FreeMor A B) (a : Account) : ℚ :=
  ((occurrences f).map fun ts => (occValue flows a ts)⁺).sum

/-- The credit total of an account at transaction granularity: the sum
    of the negative parts of the netted occurrence flows. -/
def txnCreditTotal (flows : S.Gen → Account → ℚ)
    {A B : Object} (f : S.FreeMor A B) (a : Account) : ℚ :=
  ((occurrences f).map fun ts => (occValue flows a ts)⁻).sum

/-- **The footing law at transaction granularity**: debit total less
    credit total is again the net flow. -/
theorem txn_gross_foot (flows : S.Gen → Account → ℚ)
    {A B : Object} (f : S.FreeMor A B) (a : Account) :
    txnDebitTotal flows f a - txnCreditTotal flows f a = netFlow flows f a := by
  rw [txnDebitTotal, txnCreditTotal, ← sum_map_sub, ← occurrences_foot]
  simp [posPart_sub_negPart]

/-- The four transactions of test/baseline/opt-dc.test. Endpoints play
    no part in gross totals. -/
private inductive GrossEntry where
  | employer
  | kfc
  | rebate
  | foodAndRebate

private def grossSpec : GenSpec := ⟨GrossEntry, fun _ => 0, fun _ => 0⟩

private def grossCash : Account := ⟨"Assets:Cash", "$"⟩
private def grossFood : Account := ⟨"Expenses:Food", "$"⟩
private def grossIncome : Account := ⟨"Income:Employer", "$"⟩

/-- Each transaction's postings as the engine emits them, the elided
    posting completed and listed after the written ones; the last
    transaction posts to Expenses:Food twice. -/
private def grossPosts : GrossEntry → List (Account × ℚ)
  | .employer => [(grossCash, 100), (grossIncome, -100)]
  | .kfc => [(grossFood, 20), (grossCash, -20)]
  | .rebate => [(grossFood, -5), (grossCash, 5)]
  | .foodAndRebate => [(grossFood, 20), (grossFood, -5), (grossCash, -15)]

/-- The journal as `journalTerm` builds it: the right-nested tensor of
    the four transactions, closed by the identity on the empty
    object. -/
private def grossJournal :=
  FreeMor.tensor (S := grossSpec) (.gen GrossEntry.employer)
    (.tensor (.gen GrossEntry.kfc) (.tensor (.gen GrossEntry.rebate)
      (.tensor (.gen GrossEntry.foodAndRebate) (.id 0))))

/-- **Two granularities on test/baseline/opt-dc.test.** Gross totals
    reproduce the three account rows of its `bal --dc` report: $105
    and $35 for Assets:Cash, $40 and $10 for Expenses:Food, and no
    debit and $100 of credit for Income:Employer. Netting each
    transaction first gives $35 and $5 for Expenses:Food. -/
example :
    [grossCash, grossFood, grossIncome].map
        (grossTotals (S := grossSpec) grossPosts grossJournal)
        = [(105, 35), (40, 10), (0, 100)]
      ∧ (txnDebitTotal (S := grossSpec) (postingFlows grossPosts) grossJournal grossFood,
          txnCreditTotal (S := grossSpec) (postingFlows grossPosts) grossJournal grossFood)
        = (35, 5) := by
  decide +kernel

/-- **Gross totals are not `Rel`-invariant**: the KFC entry followed by
    its reversal is `Rel`-equal to the identity, whose gross totals
    are zero, yet it debits and credits Expenses:Food $20 each. -/
example :
    GenSpec.Rel (S := grossSpec)
        (.comp (.inv (.gen GrossEntry.kfc)) (.gen GrossEntry.kfc)) (.id _)
      ∧ grossTotals (S := grossSpec) grossPosts
          (.comp (.inv (.gen GrossEntry.kfc)) (.gen GrossEntry.kfc)) grossFood = (20, 20)
      ∧ grossTotals (S := grossSpec) grossPosts (.id 0) grossFood = (0, 0) :=
  ⟨Rel.inv_comp _, by decide +kernel, by decide +kernel⟩

end GenSpec

/-- **A valuation functor on a lawful `𝕋` with nonnegative values is
    zero**, since a reversal negates the valuation (`V_inv`). Gross
    totals are nonnegative and not always zero, so no valuation functor
    on a lawful `𝕋` computes them; they are folds over terms
    (`GenSpec.grossTotals`). -/
theorem ValuationFunctor.nonneg_valuation_trivial {T : 𝕋} (W : ValuationFunctor T)
    (L : 𝕋Laws T) (hW : ∀ {A B : Object} (f : T.Hom A B), 0 ≤ W.V f)
    {A B : Object} (f : T.Hom A B) : W.V f = 0 := by
  have h := hW (T.inv f)
  rw [W.V_inv L] at h
  exact le_antisymm (neg_nonneg.mp h) (hW f)

/-- A generator specification whose generators carry labels — the
    fibration data `register` reports (dates, payees, state). -/
structure LabeledGenSpec extends GenSpec where
  label : Gen → Label

namespace LabeledGenSpec

variable (L : LabeledGenSpec)

/-- Register rows of a term: one row per generator occurrence, in
    presentation order — its label and its signed per-account delta. -/
def registerRows (flows : L.Gen → Account → ℚ)
    {A B : Object} (f : L.toGenSpec.FreeMor A B) :
    List (Label × (Account → ℚ)) :=
  (GenSpec.occurrences f).map fun ts =>
    (L.label ts.1, fun a => GenSpec.occValue flows a ts)

/-- The register foots to the balance, rows-with-labels form. -/
theorem register_foots (flows : L.Gen → Account → ℚ)
    {A B : Object} (f : L.toGenSpec.FreeMor A B) (a : Account) :
    ((L.registerRows flows f).map fun r => r.2 a).sum
      = GenSpec.netFlow flows f a := by
  have h : (L.registerRows flows f).map (fun r => r.2 a)
      = (GenSpec.occurrences f).map (GenSpec.occValue flows a) := by
    simp [registerRows, List.map_map, Function.comp]
  rw [h, GenSpec.occurrences_foot]

/-! ## Posting rows -/

/-- Rows with a running total per commodity, starting from the total
    `tot`: each row keeps its label, account and amount, and carries
    the total after its amount is added in the commodity of its
    account. -/
def runRows {α : Type} (tot : Commodity → ℚ) :
    List (α × Account × ℚ) → List (α × Account × ℚ × (Commodity → ℚ))
  | [] => []
  | (l, a, q) :: rest =>
      let tot' : Commodity → ℚ := fun c => if a.commodity = c then tot c + q else tot c
      (l, a, q, tot') :: runRows tot' rest

private theorem runRows_map {α : Type} (tot : Commodity → ℚ)
    (rows : List (α × Account × ℚ)) :
    (runRows tot rows).map (fun r => (r.1, r.2.1, r.2.2.1)) = rows := by
  induction rows generalizing tot with
  | nil => rfl
  | cons r rest ih => obtain ⟨l, a, q⟩ := r; simp [runRows, ih]

private theorem runRows_getElem {α : Type} (tot : Commodity → ℚ)
    (rows : List (α × Account × ℚ)) (i : ℕ) (hi : i < (runRows tot rows).length)
    (c : Commodity) :
    (runRows tot rows)[i].2.2.2 c
      = tot c + (((rows.take (i + 1)).filter fun r => r.2.1.commodity = c).map
          fun r => r.2.2).sum := by
  induction rows generalizing tot i with
  | nil => simp [runRows] at hi
  | cons r rest ih =>
      obtain ⟨l, a, q⟩ := r
      cases i with
      | zero => by_cases h : a.commodity = c <;> simp [runRows, h]
      | succ j =>
          simp only [runRows, List.getElem_cons_succ]
          rw [ih, List.take_succ_cons]
          by_cases h : a.commodity = c <;> simp [h, add_assoc]

/-- The postings of a term in presentation order, each with the label
    of the generator occurrence it belongs to. -/
def labeledPostings (posts : L.Gen → List (Account × ℚ))
    {A B : Object} (f : L.toGenSpec.FreeMor A B) : List (Label × Account × ℚ) :=
  (GenSpec.occurrences f).flatMap fun ts =>
    (posts ts.1).map fun p => (L.label ts.1, p.1, if ts.2 then -p.2 else p.2)

/-- Register rows at posting granularity: one row per posting of the
    term, in presentation order, with its label, account and signed
    amount and the running total per commodity after it. The running
    total starts at zero and adds each posting's amount in its
    commodity, as `calc_posts::operator()` in src/filters.cc sets the
    running total of each posting to that of the posting before it
    plus the posting's own value (lines 427, 434 and 441 at 76b9dc2b2);
    test/baseline/cmd-register.test shows that total commodity by
    commodity (the example below). These rows do not follow C++ under
    `--average` without `--collapse` or `--depth`
    (src/chain.cc:334-335 at 76b9dc2b2), where lines 415-425 and
    444-445 of src/filters.cc start every posting flagged
    ITEM_GENERATED, among them automated postings (src/xact.cc:1640),
    the further postings that complete an elided posting
    (src/xact.cc:244) and the postings of an interval report
    (src/filters.cc:503), from the total that the last such posting to
    its account reached, or from zero. C++ reads its running total
    through the value expression `total` (src/post.cc:507-514); under
    `--average`, with or without those options, the total that it
    displays is that value divided by the posting count that
    `calc_posts::operator()` keeps (src/report.h:583-586 at
    76b9dc2b2). Register rows are not bisimulated: the oracle prints no
    register, and no C++ output is compared with these rows
    mechanically; the example below transcribes by hand the totals of
    test/baseline/cmd-register.test. -/
def postingRows (posts : L.Gen → List (Account × ℚ))
    {A B : Object} (f : L.toGenSpec.FreeMor A B) :
    List (Label × Account × ℚ × (Commodity → ℚ)) :=
  runRows 0 (L.labeledPostings posts f)

private theorem labeledPostings_map (posts : L.Gen → List (Account × ℚ))
    {A B : Object} (f : L.toGenSpec.FreeMor A B) :
    (L.labeledPostings posts f).map Prod.snd = GenSpec.termPostings posts f := by
  simp [labeledPostings, GenSpec.termPostings, List.map_flatMap, Function.comp_def]

/-- The rows of `postingRows` carry the postings of the term, in
    presentation order, with nothing added or left out. -/
theorem postingRows_postings (posts : L.Gen → List (Account × ℚ))
    {A B : Object} (f : L.toGenSpec.FreeMor A B) :
    (L.postingRows posts f).map (fun r => (r.2.1, r.2.2.1))
      = GenSpec.termPostings posts f := by
  rw [← labeledPostings_map, postingRows]
  conv_rhs => rw [← runRows_map 0 (L.labeledPostings posts f), List.map_map]
  rfl

/-- **The register foots to the balance, posting by posting**: the
    amounts of the rows at an account sum to its net flow. -/
theorem postingRows_foot (posts : L.Gen → List (Account × ℚ))
    {A B : Object} (f : L.toGenSpec.FreeMor A B) (a : Account) :
    (((L.postingRows posts f).filter fun r => r.2.1 = a).map fun r => r.2.2.1).sum
      = GenSpec.netFlow (GenSpec.postingFlows posts) f a := by
  rw [← GenSpec.termPostings_foot, GenSpec.postingValues, ← L.postingRows_postings posts f,
    List.filter_map, List.map_map]
  rfl

/-- **The running total is a prefix sum**: the total that row `i`
    carries in a commodity is the sum of the amounts in that commodity
    of the term's first `i + 1` postings. -/
theorem postingRows_total (posts : L.Gen → List (Account × ℚ))
    {A B : Object} (f : L.toGenSpec.FreeMor A B) (i : ℕ)
    (hi : i < (L.postingRows posts f).length) (c : Commodity) :
    (L.postingRows posts f)[i].2.2.2 c
      = ((((GenSpec.termPostings posts f).take (i + 1)).filter
          fun p => p.1.commodity = c).map Prod.snd).sum := by
  simp only [postingRows] at hi ⊢
  rw [runRows_getElem, ← labeledPostings_map, ← List.map_take, List.filter_map,
    List.map_map, Pi.zero_apply, zero_add]
  rfl

end LabeledGenSpec

/-- The three transactions of test/baseline/cmd-register.test. -/
private inductive RegEntry where
  | phone
  | rent
  | buy

/-- Their labels: the date, the payee and the cleared state of each.
    Endpoints play no part in posting rows. -/
private def regSpec : LabeledGenSpec where
  Gen := RegEntry
  dom _ := 0
  cod _ := 0
  label
    | .phone => { Label.empty with
        payee := "Phone expense on holidays", date := "2012-01-10", state := .cleared }
    | .rent => { Label.empty with
        payee := "Rent expense", date := "2012-01-31", state := .cleared }
    | .buy => { Label.empty with
        payee := "Buy AAA", date := "2012-02-01", state := .cleared }

/-- Each transaction's postings as the engine emits them, each amount in
    its own commodity. The first and the third are priced exchanges,
    12 EUR for 10 GBP and 1 AAA at 10 GBP, and each leaves a residual
    in both of its commodities. -/
private def regPosts : RegEntry → List (Account × ℚ)
  | .phone => [(⟨"Expenses:Phone", "EUR"⟩, 12), (⟨"Assets:Cash", "GBP"⟩, -10)]
  | .rent => [(⟨"Expenses:Rent", "GBP"⟩, 550), (⟨"Assets:Cash", "GBP"⟩, -550)]
  | .buy => [(⟨"Assets:Investment", "AAA"⟩, 1), (⟨"Assets:Cash", "GBP"⟩, -10)]

/-- The journal as `journalTerm` builds it. -/
private def regJournal :=
  GenSpec.FreeMor.tensor (S := regSpec.toGenSpec) (.gen RegEntry.phone)
    (.tensor (.gen RegEntry.rent) (.tensor (.gen RegEntry.buy) (.id 0)))

/-- **The running total of test/baseline/cmd-register.test**, row by
    row in EUR, GBP and AAA, as the total column of its `reg` report
    shows it: after the first transaction it holds 12 EUR and -10 GBP,
    the residuals of the exchange, and it ends at 1 AAA, 12 EUR and
    -20 GBP. -/
example :
    (regSpec.postingRows regPosts regJournal).map
        (fun r => (r.2.2.2 "EUR", r.2.2.2 "GBP", r.2.2.2 "AAA"))
      = [(12, 0, 0), (12, -10, 0), (12, 540, 0), (12, -10, 0), (12, -10, 1),
         (12, -20, 1)] := by
  decide +kernel

end Ledger
