import Ledger.Pacioli

/-!
# Phase 9: the executable oracle

The specification-grade reference evaluator: `netFlow` computes an L2
term's per-account flow **computably** (plain functions and exact ℚ —
no `Finsupp`, whose algebra is classical), and
`netFlow_eq_flowAux` proves it agrees pointwise with the L1
denotation. "We only compute with representations; we only think
with meanings" — `netFlow` is the computing side, `flow` the
meaning side, and the agreement theorem is the bridge.

Two journals carry golden vectors. `Demo` is a three-entry January
journal (salary, rent, groceries) mirroring `test/semantic/demo.dat`,
the journal on which the C++ harness plants its detector defect; the
harness compares `ledger balance` on it with the oracle's output.
`Ellerman` is the worked vector ledger of Ellerman (2014), pp. 496-498,
in three commodities. Every golden is a named theorem proved by
`decide +kernel`, so the kernel itself evaluates the quantity it states
over exact rationals, and no auxiliary lemma or linter option stands
between a golden and its number. Every golden but
`Ellerman.entry_values` evaluates `netFlow`; that one values each
entry's own flows, so it checks the transcription and the price
arithmetic rather than the evaluator. Both journals are transcribed by
hand: the goldens check the evaluator and the two encodings, not the
parser.

Performance is irrelevant by design: this evaluator exists to be
obviously faithful to the denotation, not fast.
-/

namespace Ledger

namespace GenSpec

variable {S : GenSpec}

/-- Computable per-account flow of a term. -/
def netFlow (flows : S.Gen → Account → ℚ) :
    {A B : Object} → S.FreeMor A B → Account → ℚ
  | _, _, .gen t => flows t
  | _, _, .id _ => fun _ => 0
  | _, _, .zero _ _ => fun _ => 0
  | _, _, .comp g f => fun a => netFlow flows g a + netFlow flows f a
  | _, _, .inv f => fun a => -netFlow flows f a
  | _, _, .tensor f g => fun a => netFlow flows f a + netFlow flows g a
  | _, _, .add f g => fun a => netFlow flows f a + netFlow flows g a

/-- The oracle agrees with the L1 denotation, account by account —
    the executable and the meaning compute the same thing. -/
theorem netFlow_eq_flowAux (flowsF : S.Gen → PacioliGroup)
    {A B : Object} (f : S.FreeMor A B) (a : Account) :
    netFlow (fun t => (flowsF t : Account → ℚ)) f a
      = (flowAux flowsF f) a := by
  induction f with
  | gen t => simp [netFlow, flowAux]
  | id A => simp [netFlow, flowAux]
  | zero A B => simp [netFlow, flowAux]
  | comp g f ihg ihf =>
      simp [netFlow, flowAux, Finsupp.add_apply, ihg, ihf]
  | inv f ih => simp [netFlow, flowAux, Finsupp.neg_apply, ih]
  | tensor f g ihf ihg =>
      simp [netFlow, flowAux, Finsupp.add_apply, ihf, ihg]
  | add f g ihf ihg =>
      simp [netFlow, flowAux, Finsupp.add_apply, ihf, ihg]

/-- The oracle is `Rel`-invariant (via the agreement with `flowAux`):
    semantically equal terms report identical balances. -/
theorem netFlow_respects (flowsF : S.Gen → PacioliGroup)
    {A B : Object} {f g : S.FreeMor A B} (h : Rel f g) (a : Account) :
    netFlow (fun t => (flowsF t : Account → ℚ)) f a
      = netFlow (fun t => (flowsF t : Account → ℚ)) g a := by
  rw [netFlow_eq_flowAux, netFlow_eq_flowAux, flowAux_respects flowsF h]

/-- **The per-commodity trial balance, computing side.** If every
    generator's flows sum to zero over the commodity-`c` accounts of a
    finite set `s` (for an `s` that holds every account a generator
    touches, each generator is then a zero-row in `c`), then so do the
    flows of every term over the same accounts.

    The hypothesis is a condition on the generators, and not every
    generator the oracle emits meets it: a priced exchange leaves a
    nonzero column in each of its commodities, and a residual accepted
    as an implicit exchange or within the balancing tolerance, a
    paren-virtual posting (exempt from balancing, whether written in
    the transaction or appended by an automated transaction), and a
    timeclock entry (added without a balance check) can each do the
    same, as the docstring of `free_trial_balance` records for the
    free model. `netFlow_commodity_sum` in `Ledger/Register.lean`
    gives the unconditional form. -/
theorem netFlow_trial_balance (flows : S.Gen → Account → ℚ)
    (s : Finset Account) (c : Commodity)
    (hgen : ∀ t, ∑ a ∈ s.filter (·.commodity = c), flows t a = 0)
    {A B : Object} (f : S.FreeMor A B) :
    ∑ a ∈ s.filter (·.commodity = c), netFlow flows f a = 0 := by
  induction f with
  | gen t => simpa [netFlow] using hgen t
  | id _ => simp [netFlow]
  | zero _ _ => simp [netFlow]
  | comp g f ihg ihf => simp [netFlow, Finset.sum_add_distrib, ihg, ihf]
  | inv f ih => simp [netFlow, Finset.sum_neg_distrib, ih]
  | tensor f g ihf ihg => simp [netFlow, Finset.sum_add_distrib, ihf, ihg]
  | add f g ihf ihg => simp [netFlow, Finset.sum_add_distrib, ihf, ihg]

/-- The value at rational prices `p` of a term's flows over a list of
    accounts: the sum, over `accts`, of each account's net flow times
    the price of its commodity, computed as `netFlow` is, with plain
    functions and exact rationals. An account listed twice is counted
    twice, and an account not listed is not counted. Over a list
    without duplicates that holds every account at which the term's
    flow is nonzero, and when the flows of the generators are vectors
    of `PacioliGroup` read pointwise (as the flows `flowsFor` of
    `Driver` are, by `coe_flowsFin`), it is `priceDot`, the scalar
    product of the price vector with the term's ledger-wide property
    vector, which is Ellerman's valuation of property at a price
    vector (p. 498). The join module `Ledger/Market.lean` proves this
    as `netValue_eq_priceDot`, so that this module, which is on the
    oracle's run path, need not import `Ledger/PriceVector.lean`. -/
def netValue (flows : S.Gen → Account → ℚ) (accts : List Account)
    (p : Commodity → ℚ) {A B : Object} (f : S.FreeMor A B) : ℚ :=
  (accts.map fun a => netFlow flows f a * p a.commodity).sum

/-- The value at rational prices `p` of a term's flows at the accounts
    of `accts` named `n`: `netValue` over those accounts alone. Under
    the conditions on `accts` and on the flows stated for `netValue`,
    it is `valueHom`, the value of account name `n`'s property vector,
    as Ellerman values the assets vector of p. 498; the join module
    `Ledger/Market.lean` proves this as `netValueAt_eq_valueHom`. -/
def netValueAt (flows : S.Gen → Account → ℚ) (accts : List Account)
    (p : Commodity → ℚ) (n : AccountName) {A B : Object} (f : S.FreeMor A B) : ℚ :=
  netValue flows (accts.filter fun a => a.name = n) p f

end GenSpec

/-! ## The demo journal (`test/semantic/demo.dat`) -/

namespace Demo

/-- The three entries of the demo journal. -/
inductive Entry where
  | salary
  | rent
  | groceries
  deriving DecidableEq, Repr

def checking : Account := ⟨"Assets:Checking", "$"⟩
def salaryAcct : Account := ⟨"Income:Salary", "$"⟩
def rentAcct : Account := ⟨"Expenses:Rent", "$"⟩
def foodAcct : Account := ⟨"Expenses:Food", "$"⟩

/-- Endpoints: each entry moves value from its source account(s) to
    its target account(s). -/
def spec : GenSpec where
  Gen := Entry
  dom
    | .salary => {salaryAcct}
    | .rent => {checking}
    | .groceries => {checking}
  cod
    | .salary => {checking}
    | .rent => {rentAcct}
    | .groceries => {foodAcct}

/-- Per-entry flows, debit-positive, in dollars. Each entry balances:
    its flows sum to zero across accounts. -/
def flows : Entry → Account → ℚ
  | .salary => fun a =>
      if a = checking then 5000 else if a = salaryAcct then -5000 else 0
  | .rent => fun a =>
      if a = checking then -2000 else if a = rentAcct then 2000 else 0
  | .groceries => fun a =>
      if a = checking then -150 else if a = foodAcct then 150 else 0

/-- Embed a journal entry as an atomic morphism. -/
def entry (e : Entry) : spec.FreeMor (spec.dom e) (spec.cod e) :=
  GenSpec.FreeMor.gen (S := spec) e

/-- January as a single parallel composite — the journal's entry
    order is presentation, not meaning. -/
def january :=
  GenSpec.FreeMor.tensor
    (GenSpec.FreeMor.tensor (entry Entry.salary) (entry Entry.rent))
    (entry Entry.groceries)

/-! ### Golden vectors

The oracle's expected balances for the demo journal. The C++
`ledger -f test/semantic/demo.dat balance --flat` report must agree
(see `test/semantic/`). -/

theorem golden_checking : GenSpec.netFlow flows january checking = 2850 := by
  decide +kernel

theorem golden_salary : GenSpec.netFlow flows january salaryAcct = -5000 := by
  decide +kernel

theorem golden_rent : GenSpec.netFlow flows january rentAcct = 2000 := by
  decide +kernel

theorem golden_food : GenSpec.netFlow flows january foodAcct = 150 := by
  decide +kernel

/-- The demo journal balances: every entry's flows sum to zero, so
    the whole month's do — the trial balance, concretely. -/
theorem golden_trial_balance :
    GenSpec.netFlow flows january checking
      + GenSpec.netFlow flows january salaryAcct
      + GenSpec.netFlow flows january rentAcct
      + GenSpec.netFlow flows january foodAcct = 0 := by
  decide +kernel

end Demo

/-! ## Ellerman's worked vector ledger (pp. 489, 496-498)

Ellerman, "On Double-Entry Bookkeeping: The Mathematical Treatment",
Accounting Education 23:5 (2014) 483-501. On pp. 496-498 a vector
journal over three types of property, "cash, outputs (widgets), and
inputs (half-widgets)" (p. 496), is posted to an opening ledger of
Assets, Liabilities and Equity; here the three types are the
commodities `$`, `WIDGET` and `HALF`. The postings of each entry are
its row in the single-sided table of p. 498, debit-positive, with zero
components left out. Flows and endpoints are computed from those
postings as `flowsFor` and `specFor` compute them from the engine's
output, and the journal is the right-nested tensor that `journalTerm`
builds. The goldens state p. 498's ending row, its trial balance in
each commodity, and its value at the prices of p. 498; valued at the
same prices, the entries reproduce the scalar example of p. 489.

The journal is transcribed by hand, since `Parse` and `Journal` contain
partial definitions the kernel cannot evaluate, and `Ellerman.price` is
a hand-written rational function: `Ellerman.ending_value` and
`Ellerman.entry_values` check the arithmetic of pp. 489 and 498, not
`Ledger/Valuation.lean` and not market valuation. -/

namespace Ellerman

/-- The five entries: the opening balance sheet of p. 497 and
    transactions 1, 2a, 2b and 3 of the same page. Every transaction
    except the loan payment, transaction 3, posts against Equity, since
    the article deals "for simplicity, directly with equity rather than
    using 'income statement' or property-flow accounts" (p. 497).
    Transaction 2b, the sale of 20 widgets for $100 each, therefore
    carries an Equity leg that reverses its Assets leg in each property
    type. The encoding transcribes the article's journal and makes no
    claim about how a sale ought to be booked. -/
inductive Entry where
  | opening
  | used
  | produced
  | sold
  | loan
  deriving DecidableEq, Repr

/-- The three types of property in the article's order: cash, outputs
    (widgets) and inputs (half-widgets). -/
def commodities : List Commodity := ["$", "WIDGET", "HALF"]

/-- The accounts of the balance-sheet equation. -/
def accounts : List AccountName := ["Assets", "Liabilities", "Equity"]

/-- The postings of each entry: its row in the single-sided table of
    p. 498, debit-positive, with zero components left out. -/
def postings : Entry → List (Account × ℚ)
  | .opening =>
      [(⟨"Assets", "$"⟩, 9000), (⟨"Assets", "WIDGET"⟩, 40), (⟨"Assets", "HALF"⟩, 50),
       (⟨"Liabilities", "$"⟩, -10000),
       (⟨"Equity", "$"⟩, 1000), (⟨"Equity", "WIDGET"⟩, -40), (⟨"Equity", "HALF"⟩, -50)]
  | .used => [(⟨"Assets", "HALF"⟩, -30), (⟨"Equity", "HALF"⟩, 30)]
  | .produced => [(⟨"Assets", "WIDGET"⟩, 15), (⟨"Equity", "WIDGET"⟩, -15)]
  | .sold =>
      [(⟨"Assets", "$"⟩, 2000), (⟨"Assets", "WIDGET"⟩, -20),
       (⟨"Equity", "WIDGET"⟩, 20), (⟨"Equity", "$"⟩, -2000)]
  | .loan => [(⟨"Assets", "$"⟩, -800), (⟨"Liabilities", "$"⟩, 800)]

/-- Per-entry flows, summed as `flowsFor` sums a generator's postings.
    No entry of p. 498 posts twice to one account and commodity, so
    each sum here has at most one term. -/
def flows (e : Entry) (a : Account) : ℚ :=
  ((postings e).filter fun p => p.1 = a).foldl (fun s p => s + p.2) 0

/-- Endpoints as `specFor` builds them: an entry's domain holds the
    accounts of its negative postings, its codomain those of its
    positive postings. -/
def spec : GenSpec where
  Gen := Entry
  dom e := (((postings e).filter fun p => p.2 < 0).map Prod.fst : List Account)
  cod e := (((postings e).filter fun p => p.2 > 0).map Prod.fst : List Account)

/-- Embed an entry as an atomic morphism. -/
def entry (e : Entry) : spec.FreeMor (spec.dom e) (spec.cod e) :=
  GenSpec.FreeMor.gen (S := spec) e

/-- The journal in the article's order, built as `journalTerm` builds
    it: the right-nested tensor of the entries, closed by the identity
    on the empty object. -/
def journal :=
  GenSpec.FreeMor.tensor (entry Entry.opening)
    (GenSpec.FreeMor.tensor (entry Entry.used)
      (GenSpec.FreeMor.tensor (entry Entry.produced)
        (GenSpec.FreeMor.tensor (entry Entry.sold)
          (GenSpec.FreeMor.tensor (entry Entry.loan) (GenSpec.FreeMor.id (S := spec) 0)))))

/-! ### Golden vectors

p. 498's ending row, `(10200, 35, 20)` for Assets, `(-9200, 0, 0)` for
Liabilities and `(-1000, -35, -20)` for Equity: the ending balance
sheet in the form A - L - E = 0. -/

theorem assets_cash : GenSpec.netFlow flows journal ⟨"Assets", "$"⟩ = 10200 := by
  decide +kernel

theorem assets_widget : GenSpec.netFlow flows journal ⟨"Assets", "WIDGET"⟩ = 35 := by
  decide +kernel

theorem assets_half : GenSpec.netFlow flows journal ⟨"Assets", "HALF"⟩ = 20 := by
  decide +kernel

theorem liabilities_cash : GenSpec.netFlow flows journal ⟨"Liabilities", "$"⟩ = -9200 := by
  decide +kernel

theorem equity_cash : GenSpec.netFlow flows journal ⟨"Equity", "$"⟩ = -1000 := by
  decide +kernel

theorem equity_widget : GenSpec.netFlow flows journal ⟨"Equity", "WIDGET"⟩ = -35 := by
  decide +kernel

theorem equity_half : GenSpec.netFlow flows journal ⟨"Equity", "HALF"⟩ = -20 := by
  decide +kernel

/-- Liabilities end with no goods: their widget and half-widget
    components are zero. -/
theorem liabilities_goods :
    GenSpec.netFlow flows journal ⟨"Liabilities", "WIDGET"⟩ = 0
      ∧ GenSpec.netFlow flows journal ⟨"Liabilities", "HALF"⟩ = 0 := by
  decide +kernel

/-- The ending ledger is a zero-row in each type of property: the trial
    balance of p. 498, commodity by commodity. -/
theorem trial_balance_componentwise :
    ∀ c ∈ commodities,
      (accounts.map fun n => GenSpec.netFlow flows journal ⟨n, c⟩).sum = 0 := by
  decide +kernel

/-- The prices per unit of p. 498: 1 for cash, 100 for a widget and 40
    for a half-widget. -/
def price : Commodity → ℚ
  | "$" => 1
  | "WIDGET" => 100
  | "HALF" => 40
  | _ => 0

/-- The value at `price` of one account under a flow assignment: the
    scalar product of p. 498, price vector times property vector. -/
def value (f : Account → ℚ) (n : AccountName) : ℚ :=
  (commodities.map fun c => price c * f ⟨n, c⟩).sum

/-- p. 498, "Scalar equation = price vector times vector equation": the
    ending ledger, valued at `price`, is 14500, -9200 and -5300
    debit-positive, which decodes to 14500 = 9200 + 5300, the ending
    balance sheet of the scalar example of p. 489. -/
theorem ending_value :
    accounts.map (value (GenSpec.netFlow flows journal)) = [14500, -9200, -5300] := by
  decide +kernel

/-- Each entry, valued at `price`, is the matching entry of the scalar
    example of p. 489, debit-positive: the opening balance sheet
    15000 = 10000 + 5000, transaction 1 of 1200, transaction 2 of 1500
    as 2a, and transaction 3 of 800. The sale 2b, which the vector
    journal splits from production (p. 497), is worth zero. The
    statement does not evaluate `netFlow`: it checks the transcription
    of the postings and the price arithmetic, not the evaluator. -/
theorem entry_values :
    [Entry.opening, .used, .produced, .sold, .loan].map
        (fun e => accounts.map (value (flows e)))
      = [[15000, -10000, -5000], [-1200, 0, 1200], [1500, 0, -1500], [0, 0, 0],
          [-800, 800, 0]] := by
  decide +kernel

end Ellerman

end Ledger
