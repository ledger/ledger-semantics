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

`Demo` is a three-entry January journal (salary, rent, groceries)
mirroring `test/semantic/demo.dat`; the golden-vector examples at the
bottom are the oracle's expected balances for it, checked by the
kernel. The C++ bisimulation exhibit (Phase 10) compares `ledger
balance` on the same journal against these numbers.

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

private theorem ne₁ : (salaryAcct = checking) = False := eq_false (by decide)
private theorem ne₂ : (salaryAcct = rentAcct) = False := eq_false (by decide)
private theorem ne₃ : (salaryAcct = foodAcct) = False := eq_false (by decide)
private theorem ne₄ : (rentAcct = checking) = False := eq_false (by decide)
private theorem ne₅ : (rentAcct = salaryAcct) = False := eq_false (by decide)
private theorem ne₆ : (rentAcct = foodAcct) = False := eq_false (by decide)
private theorem ne₇ : (foodAcct = checking) = False := eq_false (by decide)
private theorem ne₈ : (foodAcct = salaryAcct) = False := eq_false (by decide)
private theorem ne₉ : (foodAcct = rentAcct) = False := eq_false (by decide)

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

example : GenSpec.netFlow flows january checking = 2850 := by
  simp [GenSpec.netFlow, january, entry, flows, ne₁, ne₂, ne₃, ne₄, ne₅,
    ne₆, ne₇, ne₈, ne₉] <;> norm_num

example : GenSpec.netFlow flows january salaryAcct = -5000 := by
  simp [GenSpec.netFlow, january, entry, flows, ne₁, ne₂, ne₃, ne₄, ne₅,
    ne₆, ne₇, ne₈, ne₉] <;> norm_num

example : GenSpec.netFlow flows january rentAcct = 2000 := by
  simp [GenSpec.netFlow, january, entry, flows, ne₁, ne₂, ne₃, ne₄, ne₅,
    ne₆, ne₇, ne₈, ne₉] <;> norm_num

example : GenSpec.netFlow flows january foodAcct = 150 := by
  simp [GenSpec.netFlow, january, entry, flows, ne₁, ne₂, ne₃, ne₄, ne₅,
    ne₆, ne₇, ne₈, ne₉] <;> norm_num

/-- The demo journal balances: every entry's flows sum to zero, so
    the whole month's do — the trial balance, concretely. -/
example :
    GenSpec.netFlow flows january checking
      + GenSpec.netFlow flows january salaryAcct
      + GenSpec.netFlow flows january rentAcct
      + GenSpec.netFlow flows january foodAcct = 0 := by
  simp [GenSpec.netFlow, january, entry, flows, ne₁, ne₂, ne₃, ne₄, ne₅,
    ne₆, ne₇, ne₈, ne₉] <;> norm_num

end Demo

end Ledger
