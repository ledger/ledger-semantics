import Ledger.Register
import Ledger.TAccount

/-!
# Gross totals as Ellerman's T-accounts

On p. 489 Ellerman posts a journal to a ledger by adding the zero-term
of each transaction to the equation zero-account of the opening
balance sheet, T-account by T-account, and he gives the ending ledger
both as that sum and "(in reduced form)": `[16500 // 2000]` and
`[14500 // 0]` for Assets, `[800 // 10000]` and `[0 // 9200]` for
Liabilities, and `[1200 // 6500]` and `[0 // 5300]` for Equity. On
p. 490 the three transaction zero-terms alone add up to the "Total
transaction zero-term", `[1500 // 2000]` for Assets, and on p. 491 the
change in debits of 1500 and the change in credits of 2000 that a
transactions table shows for Assets are "just an implicit T-term
`[1500 // 2000]` for the changes in the account". The two sides of
such an unreduced T-account are gross totals. `Ledger/Register.lean`
computes gross totals as rational numbers, at two granularities:
`debitTotal` and `creditTotal`, paired in `grossTotals`, sum the
positive amounts and the magnitudes of the negative amounts posted to
an account, posting by posting, which is how the option `--dc` of C++
splits them (`Ledger/Register.lean` gives the source), while
`txnDebitTotal` and `txnCreditTotal` first net each generator
occurrence at the account, as Ellerman adds the T-terms of whole
transactions. This module reads both as the T-accounts of
`Ledger/TAccount.lean`, so that Ellerman's equality of T-accounts and
his Pacioli group apply to them.

`grossLedger` adds the T-term `[x⁺ // x⁻]` (p. 494) of every posting
of a term, and `txnGrossLedger` adds that of the net flow of every
generator occurrence, or its reversal `[x⁻ // x⁺]` when the occurrence
is reversed; neither sum is reduced. `grossLedger_sides` states that
the two sides of `grossLedger` at an account are `debitTotal` and
`creditTotal`, and `txnGrossLedger_sides` that those of
`txnGrossLedger` are `txnDebitTotal` and `txnCreditTotal`. By
`net_grossLedger` and `net_txnGrossLedger`, the net balance
`TAccount.net` of either, which is the image of its class under the
debit isomorphism, is the flow denotation `flowAux` of the term when
the flows of each generator are the sums of its postings
(`postingFlowsF`). The two granularities therefore give pairs that can
differ but always have equal cross-sums, which is Ellerman's equality
of T-accounts (Table 1, p. 485) and `grossLedger_crossEq`. For
Expenses:Food in test/baseline/opt-dc.test, whose gross totals are $40
and $10 and whose totals at transaction granularity are $35 and $5
(the example in `Ledger/Register.lean`), the two T-accounts are
`[40 // 10]` and `[35 // 5]`, distinct pairs with 40 + 5 = 10 + 35, as
an example below checks. `toP_grossLedger` identifies the class of
`grossLedger` in Ellerman's Pacioli group `TAccount.PacioliP`: it is
the preimage under `TAccount.debitIso` of the denotation `flow` of the
term's class in `FreeHom`. Gross totals are not invariant under `Rel`,
as the docstring of `Ledger/Register.lean` records, but the class of
the T-account that they form is, because it depends on the term only
through that denotation (an example below). The example at the end of
this module reproduces the ending ledger of p. 489, unreduced and
reduced, and the total transaction zero-term of p. 490 at both
granularities, which agree on that table because each of its rows
posts to each account at most once.

This is a join module: it imports the executable module `Register`
and the specification leaf `TAccount` only to state these proofs, and
it holds only the definitions and theorems that they need. No module
on the oracle's run path, which is the import closure of `Driver`,
imports it. The proofs sit here rather than in `Register.lean` so that
importing `Register.lean` does not bring in `TAccount.lean` and the
Mathlib modules that it imports.
-/

namespace Ledger

namespace GenSpec

variable {S : GenSpec}

open TAccount

/-- The flows of a generator that records its postings as a list, as a
    vector of the carrier `PacioliGroup`: the sum, over its postings,
    of the vector that holds the posting's amount at its account. -/
noncomputable def postingFlowsF (posts : S.Gen → List (Account × ℚ)) (t : S.Gen) :
    PacioliGroup :=
  ((posts t).map fun p => Finsupp.single p.1 p.2).sum

private theorem sum_single_apply (l : List (Account × ℚ)) (a : Account) :
    ((l.map fun p => Finsupp.single p.1 p.2).sum : PacioliGroup) a
      = ((l.filter fun p => p.1 = a).map Prod.snd).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      rw [List.map_cons, List.sum_cons, Finsupp.add_apply, ih, List.filter_cons]
      by_cases h : x.1 = a
      · simp [h]
      · simp [h]

/-- `postingFlowsF` and `postingFlows` agree account by account. -/
theorem postingFlowsF_apply (posts : S.Gen → List (Account × ℚ)) (t : S.Gen)
    (a : Account) : postingFlowsF posts t a = postingFlows posts t a := by
  rw [postingFlowsF, sum_single_apply, postingFlows,
    ← List.foldl_map (f := Prod.snd) (g := (· + ·)), ← List.sum_eq_foldl]

private theorem coe_postingFlowsF (posts : S.Gen → List (Account × ℚ)) :
    (fun t => ⇑(postingFlowsF posts t)) = postingFlows posts := by
  funext t a
  exact postingFlowsF_apply posts t a

private theorem flowAux_postingFlowsF (posts : S.Gen → List (Account × ℚ))
    {A B : Object} (f : S.FreeMor A B) (a : Account) :
    flowAux (postingFlowsF posts) f a = netFlow (postingFlows posts) f a := by
  rw [← netFlow_eq_flowAux, coe_postingFlowsF]

/-- The gross ledger of a term at posting granularity: the sum, not
    reduced, of the T-terms `[x⁺ // x⁻]` of its postings, each taken at
    the account it is posted to. -/
noncomputable def grossLedger (posts : S.Gen → List (Account × ℚ))
    {A B : Object} (f : S.FreeMor A B) : TAccount Account :=
  ((termPostings posts f).map fun p => reduce (Finsupp.single p.1 p.2)).sum

/-- The gross ledger of a term at transaction granularity, Ellerman's:
    the sum, not reduced, of the T-terms of the net flows of its
    generator occurrences, with debit and credit exchanged for a
    reversed occurrence (Table 1, p. 485). -/
noncomputable def txnGrossLedger (flowsF : S.Gen → PacioliGroup)
    {A B : Object} (f : S.FreeMor A B) : TAccount Account :=
  ((occurrences f).map fun ts =>
    if ts.2 then swap (reduce (flowsF ts.1)) else reduce (flowsF ts.1)).sum

/-- **The net balance of the gross ledger is the flow denotation**: its
    debits less its credits, account by account, are the term's flow,
    the flows of each generator being the sums of its postings. -/
theorem net_grossLedger (posts : S.Gen → List (Account × ℚ))
    {A B : Object} (f : S.FreeMor A B) :
    net (grossLedger posts f) = flowAux (postingFlowsF posts) f := by
  ext a
  rw [grossLedger, map_list_sum, List.map_map]
  have h1 : (net ∘ fun p : Account × ℚ => reduce (Finsupp.single p.1 p.2))
      = fun p => Finsupp.single p.1 p.2 := by
    funext p
    simp [net_reduce]
  have h2 := termPostings_foot posts f a
  rw [postingValues] at h2
  rw [h1, sum_single_apply, h2, flowAux_postingFlowsF]

/-- **The same at transaction granularity**: the net balance of the
    gross ledger of whole occurrences is the flow denotation. -/
theorem net_txnGrossLedger (flowsF : S.Gen → PacioliGroup)
    {A B : Object} (f : S.FreeMor A B) :
    net (txnGrossLedger flowsF f) = flowAux flowsF f := by
  ext a
  rw [txnGrossLedger, map_list_sum, List.map_map, ← netFlow_eq_flowAux,
    ← occurrences_foot]
  have key : ∀ l : List (S.Gen × Bool),
      ((l.map (net ∘ fun ts => if ts.2 then swap (reduce (flowsF ts.1))
        else reduce (flowsF ts.1))).sum : PacioliGroup) a
        = (l.map (occValue (fun t => (flowsF t : Account → ℚ)) a)).sum := by
    intro l
    induction l with
    | nil => simp
    | cons x xs ih =>
        rw [List.map_cons, List.sum_cons, Finsupp.add_apply, ih, List.map_cons,
          List.sum_cons]
        congr 1
        obtain ⟨t, b⟩ := x
        cases b <;> simp [occValue, net_swap, net_reduce]
  exact key _

/-- **The two granularities have equal cross-sums**: posting by posting
    and transaction by transaction, the gross ledgers are equal
    T-accounts in the sense of Table 1 (p. 485), although as pairs they
    can differ (the example on test/baseline/opt-dc.test below). -/
theorem grossLedger_crossEq (posts : S.Gen → List (Account × ℚ))
    {A B : Object} (f : S.FreeMor A B) :
    CrossEq (grossLedger posts f) (txnGrossLedger (postingFlowsF posts) f) := by
  rw [← net_eq_net_iff, net_grossLedger, net_txnGrossLedger]

/-- **Unreduced and reduced** (pp. 489 and 491): the class of the gross
    ledger in the Pacioli group is the preimage under the debit
    isomorphism of the denotation of the term's class, which is the
    class of the reduced T-account `[v⁺ // v⁻]` of its net flow `v`
    (`TAccount.debitIso_symm_apply`). On p. 491 the equation
    `[16500 // 2000] = [14500 // 0]` "holds by the equality of
    cross-sums". -/
theorem toP_grossLedger (posts : S.Gen → List (Account × ℚ))
    {A B : Object} (f : S.FreeMor A B) :
    toP (grossLedger posts f)
      = debitIso.symm (flow (postingFlowsF posts) (⟦f⟧ : FreeHom S A B)) := by
  rw [debitIso_symm_apply, toP_eq_toP_iff, ← net_eq_net_iff, net_reduce, flow_mk,
    net_grossLedger]

/-- **The sides of the gross ledger are the gross totals**: at every
    account, its debit side is `debitTotal` and its credit side is
    `creditTotal`. -/
theorem grossLedger_sides (posts : S.Gen → List (Account × ℚ))
    {A B : Object} (f : S.FreeMor A B) (a : Account) :
    ((grossLedger posts f).1 a : ℚ) = debitTotal posts f a
      ∧ ((grossLedger posts f).2 a : ℚ) = creditTotal posts f a := by
  have key : ∀ l : List (Account × ℚ),
      (((l.map fun p => reduce (Finsupp.single p.1 p.2)).sum).1 a : ℚ)
          = (((l.filter fun p => p.1 = a).map Prod.snd).map fun q => q⁺).sum
        ∧ (((l.map fun p => reduce (Finsupp.single p.1 p.2)).sum).2 a : ℚ)
          = (((l.filter fun p => p.1 = a).map Prod.snd).map fun q => q⁻).sum := by
    intro l
    induction l with
    | nil => simp
    | cons x xs ih =>
        rw [List.map_cons, List.sum_cons, Prod.fst_add, Prod.snd_add, Finsupp.add_apply,
          Finsupp.add_apply, NNRat.cast_add, NNRat.cast_add, ih.1, ih.2, List.filter_cons]
        have hpos : x.2⁺ = max x.2 0 := rfl
        have hneg : x.2⁻ = max (-x.2) 0 := rfl
        by_cases h : x.1 = a
        · simp [h, reduce, coe_toNNRat_eq_max, hpos, hneg]
        · simp [h, reduce]
  exact key _

/-- **The sides of the gross ledger of whole occurrences are the totals
    at transaction granularity**: at every account, its debit side is
    `txnDebitTotal` and its credit side is `txnCreditTotal`. -/
theorem txnGrossLedger_sides (flowsF : S.Gen → PacioliGroup)
    {A B : Object} (f : S.FreeMor A B) (a : Account) :
    ((txnGrossLedger flowsF f).1 a : ℚ) = txnDebitTotal (fun t => ⇑(flowsF t)) f a
      ∧ ((txnGrossLedger flowsF f).2 a : ℚ)
        = txnCreditTotal (fun t => ⇑(flowsF t)) f a := by
  have key : ∀ l : List (S.Gen × Bool),
      (((l.map fun ts : S.Gen × Bool => if ts.2 then swap (reduce (flowsF ts.1))
          else reduce (flowsF ts.1)).sum).1 a : ℚ)
          = (l.map fun ts => (occValue (fun t => ⇑(flowsF t)) a ts)⁺).sum
        ∧ (((l.map fun ts : S.Gen × Bool => if ts.2 then swap (reduce (flowsF ts.1))
          else reduce (flowsF ts.1)).sum).2 a : ℚ)
          = (l.map fun ts => (occValue (fun t => ⇑(flowsF t)) a ts)⁻).sum := by
    intro l
    induction l with
    | nil => simp
    | cons x xs ih =>
        rw [List.map_cons, List.sum_cons, Prod.fst_add, Prod.snd_add, Finsupp.add_apply,
          Finsupp.add_apply, NNRat.cast_add, NNRat.cast_add, ih.1, ih.2, List.map_cons,
          List.sum_cons, List.map_cons, List.sum_cons]
        obtain ⟨t, b⟩ := x
        have hpos : ∀ q : ℚ, q⁺ = max q 0 := fun _ => rfl
        have hneg : ∀ q : ℚ, q⁻ = max (-q) 0 := fun _ => rfl
        cases b <;> simp [occValue, swap, reduce, coe_toNNRat_eq_max, hpos, hneg]
  exact key _

/-- **The class of the gross ledger is `Rel`-invariant**: `Rel`-equal
    terms give gross ledgers of one class in the Pacioli group, by
    `toP_grossLedger`, though their gross totals can differ. -/
example (posts : S.Gen → List (Account × ℚ)) {A B : Object} {f g : S.FreeMor A B}
    (h : Rel f g) : toP (grossLedger posts f) = toP (grossLedger posts g) := by
  rw [toP_grossLedger, toP_grossLedger, Quotient.sound h]

/-- The debit and credit sides of a T-account at one account, as
    rationals. -/
private def sidesAt (x : TAccount Account) (a : Account) : ℚ × ℚ :=
  ((x.1 a : ℚ), (x.2 a : ℚ))

/-- The four transactions of test/baseline/opt-dc.test, transcribed as
    in the example of gross totals in `Ledger/Register.lean`, whose
    definitions are private to that module. Endpoints play no part in
    gross totals. -/
private inductive OptDcEntry where
  | employer
  | kfc
  | rebate
  | foodAndRebate

private def optDcSpec : GenSpec := ⟨OptDcEntry, fun _ => 0, fun _ => 0⟩

private def optDcCash : Account := ⟨"Assets:Cash", "$"⟩
private def optDcFood : Account := ⟨"Expenses:Food", "$"⟩
private def optDcIncome : Account := ⟨"Income:Employer", "$"⟩

/-- Each transaction's postings as the engine emits them, the elided
    posting completed and listed after the written ones; the last
    transaction posts to Expenses:Food twice. -/
private def optDcPosts : OptDcEntry → List (Account × ℚ)
  | .employer => [(optDcCash, 100), (optDcIncome, -100)]
  | .kfc => [(optDcFood, 20), (optDcCash, -20)]
  | .rebate => [(optDcFood, -5), (optDcCash, 5)]
  | .foodAndRebate => [(optDcFood, 20), (optDcFood, -5), (optDcCash, -15)]

/-- The journal as `journalTerm` builds it: the right-nested tensor of
    the four transactions, closed by the identity on the empty
    object. -/
private def optDcJournal :=
  FreeMor.tensor (S := optDcSpec) (.gen OptDcEntry.employer)
    (.tensor (.gen OptDcEntry.kfc) (.tensor (.gen OptDcEntry.rebate)
      (.tensor (.gen OptDcEntry.foodAndRebate) (.id 0))))

/-- **The two granularities differ as pairs** (test/baseline/opt-dc.test):
    at Expenses:Food the gross ledger is `[40 // 10]`, the two postings
    to it in the last transaction being counted separately, and the
    gross ledger of whole transactions is `[35 // 5]`. The two gross
    ledgers are therefore distinct T-accounts, although their
    cross-sums are equal by `grossLedger_crossEq`. -/
example :
    sidesAt (grossLedger (S := optDcSpec) optDcPosts optDcJournal) optDcFood = (40, 10)
      ∧ sidesAt (txnGrossLedger (S := optDcSpec) (postingFlowsF optDcPosts) optDcJournal)
          optDcFood = (35, 5)
      ∧ grossLedger (S := optDcSpec) optDcPosts optDcJournal
          ≠ txnGrossLedger (S := optDcSpec) (postingFlowsF optDcPosts) optDcJournal := by
  refine ⟨?_, ?_, fun h => absurd (congrArg (sidesAt · optDcFood) h) ?_⟩ <;>
    simp only [sidesAt, grossLedger_sides, txnGrossLedger_sides, coe_postingFlowsF] <;>
    decide +kernel

/-- The four rows of the table on p. 489: the equation zero-account of
    the opening balance sheet and the zero-terms of the three
    transactions, inputs used up, product added and a principal
    payment. Endpoints play no part in gross totals. -/
private inductive Row489 where
  | opening
  | inputsUsed
  | productAdded
  | loanPaid

private def spec489 : GenSpec := ⟨Row489, fun _ => 0, fun _ => 0⟩

private def assets489 : Account := ⟨"Assets", "$"⟩
private def liabilities489 : Account := ⟨"Liabilities", "$"⟩
private def equity489 : Account := ⟨"Equity", "$"⟩

/-- Each row as signed postings, debit-positive: the T-term `[x // 0]`
    is the posting of `x` and the T-term `[0 // y]` that of `-y`. -/
private def posts489 : Row489 → List (Account × ℚ)
  | .opening => [(assets489, 15000), (liabilities489, -10000), (equity489, -5000)]
  | .inputsUsed => [(assets489, -1200), (equity489, 1200)]
  | .productAdded => [(assets489, 1500), (equity489, -1500)]
  | .loanPaid => [(assets489, -800), (liabilities489, 800)]

/-- The three transactions as `journalTerm` builds them: the
    right-nested tensor of their rows, closed by the identity on the
    empty object. -/
private def transactions489 :=
  FreeMor.tensor (S := spec489) (.gen Row489.inputsUsed)
    (.tensor (.gen Row489.productAdded) (.tensor (.gen Row489.loanPaid) (.id 0)))

/-- The journal of the four rows as `journalTerm` builds it, the
    opening row first. -/
private def journal489 :=
  FreeMor.tensor (S := spec489) (.gen Row489.opening) transactions489

/-- A T-account read off at Assets, Liabilities and Equity, in the
    order of the columns of the table on p. 489. -/
private def table489 (x : TAccount Account) : List (ℚ × ℚ) :=
  [assets489, liabilities489, equity489].map (sidesAt x)

/-- **Ellerman's ledger on pp. 489 and 490**: the gross ledger of the
    four rows is the ending equation zero-account, `[16500 // 2000]`,
    `[800 // 10000]` and `[1200 // 6500]` for Assets, Liabilities and
    Equity, and its reduced form `TAccount.reduced` is `[14500 // 0]`,
    `[0 // 9200]` and `[0 // 5300]`; the gross ledger of the three
    transactions alone is the total transaction zero-term,
    `[1500 // 2000]`, `[800 // 0]` and `[1200 // 1500]`. Each row posts
    to each account at most once, so posting by posting and
    transaction by transaction the gross ledgers agree on this table,
    and both are checked. -/
example :
    table489 (grossLedger (S := spec489) posts489 journal489)
        = [(16500, 2000), (800, 10000), (1200, 6500)]
      ∧ table489 (txnGrossLedger (S := spec489) (postingFlowsF posts489) journal489)
        = [(16500, 2000), (800, 10000), (1200, 6500)]
      ∧ table489 (reduced (grossLedger (S := spec489) posts489 journal489))
        = [(14500, 0), (0, 9200), (0, 5300)]
      ∧ table489 (reduced (txnGrossLedger (S := spec489) (postingFlowsF posts489) journal489))
        = [(14500, 0), (0, 9200), (0, 5300)]
      ∧ table489 (grossLedger (S := spec489) posts489 transactions489)
        = [(1500, 2000), (800, 0), (1200, 1500)]
      ∧ table489 (txnGrossLedger (S := spec489) (postingFlowsF posts489) transactions489)
        = [(1500, 2000), (800, 0), (1200, 1500)] := by
  simp only [table489, List.map_cons, List.map_nil, sidesAt, grossLedger_sides,
    txnGrossLedger_sides, coe_postingFlowsF, ← reduce_net_eq_reduced, net_grossLedger,
    net_txnGrossLedger, reduce, Finsupp.mapRange_apply, Finsupp.coe_neg, Pi.neg_apply,
    coe_toNNRat_eq_max, flowAux_postingFlowsF]
  decide +kernel

end GenSpec

end Ledger
