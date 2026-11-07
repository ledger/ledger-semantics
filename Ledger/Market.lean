import Ledger.Oracle
import Ledger.PriceVector

/-!
# The oracle's valuation agrees with the price-vector valuation

Ellerman values property at a price vector (p. 498): "Multiplying the
physical quantities by their price and adding up ... yields the value
of the property vectors". `Ledger/PriceVector.lean` states that
valuation on the carrier `PacioliGroup` as `priceDot`, the scalar
product of a price vector with the ledger-wide property vector, and as
`valueHom`, the value of one account name's property vector. Both are
noncomputable. `Ledger/Oracle.lean` computes the same values with
plain functions and exact rationals: `netValue` sums, over a list of
accounts, each account's net flow `netFlow` times the price of its
commodity, and `netValueAt` does the same over the accounts of the
list that bear one name.

`netValue_eq_priceDot` proves that `netValue` is `priceDot` of the
flow denotation `flow` of the term's class in `FreeHom`, and
`netValueAt_eq_valueHom` proves that `netValueAt` is `valueHom` of the
same flow. Both assume that the list of accounts has no duplicates and
holds every account at which the term's flow is nonzero, since a list
sum counts an account once for each time it is listed and never counts
an account that is not listed. Both pass through `netFlow_eq_flowAux`,
the agreement of `netFlow` with the L1 denotation, account by account,
and take the flows of the generators as vectors of `PacioliGroup` read
pointwise, the form in which that theorem states them; the
per-generator flows `flowsFor` of `Driver` have that form by
`coe_flowsFin` in `Ledger/DriverTwoSides.lean`.

This is a join module: it imports the executable module `Oracle` and
the specification leaf `PriceVector` only to state these proofs, and
it holds only them and one list lemma that they use. No module on the
oracle's run path, which is the import closure of `Driver`, imports
it. The proofs sit here rather than in `Oracle.lean` so that the run
path does not load `Ledger/PriceVector.lean`, the modules
`Ledger/TimedPrices.lean` and `Ledger/Derived.lean` that it brings in,
or the Mathlib module of `Finsupp.linearCombination`.
-/

namespace Ledger

namespace GenSpec

variable {S : GenSpec}

/-- **The oracle's value is the price-vector value.** Over a list of
    accounts without duplicates that holds every account at which the
    term's flow is nonzero, `netValue` at prices `p` is the scalar
    product `priceDot p` of the flow of the term's class. -/
theorem netValue_eq_priceDot (flowsF : S.Gen → PacioliGroup)
    (accts : List Account) (hnd : accts.Nodup) (p : Commodity → ℚ)
    {A B : Object} (f : S.FreeMor A B)
    (hsupp : (flowAux flowsF f).support ⊆ accts.toFinset) :
    netValue (fun t => (flowsF t : Account → ℚ)) accts p f
      = priceDot p (flow flowsF (⟦f⟧ : FreeHom S A B)) := by
  rw [priceDot_apply, flow_mk, netValue]
  simp only [netFlow_eq_flowAux]
  rw [Finsupp.sum_of_support_subset _ hsupp _ (fun a _ => by simp), List.sum_toFinset _ hnd]

/-- Summing over the elements of a list that satisfy a predicate is
    summing over the whole list a function that is zero where the
    predicate fails: Mathlib's `List.sum_map_ite` with the second
    function zero. -/
private theorem sum_filter_map_ite {α : Type} (l : List α) (P : α → Prop) [DecidablePred P]
    (g : α → ℚ) :
    ((l.filter fun x => decide (P x)).map g).sum
      = (l.map fun x => if P x then g x else 0).sum := by
  rw [List.sum_map_ite]
  simp

/-- **The oracle's value at one account name is the per-account
    value.** Over a list of accounts without duplicates that holds
    every account at which the term's flow is nonzero, `netValueAt` at
    prices `p` and account name `n` is `valueHom p n` of the flow of
    the term's class. -/
theorem netValueAt_eq_valueHom (flowsF : S.Gen → PacioliGroup)
    (accts : List Account) (hnd : accts.Nodup) (p : Commodity → ℚ) (n : AccountName)
    {A B : Object} (f : S.FreeMor A B)
    (hsupp : (flowAux flowsF f).support ⊆ accts.toFinset) :
    netValueAt (fun t => (flowsF t : Account → ℚ)) accts p n f
      = valueHom p n (flow flowsF (⟦f⟧ : FreeHom S A B)) := by
  rw [valueHom_apply, flow_mk, netValueAt, netValue]
  simp only [netFlow_eq_flowAux]
  rw [Finsupp.sum_of_support_subset _ hsupp _ (fun a _ => by simp), List.sum_toFinset _ hnd,
    sum_filter_map_ite]

end GenSpec

end Ledger
