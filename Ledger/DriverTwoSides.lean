import Ledger.Driver
import Ledger.TwoSides

/-!
# The oracle's generators are coherent with their ends

`Driver.specFor` gives each generator the accounts of its negative
postings as its domain and the accounts of its positive postings as
its codomain: its credited and its debited accounts. This module
proves that the construction is coherent in the sense of
`TwoSides.lean` (`specFor_coherent`), and transfers the facts of that
module to the oracle's generators through `flowsFin_apply` and to its
journal term through `netFlow_eq_flowAux`.

The module holds only proofs and the two definitions they need. It
sits above `Driver.lean` so that neither `Oracle.lean` nor
`Driver.lean` imports `TwoSides.lean`, which would otherwise enter
the closure that the interpreted oracle loads and bring with it a
Mathlib import that the closure does not yet contain.

The theorems about balance (`flowsFin_two_ends`,
`flowsFor_eq_zero_of_dom_eq_zero`) concern generators whose flow is a
zero-row, and the oracle routinely emits others. Among them, a priced
trade is balanced on weights but records its own amounts, a
paren-virtual posting is exempt from balancing, and a timeclock entry
is added without a balance check (see the module docstring of
`Journal.lean`). By `flowsFor_eq_zero_of_dom_eq_zero`, a generator
with an empty domain has a nonzero flow exactly when that flow is not
a zero-row, which is Ellerman's `[x // 0]` with `x ≠ 0`.
-/

namespace Ledger

namespace Driver

open GenSpec

theorem foldl_add_snd (l : List (Account × ℚ)) (s : ℚ) :
    l.foldl (fun s p => s + p.2) s = s + (l.map Prod.snd).sum := by
  induction l generalizing s with
  | nil => simp
  | cons p l ih => simp [List.foldl, ih, add_assoc]

/-- The mirror of Mathlib's `List.sum_nonneg`, which has no nonpositive
    counterpart of its own at this pin; it is `List.sum_le_card_nsmul`
    at zero. -/
theorem list_sum_nonpos (l : List ℚ) (h : ∀ x ∈ l, x ≤ 0) : l.sum ≤ 0 := by
  simpa using List.sum_le_card_nsmul l 0 h

/-- `specFor_coherent` at one generator and one account. -/
theorem specFor_coherent_at (arr : Array (List (Account × ℚ)))
    (i : Fin arr.size) (a : Account) :
    (0 < flowsFor arr i a → a ∈ (specFor arr).cod i) ∧
    (flowsFor arr i a < 0 → a ∈ (specFor arr).dom i) := by
  simp only [flowsFor, foldl_add_snd, zero_add]
  constructor
  · intro h
    obtain ⟨q, hq, hpos⟩ :
        ∃ q ∈ ((arr[i]).filter fun p => p.1 = a).map Prod.snd, 0 < q := by
      by_contra hno
      exact absurd h (not_lt.mpr (list_sum_nonpos _ fun x hx =>
        not_lt.mp fun h' => hno ⟨x, hx, h'⟩))
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
    obtain ⟨hmem, hpa⟩ := List.mem_filter.mp hp
    have hpa : p.1 = a := by simpa using hpa
    show a ∈ (((arr[i]).filter fun p => p.2 > 0).map Prod.fst : Multiset Account)
    rw [Multiset.mem_coe]
    exact List.mem_map.mpr ⟨p, List.mem_filter.mpr ⟨hmem, by simpa using hpos⟩, hpa⟩
  · intro h
    obtain ⟨q, hq, hneg⟩ :
        ∃ q ∈ ((arr[i]).filter fun p => p.1 = a).map Prod.snd, q < 0 := by
      by_contra hno
      exact absurd h (not_lt.mpr (List.sum_nonneg fun x hx =>
        not_lt.mp fun h' => hno ⟨x, hx, h'⟩))
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
    obtain ⟨hmem, hpa⟩ := List.mem_filter.mp hp
    have hpa : p.1 = a := by simpa using hpa
    show a ∈ (((arr[i]).filter fun p => p.2 < 0).map Prod.fst : Multiset Account)
    rw [Multiset.mem_coe]
    exact List.mem_map.mpr ⟨p, List.mem_filter.mpr ⟨hmem, by simpa using hneg⟩, hpa⟩

/-- **The oracle's endpoints are coherent**: `specFor` puts every
    account whose net flow in a generator is positive in that
    generator's codomain, and every account whose net flow is negative
    in its domain. -/
theorem specFor_coherent (arr : Array (List (Account × ℚ))) :
    (specFor arr).SignCoherent (flowsFor arr) :=
  fun i a => specFor_coherent_at arr i a

/-- A posting list as a Pacioli vector. -/
noncomputable def postingsFlow (l : List (Account × ℚ)) : PacioliGroup :=
  (l.map fun p => Finsupp.single p.1 p.2).sum

theorem postingsFlow_apply (l : List (Account × ℚ)) (a : Account) :
    postingsFlow l a = ((l.filter fun p => p.1 = a).map Prod.snd).sum := by
  induction l with
  | nil => simp [postingsFlow]
  | cons p l ih =>
    simp only [postingsFlow, List.map_cons, List.sum_cons, Finsupp.add_apply] at ih ⊢
    rw [ih, List.filter_cons]
    by_cases h : p.1 = a
    · simp [h]
    · simp [h]

/-- The `PacioliGroup` form of `flowsFor`, for transfer through
    `netFlow_eq_flowAux`. -/
noncomputable def flowsFin (arr : Array (List (Account × ℚ))) (i : Fin arr.size) :
    PacioliGroup :=
  postingsFlow arr[i]

theorem flowsFin_apply (arr : Array (List (Account × ℚ))) (i : Fin arr.size)
    (a : Account) : flowsFin arr i a = flowsFor arr i a := by
  simp only [flowsFin, postingsFlow_apply, flowsFor, foldl_add_snd, zero_add]

theorem coe_flowsFin (arr : Array (List (Account × ℚ))) :
    (fun i => ⇑(flowsFin arr i)) = flowsFor arr := by
  funext i a
  exact flowsFin_apply arr i a

theorem specFor_coherent_fin (arr : Array (List (Account × ℚ))) :
    (specFor arr).SignCoherent (fun i => flowsFin arr i) := by
  intro i a
  simp only [flowsFin_apply]
  exact specFor_coherent_at arr i a

/-- The journal term is a tensor of generators, hence composition-free. -/
theorem journalTerm_compFree (S : GenSpec) :
    ∀ ts : List S.Gen, (journalTerm S ts).2.2.CompFree
  | [] => trivial
  | t :: rest => by
      have ih := journalTerm_compFree S rest
      rcases h : journalTerm S rest with ⟨A, B, f⟩
      rw [h] at ih
      rw [journalTerm, h]
      exact ⟨trivial, ih⟩

/-- **The oracle's journal term is coherent with its ends**: the flow
    that `netFlow` computes for the tensor of the generators credits
    only accounts in the total domain and debits only accounts in the
    total codomain. -/
theorem journalTerm_coherent (arr : Array (List (Account × ℚ)))
    (ts : List (Fin arr.size)) :
    EndsCoherent (journalTerm (specFor arr) ts).1 (journalTerm (specFor arr) ts).2.1
      (netFlow (flowsFor arr) (journalTerm (specFor arr) ts).2.2) := by
  have h := endsCoherent_flowAux (specFor_coherent_fin arr)
    (journalTerm (specFor arr) ts).2.2 (journalTerm_compFree (specFor arr) ts)
  have e : ∀ a, netFlow (flowsFor arr) (journalTerm (specFor arr) ts).2.2 a
      = flowAux (flowsFin arr) (journalTerm (specFor arr) ts).2.2 a := fun a => by
    rw [← coe_flowsFin]
    exact netFlow_eq_flowAux (S := specFor arr) (flowsFin arr) _ a
  intro a
  rw [e]
  exact h a

/-- **Equal debits and credits on the two ends of an oracle
    generator**: for a generator whose flow is a zero-row, in each
    commodity the debits over its codomain equal the credits over its
    domain. -/
theorem flowsFin_two_ends (arr : Array (List (Account × ℚ))) (i : Fin arr.size)
    (hbal : flowsFin arr i ∈ zeroRows) (c : Commodity) :
    ∑ a ∈ ((specFor arr).cod i).toFinset with a.commodity = c, (flowsFin arr i a)⁺
      = ∑ a ∈ ((specFor arr).dom i).toFinset with a.commodity = c,
          (flowsFin arr i a)⁻ :=
  two_ends (specFor_coherent_fin arr i) hbal c

/-- An oracle generator with an empty domain whose flow is a zero-row
    moves nothing. -/
theorem flowsFor_eq_zero_of_dom_eq_zero (arr : Array (List (Account × ℚ)))
    (i : Fin arr.size) (hdom : (specFor arr).dom i = 0)
    (hbal : flowsFin arr i ∈ zeroRows) (a : Account) : flowsFor arr i a = 0 := by
  have hz := eq_zero_of_endsCoherent_dom_eq_zero hdom (specFor_coherent_fin arr i) hbal
  rw [← flowsFin_apply, hz]
  rfl

end Driver

end Ledger
