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

end GenSpec

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

end LabeledGenSpec

end Ledger
