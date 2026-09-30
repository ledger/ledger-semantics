import Mathlib.GroupTheory.MonoidLocalization.GrothendieckGroup
import Mathlib.Order.Preorder.Finsupp
import Mathlib.Data.Finsupp.Order
import Mathlib.Data.NNRat.Order
import Ledger.Pacioli

/-!
# T-accounts and Ellerman's Pacioli group, literally

Ellerman, "On Double-Entry Bookkeeping: The Mathematical Treatment",
Accounting Education 23:5 (2014) 483-501. Table 1 (p. 485): a
T-account `[d // c]` is an ordered pair of unsigned quantities; two
T-accounts are equal when their cross-sums are equal; every T-account
has a unique reduced representation `[d - min(d,c) // c - min(d,c)]`.
Page 486: the group so obtained is isomorphic to the signed quantities
in two ways, by the debit isomorphism `[d // c] ↦ d - c` and by the
credit isomorphism `[d // c] ↦ c - d`. Page 494: the inverse of the
debit isomorphism is `x ↦ [x⁺ // x⁻]`. Note 6 permits rationals.

The construction is generic in an index type `ι`, with coefficients
`ι →₀ ℚ≥0`, and the group is Mathlib's `Algebra.GrothendieckAddGroup`
of that monoid. At `ι = Account` the debit isomorphism lands in
`PacioliGroup` (`accountDebitIso`), so the carrier of the denotation
is the signed, single-sided image of this group under the debit
isomorphism. The oracle computes with representations of that
carrier, plain functions into exact rationals, and
`netFlow_eq_flowAux` proves its `netFlow` equal to the denotation
account by account. The debit-positive convention of the oracle's
rows is inherited from the journal syntax and fixed by the output
protocol; under the credit isomorphism every row would be negated.

This is a specification leaf. No module on the oracle's run path
imports it, and nothing in the oracle uses it.
-/

namespace Ledger

/-- Ellerman's T-account `[d // c]` (p. 486): unsigned debit and credit
    totals, indexed by `ι`. -/
abbrev TAccount (ι : Type*) : Type _ := (ι →₀ ℚ≥0) × (ι →₀ ℚ≥0)

namespace TAccount

variable {ι : Type*}

/-! ## Table 1, on pairs -/

/-- Table 1 (p. 485): `[x // y] = [w // z]` if `x + z = y + w`. -/
def CrossEq (x y : TAccount ι) : Prop := x.1 + y.2 = x.2 + y.1

/-- Reversal of a T-account: debit and credit sides exchanged. Table 1
    (p. 485) obtains the additive inverse of a T-account this way. -/
def swap (x : TAccount ι) : TAccount ι := (x.2, x.1)

/-- A T-account is reduced when, in each coordinate, one side is zero. -/
def IsReduced (x : TAccount ι) : Prop := x.1 ⊓ x.2 = 0

/-- Table 1's reduced representation `[x - min(x,y) // y - min(x,y)]`,
    with truncated subtraction on unsigned quantities. -/
noncomputable def reduced (x : TAccount ι) : TAccount ι :=
  (x.1 - x.1 ⊓ x.2, x.2 - x.1 ⊓ x.2)

/-- The inclusion of unsigned quantities into signed ones. -/
noncomputable def unsignedEmbed : (ι →₀ ℚ≥0) →+ (ι →₀ ℚ) :=
  Finsupp.mapRange.addMonoidHom NNRat.coeHom.toAddMonoidHom

@[simp] theorem unsignedEmbed_apply (f : ι →₀ ℚ≥0) (i : ι) :
    unsignedEmbed f i = (f i : ℚ) := by
  simp [unsignedEmbed]

theorem unsignedEmbed_injective : Function.Injective (unsignedEmbed (ι := ι)) := by
  intro f g h
  ext i
  have := DFunLike.congr_fun h i
  simpa using this

/-- Net debit balance of a T-account (p. 486: `[x // y] ↦ x - y`). -/
noncomputable def net : TAccount ι →+ (ι →₀ ℚ) :=
  unsignedEmbed.comp (AddMonoidHom.fst _ _) - unsignedEmbed.comp (AddMonoidHom.snd _ _)

theorem net_apply (x : TAccount ι) : net x = unsignedEmbed x.1 - unsignedEmbed x.2 := rfl

/-- Cross-sum equality is exactly equality of net balances. -/
theorem net_eq_net_iff (x y : TAccount ι) : net x = net y ↔ CrossEq x y := by
  rw [net_apply, net_apply, sub_eq_sub_iff_add_eq_add, ← map_add, ← map_add,
    unsignedEmbed_injective.eq_iff, add_comm y.1]
  rfl

theorem crossEq_equivalence : Equivalence (CrossEq (ι := ι)) where
  refl x := (net_eq_net_iff x x).1 rfl
  symm {x y} h := (net_eq_net_iff y x).1 ((net_eq_net_iff x y).2 h).symm
  trans {x y z} h₁ h₂ :=
    (net_eq_net_iff x z).1 (((net_eq_net_iff x y).2 h₁).trans ((net_eq_net_iff y z).2 h₂))

theorem net_swap (x : TAccount ι) : net (swap x) = -net x := by
  rw [net_apply, net_apply, neg_sub]
  rfl

/-- Jordan decomposition of a signed vector into a reduced T-account:
    `v ↦ [v⁺ // v⁻]`. -/
noncomputable def reduce (v : ι →₀ ℚ) : TAccount ι :=
  (v.mapRange Rat.toNNRat Rat.toNNRat_zero, (-v).mapRange Rat.toNNRat Rat.toNNRat_zero)

theorem coe_toNNRat_eq_max (q : ℚ) : (q.toNNRat : ℚ) = max q 0 := rfl

theorem net_reduce (v : ι →₀ ℚ) : net (reduce v) = v := by
  ext i
  simp only [net_apply, reduce, Finsupp.coe_sub, Pi.sub_apply, unsignedEmbed_apply,
    Finsupp.mapRange_apply, Finsupp.coe_neg, Pi.neg_apply, coe_toNNRat_eq_max]
  exact max_zero_sub_eq_self (v i)

theorem reduce_isReduced (v : ι →₀ ℚ) : IsReduced (reduce v) := by
  refine Finsupp.ext fun i => ?_
  simp only [reduce, Finsupp.inf_apply, Finsupp.mapRange_apply, Finsupp.coe_neg,
    Pi.neg_apply, Finsupp.coe_zero, Pi.zero_apply]
  rcases le_total (v i) 0 with h | h
  · rw [Rat.toNNRat_eq_zero.2 h]
    exact inf_eq_left.2 (by simp)
  · rw [Rat.toNNRat_eq_zero.2 (neg_nonpos.2 h)]
    exact inf_eq_right.2 (by simp)

/-- On a reduced T-account, one side of each coordinate is zero. -/
theorem IsReduced.eq_zero_or_eq_zero {x : TAccount ι} (hx : IsReduced x) (i : ι) :
    x.1 i = 0 ∨ x.2 i = 0 := by
  have hi : x.1 i ⊓ x.2 i = 0 := by
    simpa using DFunLike.congr_fun hx i
  rcases le_total (x.1 i) (x.2 i) with h | h
  · left; rwa [inf_eq_left.2 h] at hi
  · right; rwa [inf_eq_right.2 h] at hi

theorem reduce_net {x : TAccount ι} (hx : IsReduced x) : reduce (net x) = x := by
  refine Prod.ext ?_ ?_ <;> refine Finsupp.ext fun i => ?_ <;>
    simp only [reduce, Finsupp.mapRange_apply, net_apply, Finsupp.coe_neg, Pi.neg_apply,
      Finsupp.coe_sub, Pi.sub_apply, unsignedEmbed_apply] <;>
    rcases hx.eq_zero_or_eq_zero i with h | h <;> simp [h]

/-- Table 1: the reduced representation is unique. -/
theorem reduced_unique {x y : TAccount ι} (hx : IsReduced x) (hy : IsReduced y)
    (h : CrossEq x y) : x = y := by
  rw [← reduce_net hx, ← reduce_net hy, (net_eq_net_iff x y).2 h]

/-- Table 1's formula `[x - min(x,y) // y - min(x,y)]` is the Jordan
    decomposition of the net balance. -/
theorem reduce_net_eq_reduced (x : TAccount ι) : reduce (net x) = reduced x := by
  refine Prod.ext ?_ ?_ <;> refine Finsupp.ext fun i => ?_ <;>
    simp only [reduce, reduced, Finsupp.mapRange_apply, net_apply, Finsupp.coe_sub,
      Pi.sub_apply, unsignedEmbed_apply, Finsupp.tsub_apply, Finsupp.inf_apply, neg_sub]
  · rcases le_total (x.1 i) (x.2 i) with h | h
    · rw [inf_eq_left.2 h, tsub_self, Rat.toNNRat_eq_zero, sub_nonpos]
      exact_mod_cast h
    · rw [inf_eq_right.2 h, NNRat.sub_def]
  · rcases le_total (x.1 i) (x.2 i) with h | h
    · rw [inf_eq_left.2 h, NNRat.sub_def]
    · rw [inf_eq_right.2 h, tsub_self, Rat.toNNRat_eq_zero, sub_nonpos]
      exact_mod_cast h

theorem reduced_isReduced (x : TAccount ι) : IsReduced (reduced x) := by
  rw [← reduce_net_eq_reduced]; exact reduce_isReduced _

theorem reduced_crossEq (x : TAccount ι) : CrossEq (reduced x) x := by
  rw [← net_eq_net_iff, ← reduce_net_eq_reduced, net_reduce]

/-! ## The Pacioli group as Mathlib's Grothendieck group -/

/-- Ellerman's Pacioli group `P(M)` for `M = ι →₀ ℚ≥0`: Mathlib's
    Grothendieck group of the unsigned quantities. -/
abbrev PacioliP (ι : Type*) : Type _ := Algebra.GrothendieckAddGroup (ι →₀ ℚ≥0)

/-- The class `[d // c]` of a T-account in `P(M)`. -/
noncomputable def toP (x : TAccount ι) : PacioliP ι :=
  AddLocalization.mk x.1 ⟨x.2, AddSubmonoid.mem_top x.2⟩

/-- Table 1, literally: two T-accounts denote the same element of the
    Pacioli group exactly when their cross-sums are equal. -/
theorem toP_eq_toP_iff (x y : TAccount ι) : toP x = toP y ↔ CrossEq x y := by
  rw [toP, toP, AddLocalization.mk_eq_mk_iff', CrossEq, add_comm]

theorem toP_surjective : Function.Surjective (toP (ι := ι)) := by
  intro a
  induction a using AddLocalization.induction_on with
  | H y => exact ⟨(y.1, y.2), rfl⟩

/-- Table 1 (p. 485): T-accounts add by adding debits to debits and
    credits to credits, `[x // y] + [w // z] = [x + w // y + z]`. -/
theorem toP_add (x y : TAccount ι) : toP (x + y) = toP x + toP y := by
  rw [toP, toP, toP, AddLocalization.mk_add]
  rfl

/-- Table 1 (p. 485): the additive inverse of a T-account reverses its
    debit and credit entries, `-[x // y] = [y // x]`. -/
theorem toP_swap (x : TAccount ι) : toP (swap x) = -toP x := by
  rw [toP, toP, Algebra.GrothendieckAddGroup.neg_mk]
  rfl

/-- The debit homomorphism: the Grothendieck lift of the inclusion. -/
noncomputable def debit : PacioliP ι →+ (ι →₀ ℚ) :=
  Algebra.GrothendieckAddGroup.lift unsignedEmbed

theorem debit_of (m : ι →₀ ℚ≥0) :
    debit (Algebra.GrothendieckAddGroup.of m) = unsignedEmbed m := by
  have h := Algebra.GrothendieckAddGroup.lift.symm_apply_apply (unsignedEmbed (ι := ι))
  rw [Algebra.GrothendieckAddGroup.lift_symm_apply] at h
  exact DFunLike.congr_fun h m

theorem of_eq_toP (m : ι →₀ ℚ≥0) : Algebra.GrothendieckAddGroup.of m = toP (m, 0) := rfl

theorem toP_eq_of_sub_of (x : TAccount ι) :
    toP x = Algebra.GrothendieckAddGroup.of x.1 - Algebra.GrothendieckAddGroup.of x.2 := by
  have hx : x = (x.1, 0) + swap (x.2, 0) := by
    simp [swap]
  rw [of_eq_toP, of_eq_toP, sub_eq_add_neg, ← toP_swap, ← toP_add, ← hx]

theorem debit_toP (x : TAccount ι) : debit (toP x) = net x := by
  rw [toP_eq_of_sub_of, map_sub, debit_of, debit_of, net_apply]

theorem debit_injective : Function.Injective (debit (ι := ι)) := by
  intro a b h
  obtain ⟨x, rfl⟩ := toP_surjective a
  obtain ⟨y, rfl⟩ := toP_surjective b
  rw [debit_toP, debit_toP, net_eq_net_iff] at h
  exact (toP_eq_toP_iff x y).2 h

theorem debit_surjective : Function.Surjective (debit (ι := ι)) :=
  fun v => ⟨toP (reduce v), by rw [debit_toP, net_reduce]⟩

theorem debit_bijective : Function.Bijective (debit (ι := ι)) :=
  ⟨debit_injective, debit_surjective⟩

/-- Ellerman's debit isomorphism (p. 486 direction: `[d // c] ↦ d - c`). -/
noncomputable def debitIso : PacioliP ι ≃+ (ι →₀ ℚ) :=
  AddEquiv.ofBijective debit debit_bijective

/-- Ellerman's credit isomorphism (`[d // c] ↦ c - d`). -/
noncomputable def creditIso : PacioliP ι ≃+ (ι →₀ ℚ) :=
  debitIso.trans (AddEquiv.neg _)

@[simp] theorem debitIso_toP (x : TAccount ι) : debitIso (toP x) = net x :=
  debit_toP x

@[simp] theorem creditIso_toP (x : TAccount ι) : creditIso (toP x) = net (swap x) := by
  simp [creditIso, net_swap]

theorem debitIso_of (m : ι →₀ ℚ≥0) :
    debitIso (Algebra.GrothendieckAddGroup.of m) = unsignedEmbed m :=
  debit_of m

/-- The p. 494 presentation of the debit isomorphism: `x ↦ [x⁺ // x⁻]`. -/
theorem debitIso_symm_apply (v : ι →₀ ℚ) : debitIso.symm v = toP (reduce v) := by
  rw [AddEquiv.symm_apply_eq, debitIso_toP, net_reduce]

/-- The p. 494 presentation of the credit isomorphism: `x ↦ [x⁻ // x⁺]`. -/
theorem creditIso_symm_apply (v : ι →₀ ℚ) : creditIso.symm v = toP (swap (reduce v)) := by
  rw [AddEquiv.symm_apply_eq, creditIso_toP, net_swap, net_swap, neg_neg, net_reduce]

/-- The two isomorphisms differ by the sign: debit and credit are the
    two orientations of one group. -/
theorem creditIso_apply (a : PacioliP ι) : creditIso a = -debitIso a := rfl

/-- "Beginning Ledger + Journal = Ending Ledger" (p. 496), read through
    the debit isomorphism. The statement is the additivity of that
    isomorphism, which carries the T-account update of p. 496 onto the
    update of p. 492, "Initial ledger + journal = ending ledger using
    single-sided accounts and signed numbers". -/
theorem debitIso_beginning_add_journal (b j : PacioliP ι) :
    debitIso (b + j) = debitIso b + debitIso j := map_add _ _ _

/-- The universal property: every additive readout of unsigned quantities
    into a commutative group extends uniquely to the Pacioli group. -/
theorem existsUnique_extension {G : Type*} [AddCommGroup G] (φ : (ι →₀ ℚ≥0) →+ G) :
    ∃! ψ : PacioliP ι →+ G, ψ.comp Algebra.GrothendieckAddGroup.of = φ := by
  refine ⟨Algebra.GrothendieckAddGroup.lift φ, ?_, fun ψ hψ => ?_⟩
  · have h := Algebra.GrothendieckAddGroup.lift.symm_apply_apply φ
    rwa [Algebra.GrothendieckAddGroup.lift_symm_apply] at h
  · rw [← hψ, ← Algebra.GrothendieckAddGroup.lift_symm_apply,
      Equiv.apply_symm_apply]

/-- At `ι = Account`, the debit isomorphism lands in `PacioliGroup` by
    definition: the signed carrier is the debit image of the Pacioli group. -/
noncomputable def accountDebitIso : PacioliP Account ≃+ PacioliGroup := debitIso

end TAccount
end Ledger

