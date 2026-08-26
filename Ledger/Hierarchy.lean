import Ledger.Groupoid

/-!
# Account hierarchy: forest with roll-up morphisms

The account hierarchy is a **forest** — a disjoint union of rooted
trees where each account has at most one parent (decision D6, source
evidence `src/account.h:101`). `Cash:Checking` is-a `Cash` is-an
`Asset`; the colon-separated name encodes a unique path from a root;
aliases create alternative names, not alternative parents.

## Roll-up morphisms

For each parent edge `parent a = some b` there is a roll-up morphism
`{a} → {b}` in 𝕋 — a transaction moving the balance of the child into
the parent. Chains of edges (`ParentChain`) compose to roll-ups along
ancestor paths (`rollupChain`), and single-edge roll-ups extend to
multisets via the monoidal structure.

Phase 1's `rollup_refl` field (`∃ h : parent a = none, True`) was
vacuous placeholder text and is deleted; path functoriality is now
*defined* (`rollupChain` composes by construction) rather than
asserted. The theorem that roll-ups preserve valuation — the fact that
makes reports-as-colimits well-defined — is proved in
`Theorems.lean` (`rollup_preserves_valuation`,
`rollup_chain_preserves_valuation`).
-/

namespace Ledger

/-- An account forest: each account has at most one parent, and the
    parent relation is well-founded (no cycles). Equivalently, a
    disjoint union of rooted trees. -/
structure AccountForest where
  /-- The type of account identifiers. -/
  Account : Type
  /-- `some p` — this account's parent is `p`; `none` — a root. -/
  parent : Account → Option Account
  /-- Following `parent` upward terminates: an account is accessible
      once its parent is. Excludes cycles *and* rootless infinite
      ascent, and is exactly what makes `rootOf` definable by
      well-founded recursion.

      (Phase 4 finding: Phase 1 stated well-foundedness of the
      *converse* relation — accessibility from children — which also
      excludes cycles but permits an account whose parent chain never
      reaches a root, and supports no recursion toward roots.) -/
  wellFounded : WellFounded (fun b a => parent a = some b)

namespace AccountForest

/-- `le F a b` — `b` is an ancestor of `a` (reflexive-transitive
    closure of the parent relation). -/
inductive le (F : AccountForest) : F.Account → F.Account → Prop where
  | refl (a : F.Account) : le F a a
  | step {a b c : F.Account} :
      F.parent a = some b → le F b c → le F a c

/-- A root account has no parent. -/
def isRoot (F : AccountForest) (a : F.Account) : Prop :=
  F.parent a = none

/-- The root above an account: follow `parent` until it runs out.
    Well-founded recursion on the (corrected) `wellFounded` field. -/
def rootOf (F : AccountForest) : F.Account → F.Account :=
  F.wellFounded.fix fun a ih =>
    match h : F.parent a with
    | some b => ih b h
    | none => a

theorem rootOf_parent_none {F : AccountForest} {a : F.Account}
    (h : F.parent a = none) : F.rootOf a = a := by
  unfold rootOf
  rw [WellFounded.fix_eq]
  split
  · next heq => rw [h] at heq; exact absurd heq (by simp)
  · rfl

theorem rootOf_parent_some {F : AccountForest} {a b : F.Account}
    (h : F.parent a = some b) : F.rootOf a = F.rootOf b := by
  unfold rootOf
  rw [WellFounded.fix_eq]
  split
  · next b' heq =>
      rw [h] at heq
      injection heq with hb
      rw [hb]
  · next heq => rw [h] at heq; exact absurd heq (by simp)

/-- Every account's root is a root. -/
theorem rootOf_isRoot (F : AccountForest) (a : F.Account) :
    F.isRoot (F.rootOf a) := by
  induction a using F.wellFounded.induction with
  | _ a ih =>
    cases h : F.parent a with
    | none => rw [rootOf_parent_none h]; exact h
    | some b => rw [rootOf_parent_some h]; exact ih b h

/-- A root is its own root. -/
theorem rootOf_of_isRoot {F : AccountForest} {a : F.Account}
    (h : F.isRoot a) : F.rootOf a = a :=
  rootOf_parent_none h

/-- A concrete chain of parent edges from `a` up to `c`. The
    `Type`-level companion of `le` (which is a `Prop`), so that
    roll-up morphisms can be built by recursion over it. -/
inductive ParentChain (F : AccountForest) : F.Account → F.Account → Type where
  | refl (a : F.Account) : ParentChain F a a
  | step {a b c : F.Account} :
      F.parent a = some b → ParentChain F b c → ParentChain F a c

/-- Every chain witnesses ancestry. -/
theorem ParentChain.to_le {F : AccountForest} :
    ∀ {a c : F.Account}, ParentChain F a c → le F a c
  | _, _, .refl a => le.refl a
  | _, _, .step h rest => le.step h rest.to_le

end AccountForest

/-- Roll-up data: an embedding of forest accounts as singleton objects
    of 𝕋, and a roll-up morphism for each parent edge. -/
structure RollupFunctor (F : AccountForest) (T : 𝕋) where
  /-- Map each forest account to an object of 𝕋. -/
  embed : F.Account → Object
  /-- For each parent edge `a → b`, a morphism moving the balance of
      the child into the parent. -/
  rollup : (a b : F.Account) → F.parent a = some b →
    T.Hom (embed a) (embed b)

namespace RollupFunctor

variable {F : AccountForest} {T : 𝕋} (R : RollupFunctor F T)

/-- Roll up along a whole ancestor chain, by composition. Path
    functoriality holds *by definition*: the chain `step h rest`
    rolls up the edge, then the rest. -/
def rollupChain : {a c : F.Account} → F.ParentChain a c →
    T.Hom (R.embed a) (R.embed c)
  | _, _, .refl a => T.id (R.embed a)
  | _, _, .step h rest => T.comp (rollupChain rest) (R.rollup _ _ h)

@[simp] theorem rollupChain_refl (a : F.Account) :
    R.rollupChain (.refl a) = T.id (R.embed a) := by
  simp [rollupChain]

@[simp] theorem rollupChain_step {a b c : F.Account}
    (h : F.parent a = some b) (rest : F.ParentChain b c) :
    R.rollupChain (.step h rest)
      = T.comp (R.rollupChain rest) (R.rollup a b h) := by
  simp [rollupChain]

end RollupFunctor

end Ledger
