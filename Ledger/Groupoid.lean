import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Ledger.Accounts

/-!
# The free symmetric monoidal groupoid 𝕋

The core mathematical object. `𝕋` is the free symmetric monoidal
groupoid enriched over commutative monoids, and this file says so in
the standard vocabulary: for every lawful model `L : 𝕋Laws T`, the
tagged object type `L.Obj` carries genuine Mathlib instances of
`Category`, `Groupoid`, `MonoidalCategory`, `SymmetricCategory`, and
a per-hom-set `AddCommMonoid` (see the bridge section at the end).
The fields of `𝕋` and `𝕋Laws` are exactly the data and obligations a
model must supply to earn those instances; all monoidal coherence
(pentagon, triangle, hexagons, naturality) is then inherited from
Mathlib rather than restated here. The one standard structure that
is deliberately ABSENT is `Preadditive`-style compatibility between
hom-addition and composition: decision D16 proves that those laws
degenerate every valuation to zero, so `𝕋` is a symmetric monoidal
groupoid whose hom-sets carry commutative-monoid structure that
interacts only with valuations.

- **Objects**: `Object` — the free commutative monoid `Multiset Account`
  (concrete; see `Accounts.lean`). Tensor on objects is `+`, the unit
  is `0`, and the monoidal structure is **strict**: associativity,
  commutativity, and unit hold as object equalities.
- **Morphisms**: an abstract family `Hom : Object → Object → Type`,
  closed under composition, inverse, tensor, and hom-set addition.
  No computational representation is given here; `Ledger.Free` and
  `Ledger.Pacioli` supply representations (free construction, Pacioli
  skeleton) that satisfy these axioms.

## What is structure and what is derived

Structure (`𝕋` fields): `Hom`, per-hom-set `AddCommMonoid` (the CMon
enrichment — Mathlib's class, so `f + g` and `0` notation and all
commutative-monoid laws come for free), `id`, `comp`, `inv`, `tensor`.

Derived (definitions below, laws proved from `𝕋Laws`):

- `castHom` — transport of a morphism along object equalities. Free
  from `Eq`; every strict-monoidal coherence morphism is one of these.
- `braiding` — the symmetry `σ : A⊗B → B⊗A` is `castHom` of the
  identity along `add_comm A B`. It is **not** structure (decision D9):
  since objects are multisets, `A + B = B + A` already holds, and no
  observation of the design (valuation, labels, reports) distinguishes
  the permutation morphism from the identity. Its laws (`braid_invol`,
  balance) are theorems, proved from nothing.
- `inv_id`, `inv_inv` — groupoid consequences.
- `Path` and `Path.compose` — formal composition chains, used to state
  independence of composition order (`Theorems.lean`).

## Freeness

`𝕋Laws` axiomatizes *equations*; it cannot say the groupoid has *no
more* equations (freeness proper arrives with the concrete free
construction at L2, Phase 5+). What the theorems of Phase 3 actually
need is weaker and is captured by `Generated`: every morphism is
reachable from the atomic generators by the six operations. This is an
induction principle — the formal content of "a journal is a finite
text: every flow it denotes is built from its entries."
-/

namespace Ledger

/-- The free symmetric monoidal groupoid enriched over CMon — the
    **specification** every representation must implement. `Hom` is
    abstract; only its properties (via `𝕋Laws`) are specified.

    The CMon enrichment is Mathlib's `AddCommMonoid` on each hom-set:
    `f + g` aggregates two transactions of the same shape, `0` is the
    empty (balanced, moves-nothing) transaction. -/
structure 𝕋 where
  /-- Morphisms (transactions) — an abstract family of types. -/
  Hom : Object → Object → Type
  /-- CMon enrichment: each hom-set is a commutative monoid. -/
  homAddCommMonoid : ∀ A B : Object, AddCommMonoid (Hom A B)
  /-- Identity morphism: doing nothing on an account multiset. -/
  id : (A : Object) → Hom A A
  /-- Sequential composition: `comp g f` chains `f` then `g` through an
      intermediate account multiset. -/
  comp : {A B C : Object} → Hom B C → Hom A B → Hom A C
  /-- Inverse: reverse a transaction. Always defined (groupoid). -/
  inv : {A B : Object} → Hom A B → Hom B A
  /-- Parallel composition: two independent transactions at once. -/
  tensor : {A B C D : Object} → Hom A B → Hom C D → Hom (A + C) (B + D)

attribute [instance] 𝕋.homAddCommMonoid

namespace 𝕋

variable {T : 𝕋}

/-- Transport a morphism along equalities of its endpoints. In the
    strict monoidal setting every coherence morphism (associator,
    unitor, braiding) is `castHom` of an identity. -/
def castHom (T : 𝕋) : {A A' B B' : Object} → A = A' → B = B' →
    T.Hom A B → T.Hom A' B'
  | _, _, _, _, rfl, rfl, f => f

@[simp] theorem castHom_rfl {A B : Object} (f : T.Hom A B) :
    T.castHom rfl rfl f = f := rfl

/-- To prove two morphisms across an object equality heterogeneously
    equal, transport one and prove plain equality. -/
theorem heq_of_castHom_eq {T : 𝕋} {A A' B B' : Object}
    (hA : A = A') (hB : B = B') {x : T.Hom A B} {y : T.Hom A' B'}
    (h : T.castHom hA hB x = y) : HEq x y := by
  subst hA; subst hB; exact heq_of_eq h

/-- The symmetry (braiding) `σ_{A,B} : A ⊗ B → B ⊗ A`, derived as
    transport of the identity along commutativity of the object
    monoid. Decision D9: on multiset objects the permutation morphism
    is semantically the identity, so it is not structure. -/
def braiding (T : 𝕋) (A B : Object) : T.Hom (A + B) (B + A) :=
  T.castHom rfl (add_comm A B) (T.id (A + B))

/-- Formal composition chains `A → ⋯ → B`, used to state theorems
    about *how a composite was assembled* (e.g. independence of
    composition order). Not a representation of `Hom` — the morphisms
    in a chain are still abstract. -/
inductive Path (T : 𝕋) : Object → Object → Type where
  | nil (A : Object) : Path T A A
  | cons {A B C : Object} (g : T.Hom B C) (rest : Path T A B) : Path T A C

/-- Compose a chain into a single morphism. -/
def Path.compose : {A B : Object} → Path T A B → T.Hom A B
  | _, _, .nil A => T.id A
  | _, _, .cons g rest => T.comp g (compose rest)

@[simp] theorem Path.compose_nil (A : Object) :
    (Path.nil (T := T) A).compose = T.id A := by
  simp [Path.compose]

@[simp] theorem Path.compose_cons {A B C : Object}
    (g : T.Hom B C) (rest : T.Path A B) :
    (Path.cons g rest).compose = T.comp g rest.compose := by
  simp [Path.compose]

/-- **Generatedness**: every morphism of `T` is reachable from a class
    `IsGen` of atomic generators (the journal's entries) by identity,
    zero, composition, inverse, tensor, and addition — stated as an
    induction principle over the abstract `Hom`.

    This is the fragment of freeness the fundamental theorems consume:
    freeness says "generated, with no relations beyond the structural
    ones"; the theorems only need "generated". -/
structure Generated (T : 𝕋) where
  /-- The atomic generators (journal entries). -/
  IsGen : ∀ {A B : Object}, T.Hom A B → Prop
  /-- Induction over the generated groupoid. -/
  induction :
    ∀ (P : ∀ {A B : Object}, T.Hom A B → Prop),
      (∀ {A B : Object} (f : T.Hom A B), IsGen f → P f) →
      (∀ A : Object, P (T.id A)) →
      (∀ A B : Object, P (0 : T.Hom A B)) →
      (∀ {A B C : Object} (g : T.Hom B C) (f : T.Hom A B),
        P g → P f → P (T.comp g f)) →
      (∀ {A B : Object} (f : T.Hom A B), P f → P (T.inv f)) →
      (∀ {A B C D : Object} (f : T.Hom A B) (g : T.Hom C D),
        P f → P g → P (T.tensor f g)) →
      (∀ {A B : Object} (f g : T.Hom A B), P f → P g → P (f + g)) →
      ∀ {A B : Object} (f : T.Hom A B), P f

end 𝕋

/-- The fundamental laws (K3). A representation satisfying `𝕋Laws` is a
    model of 𝕋; one that does not is wrong.

    Commutative-monoid laws on hom-sets (T10, T11) are **not** stated
    here — they come with the `AddCommMonoid` instances. The braiding
    laws (T7) are not stated here — they are proved (`braid_invol`).

    The coherence laws `tensor_assoc`, `tensor_comm`, `tensor_unit`
    relate morphisms whose endpoint objects are equal only
    propositionally, so they are stated with `HEq`.

    **Aggregation is compatible with nothing but the valuation**
    (decision D16). Neither composition nor tensor distributes over
    hom-set `+`, and composition does not absorb `0`: each candidate
    law is refuted by the valuation, which counts some flow twice —
    e.g. `V((g + g') ∘ f) = V g + V g' + V f` but
    `V(g∘f + g'∘f) = V g + V g' + 2·V f`. Worse, Phase 1's
    `comp_zero` (`f ∘ 0 = 0`) together with `V_comp` *forced
    `V f = 0` for every morphism* — the whole Phase 1 axiom set
    admitted only the identically-zero valuation. The flow model in
    `Pacioli.lean` (which exists precisely because these laws are
    gone) is the standing witness of non-degeneracy. Consequently 𝕋
    is *not* a CMon-enriched category in the standard sense: hom-sets
    carry CMon structure (aggregation), and that structure interacts
    only with valuations (`V_add`). -/
structure 𝕋Laws (T : 𝕋) where
  /-- T1 — composition is associative. -/
  comp_assoc : ∀ {A B C D : Object}
    (h : T.Hom C D) (g : T.Hom B C) (f : T.Hom A B),
    T.comp h (T.comp g f) = T.comp (T.comp h g) f
  /-- T2 — left identity. -/
  id_comp : ∀ {A B : Object} (f : T.Hom A B), T.comp (T.id B) f = f
  /-- T2 — right identity. -/
  comp_id : ∀ {A B : Object} (f : T.Hom A B), T.comp f (T.id A) = f
  /-- T3 — left inverse: reversing after doing is doing nothing. -/
  inv_comp : ∀ {A B : Object} (f : T.Hom A B),
    T.comp (T.inv f) f = T.id A
  /-- T3 — right inverse. -/
  comp_inv : ∀ {A B : Object} (f : T.Hom A B),
    T.comp f (T.inv f) = T.id B
  /-- T5 — tensor of identities is the identity. -/
  tensor_id : ∀ A B : Object, T.tensor (T.id A) (T.id B) = T.id (A + B)
  /-- T6 — interchange: sequential and parallel composition commute. -/
  tensor_comp : ∀ {A B C A' B' C' : Object}
    (g : T.Hom B C) (f : T.Hom A B) (g' : T.Hom B' C') (f' : T.Hom A' B'),
    T.comp (T.tensor g g') (T.tensor f f') = T.tensor (T.comp g f) (T.comp g' f')
  /-- T4 — tensor is associative (strict: endpoints are equal objects). -/
  tensor_assoc : ∀ {A B C D E F : Object}
    (f : T.Hom A B) (g : T.Hom C D) (h : T.Hom E F),
    HEq (T.tensor (T.tensor f g) h) (T.tensor f (T.tensor g h))
  /-- T7 — tensor is commutative (strict symmetry: posting order within
      a transaction is meaningless). -/
  tensor_comm : ∀ {A B C D : Object} (f : T.Hom A B) (g : T.Hom C D),
    HEq (T.tensor f g) (T.tensor g f)
  /-- T4' — the empty transaction on no accounts is neutral for tensor. -/
  tensor_unit : ∀ {A B : Object} (f : T.Hom A B),
    HEq (T.tensor f (T.id 0)) f

namespace 𝕋Laws

variable {T : 𝕋}

/-- The inverse of the identity is the identity. Derived, not a law. -/
theorem inv_id (L : 𝕋Laws T) (A : Object) : T.inv (T.id A) = T.id A := by
  have h := L.inv_comp (T.id A)
  rwa [L.comp_id] at h

/-- Reversal is involutive: reversing a reversal restores the
    transaction. Derived, not a law. -/
theorem inv_inv (L : 𝕋Laws T) {A B : Object} (f : T.Hom A B) :
    T.inv (T.inv f) = f :=
  calc T.inv (T.inv f)
      = T.comp (T.inv (T.inv f)) (T.id A) := (L.comp_id _).symm
    _ = T.comp (T.inv (T.inv f)) (T.comp (T.inv f) f) := by
        rw [L.inv_comp]
    _ = T.comp (T.comp (T.inv (T.inv f)) (T.inv f)) f := L.comp_assoc _ _ _
    _ = T.comp (T.id B) f := by rw [L.inv_comp]
    _ = f := L.id_comp f

/-- Composing transported identities in both directions is the
    identity — the generic fact behind `braid_invol`. -/
theorem comp_cast_id_cast_id (L : 𝕋Laws T) {X Y : Object}
    (h : X = Y) (h' : Y = X) :
    T.comp (T.castHom rfl h' (T.id Y)) (T.castHom rfl h (T.id X)) = T.id X := by
  subst h
  exact L.id_comp (T.id X)

/-- T7 (worksheet) — the braiding is involutive. A theorem, not a law:
    the braiding is transport of the identity, so this is a fact about
    casts and `id_comp`. -/
theorem braid_invol (L : 𝕋Laws T) (A B : Object) :
    T.comp (T.braiding B A) (T.braiding A B) = T.id (A + B) :=
  L.comp_cast_id_cast_id (add_comm A B) (add_comm B A)

end 𝕋Laws

end Ledger

/-! ## The bridge: 𝕋 in the standard vocabulary

A lawful model is, literally, a symmetric monoidal groupoid with
commutative-monoid hom-sets. The instances below make that sentence
type-check. The objects are tagged by the laws (`L.Obj` is `Object`
carrying `L` in its type) so that each model's instances are its
own. Every coherence isomorphism of the strict structure is
`eqToHom` of an equality in the object monoid, so every coherence
obligation reduces, through `conj_eqToHom_iff_heq`, to one of the
`HEq` law fields or to `eqToHom` algebra. -/

namespace Ledger

open CategoryTheory MonoidalCategory

/-- The objects of a lawful model, tagged by its laws so that the
    category-theoretic instances attach to this model alone. -/
def 𝕋Laws.Obj {T : 𝕋} (_L : 𝕋Laws T) : Type := Object

namespace 𝕋Laws

variable {T : 𝕋} {L : 𝕋Laws T}

instance : AddCommMonoid L.Obj := inferInstanceAs (AddCommMonoid Object)

instance : Category L.Obj where
  Hom A B := T.Hom A B
  id A := T.id A
  comp f g := T.comp g f
  id_comp := L.comp_id
  comp_id := L.id_comp
  assoc f g h := L.comp_assoc h g f

/-- Every transaction is reversible: a lawful model is a groupoid. -/
instance : Groupoid L.Obj where
  inv := T.inv
  inv_comp := L.comp_inv
  comp_inv := L.inv_comp

/-- In this strict setting `eqToHom` is transport of the identity,
    which is the bespoke `castHom` on identities. -/
theorem eqToHom_eq_castHom {A B : L.Obj} (h : A = B) :
    eqToHom h = T.castHom rfl h (T.id A) := by
  subst h; rfl

instance : MonoidalCategoryStruct L.Obj where
  tensorObj A B := A + B
  whiskerLeft X _ _ f := T.tensor (T.id X) f
  whiskerRight f Y := T.tensor f (T.id Y)
  tensorHom f g := T.tensor f g
  tensorUnit := (0 : Object)
  associator A B C := eqToIso (add_assoc A B C)
  leftUnitor A := eqToIso (zero_add A)
  rightUnitor A := eqToIso (add_zero A)

private theorem tensorHom_eqToHom_id {A B : L.Obj} (h : A = B)
    (Z : L.Obj) :
    (eqToHom h ⊗ₘ 𝟙 Z) = eqToHom (congrArg (· + Z) h) := by
  subst h
  simpa using L.tensor_id A Z

private theorem id_tensorHom_eqToHom (Z : L.Obj) {A B : L.Obj}
    (h : A = B) :
    (𝟙 Z ⊗ₘ eqToHom h) = eqToHom (congrArg (Z + ·) h) := by
  subst h
  simpa using L.tensor_id Z A

private theorem whiskerRight_eqToHom {A B : L.Obj} (h : A = B)
    (Z : L.Obj) :
    (eqToHom h ▷ Z) = eqToHom (congrArg (· + Z) h) := by
  subst h
  simpa using L.tensor_id A Z

private theorem whiskerLeft_eqToHom (Z : L.Obj) {A B : L.Obj}
    (h : A = B) :
    (Z ◁ eqToHom h) = eqToHom (congrArg (Z + ·) h) := by
  subst h
  simpa using L.tensor_id Z A

/-- A lawful model is a monoidal category, strictly: all coherence
    isomorphisms are `eqToHom`s of object-monoid equalities. -/
instance : MonoidalCategory L.Obj :=
  .ofTensorHom
    (id_tensorHom_id := L.tensor_id)
    (id_tensorHom := by intros; rfl)
    (tensorHom_id := by intros; rfl)
    (tensorHom_comp_tensorHom := fun f₁ f₂ g₁ g₂ =>
      L.tensor_comp g₁ f₁ g₂ f₂)
    (associator_naturality := by
      intro X₁ X₂ X₃ Y₁ Y₂ Y₃ f₁ f₂ f₃
      simp only [associator, eqToIso.hom]
      rw [comp_eqToHom_iff, Category.assoc]
      refine (conj_eqToHom_iff_heq _ _ (add_assoc X₁ X₂ X₃)
        (add_assoc Y₁ Y₂ Y₃)).mpr ?_
      exact L.tensor_assoc f₁ f₂ f₃)
    (leftUnitor_naturality := by
      intro X Y f
      simp only [leftUnitor, eqToIso.hom]
      rw [comp_eqToHom_iff, Category.assoc]
      refine (conj_eqToHom_iff_heq _ _ (zero_add X) (zero_add Y)).mpr ?_
      exact (L.tensor_comm (T.id 0) f).trans (L.tensor_unit f))
    (rightUnitor_naturality := by
      intro X Y f
      simp only [rightUnitor, eqToIso.hom]
      rw [comp_eqToHom_iff, Category.assoc]
      refine (conj_eqToHom_iff_heq _ _ (add_zero X) (add_zero Y)).mpr ?_
      exact L.tensor_unit f)
    (pentagon := fun W X Y Z => by
      simp only [associator, eqToIso.hom]
      rw [tensorHom_eqToHom_id, id_tensorHom_eqToHom]
      simp [eqToHom_trans])
    (triangle := fun X Y => by
      simp only [associator, leftUnitor, rightUnitor, eqToIso.hom]
      rw [tensorHom_eqToHom_id, id_tensorHom_eqToHom]
      simp [eqToHom_trans])

/-- Posting order is meaningless: a lawful model is symmetric, with
    the braiding given by commutativity of the object monoid. -/
instance : BraidedCategory L.Obj where
  braiding A B := eqToIso (add_comm A B)
  braiding_naturality_right := by
    intro X Y Z f
    simp only [eqToIso.hom]
    rw [comp_eqToHom_iff, Category.assoc]
    refine (conj_eqToHom_iff_heq _ _ (add_comm X Y) (add_comm X Z)).mpr ?_
    exact L.tensor_comm (T.id X) f
  braiding_naturality_left := by
    intro X Y f Z
    simp only [eqToIso.hom]
    rw [comp_eqToHom_iff, Category.assoc]
    refine (conj_eqToHom_iff_heq _ _ (add_comm X Z) (add_comm Y Z)).mpr ?_
    exact L.tensor_comm f (T.id Z)
  hexagon_forward := fun X Y Z => by
    simp only [associator, eqToIso.hom]
    rw [whiskerRight_eqToHom, whiskerLeft_eqToHom]
    simp [eqToHom_trans]
  hexagon_reverse := fun X Y Z => by
    simp only [associator, eqToIso.hom, eqToIso.inv]
    rw [whiskerRight_eqToHom, whiskerLeft_eqToHom]
    simp [eqToHom_trans]

instance : SymmetricCategory L.Obj where
  symmetry := fun A B => by
    show eqToHom (add_comm A B) ≫ eqToHom (add_comm B A) = 𝟙 (A + B)
    simp [eqToHom_trans]

/-- The CMon enrichment, stated on the categorical homs. It is
    deliberately bare: no `Preadditive` instance exists or may be
    added, because compatibility between `+` and `≫` degenerates
    every valuation to zero (decision D16; see
    `zero_absorption_degenerates` in `Ledger.Pacioli`). -/
instance (A B : L.Obj) : AddCommMonoid (A ⟶ B) := T.homAddCommMonoid A B

/-- The braiding of the bridge agrees with the bespoke `braiding`. -/
theorem braiding_eq_castHom (A B : L.Obj) :
    (β_ A B).hom = T.braiding A B := by
  have h : (β_ A B).hom = eqToHom (add_comm A B) := rfl
  rw [h, eqToHom_eq_castHom]
  rfl

/-- `braid_invol`, re-derived from the standard API: symmetry of the
    braiding is exactly the bespoke involution law. -/
example (A B : L.Obj) :
    T.comp (T.braiding B A) (T.braiding A B) = T.id (A + B) := by
  have h := SymmetricCategory.symmetry (C := L.Obj) A B
  rw [braiding_eq_castHom, braiding_eq_castHom] at h
  exact h

end 𝕋Laws

end Ledger
