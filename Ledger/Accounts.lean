import Mathlib.Algebra.Order.Group.Multiset
import Ledger.Basic

/-!
# Objects: the free commutative monoid on accounts

Objects of `𝕋` are elements of the free commutative monoid on `Account`
pairs — multisets. This is the **semantic domain** for objects; it is
concrete because multisets of accounts already *are* the mathematical
object, with no further abstraction wanted. Only morphisms (in
`Groupoid.lean`) are axiomatized.

## The strict monoidal structure comes for free

`Multiset Account` is an `AddCancelCommMonoid` in Mathlib:

- the tensor product ⊗ of the design worksheet **is** multiset sum `+`;
- the monoidal unit `I` **is** the empty multiset `0`;
- associativity, commutativity, and unit laws of ⊗ hold as *equalities*
  of objects (`add_assoc`, `add_comm`, `add_zero`), not as coherence
  isomorphisms.

Consequently 𝕋 is a **strict** symmetric monoidal groupoid: no
associator or unitor structure is needed, and the braiding morphism is
derived (transport of the identity along `add_comm` — see
`𝕋.braiding` in `Groupoid.lean`). This resolves the worksheet's open
question "strict vs. weak monoidal" — decision D9: strict, with the
note that any weak model strictifies by Mac Lane coherence.

Per the method's rule — delete bespoke names that standard classes
supply — this module intentionally re-states *nothing*: `add_comm`,
`add_assoc`, `add_zero`, `zero_add` from Mathlib are the tensor laws.
-/

namespace Ledger

/-- An object of 𝕋 is a multiset of account×commodity pairs — the free
    commutative monoid on `Account`. Tensor is `+`, the unit is `0`. -/
abbrev Object : Type := Multiset Account

end Ledger
