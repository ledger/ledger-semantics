import Ledger.Groupoid

/-!
# Labels fibration

Every morphism (transaction) in `𝕋` carries a label — metadata that
does not participate in the compositional structure of the groupoid.

## The fibration

The label assignment is a fibration over the discrete category of
labels:

- Labels do NOT compose: `label (g ∘ f)` has no defined relation to
  `label g` and `label f`. Composition is about account flow, not
  about metadata.
- Identity transactions carry the empty label (`label_id`).

## A law removed (decision D14)

Phase 1 also demanded `label (inv f) = ofReversal (label f)` with
`ofReversal` prepending "Reversal of " to the payee. That law is
**inconsistent**: `inv` is involutive (`𝕋Laws.inv_inv`), so it forces
`label f = ofReversal (ofReversal (label f))` — but string prepending
is not an involution. The Phase 1 `LabeledGroupoid` was therefore
uninhabited for every lawful `T` with any morphism. This went
undetected because the module was never elaborated (the vacuous-build
defect, ledger-nu3).

The repair: labels of inverses are unconstrained, matching the C++
source, which derives no label for a reversal (there is no reversal
operation in the journal syntax at all — reversals are structural).
`Label.ofReversal` is kept as a derived convenience with no law.
-/

namespace Ledger

/-- The state of a transaction (its clearing status). -/
inductive LabelState where
  | uncleared
  | cleared
  | pending
  | reconciled
  deriving BEq, DecidableEq, Repr, Inhabited

/-- A label attached to a transaction. Fields are the minimal common
    metadata; extensible with optional fields in later phases. -/
structure Label where
  payee : String
  date : String          -- ISO 8601 date
  effectiveDate : String -- effective date (may differ from entry date)
  description : String
  state : LabelState
  deriving BEq, DecidableEq, Repr, Inhabited

namespace Label

/-- The empty label — identity transactions carry this. -/
def empty : Label :=
  { payee := ""
  , date := ""
  , effectiveDate := ""
  , description := ""
  , state := LabelState.uncleared
  }

/-- A conventional label for a reversal, as a *derived convenience*.
    Deliberately not a law of `LabeledGroupoid`: it is not an
    involution, so demanding `label (inv f) = ofReversal (label f)`
    contradicts `inv_inv` (see the module docstring). -/
def ofReversal (l : Label) : Label :=
  { l with
    payee := "Reversal of " ++ l.payee
  , description := "Reversal of: " ++ l.description
  }

end Label

/-- A groupoid equipped with a label fibration: metadata assigned to
    each morphism, constrained only where the structure forces it. -/
structure LabeledGroupoid where
  T : 𝕋
  laws : 𝕋Laws T
  label : ∀ {A B : Object}, T.Hom A B → Label
  /-- Identity transactions carry the empty label. -/
  label_id : ∀ A : Object, label (T.id A) = Label.empty

end Ledger
