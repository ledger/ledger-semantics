import Ledger.Valuation

/-!
# Auto-xact derivation system (P3 — separate layer)

Automated transactions (`= expr`), balance assertions, and checks form
a **derivation system** operating on the free groupoid `𝕋`. They are
not morphisms: they do not compose with transactions, are not
reversible, and do not satisfy the groupoid laws. They are rewrite
rules — when a predicate matches a transaction, fixed template
postings are adjoined by tensor.

The derivation relation `Derives rules f f'` is a `Prop`: it specifies
WHAT derivation means, not HOW to compute it (Phase 5+ provides the
computation).

## Key theorem

Derivation preserves every valuation whose value on the templates is
zero: auto-xacts reclassify value between accounts, never create or
destroy it (`derivation_preserves_valuation`).

Not yet modeled (recorded, Phase 4): periodic transactions (`~ period`,
scheduled generators) and balance *assignments* (`= AMOUNT` with no
posting amount — completions that compute, rather than assert, a
value). See the worksheet's open questions.
-/

namespace Ledger

/-- A single derivation rule: a predicate plus template postings.
    When `predicate f` holds, applying the rule to `f : A → B` yields
    `f ⊗ template : A + templateDom → B + templateCod`. -/
structure DerivationRule (T : 𝕋) where
  /-- Rule name (for enable/disable/delete commands). -/
  name : Option String
  /-- When does this rule apply? -/
  predicate : ∀ {A B : Object}, T.Hom A B → Prop
  /-- The domain of the additional postings. -/
  templateDom : Object
  /-- The codomain of the additional postings. -/
  templateCod : Object
  /-- The additional postings to add (a fixed template). -/
  template : T.Hom templateDom templateCod

/-- The derivation relation: applying a list of rules in order to
    `f : A → B` yields `f' : A' → B'`. Domain and codomain grow as
    templates are adjoined by tensor. -/
inductive Derives (T : 𝕋) : List (DerivationRule T) →
    ∀ {A B : Object}, T.Hom A B →
    ∀ {A' B' : Object}, T.Hom A' B' → Prop where
  /-- Empty rule list: no change. -/
  | nil : ∀ {A B : Object} (f : T.Hom A B),
      Derives T [] f f
  /-- Rule doesn't match: skip it. -/
  | skip : ∀ {r rules A B A' B'} {f : T.Hom A B} {f' : T.Hom A' B'},
      ¬ r.predicate f →
      Derives T rules f f' →
      Derives T (r :: rules) f f'
  /-- Rule matches: tensor the template onto the transaction, then
      continue with the remaining rules. -/
  | apply : ∀ {r rules A B A' B'} {f : T.Hom A B} {f' : T.Hom A' B'},
      r.predicate f →
      Derives T rules (T.tensor f r.template) f' →
      Derives T (r :: rules) f f'

/-- The auto-xact derivation system: a finite ordered list of rules,
    applied in list order. -/
structure DerivationSystem (T : 𝕋) where
  rules : List (DerivationRule T)

/-- **Derivation preserves valuation**: if every rule's template
    balances (`W.V template = 0` — the double-entry requirement on
    auto-xact postings), then derivation does not change the measured
    flow. By induction on `Derives`; the `apply` case is `V_tensor`. -/
theorem derivation_preserves_valuation (T : 𝕋) (W : ValuationFunctor T)
    (rules : List (DerivationRule T))
    {A B A' B' : Object} {f : T.Hom A B} {f' : T.Hom A' B'}
    (h : Derives T rules f f') :
    (∀ r ∈ rules, W.V r.template = 0) → W.V f' = W.V f := by
  induction h with
  | nil f => intro _; rfl
  | skip hpred hd ih =>
      intro hb
      exact ih fun r hr => hb r (List.mem_cons_of_mem _ hr)
  | apply hpred hd ih =>
      intro hb
      rw [ih fun r hr => hb r (List.mem_cons_of_mem _ hr), W.V_tensor,
        hb _ List.mem_cons_self, add_zero]

end Ledger
