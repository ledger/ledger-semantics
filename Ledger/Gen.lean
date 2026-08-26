import Mathlib.Data.Rat.Defs
import Ledger.Basic

/-!
# Property-sweep journal generator (acceptance card 1, rung 2)

Emits random **balanced** journals in the stage-1 `.dat` subset, for
the differential sweep to replay through both the C++ ledger and the
Lean oracle. Determinism is part of the comparison tuple: the seed and
the generator's identity pin the corpus — regenerate, never hand-edit.
The generator never authors expectations (single-oracle doctrine): the
oracle side of the sweep computes the expected balances live.

Entry shapes exercised, decided by the seeded PRNG:
  - 2–4 postings; prefix (`$`, `€`) and suffix (`GEN`) commodities;
  - `$-12.34`, `$ -12.34`, and `-12.34 GEN` amount spellings; comma
    grouping on large amounts; tab and double-space separators;
  - explicit closing postings (single-commodity entries) and elided
    postings (possibly completing several commodities at once);
  - posting status flags and trailing notes (label noise the flows
    must ignore).

Run: `lake env lean --run Ledger/Gen.lean SEED XACTS OUTFILE`
-/

namespace Ledger

namespace Gen

/-- Deterministic 64-bit LCG (Knuth MMIX constants). -/
def next (s : UInt64) : UInt64 :=
  s * 6364136223846793005 + 1442695040888963407

structure Rng where
  state : UInt64

def Rng.step (r : Rng) : UInt64 × Rng :=
  let s := next r.state
  (s, ⟨s⟩)

/-- A pseudo-random `Nat` below `n` (n > 0). -/
def Rng.below (r : Rng) (n : Nat) : Nat × Rng :=
  let (v, r) := r.step
  ((v >>> 16).toNat % n, r)

def commodities : List (String × Bool) :=
  [("$", true), ("€", true), ("GEN", false)]   -- (symbol, prefix?)

def accountPool : List String :=
  ((List.range 12).map fun i => s!"Assets:Gen{i}")
    ++ ((List.range 12).map fun i => s!"Expenses:Gen{i}")

/-- Cents in [-999999, 999999] \ {0}. -/
def Rng.cents (r : Rng) : Int × Rng :=
  let (m, r) := r.below 999999
  let (sgn, r) := r.below 2
  let v : Int := Int.ofNat (m + 1)
  ((if sgn == 0 then v else -v), r)

/-- Format cents as a decimal with commas optionally grouped into the
    integer part (`12,345.67`). -/
def fmtCents (withCommas : Bool) (c : Int) : String :=
  let n := c.natAbs
  let ip := n / 100
  let fp := n % 100
  let ipStr :=
    if withCommas && ip ≥ 1000 then
      let s := toString ip
      let cs := s.toList.reverse
      let rec group : List Char → List Char
        | a :: b :: c :: rest@(_ :: _) => a :: b :: c :: ',' :: group rest
        | l => l
      String.ofList (group cs).reverse
    else toString ip
  let fpStr := if fp < 10 then s!"0{fp}" else toString fp
  let sign := if c < 0 then "-" else ""
  s!"{sign}{ipStr}.{fpStr}"

/-- Spell an amount in one of the concrete syntaxes. -/
def spellAmount (style : Nat) (comm : String) (prefixSym : Bool)
    (c : Int) : String :=
  let commas := style % 2 == 0
  if prefixSym then
    match style % 3 with
    | 0 => s!"{comm}{fmtCents commas c}"                          -- $-12.34
    | 1 => s!"{comm} {fmtCents commas c}"                         -- $ -12.34
    | _ =>
        if c < 0 then s!"-{comm}{fmtCents commas (-c)}"           -- -$12.34
        else s!"{comm}{fmtCents commas c}"
  else
    s!"{fmtCents commas c} {comm}"                                -- -12.34 GEN

structure Posting where
  account : String
  amountStr : Option String

def emitXact (idx : Nat) (ps : List Posting) (note : Bool) : String :=
  let day := idx % 28 + 1
  let month := idx / 28 % 12 + 1
  let header := s!"2026/{month}/{day} Generated {idx}"
  let lines := ps.map fun p =>
    match p.amountStr with
    | some a => s!"    {p.account}    {a}"
    | none => s!"    {p.account}"
  let noteLine := if note then ["    ; generated: label noise"] else []
  String.intercalate "\n" (header :: (noteLine ++ lines)) ++ "\n"

/-- Generate one transaction; returns its text. -/
def genXact (idx : Nat) (r : Rng) : String × Rng :=
  let (elide, r) := r.below 2
  let (commIdx, r) := r.below commodities.length
  let (comm, prefixSym) := commodities[commIdx % commodities.length]!
  let (note, r) := r.below 4
  if elide == 0 then
    -- explicit single-commodity entry: k postings + closing posting
    let (k, r) := r.below 3
    let rec build (n : Nat) (sum : Int) (acc : List Posting) (r : Rng) :
        List Posting × Rng :=
      match n with
      | 0 =>
          let (ai, r) := r.below accountPool.length
          let closing : Posting :=
            { account := accountPool[ai % accountPool.length]!
              amountStr := some (spellAmount 1 comm prefixSym (-sum)) }
          ((closing :: acc).reverse, r)
      | m + 1 =>
          let (ai, r) := r.below accountPool.length
          let (c, r) := r.cents
          let (style, r) := r.below 6
          let p : Posting :=
            { account := accountPool[ai % accountPool.length]!
              amountStr := some (spellAmount style comm prefixSym c) }
          build m (sum + c) (p :: acc) r
    let (ps, r) := build (k + 1) 0 [] r
    (emitXact idx ps (note == 0), r)
  else
    -- elided entry: possibly two commodities, one elided completion
    let (two, r) := r.below 3
    let (commIdx2, r) := r.below commodities.length
    let (comm2, prefixSym2) := commodities[commIdx2 % commodities.length]!
    let (a1, r) := r.below accountPool.length
    let (a2, r) := r.below accountPool.length
    let (a3, r) := r.below accountPool.length
    let (c1, r) := r.cents
    let (c2, r) := r.cents
    let (s1, r) := r.below 6
    let (s2, r) := r.below 6
    let p1 : Posting :=
      { account := accountPool[a1 % accountPool.length]!
        amountStr := some (spellAmount s1 comm prefixSym c1) }
    let p2 : List Posting :=
      if two == 0 && comm2 != comm then
        [{ account := accountPool[a2 % accountPool.length]!
           amountStr := some (spellAmount s2 comm2 prefixSym2 c2) }]
      else []
    let pe : Posting :=
      { account := accountPool[a3 % accountPool.length]!, amountStr := none }
    (emitXact idx (p1 :: p2 ++ [pe]) (note == 0), r)

def genJournal (seed : Nat) (n : Nat) : String :=
  let header :=
    s!"; generated by lean/Ledger/Gen.lean — seed {seed}, {n} xacts\n" ++
    "; regenerate, never hand-edit (comparison-tuple discipline)\n\n"
  let rec go (i : Nat) (r : Rng) (acc : List String) : List String :=
    match i with
    | 0 => acc.reverse
    | m + 1 =>
        let (x, r) := genXact (n - i) r
        go m r (x :: acc)
  header ++ String.intercalate "\n" (go n ⟨UInt64.ofNat seed⟩ [])

end Gen

end Ledger

def main (args : List String) : IO Unit := do
  match args with
  | [seedS, nS, out] =>
      let seed := seedS.toNat!
      let n := nS.toNat!
      IO.FS.writeFile out (Ledger.Gen.genJournal seed n)
      IO.println s!"wrote {out} (seed {seed}, {n} xacts)"
  | _ =>
      IO.eprintln "usage: lake env lean --run Ledger/Gen.lean SEED XACTS OUTFILE"
      throw (IO.userError "bad args")
