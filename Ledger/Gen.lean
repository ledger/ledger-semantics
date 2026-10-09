import Mathlib.Data.Rat.Defs
import Ledger.Basic

/-!
# Property-sweep journal generator (acceptance card 1, rung 2)

Emits random journals in the stage-1 `.dat` subset, for the
differential sweep to replay through both the C++ ledger and the Lean
oracle. Every entry balances in its real postings: in each commodity,
as written or once its elided posting is completed; at its stated cost,
when it has one; and, in the exchange shape, only at the rate that C++
infers from its two postings in different commodities (Phase 3 of
`finalize`, src/xact.cc:374-473 at 76b9dc2b2), which the oracle
reproduces for this shape (`impliedExchange` in Journal). Determinism
is part of the comparison tuple: the seed and the generator's identity
pin the corpus, which is regenerated and never edited by hand. The
shape roll has had ten outcomes instead of eight since the reversal-pair
and exchange shapes were added, which changes the shape of about four
draws in five, so every seed yields a different corpus than it did
before, and a corpus generated earlier cannot be reproduced from its
seed by this revision. The generator never authors expectations
(single-oracle doctrine): the oracle side of the sweep computes the
expected balances live.

Entry shapes exercised, decided by the seeded PRNG:
  - two to five written postings per entry; prefix (`$`, `€`) and
    suffix (`GEN`) commodities;
  - `$-12.34`, `$ -12.34`, `-$12.34` and `-12.34 GEN` amount
    spellings, with comma grouping on large amounts;
  - explicit closing postings (single-commodity entries) and elided
    postings (possibly completing several commodities at once);
  - per-unit costs, `N GOODS @ PRICE`, with two-decimal prices, an
    integral unit count, and either commodity spelling for the price;
    the closing posting is explicit or elided;
  - three-commodity entries closed by a single elided posting, which
    C++ completes by fanning out one generated posting per commodity
    (no balance assignments are ever emitted);
  - automated-transaction blocks, `= /regex/` with bare-number
    multiplier postings (a virtual one, or a real pair that cancels),
    placed at a seeded position so some matching entries precede the
    rule and some follow it;
  - reversal pairs, `[x // y] + [y // x] = [0 // 0]` in the notation of
    Ellerman (2014), p. 486: an explicit single-commodity entry among
    the accounts `Assets:Rev0` to `Assets:Rev3`, which no other shape
    touches, followed on the same day by its reversal, so that each of
    those accounts nets to exactly zero;
  - two-commodity exchanges: two postings in different commodities, of
    opposite signs, with no cost, lot or elided posting, each keeping
    its own amount; such an entry is the value collapse, under an
    inferred price, of an exchange such as Ellerman's transaction 2b
    (pp. 497-498), not Ledger's spelling of that transaction;
  - a note line under the payee (label noise the flows must ignore).

Exactness is part of the contract, not decoration. Every construct is
chosen so the reported balances land exactly on the commodity's
two-decimal display precision: unit counts are integers, prices carry
two decimals, and the postings a multiplier can match carry whole
currency units. The rate that C++ infers for an exchange need not be
exact at any precision, but no balance reports it. Every total is
therefore a whole number of cents or of units, so the generated
journals reach the driver's suppression of a total that is exactly
zero, through the reversal accounts, and never its suppression of a
nonzero total that shows as zero (`balancesOf` and `displayRow` in
Driver). A value that fell exactly halfway between two displayable
cents would be decided by the binary approximation through which C++
prints an amount (`stream_out_mpq`, src/amount.cc:208-245), which the
oracle reproduces in `Parse.cppRoundAt`; the generator still does not
manufacture such ties, because a sweep corpus is meant to grow
*construct* coverage, and a tie exercises the rounding of the display
rather than any construct of the journal.

The generator never authors expectations, only journals.

Run: `lake env lean --run Ledger/Gen.lean SEED DRAWS OUTFILE`, where
DRAWS counts the draws of the shape roll; a reversal pair is one draw
and two transactions, so a corpus holds one transaction more than its
draws for each reversal pair in it.
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

/-- Goods commodities: they appear only as the *amount* of a
    cost-annotated posting, never as a cost, so a posting's cost is
    always of a different commodity than its amount. -/
def goodsCommodities : List String := ["GENX", "GENY", "AAPL", "VBMFX"]

/-- Accounts that hold cost-annotated goods. Kept out of
    `accountPool` so no elided completion ever lands here. -/
def lotAccounts : List String :=
  (List.range 4).map fun i => s!"Assets:Lot{i}"

/-- Accounts the automated-transaction rules match. Kept out of
    `accountPool` so the only amounts a multiplier ever sees are the
    whole currency units emitted by the auto-target shape. -/
def autoAccounts : List String :=
  (List.range 4).map fun i => s!"Expenses:Auto{i}"

/-- Accounts that only reversal pairs touch. Kept out of `accountPool`
    and unmatched by the automated rules, so that each of them nets to
    exactly zero over the journal. -/
def revAccounts : List String :=
  (List.range 4).map fun i => s!"Assets:Rev{i}"

/-- Multipliers whose product with a whole currency unit is exact at
    two decimals. -/
def multipliers : List String := ["0.10", "0.20", "0.25", "0.50"]

/-- Pick one element of a non-empty list of strings. -/
def Rng.pick (r : Rng) (xs : List String) : String × Rng :=
  let (i, r) := r.below xs.length
  (xs[i % xs.length]!, r)

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

/-- The text of one transaction, dated by the draw index `idx`, with
    the payee `payee`, a note line when `note` holds, and the postings
    `ps`. -/
def emitXact (idx : Nat) (ps : List Posting) (note : Bool)
    (payee : String := s!"Generated {idx}") : String :=
  let day := idx % 28 + 1
  let month := idx / 28 % 12 + 1
  let header := s!"2026/{month}/{day} {payee}"
  let lines := ps.map fun p =>
    match p.amountStr with
    | some a => s!"    {p.account}    {a}"
    | none => s!"    {p.account}"
  let noteLine := if note then ["    ; generated: label noise"] else []
  String.intercalate "\n" (header :: (noteLine ++ lines)) ++ "\n"

/-- A per-unit cost entry: `N GOODS @ PRICE` against an explicit or
    elided closing posting. `N` is an integer and `PRICE` carries two
    decimals, so `N × PRICE` is exact at the money commodity's display
    precision and the entry balances on the cost side. -/
def genCostXact (idx : Nat) (note : Bool) (r : Rng) : String × Rng :=
  let (goods, r) := r.pick goodsCommodities
  let (lot, r) := r.pick lotAccounts
  let (units0, r) := r.below 40
  let (sgn, r) := r.below 4
  let (price0, r) := r.below 99999
  let (mIdx, r) := r.below commodities.length
  let (money, prefixSym) := commodities[mIdx % commodities.length]!
  let (pStyle, r) := r.below 6
  let (cStyle, r) := r.below 6
  let (ai, r) := r.below accountPool.length
  let (elideClose, r) := r.below 3
  -- units ∈ [1, 40], negated a quarter of the time (a sale)
  let units : Int := if sgn == 0 then -(Int.ofNat (units0 + 1))
                     else Int.ofNat (units0 + 1)
  let priceCents : Int := Int.ofNat (price0 + 1)
  let total : Int := units * priceCents
  let priceStr := spellAmount pStyle money prefixSym priceCents
  let unitsStr := if units < 0 then s!"-{units.natAbs}" else toString units.natAbs
  let pLot : Posting :=
    { account := lot, amountStr := some s!"{unitsStr} {goods} @ {priceStr}" }
  let pClose : Posting :=
    { account := accountPool[ai % accountPool.length]!
      amountStr :=
        if elideClose == 0 then none
        else some (spellAmount cStyle money prefixSym (-total)) }
  (emitXact idx [pLot, pClose] note, r)

/-- A three-commodity entry closed by one elided posting: C++ fans the
    residual out into one generated posting per commodity. No balance
    assignment is involved — the completion is inferred, not asserted. -/
def genMixedElisionXact (idx : Nat) (note : Bool) (r : Rng) : String × Rng :=
  let (extra, r) := r.below 2
  let rec build (cs : List (String × Bool)) (acc : List Posting) (r : Rng) :
      List Posting × Rng :=
    match cs with
    | [] => (acc.reverse, r)
    | (comm, prefixSym) :: rest =>
        let (ai, r) := r.below accountPool.length
        let (c, r) := r.cents
        let (style, r) := r.below 6
        let p : Posting :=
          { account := accountPool[ai % accountPool.length]!
            amountStr := some (spellAmount style comm prefixSym c) }
        build rest (p :: acc) r
  -- one posting per commodity, plus (sometimes) a second in the first
  let (ps, r) :=
    build (if extra == 0 then commodities ++ [commodities[0]!] else commodities) [] r
  let (ae, r) := r.below accountPool.length
  let pe : Posting :=
    { account := accountPool[ae % accountPool.length]!, amountStr := none }
  (emitXact idx (ps ++ [pe]) note, r)

/-- An entry whose first posting lands on an account the automated
    rules match, carrying a whole number of currency units so every
    multiplier product is exact at two decimals. -/
def genAutoTargetXact (idx : Nat) (note : Bool) (r : Rng) : String × Rng :=
  let (acct, r) := r.pick autoAccounts
  let (mIdx, r) := r.below commodities.length
  let (money, prefixSym) := commodities[mIdx % commodities.length]!
  let (whole, r) := r.below 5000
  let (sgn, r) := r.below 5
  let (s1, r) := r.below 6
  let (s2, r) := r.below 6
  let (ai, r) := r.below accountPool.length
  let units : Int := Int.ofNat ((whole + 1) * 100)
  let amt : Int := if sgn == 0 then -units else units
  let p1 : Posting :=
    { account := acct, amountStr := some (spellAmount s1 money prefixSym amt) }
  let p2 : Posting :=
    { account := accountPool[ai % accountPool.length]!
      amountStr := some (spellAmount s2 money prefixSym (-amt)) }
  (emitXact idx [p1, p2] note, r)

/-- A reversal pair, `[x // y] + [y // x] = [0 // 0]` in the notation of
    Ellerman (2014), p. 486: an explicit entry of two or three postings
    in the commodity `comm` among the accounts `Assets:Rev0` to
    `Assets:Rev3`, its last posting closing it, and, on the same day,
    its reversal, which negates every amount and takes the payee that
    `Label.ofReversal` gives a reversal. Each of those accounts nets to
    exactly zero over the pair. -/
def genReversalPair (idx : Nat) (comm : String) (prefixSym : Bool)
    (note : Bool) (r : Rng) : String × Rng :=
  let (k, r) := r.below 2
  -- the account, cents and spelling style of each posting, the closing
  -- posting last
  let rec build (n : Nat) (sum : Int) (acc : List (String × Int × Nat))
      (r : Rng) : List (String × Int × Nat) × Rng :=
    match n with
    | 0 =>
        let (a, r) := r.pick revAccounts
        (((a, -sum, 1) :: acc).reverse, r)
    | m + 1 =>
        let (a, r) := r.pick revAccounts
        let (c, r) := r.cents
        let (style, r) := r.below 6
        build m (sum + c) ((a, c, style) :: acc) r
  let (ps, r) := build (k + 1) 0 [] r
  let side := fun (sgn : Int) => ps.map fun (a, c, style) =>
    ({ account := a
       amountStr := some (spellAmount style comm prefixSym (sgn * c)) } : Posting)
  (emitXact idx (side 1) note ++ "\n"
    ++ emitXact idx (side (-1)) false (payee := s!"Reversal of Generated {idx}"), r)

/-- A two-posting exchange: amounts of opposite signs in two different
    commodities of `commodities`, whole cents each, with no cost, lot or
    elided posting. C++ balances it at the rate that it infers from the
    two amounts (Phase 3 of `finalize`, src/xact.cc:374-473 at
    76b9dc2b2), the oracle accepts it as C++ does (`impliedExchange` in
    Journal), and each posting keeps its own amount. -/
def genExchangeXact (idx : Nat) (note : Bool) (r : Rng) : String × Rng :=
  let (i1, r) := r.below commodities.length
  let (d, r) := r.below (commodities.length - 1)
  -- a commodity other than the first
  let i2 := (i1 + d + 1) % commodities.length
  let (c1, p1) := commodities[i1 % commodities.length]!
  let (c2, p2) := commodities[i2]!
  let (a1, r) := r.below accountPool.length
  let (a2, r) := r.below accountPool.length
  let (m1, r) := r.below 999999
  let (m2, r) := r.below 999999
  let (sgn, r) := r.below 2
  let (s1, r) := r.below 6
  let (s2, r) := r.below 6
  let v1 : Int := Int.ofNat (m1 + 1)
  let v2 : Int := Int.ofNat (m2 + 1)
  let (q1, q2) := if sgn == 0 then (v1, -v2) else (-v1, v2)
  let ps : List Posting :=
    [{ account := accountPool[a1 % accountPool.length]!
       amountStr := some (spellAmount s1 c1 p1 q1) },
     { account := accountPool[a2 % accountPool.length]!
       amountStr := some (spellAmount s2 c2 p2 q2) }]
  (emitXact idx ps note, r)

/-- Generate the transaction of one draw, or the two of a reversal
    pair; returns their text.

    The ten outcomes of the `below 10` roll select the shape: 0/2/6
    explicit single-commodity, 1/7 the original one-or-two-commodity
    elision, and one outcome each for the cost (3),
    three-commodity-elision (4) and auto-target (5) shapes, for a
    reversal pair through the accounts `Assets:Rev0` to `Assets:Rev3`
    (8), and for a two-commodity implicit exchange (9). The roll had
    eight outcomes before shapes 8 and 9 were added; widening it changed
    the shapes that a seed draws, and with them the corpus it yields.
    The commodity roll happens before the dispatch because the shapes
    that pick their own commodities still consume it: the draw sequence
    is what makes a seed reproducible, so it stays fixed for every
    shape. -/
def genXact (idx : Nat) (r : Rng) : String × Rng :=
  let (shape, r) := r.below 10
  let (commIdx, r) := r.below commodities.length
  let (comm, prefixSym) := commodities[commIdx % commodities.length]!
  let (note, r) := r.below 4
  if shape == 3 then genCostXact idx (note == 0) r
  else if shape == 4 then genMixedElisionXact idx (note == 0) r
  else if shape == 5 then genAutoTargetXact idx (note == 0) r
  else if shape == 8 then genReversalPair idx comm prefixSym (note == 0) r
  else if shape == 9 then genExchangeXact idx (note == 0) r
  else
  let elide := shape % 2
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

/-- One automated-transaction block, and the entry index it precedes. -/
structure Rule where
  pos : Nat
  text : String

/-- Spell one `= /regex/` block. Form 0 is the canonical single
    virtual multiplier (`(Equity:Tithe)  0.10`), which does not have to
    balance; form 1 is a real pair that cancels, so the entry it
    extends still verifies as balanced. -/
def ruleText (form : Nat) (mult : String) (rxIdx : Nat) : String :=
  let rx := if rxIdx == 0 then "/^Expenses:Auto/" else "/Auto[0-3]$/"
  if form == 0 then
    s!"= {rx}\n    (Equity:Tithe)    {mult}\n"
  else
    s!"= {rx}\n    Expenses:Tithe    {mult}\n    Equity:Tithe    -{mult}\n"

/-- One or two rules, each at a seeded position in the first third of
    the journal, so matching entries fall on both sides of a rule. -/
def genRules (n : Nat) (r : Rng) : List Rule × Rng :=
  let (cnt, r) := r.below 2
  let rec go (k : Nat) (r : Rng) (acc : List Rule) : List Rule × Rng :=
    match k with
    | 0 => (acc.reverse, r)
    | m + 1 =>
        let (form, r) := r.below 2
        let (mult, r) := r.pick multipliers
        let (rxIdx, r) := r.below 2
        let (pos, r) := r.below (n / 3 + 1)
        go m r ({ pos, text := ruleText form mult rxIdx } :: acc)
  go (cnt + 1) r []

def genJournal (seed : Nat) (n : Nat) : String :=
  let header :=
    s!"; generated by lean/Ledger/Gen.lean, seed {seed}, {n} draws\n" ++
    "; regenerate, never hand-edit (comparison-tuple discipline)\n\n"
  let (rules, r0) := genRules n ⟨UInt64.ofNat seed⟩
  let rec go (i : Nat) (r : Rng) (acc : List String) : List String :=
    match i with
    | 0 => acc.reverse
    | m + 1 =>
        let idx := n - i
        let (x, r) := genXact idx r
        let here := (rules.filter fun rule => rule.pos == idx).map Rule.text
        go m r (x :: (here.reverse ++ acc))
  header ++ String.intercalate "\n" (go n r0 [])

end Gen

end Ledger

def main (args : List String) : IO Unit := do
  match args with
  | [seedS, nS, out] =>
      let seed := seedS.toNat!
      let n := nS.toNat!
      IO.FS.writeFile out (Ledger.Gen.genJournal seed n)
      IO.println s!"wrote {out} (seed {seed}, {n} draws)"
  | _ =>
      IO.eprintln "usage: lake env lean --run Ledger/Gen.lean SEED DRAWS OUTFILE"
      throw (IO.userError "bad args")
