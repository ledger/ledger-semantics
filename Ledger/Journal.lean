import Ledger.Parse

/-!
# The journal engine: directives, transactions, and final flows

Stateful upper half of the L4 → L2 mapping (lexical lower half in
`Parse.lean`). Consumes journal text (with `include`s already spliced
by the driver — parsing stays pure) and produces one generator per
effective transaction: its final per-account, per-commodity flows.

Semantics implemented, each pinned by the C++ suite's own expected
outputs (the `SemanticBisimulation` ctest is the standing check):

- **Balancing**: per commodity and per pool, on *weights*, not on own
  amounts, while the recorded flows are own amounts.
  - *Pools*: real and deferred postings balance together,
    bracket-virtuals `[A]` apart (regress/563), and paren-virtuals
    `(A)` are exempt.
  - *First pass*: a posting weighs its `@`/`@@` cost if it has one
    and else its own amount. No lot is valued, except that outside a
    periodic template a lot priced in the commodity of its posting's
    cost adds its rounded gain to that cost (baseline/opt-base). C++
    Phase 6 does so for a posting of the real pool whose amount has a
    commodity (xact.cc:692-729); for a bracket-virtual posting it
    adds the gain to the real balance, and for an amount with no
    commodity it adds none, two departures that the comment beside
    `costVal` records.
  - *Elision and bucket*: one elided posting absorbs the residual per
    commodity, and a `bucket` account absorbs a real residual only in
    a transaction of a single posting, counting the parsed postings of
    every kind (xact.cc:368).
  - *Implicit exchange*: otherwise a two-commodity real residual, its
    commodities keyed by lot price as C++ keys them, is an implicit
    exchange only where C++ infers one (Phase 3, `impliedExchange`,
    which lists its departures), and a bracket-virtual residual never
    is. Where C++ converts, its verdict decides, and neither the
    allowance nor the second pass below applies. Where the top
    posting's key is not an entry of the real balance, C++ takes the
    two entries in an unspecified order (balance.h:99,
    xact.cc:422-423), and when the two orders lead to different
    verdicts, the order-dependent rule passes a real residual in
    exactly two commodities.
  - *Zero test and allowance*: the zero test rounds at display
    precision, widened in the real pool for a cost commodity shown
    without decimals (regress/1114), and asks for exact zero in the
    null commodity. A residual left to these tests passes when its
    part in each commodity passes the zero test or lies within the sum
    of half a unit in the last place of each cost written with
    decimals in that commodity. In either pool that allowance stands
    in for the per-unit cost rounding that C++ adjusts in the real
    pool alone (regress/1125, `costTol`).
  - *Second pass*: only a real residual that still fails reaches a
    second pass (regress/coverage-wave3-fixated-price), which weighs
    each lot at its price `{P}`×qty, in place of its cost except in a
    periodic template; its residual must pass the zero test or the
    order-dependent rule. The bracket-virtual pool has no second
    pass. C++ values a lot only in Phase 4, for a fixated lot on a
    posting without a cost, and in Phase 6, for a lot whose posting
    has a cost, written or computed, in the lot price's commodity or
    whose cost itself carries a lot price in that commodity
    (xact.cc:475-518, 692-774), and it adds neither value to the
    bracket-virtual balance (xact.cc:505-516, 712-713). The docstring
    of `impliedExchange` lists the lot shapes known to be accepted
    here in consequence, a lot whose posting has a cost in another
    commodity among them.
  - *Flows*: the recorded flows are each posting's own amount, never
    its weight, so a transaction balanced through a cost, a lot value
    or an implicit exchange can leave nonzero per-commodity totals:
    regress/1784 totals 28 ABCDEF and -280.00 EUR, and an unfiltered
    `equity` report books the negation of such totals to
    Equity:Opening Balances (baseline/cmd-equity).
- **Assignments** `= AMT` on an amountless posting: computed
  sequentially against the running account balance including earlier
  postings of the same transaction (regress/1005). With an amount
  present it is an assertion: positive tests pass their assertions by
  definition, so it is checked *by the C++ side* and dropped here.
- **Auto-xacts** `= /regex/`: template postings (fixed amounts or
  bare multipliers × the matched posting's amount) are appended per
  matching real posting of each later transaction — after balancing,
  as `extend_xact` does; templates may be virtual.
- **Timeclock** `i`/`o`: time postings (duration in canonical
  seconds), with the opposite amount posted to the bucket account
  when one is declared (regress/1607); no balance check.
- **UUID dedup**: a transaction whose note carries an already-seen
  `UUID:` is dropped whole (C++ `journal.cc` semantics) — the one
  documented non-flow-inert label.
- **Periodic templates** `~`: finalized as a transaction without a
  date against the state before them, booking no lot gain and with no
  UUID de-duplication. As C++ `parse_posts` reads the postings, a line
  beginning with `;` is dropped and a line beginning with `assert `,
  `check ` or `expr ` is a posting. The result is discarded, together
  with the display precisions and amount styles that its amounts teach
  C++, a departure that `flushPending` records; an error in the
  template is reported with the prefix `periodic transaction: `.
- **Flow-inert directives** are consumed with a justification in
  `handleDirective`; unknown constructs remain named errors.
-/

namespace Ledger

namespace Journal

open Parse

inductive PostKind where
  | real | virtualBal | virtualUnbal | deferred
  deriving Repr, DecidableEq

structure PostSpec where
  line : Nat
  inferred : Bool := false
  amtDecs : Nat := 0
  costDecs : Nat := 0
  gainVal : Option Amount := none
  account : String
  kind : PostKind
  note : String := ""
  amount : Option Amount := none
  costVal : Option Amount := none    -- @/@@ substitution (pass 1)
  lotVal : Option Amount := none     -- {P}/{=P} substitution (pass 2)
  /-- the lot price per unit of the amount's own lot, one written
      before any cost or balance assertion: `{P}`, or `{{T}}` divided
      by the absolute quantity when that is nonzero. On a zero
      quantity C++ rejects `{{T}}` (a division by zero, amount.cc:1911)
      and this keeps `T`. `impliedExchange` keys the amount by it, as
      C++ keys an annotated amount by its per-unit price
      (annotate.h:120-125), and a `{P}` survives a zero quantity, which
      `lotVal` does not. C++ rounds the quotient of `{{T}}`
      (amount.cc:1909-1923), where this keeps it exact. `finalizeXact`
      divides it by the factor by which a commodity equivalence
      reduces the amount, as C++ does (amount.cc:1153-1176). -/
  lotUnit : Option Amount := none
  /-- the lot price of `lotUnit` is written as a total, `{{T}}` or
      `{{=T}}`, on an amount with a commodity. C++ marks such an
      annotation ANNOTATION_PRICE_NOT_PER_UNIT (annotate.cc:161-164),
      divides the per-unit price out of the total and interns the
      annotated commodity (amount.cc:1908-1925); on an amount without a
      commodity it keeps no annotation (amount.cc:1908), and so, unlike
      `lotUnit`, this is not set there. When the matched posting has a
      cost and the template posting none, an automated posting whose
      amount copies an annotation that bears the mark takes its
      per-unit price, unscaled by its quantity and negated for a
      negative amount, as its whole cost (xact.cc:1611-1621).

      This field records what the posting writes, while C++ keeps the
      mark on the interned commodity. The mark is not a semantic flag
      (annotate.h:95), so annotations that differ only in it are equal
      and ordered alike (annotate.h:120-125, annotate.cc:122-128), and
      the pool returns the annotated commodity already interned for the
      same base, per-unit price, date, tag, value expression and fixated
      flag (pool.cc:200, 212-243). The lot of a key interned first in parse order, in the
      same transaction or an earlier one, therefore decides the mark for
      every later lot of that key, and a rule that takes this field for
      the mark departs from C++ in each direction. Under `= /Assets:A/`
      with `Assets:X 1` and `Assets:Y $-50`, C++ rejects
      `10 AAA {{$50}} @ $5` against `$-50` with the remainder `$-45`,
      but accepts it after an earlier transaction of
      `10 AAA {$5} @ $5`, and accepts `10 AAA {{$50}}` written after
      `10 AAA {$5}` in one transaction against `$-100`, where this field
      is set (fail-closed). It accepts `10 AAA {$5} @ $5` against `$-50`
      alone, but rejects it with the remainder `$-45` after an earlier
      transaction of `10 AAA {{$50}} @ $5`, where this field is not set
      (fail-open). -/
  lotTotal : Bool := false
  assignTarget : Option Amount := none
  /-- the amount itself is annotated (`{lot}`, `[date]` or `(note)`
      before any cost or balance assertion): C++'s
      `amount.has_annotation()`, which picks the top posting of an
      implicit exchange (xact.cc:386-393). C++ discards the annotation
      of an amount with no commodity (amount.cc:1908), and so does
      this flag. The two departures recorded at `fixated` apply to
      this flag as well. -/
  annotated : Bool := false
  /-- the amount's own lot price is fixated, `{=P}` or `{{=T}}`
      (ANNOTATION_PRICE_FIXATED, annotate.cc:169), under the same
      conditions as `annotated`. Unlike `LotPrice.fixated` in
      `Ledger/Lots.lean`, it is not set by the fixated costs `@ =P` and
      `@@ =T`: C++ fixates the annotation price they meet only in
      Phase 6 of finalize (xact.cc:816-819), after Phase 3 has chosen
      the top posting. Two departures affect both flags and the lot
      key of `impliedExchange`: the annotation C++ adds for an `apply
      fixed` rate (textual_xacts.cc:626-638) is not parsed and sets
      neither flag, and on a balance assignment `= AMT` both flags are
      false and the amount has no lot, although C++ can carry the
      target's lot or the account's single lot into the amount it
      computes (textual_xacts.cc:843-862). Each can fail either way;
      the docstring of `impliedExchange` gives a journal shape for each
      direction. -/
  fixated : Bool := false
  /-- the precision of an explicit cost amount: the cost literal's
      decimals, plus the amount's precision for a per-unit `@`
      (textual_xacts.cc:699-710, amount.cc:720), raised to the basis's
      precision when the posting's own lot price is in the cost's
      commodity and the basis differs from the cost at all, even by a
      gain that rounds to zero (xact.cc:696, 729; `parseAmountField`
      states the remaining conditions); 0 without a cost. This is the
      precision at which Phase 6 of `xact_base_t::finalize` leaves the
      cost, except where Phase 6 rewrites a cost that carries its own
      lot price into that price's commodity (xact.cc:735-774), and
      `costPrec` stays with the cost as written. The final zero test of
      `finalizeXact` widens a cost commodity of display precision 0 to
      the first positive `costPrec` of a cost in it (`zeroTestPrec`,
      regress/1114), whose docstring records the departures. -/
  costPrec : Nat := 0
  deriving Repr

instance : Inhabited PostSpec :=
  ⟨{ line := 0, account := "", kind := .real }⟩

structure AutoPost where
  account : String
  kind : PostKind
  fixed : Option Amount
  mult : ℚ
  exprSrc : Option String := none
  deriving Repr

inductive DateCmp where
  | ge | gt | le | lt
  deriving Repr, DecidableEq

inductive AmtCmp where
  | ge | gt | le | lt | eq
  deriving Repr, DecidableEq

/-- One disjunct of an auto-xact predicate. -/
structure PredSpec where
  accRxs : List Rx := []
  negRxs : List Rx := []
  dateTerms : List (DateCmp × Int) := []   -- epoch-day bounds
  payeeRx : Option Rx := none
  commentRx : Option Rx := none
  commodityEq : Option String := none
  amountTerms : List (AmtCmp × ℚ) := []
  /-- `%TAG`, `%TAG=VALUE`, `%/re/`: tag (regex) with optional value -/
  tagReq : Option (Rx × Option String) := none
  /-- `!%TAG` / `!%/re/`: tag must be absent -/
  negTag : Option Rx := none
  /-- `date =~ /re/` against the YYYY/MM/DD form -/
  dateRx : Option Rx := none
  /-- `code =~ /re/` against the header code -/
  codeRx : Option Rx := none
  /-- `account("N").total CMP q`: live balance comparisons -/
  acctTotal : List (String × AmtCmp × ℚ) := []
  /-- `any(rx [and R])`: another posting matches (real-only if true) -/
  anyRx : Option (Rx × Bool) := none
  /-- `all(rx)`: every posting in the current set matches -/
  allRx : Option Rx := none

structure AutoRule where
  branches : List PredSpec
  posts : List AutoPost
  name : Option String := none
  active : Bool := true
  noteTag : String := "" 


private inductive Pending where
  | none
  | xact (line : Nat) (header : String) (posts : List (Nat × String))
  | auto (rule : List (Nat × String))     -- predicate handled at open
  -- a `~` template: balance-checked by `flushPending`, flows discarded
  | periodic (line : Nat) (header : String) (posts : List (Nat × String))
  | acctBlock (frames : List (Nat × String))
  | commBlock (comm : String)
  | ignoreBlock

structure St where
  amt : AmtCtx := {}
  /-- commodity aliases (from `commodity` block `alias` subs) -/
  commAliases : List (String × String) := []
  /-- account-block `payee` rules: payee regex → account -/
  payeeAccountRules : List (Rx × String) := []
  /-- commodity → max fractional digits seen in literal own amounts -/
  precisions : List (String × Nat) := []
  /-- commodity = factor × base (C directives; seeded with time) -/
  equivs : List (String × ℚ × String) := [("h", 3600, "s"), ("m", 60, "s")]
  aliases : List (String × String) := []
  rewrites : List (Rx × String) := []
  applyStack : List (Option String) := []
  bucket : Option String := none
  autos : List AutoRule := []
  autoPred : List (List PredSpec × Option String) := []
  defaultYear : Option Int := none
  uuids : List String := []
  balances : List ((String × String) × ℚ) := []
  datedEvents : List ((String × String) × Int × ℚ × Bool) := []
  gens : List (List (Account × ℚ)) := []   -- reversed
  pending : Pending := .none
  clockIn : List (ℚ × String) := []
  nowSecs : Option ℚ := none
  recursiveAliases : Bool := false
  errFlag : Bool := false
  tentativePrec : List String := []
  lockedPrec : List String := []
  dfmt : Option (List Char) := none
  /-- (account, commodity) → (flows, inferred flows): drives the
      BIGINT_COST_PREC display rule for lone inferred balances -/
  flowStats : List ((String × String) × Nat × Nat) := []
  inComment : Bool := false

private def err {α} (line : Nat) (msg : String) : Except String α :=
  .error s!"line {line}: {msg}"

/-! ## Small helpers -/

/-- Resolve a commodity through the equivalence chain to
    (factor, base). -/
def resolveEquiv (equivs : List (String × ℚ × String)) (comm : String) :
    ℚ × String :=
  let rec go (fuel : Nat) (f : ℚ) (c : String) : ℚ × String :=
    match fuel with
    | 0 => (f, c)
    | fuel + 1 =>
        match equivs.find? fun (u, _, _) => u == c with
        | some (_, k, base) => go fuel (f * k) base
        | none => (f, c)
  go 8 1 comm

private def canonAmt (st : St) (a : Amount) : Amount :=
  let comm := (st.commAliases.lookup a.comm).getD a.comm
  let (f, base) := resolveEquiv st.equivs comm
  ⟨base, a.q * f⟩

private def bumpPrecision (st : St) (comm : String) (d : Nat) : St :=
  -- migrating parses raise the commodity's precision to the maximum
  -- observed (amount.cc: `prec > commodity().precision()`); a price
  -- directive's precision is tentative and the first explicit-decimal
  -- amount replaces it outright (COMMODITY_PRECISION_FROM_PRICE);
  -- `format`/`D` declarations LOCK it (COMMODITY_STYLE_NO_MIGRATE)
  if st.lockedPrec.contains comm then st
  else if st.tentativePrec.contains comm && d > 0 then
    { st with
      precisions := (comm, d) :: st.precisions.filter (fun (c, _) => c != comm)
      tentativePrec := st.tentativePrec.filter (· != comm) }
  else
    let st' :=
      match st.precisions.lookup comm with
      | some p => if d > p then
          { st with precisions := st.precisions.map fun (c, v) =>
              if c = comm then (c, d) else (c, v) }
        else st
      | none => { st with precisions := (comm, d) :: st.precisions }
    { st' with amt := { st'.amt with precs := st'.precisions } }

/-- Does `q` round to zero at `p` decimals? -/
private def roundsToZeroAt (p : Nat) (q : ℚ) : Bool :=
  let scaled := (if q < 0 then -q else q) * (10 ^ p : ℕ)
  scaled * 2 ≤ 1

/-- Display-precision-tolerant zero test: does the residual round to
    zero at the commodity's learned precision? (Cost amounts never
    feed precision — confirmed on standard.dat's 22-decimal prices.) -/
private def roundsToZero (st : St) (comm : String) (q : ℚ) : Bool :=
  roundsToZeroAt ((st.precisions.lookup comm).getD 0) q

/-- The precision at which the final zero test of a real pool reads a
    residual in `comm` (xact.cc:868-895, issue #1114, regress/1114).
    C++ widens a cost commodity of display precision 0 to the precision
    of the first explicit cost in it whose precision is positive, as
    Phase 6 leaves that cost, on a posting of any kind
    (`PostSpec.costPrec`), so that a sub-unit remainder is not read as
    zero; it restores the precision before it tests the bracket-virtual
    balance (xact.cc:971-979), which `finalizeXact` therefore tests at
    the display precision. C++ widens no cost without a commodity
    (xact.cc:881) and tests a residual without one exactly, in either
    pool (amount.cc:1378, 1429); `finalizeXact` does the same, apart
    from the regress/1125 tolerance beside `costTol`, and never asks
    this function about the null commodity. `posts` are the
    transaction's postings in order, before automated postings are
    added.

    `parseAmountField` approximates the precision of an amount
    expression and of a lot price, compares the commodities of a lot
    price and a cost as written, and keeps a cost in the commodity in
    which it is written; the display precision read here is the one
    that this reader learns. Each departure below was measured against
    C++ and is marked with the direction in which it fails:
    - a cost written as an expression counts only its literals'
      decimals, while C++ extends a division by six places
      (amount.cc:805-812) and, parsing a cost without migration, does
      not cap the quotient (amount.cc:1832-1835), so the cost of
      `1 FOO @ ($1.4/1.4000001)` has precision 14 where it counts 7
      here: `2 FOO @ ($100/9)` against `-$22`, and `2 FOO @@ ($200/9)`
      against `-$22`, are accepted here and rejected by C++
      (fail-open);
    - C++ caps the precision of a product or quotient amount at its
      commodity's display precision plus six (amount.cc:748-749,
      825-826), so `(1.25/3 FOO)` has precision 6 where it counts 8
      here: a transaction of `(1.25/3 FOO) @ 1 EUR`,
      `(-1.25/3 FOO) @ 1 EUR`, `1 BAR @ 0.0000001 EUR` and `0 EUR` is
      rejected here and accepted by C++ (fail-closed);
    - a quotient counts its larger operand's decimals plus six, where
      C++ adds both operands' precisions and six (amount.cc:811-812),
      which shows once the cap does not bind: after `1.00 FOO` has
      taught FOO two places, `(1.5/0.5 FOO) @ 1 EUR` with
      `1 BAR @ 0.000000006 EUR` against `-3 EUR` is accepted here and
      rejected by C++ (fail-open);
    - a product counts its larger factor's decimals, or six more when
      its value is not representable at them, where C++ adds the
      factors' precisions, and two places more for a `%` factor
      (amount.cc:720, 733):
      `(0.5 * 0.4 FOO) @ 1 EUR` against `-1 BAR @ 0.16 EUR` is accepted
      here and rejected by C++ (fail-open), and
      `(0.5 * 0.5 FOO) @ 4 EUR` with `1 BAR @ 0.001 EUR` against
      `-1 EUR`, and `(1 FOO * 50%) @ 1 EUR` twice with
      `1 BAR @ 0.001 EUR` against `-1 EUR`, are rejected here and
      accepted by C++ (fail-closed);
    - C++ tests the residual exactly when its precision does not exceed
      the widened one (amount.cc:1407), where this rounds at the
      widened precision: `(1/3000000 FOO) @ 1 EUR` against `0 EUR` is
      accepted here and rejected by C++ (fail-open);
    - the raise of Phase 6 compares the lot price's commodity with the
      cost's before `finalizeXact` resolves a `commodity` alias, which
      C++ resolves as it parses (pool.cc:150-155), so where `E` is an
      alias of `EUR`, `-0.5 FOO {1.001 E} @ 1 EUR` twice with
      `1 BAR @@ 0.0004 EUR` against `1 EUR`, whose cost C++ raises to
      precision 4, is accepted here and rejected by C++ (fail-open);
    - the raise reads a `{P}` price at its own literal's decimals, while
      C++ keys an annotated commodity by the value of its price
      (pool.cc:200, annotate.cc:97-100) and so reads the price at the
      decimals of the first literal of that value which annotated the
      commodity: after `1 FOO {1.00100 EUR}`,
      `-0.5 FOO {1.001 EUR} @ 1 EUR` twice with `(4/100000 EUR)`
      against `1 EUR` is accepted here and rejected by C++
      (fail-open), and after `1 FOO {1.001 EUR}` the same transaction
      written with `{1.00100 EUR}` is rejected here and accepted by C++
      (fail-closed);
    - where a cost carries its own lot price in the commodity of the
      posting's basis, Phase 6 rewrites the cost into that commodity
      (xact.cc:735-774), and C++ widens that commodity to the precision
      of the rewritten cost, while `costPrec` stays with the cost as
      written: `10 FOO {1 USD} @ 2 EUR {0.5 USD}` and
      `-20 EUR {0.5 USD}` with `(1/10 USD)` against `0 USD` are
      accepted here and rejected by C++ (fail-open);
    - the display precision read here omits what C++ learns from the
      amounts of an automated transaction's postings
      (textual_xacts.cc:271) and of a periodic template
      (textual_xacts.cc:952), from a `define` and a typed metadata
      value, which it evaluates as expressions whose amounts migrate
      their precision (textual_directives.cc:1081, metadata.cc:194,
      token.cc:555), and from an `apply fixed` rate
      (textual_directives.cc:534-535). Where C++ holds a positive
      precision from one of these it widens nothing, so after
      `= /^NEVER/` with `(Y) 0.50 EUR`, `~ Monthly` with `X 0.50 EUR`
      against an elided `Y`, `define x = 0.50 EUR`, `; X:: 0.50 EUR` or
      `apply fixed BAZ 0.50 EUR`, the transaction `1.0001 FOO @ 1 EUR`
      against `-1 BAR @ 1 EUR` is rejected here and accepted by C++
      (fail-closed). The comment on periodic templates in
      `flushPending` and the `apply fixed` entry of `impliedExchange`
      record what the same gaps do to the other tests. -/
private def zeroTestPrec (st : St) (posts : List PostSpec) (comm : String) :
    Nat :=
  match (st.precisions.lookup comm).getD 0 with
  | 0 => ((posts.find? fun q => q.costPrec > 0
            && q.costVal.any (·.comm == comm)).map (·.costPrec)).getD 0
  | p => p

private def lookupBal (st : St) (acct comm : String) : ℚ :=
  (st.balances.lookup (acct, comm)).getD 0

private def bumpStat (st : St) (acct comm : String) (inf : Bool) : St :=
  let key := (acct, comm)
  match st.flowStats.lookup key with
  | some _ => { st with flowStats := st.flowStats.map fun (k, t, i) =>
      if k = key then (k, t + 1, i + (if inf then 1 else 0)) else (k, t, i) }
  | none => { st with flowStats :=
      (key, 1, if inf then 1 else 0) :: st.flowStats }

private def lockPrecision (st : St) (comm : String) (d : Nat) : St :=
  let st := { st with
    precisions := (comm, d) :: st.precisions.filter (fun (c, _) => c != comm)
    tentativePrec := st.tentativePrec.filter (· != comm)
    lockedPrec := comm :: st.lockedPrec }
  { st with amt := { st.amt with precs := st.precisions } }

private def bumpBal (st : St) (acct comm : String) (dq : ℚ) : St :=
  let key := (acct, comm)
  match st.balances.lookup key with
  | some _ =>
      { st with balances := st.balances.map fun (k, v) =>
          if k = key then (k, v + dq) else (k, v) }
  | none => { st with balances := (key, dq) :: st.balances }

/-- Resolve an account name: exact alias, then `apply account`
    prefixes (innermost last). -/
private def resolveAccount (st : St) (name : String) : String :=
  -- journal_t::expand_aliases: whole-name lookup first, else walk
  -- single components (first only unless --recursive-aliases); each
  -- alias expands at most once, and a component whose target already
  -- sits colon-aligned at that position is skipped (#3132); loop to
  -- fixpoint only under --recursive-aliases
  let lookupAlias := fun (n : String) => st.aliases.lookup n
  let expandOnce := fun (seen : List String) (n : String) =>
    match lookupAlias n with
    | some t => if seen.contains n then none else some (n, t)
    | none =>
        let comps := n.splitOn ":"
        let rec walk (pre : List String) (rest : List String) :
            Option (String × String) :=
          match rest with
          | [] => none
          | c :: cs =>
              let hit :=
                match lookupAlias c with
                | some t =>
                    if seen.contains c then none
                    else
                      -- colon-aligned target already present here?
                      let upto := String.intercalate ":" ((pre ++ [c]))
                      if upto == t || upto.endsWith (":" ++ t) then none
                      else
                        let newName := String.intercalate ":"
                          ((pre ++ [t] ++ cs))
                        some (c, newName)
                | none => none
              match hit with
              | some r => some r
              | none =>
                  if st.recursiveAliases then walk (pre ++ [c]) cs else none
        walk [] comps
  let rec fix (fuel : Nat) (seen : List String) (n : String) : String :=
    match fuel with
    | 0 => n
    | fuel + 1 =>
        match expandOnce seen n with
        | some (used, n') =>
            if st.recursiveAliases then fix fuel (used :: seen) n' else n'
        | none => n
  let name := fix 10 [] name
  let prefixes := st.applyStack.filterMap id
  prefixes.foldl (fun acc p => s!"{p}:{acc}") name

private def daysFromCivil (y m d : Int) : Int :=
  let y := y - (if m <= 2 then 1 else 0)
  let era := (if y ≥ 0 then y else y - 399) / 400
  let yoe := y - era * 400
  let mp := (m + 9) % 12
  let doy := (153 * mp + 2) / 5 + d - 1
  let doe := yoe * 365 + yoe / 4 - yoe / 100 + doy
  era * 146097 + doe

/-- `2007/03/01 23:00:00` (or `-`/`.` separators, `HH:MM`) → epoch
    seconds. -/
private def parseDateTime (line : Nat) (dateS timeS : String) :
    Except String ℚ := do
  let dparts := dateS.splitOn "/" |>.flatMap (·.splitOn "-")
    |>.flatMap (·.splitOn ".")
  let tparts := timeS.splitOn ":"
  let civil := fun (a b c : Int) =>
    if c ≥ 1000 then daysFromCivil c a b else daysFromCivil a b c
  match dparts.map String.toNat?, tparts.map String.toNat? with
  | [some y, some mo, some d], [some h, some mi, some s] =>
      pure ((civil y mo d) * 86400 + h * 3600 + mi * 60 + s : Int)
  | [some y, some mo, some d], [some h, some mi] =>
      pure ((civil y mo d) * 86400 + h * 3600 + mi * 60 : Int)
  | _, _ => err line s!"malformed timeclock date/time '{dateS} {timeS}'"

/-- Parse a transaction header's date: digit runs in order, with an
    optional `--input-date-format` component order (`ymd` letters). -/
def headerDateF (fmt : Option (List Char)) (defaultYear : Option Int)
    (header : String) : Option Int :=
  let tok := String.ofList (header.toList.takeWhile fun c => c != ' ' && c != '=')
  let runs := fun (cs0 : List Char) => Id.run do
    let mut acc : List Nat := []
    let mut cs := cs0.dropWhile (fun c => !c.isDigit)
    while !cs.isEmpty do
      let run := cs.takeWhile Char.isDigit
      acc := acc ++ [(String.ofList run).toNat?.getD 0]
      cs := (cs.drop run.length).dropWhile (fun c => !c.isDigit)
    pure acc

  match fmt, runs tok.toList with
  | some order, vals =>
      if order.length == vals.length then
        let get := fun (c : Char) =>
          (order.zip vals).findSome? fun (o, v) => if o == c then some v else none
        match get 'y', get 'm', get 'd' with
        | some y, some m, some d => some (daysFromCivil y m d)
        | none, some m, some d =>
            defaultYear.map fun y => daysFromCivil y m d
        | _, _, _ => none
      else none
  | none, [y, m, d] =>
      some (if d ≥ 1000 then daysFromCivil d y m
            else daysFromCivil y m d)
  | none, [m, d] =>
      defaultYear.map fun y => daysFromCivil y m d
  | _, _ => none

/-- Parse a transaction header's date (first token; `Y` directive
    supplies the year for short dates). -/
def headerDate (defaultYear : Option Int) (header : String) : Option Int :=
  headerDateF none defaultYear header

def containsTag (notes tag : String) : Bool :=
  ((notes.splitOn (":" ++ tag ++ ":")).length > 1)
    || ((notes.splitOn (tag ++ "::")).length > 1)

private def containsUUID (s : String) : Bool :=
  (s.toLower.splitOn "uuid:").length > 1

private def uuidOf (s : String) : Option String :=
  match s.toLower.splitOn "uuid:" with
  | _ :: rest :: _ =>
      some (trimS (rest.takeWhile fun c => c != ',' && c != ';').toString)
  | _ => none

/-! ## Posting-line parsing -/

private def stripStatus (s : String) : String :=
  if s.startsWith "* " || s.startsWith "! " then
    trimS (s.drop 2).toString
  else s

/-- Recognize the account field's kind and inner name. -/
private def accountKind (line : Nat) (s : String) :
    Except String (PostKind × String) :=
  let closing (opn cls : Char) (k : PostKind) : Except String (PostKind × String) :=
    let inner := (s.drop 1).toString
    if inner.endsWith (String.ofList [cls]) then
      pure (k, trimS (String.ofList inner.toList.dropLast))
    else err line s!"unclosed '{opn}' in account '{s}'"
  if s.startsWith "(" then closing '(' ')' .virtualUnbal
  else if s.startsWith "[" then closing '[' ']' .virtualBal
  else if s.startsWith "<" then closing '<' '>' .deferred
  else pure (.real, s)

/-- Consume a balanced-bracket span: returns (inner, rest-after-close). -/
private def takeBalanced (opn cls : Char) : List Char → Option (List Char × List Char)
  | c :: rest =>
      if c != opn then none else
      let rec go (depth : Nat) (acc : List Char) : List Char → Option (List Char × List Char)
        | [] => none
        | x :: xs =>
            if x == cls then
              match depth with
              | 0 => some (acc.reverse, xs)
              | d + 1 => go d (x :: acc) xs
            else if x == opn then go (depth + 1) (x :: acc) xs
            else go depth (x :: acc) xs
      go 0 [] rest
  | [] => none

/-- What `annotLoop` reads from the tail of an amount; each field is
    the argument of `annotLoop` that bears its name. -/
private structure AnnotTail where
  lot : Option (Amount × Bool)
  cost : Option Amount
  teach : List (String × Nat)
  costDecs : Nat
  annotated : Bool
  fixated : Bool
  ownLot : Bool
  /-- the cost is a per-unit `@`, not a total `@@` -/
  perUnit : Bool
  /-- the decimals of the kept lot's literal, and whether it is a
      `{{total}}` -/
  lotLit : Option (Nat × Bool)

/-- Consume the annotation/cost/assertion tail of an amount:
    `{lot} [date] (note) @ P / @@ T / = ASSERT` in any order. -/
private partial def annotLoop (ctx : AmtCtx) (line : Nat) (a : Amount)
    (tail : String) (lot : Option (Amount × Bool)) (cost : Option Amount)
    (teach : List (String × Nat) := []) (afterCost : Bool := false)
    (costDecs : Nat := 0) (afterAssert : Bool := false)
    (annotated : Bool := false) (fixated : Bool := false)
    (ownLot : Bool := false) (perUnit : Bool := false)
    (lotLit : Option (Nat × Bool) := none) :
    Except String AnnotTail := do
  -- `annotated`, `fixated` and `ownLot`: an annotation met before any
  -- cost or assertion belongs to the posting's own amount; after a
  -- cost it annotates the cost amount, after an assertion the
  -- assertion amount (textual_xacts.cc:756-757). `ownLot` says that
  -- the lot kept was met while `own` held
  let own := !afterCost && !afterAssert
  let t := trimS tail
  if t.isEmpty || t == "." then
    pure { lot, cost, teach, costDecs, annotated, fixated, ownLot, perUnit,
           lotLit }
  else if t.startsWith "{" then
    -- `{{total}}` and `{per-unit}` lot prices, possibly `{=fixated}`;
    -- lots parse with PARSE_NO_MIGRATE — no precision teaching
    let (inner, rest) ←
      match takeBalanced '{' '}' t.toList with
      | some (i, r) => pure (i, r)
      | none => err line s!"unclosed lot price in '{t}'"
    let (inner, total) :=
      match takeBalanced '{' '}' inner with
      | some (i2, _) => (i2, true)     -- {{TOTAL}}
      | none => (inner, false)
    let innerS := trimS (String.ofList inner)
    let fix := innerS.startsWith "="
    let innerS := if fix then trimS (innerS.drop 1).toString else innerS
    let pr ← parseAmount ctx line innerS
    let lotAmt := if total && a.q != 0 then
        Amount.mk pr.amount.comm (pr.amount.q / (if a.q < 0 then -a.q else a.q))
      else pr.amount
    -- keep the FIRST lot: later braces belong to a cost amount's own
    -- annotation (feat-commodity_swap)
    -- a lot after a cost annotates the COST amount, not the posting
    -- (regress/1217)
    let lot' :=
      if afterCost then lot
      else match lot with
        | some l => some l
        | none => some (lotAmt, fix)
    let lotLit' := if afterCost || lot.isSome then lotLit
      else some (pr.decimals, total)
    -- while `own` holds, every lot taken so far is the posting's own
    annotLoop ctx line a (String.ofList rest) lot' cost teach afterCost costDecs
      (afterAssert := afterAssert) (annotated := annotated || own)
      (fixated := if own then lot'.any (·.2) else fixated)
      (ownLot := if own then lot'.isSome else ownLot) (perUnit := perUnit)
      (lotLit := lotLit')
  else if t.startsWith "[" then
    match takeBalanced '[' ']' t.toList with
    | some (_, rest) =>
        annotLoop ctx line a (String.ofList rest) lot cost teach afterCost costDecs
          (afterAssert := afterAssert) (annotated := annotated || own)
          (fixated := fixated) (ownLot := ownLot) (perUnit := perUnit)
          (lotLit := lotLit)
    | none => err line s!"unclosed lot date in '{t}'"
  else if t.startsWith "(" && !(t.startsWith "(@") then
    match takeBalanced '(' ')' t.toList with
    | some (_, rest) =>
        annotLoop ctx line a (String.ofList rest) lot cost teach afterCost costDecs
          (afterAssert := afterAssert) (annotated := annotated || own)
          (fixated := fixated) (ownLot := ownLot) (perUnit := perUnit)
          (lotLit := lotLit)
    | none => err line s!"unclosed lot note in '{t}'"
  else if t.startsWith "(@@)" || t.startsWith "@@" then
    let off := if t.startsWith "(@@)" then 4 else 2
    let rest0 := trimS (t.drop off).toString
    -- `@@ =` fixates the total cost (1794); balancing is unchanged
    let rest0 := if rest0.startsWith "=" then trimS (rest0.drop 1).toString
      else rest0
    let pr ← parseAmount ctx line rest0
    let mag := if pr.amount.q < 0 then -pr.amount.q else pr.amount.q
    let signed := if a.q < 0 then -mag else mag
    annotLoop ctx line a pr.tail lot (some ⟨pr.amount.comm, signed⟩) teach true
      (max costDecs pr.decimals) (afterAssert := afterAssert)
      (annotated := annotated) (fixated := fixated) (ownLot := ownLot)
      (perUnit := false) (lotLit := lotLit)
  else if t.startsWith "(@)" || t.startsWith "@" then
    -- per-unit costs round at the cost literal's own precision,
    -- posting by posting (regress/1125); `@ =` fixates (1794). A cost
    -- literal teaches no display precision, since C++ parses it
    -- without migration (textual_xacts.cc:691, 693-694): its decimals
    -- reach only `costDecs`
    let off := if t.startsWith "(@)" then 3 else 1
    let rest0 := trimS (t.drop off).toString
    let rest0 := if rest0.startsWith "=" then trimS (rest0.drop 1).toString
      else rest0
    let pr ← parseAmount ctx line rest0
    annotLoop ctx line a pr.tail lot
      (some ⟨pr.amount.comm, pr.amount.q * a.q⟩) teach true
      (max costDecs pr.decimals) (afterAssert := afterAssert)
      (annotated := annotated) (fixated := fixated) (ownLot := ownLot)
      (perUnit := true) (lotLit := lotLit)
  else if t.startsWith "=" then
    -- assertion: the C++ side checks it; positive tests pass it, but
    -- the literal still teaches display precision (1699). C++ parses
    -- the assertion amount with its own annotations
    -- (textual_xacts.cc:756-757), so a later `{lot}`, `[date]` or
    -- `(note)` sets neither flag nor `ownLot`; the lot reading above
    -- still takes a lot written there as the posting's own for
    -- `lotVal`, a reading that no C++ test exercises (regress/2318
    -- writes the posting's lot first)
    let pr ← parseAmount ctx line (trimS (t.drop 1).toString)
    let teach := if pr.decimals <= 6 then
        (pr.amount.comm, pr.decimals) :: teach else teach
    annotLoop ctx line a pr.tail lot cost teach afterCost costDecs
      (afterAssert := true) (annotated := annotated) (fixated := fixated)
      (ownLot := ownLot) (perUnit := perUnit) (lotLit := lotLit)
  else
    err line s!"trailing junk after amount '{t}'"

/-- The parsed amount field of a posting. -/
private structure AmountField where
  amount : Option Amount := none
  /-- the `@`/`@@` cost, adjusted by the rounded gain of a lot priced
      in the cost's commodity (pass 1); in a periodic template the cost
      as written -/
  costVal : Option Amount := none
  /-- the lot price times the quantity (pass 2) -/
  lotVal : Option Amount := none
  /-- the lot price per unit (`PostSpec.lotUnit`) -/
  lotUnit : Option Amount := none
  /-- `PostSpec.lotTotal` -/
  lotTotal : Bool := false
  assignTarget : Option Amount := none
  learned : Option (String × Bool) := none
  decimals : Nat := 0
  isExpr : Bool := false
  teach : List (String × Nat) := []
  costDecs : Nat := 0
  /-- the rounded gain of a lot priced in the cost's commodity, bound
      as `capital_gain` in automated-transaction expressions
      (`applyAutos`). It is computed in a periodic template too, where
      it reaches only the flows that `flushPending` discards. -/
  gainVal : Option Amount := none
  annotated : Bool := false
  fixated : Bool := false
  /-- `PostSpec.costPrec` -/
  costPrec : Nat := 0

/-- Parse the amount field of a posting (everything after the
    account): amount, lot annotations, cost, assertion/assignment.
    `periodic` marks a posting of a periodic template, whose cost
    books no lot gain. -/
private def parseAmountField (ctx : AmtCtx) (line : Nat) (field : String)
    (periodic : Bool := false) : Except String AmountField := do
  let field := trimS field
  if field.isEmpty then
    pure {}
  else if field.startsWith "=" then
    -- balance assignment (amountless posting); lot annotations on the
    -- target are parsed and dropped (1603), and the flags stay false
    -- (the departure recorded at `PostSpec.fixated`)
    let r ← parseAmount ctx line (trimS (field.drop 1).toString)
    let _ ← annotLoop ctx line r.amount r.tail none none
    pure { assignTarget := some r.amount, learned := r.learned
           decimals := r.decimals
           teach := if r.decimals <= 6 then [(r.amount.comm, r.decimals)] else [] }
  else do
    -- a leading lot `{P} AMT` has no witness: C++ rejects the form
    -- ("No quantity specified for amount", amount.cc:1665), since `{`
    -- cannot begin a commodity symbol (commodity.cc:331-349) and no
    -- quantity is read. The oracle accepts it, a fail-open, and reads
    -- its lot and flags as it reads a lot written after the amount.
    let (preLot, field) ←
      if field.startsWith "{" then
        match takeBalanced '{' '}' field.toList with
        | some (inner, rest) => do
            let innerS := trimS (String.ofList inner)
            let fix := innerS.startsWith "="
            let innerS := if fix then trimS (innerS.drop 1).toString else innerS
            let pr ← parseAmount ctx line innerS
            pure (some (pr.amount, fix), trimS (String.ofList rest))
        | none => err line s!"unclosed leading lot in '{field}'"
      else pure (none, field)
    let r ← parseAmount ctx line field
    let a := r.amount
    -- Two more forms that C++ rejects are accepted, both fail-open: an
    -- annotation after an amount expression, `(EXPR) {lot}`, which C++
    -- leaves unparsed and reports as an unexpected character
    -- (textual_xacts.cc:908-910), and a second lot price, date or
    -- note, which C++ reports as more than one (annotate.cc:157, 193,
    -- 249). annotLoop reads the first as it reads an annotation on a
    -- plain amount, and of two lot prices it keeps the first.
    let { lot, cost, teach, costDecs, annotated, fixated, ownLot, perUnit,
          lotLit } ←
      annotLoop ctx line a r.tail preLot none (annotated := preLot.isSome)
        (fixated := preLot.any (·.2)) (ownLot := preLot.isSome)
    -- the precision of the cost amount, for the widened zero test of
    -- `finalizeXact`: C++ keeps a cost at its literal's precision and,
    -- for a per-unit `@`, multiplies it by the amount, which adds the
    -- amount's precision (textual_xacts.cc:699-710, amount.cc:720).
    -- `Parse` does not track the precision of an expression amount,
    -- whose division C++ extends by six places (amount.cc:805-812);
    -- an expression that divides, or whose value its literals'
    -- decimals cannot represent, counts six places more than those
    -- decimals (regress/1114's `(1/9 FOO)` has precision 6). The
    -- docstring of `zeroTestPrec` lists the measured departures
    let divides := match takeBalanced '(' ')' field.toList with
      | some (inner, _) => inner.contains '/'
      | none => false
    let amtPrec :=
      if field.startsWith "("
          && (divides || roundAt r.decimals a.q != a.q) then
        r.decimals + 6
      else r.decimals
    let costPrec := if perUnit then costDecs + amtPrec else costDecs
    -- Phase 6 raises it (xact.cc:693-729): when the posting's own lot
    -- price is in the cost's commodity and the basis, the lot price
    -- times the amount kept unrounded (pool.cc:502), differs from the
    -- cost at all (xact.cc:696), C++ adds the gain to the cost, and the
    -- sum keeps the larger precision (amount.cc:630-632) even when the
    -- gain rounds to zero. A `{P}` price counts its own literal's
    -- decimals (annotate.cc:187), where C++ can reuse the annotated
    -- commodity of an earlier literal of equal value (pool.cc:200), a
    -- departure the docstring of `zeroTestPrec` records; a `{{T}}`
    -- price is divided by the amount, which adds the amount's
    -- precision and six places (amount.cc:812), and rounded at the
    -- amount's precision, the commodity's and six
    -- (amount.cc:1908-1923). Only an amount with a commodity is
    -- annotated (amount.cc:1908), a periodic template skips Phase 6
    -- (see `costVal`), and a leading lot, which C++ rejects, records
    -- no `lotLit`
    let costPrec := match lot, lotLit, cost with
      | some (p, _), some (d, total), some c =>
          if periodic || !ownLot || a.comm == "" || p.comm != c.comm then
            costPrec
          else
            let (unit, prec) :=
              if total then
                (roundAt (r.decimals + (ctx.precs.lookup p.comm).getD 0 + 6)
                  p.q, d + r.decimals + 6)
              else (p.q, d)
            if unit * a.q != c.q then max costPrec (prec + amtPrec)
            else costPrec
      | _, _, _ => costPrec
    -- xact.cc phase 4/6: a fixated lot with no cost derives the cost
    -- from the annotation; a lot WITH a cost books the rounded
    -- gain/loss (basis - cost, rounded at commodity precision plus
    -- the amount's decimals) into the effective cost. Phase 6 runs
    -- only for a transaction with a date (`if (has_date())`,
    -- xact.cc:522, item.h:262), and a periodic template never sets
    -- the `_date` it inherits from item_t (xact.h:434, item.h:161),
    -- so a template keeps the cost as written
    let gainVal := match lot, cost with
      | some (p, _), some c =>
          if p.comm == c.comm then
            let gl := (p.q * a.q) - c.q
            some (Amount.mk c.comm
              (roundAt ((ctx.precs.lookup c.comm).getD 0 + r.decimals) gl))
          else none
      | _, _ => none
    -- The gain enters the weight of the posting in its own pool: the
    -- second transaction of baseline/opt-base, `-40h {$20} @ $100.00`,
    -- balances through it in the first pass of `balancePool`. This
    -- departs from C++ in two cases, each of which can fail either
    -- way. C++ adds the gain of a bracket-virtual posting to the real
    -- balance (xact.cc:712-713) and tests the bracket-virtual balance
    -- with the cost as written (xact.cc:322-325, 973-979): a
    -- bracket-virtual `10 AAA {$5} @ $6` against a bracket-virtual
    -- `-$50` is accepted here and rejected by C++ with a remainder of
    -- `$-10` (fail-open), and against a bracket-virtual `-$60` beside a
    -- real `$10` it is rejected here and accepted by C++
    -- (fail-closed). C++ keeps no lot on an amount with no commodity
    -- (amount.cc:1908) and so adds no gain for it: `10 {$5} @ $6`
    -- against `-$50` is accepted here and rejected by C++ with a
    -- remainder of `$10` (fail-open), and against `-$60` it is
    -- rejected here and accepted by C++ (fail-closed)
    let costVal := match lot, cost with
      | some (p, _), some c =>
          if periodic then some c
          else if p.comm == c.comm then
            let basis := p.q * a.q
            let gl := basis - c.q
            let glR := roundAt ((ctx.precs.lookup c.comm).getD 0 + r.decimals) gl
            some (Amount.mk c.comm (c.q + glR))
          else some c
      | _, _ => cost
    let lotVal := lot.map fun (p, _) => Amount.mk p.comm (p.q * a.q)
    -- C++ keeps an annotation only on an amount with a commodity
    -- (amount.cc:1908); the lot of a bare number still reaches lotVal.
    -- A lot written only after a balance assertion annotates the
    -- assertion amount (textual_xacts.cc:756-757), and so it gives the
    -- posting's amount no lot key. `lotTotal` marks the posting's own
    -- lot written as a total (`lotLit`), on an amount with a commodity
    let hasComm := a.comm != ""
    pure { amount := some a, costVal, lotVal
           lotUnit := if ownLot then lot.map (·.1) else none
           lotTotal := hasComm && ownLot && lotLit.any (·.2)
           learned := r.learned
           decimals := r.decimals, isExpr := field.startsWith "(", teach
           costDecs, gainVal, annotated := hasComm && annotated
           fixated := hasComm && fixated, costPrec }

private def parsePosting (st : St) (line : Nat) (raw : String)
    (periodic : Bool := false) :
    Except String (Option PostSpec × Option (String × Bool) ×
      Option String × Nat × Bool × List (String × Nat)) := do
  let (content, note) := splitNote raw
  let content := stripStatus (trimS content)
  if content.isEmpty then
    pure (none, none, none, 0, false, [])
  else if !periodic && (content.startsWith "assert "
      || content.startsWith "check " || content.startsWith "expr ") then
    -- inline expression check/eval: verified/discarded by the C++ side.
    -- Only a dated transaction has this branch (parse_xact,
    -- textual_xacts.cc:1107-1125). C++ collects the postings of a
    -- periodic template with parse_posts, which hands every line not
    -- beginning with `;` to parse_post (textual_xacts.cc:951-952), so
    -- in a template such a line is a posting to the account it names
    pure (none, none, none, 0, false, [])
  else do
    let (acctField, amtField) := splitField content
    let (kind, name) ← accountKind line acctField
    let account := resolveAccount st name
    match amtField with
    | none => pure (some { line, account, kind, note }, none, none, 0, false, [])
    | some f => do
        let af ← parseAmountField st.amt line f periodic
        pure (some { line, account, kind, note, amount := af.amount
                     costVal := af.costVal, lotVal := af.lotVal
                     lotUnit := af.lotUnit, lotTotal := af.lotTotal
                     assignTarget := af.assignTarget, amtDecs := af.decimals
                     costDecs := af.costDecs, gainVal := af.gainVal
                     annotated := af.annotated, fixated := af.fixated
                     costPrec := af.costPrec },
              af.learned, af.amount.map (·.comm), af.decimals, af.isExpr,
              af.teach)

/-! ## Transaction finalization -/

/-- Extend a balanced transaction by its automated transactions, one
    rule at a time, as C++ runs `extend_xact` for each rule
    (journal.cc:659-661, xact.cc:1426-1691). Besides the extended
    postings it returns one batch per rule of `st.autos`, in order and
    empty for a rule that is inactive or matches nothing, of one triple
    per generated posting: the matched posting, the generated posting,
    and a flag set when the template posting has no fixed amount and the
    generated amount keeps the matched posting's commodity. The flag
    covers the bare-number multiplier, with which C++ copies the
    matched amount's annotation, and also an amount expression whose
    value is in the matched commodity, which C++ annotates only when
    that value carries the annotation. It does not cover a template
    amount without a commodity that is not a bare number, such as
    `1 @ $1`, by which C++ also multiplies (xact.cc:1546-1547) and
    which the template parser keeps as a fixed amount, a departure
    recorded beside that parser. The flag is a precondition of the
    cost that C++ derives from the annotation, not that cost itself:
    C++ derives one only when the template posting has no cost and the
    matched posting has one, written, computed by Phase 3 in the
    orientation taken, or derived by Phase 4 from a fixated lot price,
    so the full condition depends on the orientation of the pool and
    on Phase 4 (the comment in the loop gives the C++ lines). -/
private def applyAutos (st : St) (xdate : Option Int) (payee : String)
    (code : String) (dateStr : String)
    (xactNotes : String) (posts : List PostSpec) :
    List PostSpec × List (List (PostSpec × PostSpec × Bool)) :=
  -- `TAG:: value` / `TAG: value` metadata for predicates/templates
  let tagValuesOf := fun (notes : String) =>
    (notes.splitOn ";").filterMap fun seg =>
      match seg.splitOn "::" with
      | [k, v] => some (trimS k, trimS v)
      | _ =>
          -- single-colon form `; Key: Value` (783)
          let segT := trimS seg
          match segT.splitOn ": " with
          | [k, v] =>
              if !k.isEmpty && (k.toList.all fun c =>
                  c.isAlphanum || c == '_' || c == '-') then
                some (trimS k, trimS v)
              else none
          | _ => none
  let _tagValues : List (String × String) := tagValuesOf xactNotes
  let tagNames := fun (notes : String) =>
    -- `:A:B:` bare-tag runs plus valued tags
    (((notes.splitOn " ").flatMap (·.splitOn ";")).flatMap fun w =>
      let w := trimS w
      if w.length ≥ 3 && w.startsWith ":" && w.endsWith ":" then
        ((w.drop 1).toString.toList.dropLast |> String.ofList).splitOn ":"
      else []) ++ (tagValuesOf notes).map (·.1)
  let dateOk := fun (dateTerms : List (DateCmp × Int)) =>
    dateTerms.all fun (cmp, bound) =>
      match xdate with
      | none => false
      | some d =>
          match cmp with
          | .ge => d ≥ bound
          | .gt => d > bound
          | .le => d ≤ bound
          | .lt => d < bound
  -- rules outer, candidate postings inner; generated posts join the
  -- CURRENT set (quantifiers see them: cov2-fn-all) but are never
  -- themselves candidates (cov2-any-all)
  let matchBranch := fun (xactNotes : String) (cur : List PostSpec)
      (b : PredSpec) (p : PostSpec) (a : Amount) =>
    b.accRxs.all (fun rx => regexSearch rx p.account)
      && b.negRxs.all (fun rx => !(regexSearch rx p.account))
      && dateOk b.dateTerms
      && (b.payeeRx.all fun rx => regexSearch rx payee)
      && (b.commentRx.all fun rx => regexSearch rx p.note)
      && (b.commodityEq.all fun c => c == a.comm)
      && (b.amountTerms.all fun (cmp, bound) =>
            match cmp with
            | .ge => a.q >= bound
            | .gt => a.q > bound
            | .le => a.q <= bound
            | .lt => a.q < bound
            | .eq => a.q == bound)
      && (b.tagReq.all fun (rx, val?) =>
            (tagNames (xactNotes ++ ";" ++ p.note)).any fun nm =>
              regexSearch rx nm
                && (val?.all fun v =>
                      ((tagValuesOf (xactNotes ++ ";" ++ p.note)).lookup nm)
                        == some v))
      && (b.negTag.all fun rx =>
            !((tagNames (xactNotes ++ ";" ++ p.note)).any fun nm =>
                regexSearch rx nm))
      && (b.dateRx.all fun rx => regexSearch rx dateStr)
      && (b.codeRx.all fun rx => regexSearch rx code)
      && (b.acctTotal.all fun (nm, cmp, bound) =>
            let tot := st.balances.foldl (init := (0 : ℚ))
              fun acc ((a, _), v) => if a == nm then acc + v else acc
            match cmp with
            | .ge => tot >= bound
            | .gt => tot > bound
            | .le => tot <= bound
            | .lt => tot < bound
            | .eq => tot == bound)
      && (b.anyRx.all fun (rx, realOnly) =>
            cur.any fun p' =>
              (!realOnly || p'.kind == .real) && regexSearch rx p'.account)
      && (b.allRx.all fun rx =>
            cur.all fun p' => regexSearch rx p'.account)
  let instantiate := fun (xactNotes : String) (p : PostSpec) (a : Amount) =>
    fun (ap : AutoPost) =>
      let amt? : Option Amount :=
        match ap.exprSrc with
        | some src =>
            -- substitute tag("K") with the tag's value (1937)
            let src := (tagValuesOf (xactNotes ++ ";" ++ p.note)).foldl
                (init := src) fun acc (k, v) =>
              String.intercalate v
                (acc.splitOn ("tag(\"" ++ k ++ "\")"))
            let bAmt := p.costVal.getD a
            let gAmt := p.gainVal.getD ⟨(p.costVal.getD a).comm, 0⟩
            let ctx := { st.amt with
              precs := st.precisions
              defines := ("amount", a) :: ("a", a) :: ("b", bAmt)
                :: ("cost", bAmt) :: ("capital_gain", gAmt)
                :: st.amt.defines }
            match parseExprAmount ctx p.line src.toList with
            | .ok (v, _, _) =>
                -- commodity-less expression results are
                -- multipliers (615)
                some (if v.comm == "" then ⟨a.comm, v.q * a.q⟩ else v)
            | .error _ => none
        | none =>
            match ap.fixed with
            | some f => some f
            | none => some ⟨a.comm, ap.mult * a.q⟩
      amt?.map fun amt =>
        let sub := fun (pat rep acc : String) =>
          if (acc.splitOn pat).length > 1 then
            String.intercalate rep (acc.splitOn pat)
          else acc
        let acct := ap.account
        let acct := sub "$account" p.account acct
        let acct := sub "%(account)" p.account acct
        let acct := sub "%(payee)" payee acct
        { line := p.line, account := acct, kind := ap.kind
          amount := some (canonAmt st amt) : PostSpec }
  Id.run do
    let mut cand := posts.toArray
    let mut extra : List PostSpec := []
    let mut batches : List (List (PostSpec × PostSpec × Bool)) := []
    for rule in st.autos do
      if !rule.active then
        batches := batches ++ [[]]
        continue
      let mut batch : List (PostSpec × PostSpec × Bool) := []
      for i in [0:cand.size] do
        let p : PostSpec := cand[i]!
        match p.kind, p.amount with
        | PostKind.real, some a =>
            let cur := cand.toList ++ extra
            if rule.branches.any fun b => matchBranch xactNotes cur b p a then
              let gen := rule.posts.filterMap fun ap =>
                (instantiate xactNotes p a ap).map fun g => (ap, g)
              extra := extra ++ gen.map (·.2)
              -- the flag of each triple: the template posting has no
              -- fixed amount and the generated amount keeps the matched
              -- posting's commodity. That covers the bare-number
              -- multiplier, with which C++ multiplies the matched amount,
              -- annotation included (xact.cc:1546-1547), and derives the
              -- generated posting's cost from that annotation when the
              -- matched posting has a cost and the template posting none
              -- (xact.cc:1611-1627).
              -- A matched posting whose cost Phase 3 computed carries the
              -- lot price that Phase 6 gives it (xact.cc:454-465,
              -- 802-811), so that condition depends on the orientation.
              -- Phase 4 also gives a cost to every must-balance posting
              -- with a fixated lot price and no cost while the balance
              -- holds two or more entries after Phase 3 (xact.cc:475-518),
              -- as it does beside a fixated top posting, which Phase 3
              -- never converts (xact.cc:401-403): under `= /Assets:A/`
              -- with `Assets:X 0.5` and `Assets:Y $-25`, C++ accepts
              -- `10 AAA {=$5}` against `$-50`, deriving `$25` for the
              -- `5 AAA {=$5}` of `Assets:X`, and with `Assets:Y $-20` it
              -- rejects the transaction with the remainder `$5`.
              -- An amount expression whose value is in the matched
              -- commodity counts as well, although C++ takes such a
              -- value as it stands (xact.cc:1549), annotated only when
              -- the expression's value carries the annotation
              batch := batch ++ gen.map fun (ap, g) =>
                (p, g, ap.fixed.isNone && g.amount.map (·.comm) == some a.comm)
              -- the template's own note tags the matched posting, so
              -- later rules see it there (1984's :BUDGETED: guard)
              if !rule.noteTag.isEmpty then
                cand := cand.set! i { p with note := p.note ++ rule.noteTag }
        | _, _ => pure ()
      batches := batches ++ [batch]
    pure (cand.toList ++ extra, batches)

/-- A C++ balance key: the commodity, with the lot price (its
    commodity, its price per unit and its fixated flag) when the amount
    carries one. -/
private abbrev LotKey := String × Option (String × ℚ × Bool)

/-- The value that C++ accumulates as the real balance in Phase 1 of
    `finalize` (xact.cc:333, through `add_or_set_value`,
    value.h:1025-1031): null before the first amount, a single amount
    while every amount has one key, and a balance of keyed entries from
    the first amount of another key on. -/
private inductive CppSum where
  | null
  | amount (k : LotKey) (q : ℚ)
  | balance (entries : List (LotKey × ℚ))

/-- Add one keyed amount as C++ does. An amount absorbs an amount of
    its own key (value.cc:600-607); an amount of another key turns it
    into a balance, which keeps the old entry only when it is not
    exactly zero (value.cc:1548, balance.h:128-134). A balance ignores
    an exactly zero amount and otherwise accumulates per key, and it
    never erases an entry that addition brings to zero
    (balance.cc:118-133); only subtraction erases one
    (balance.cc:165-170). -/
private def CppSum.add (s : CppSum) (k : LotKey) (q : ℚ) : CppSum :=
  let addEntry := fun (es : List (LotKey × ℚ)) =>
    if q == 0 then es
    else match es.lookup k with
      | some _ => es.map fun (k', v) => if k' == k then (k', v + q) else (k', v)
      | none => es ++ [(k, q)]
  match s with
  | .null => .amount k q
  | .amount k' v =>
      if k' == k then .amount k (v + q)
      else .balance (addEntry (if v == 0 then [] else [(k', v)]))
  | .balance es => .balance (addEntry es)

/-- One orientation in which C++'s Phase 3 can take a balancing pool
    and accept it: the conversion it makes, if any, and what it leaves
    for the final zero test. -/
private structure PoolCandidate where
  /-- the two entries of the real balance that Phase 3 converts, `x`
      first, or `none` when this orientation makes no conversion -/
  exchange : Option ((LotKey × ℚ) × (LotKey × ℚ)) := none
  /-- what remains of the pool's balance for the zero test of Phase 8,
      as a list of commodities with nonzero remainders. In a candidate
      of `impliedExchange` two entries of one commodity that differ in
      their lots appear apart, as C++ keeps them; in a candidate that
      `balancePool` builds from its own residuals they merge by
      commodity (`PoolResult.candidates`) -/
  residual : List (String × ℚ) := []

/-- What C++'s Phase 3 and the zero test of Phase 8 make of a real
    balance of two entries in one orientation (`impliedExchange`). -/
private inductive Verdict where
  /-- C++ makes no conversion; the entries that Phase 8 then tests,
      exact zeros dropped, when each of them passes, and `none` when
      one fails -/
  | declines (left : Option (List (String × ℚ)))
  /-- C++ converts, and the transaction fails -/
  | fails
  /-- C++ converts, and every entry that Phase 8 tests passes; those
      entries, exact zeros dropped -/
  | passes (left : List (String × ℚ))

/-- What `impliedExchange` finds C++'s Phase 3 doing with a real
    balance. -/
private inductive Exchange where
  /-- C++ converts, and the balance it leaves passes Phase 8 in every
      order that C++ can take: one candidate per orientation -/
  | converts (cands : List PoolCandidate)
  /-- C++ converts, and the transaction fails -/
  | fails
  /-- C++ makes no conversion -/
  | declines
  /-- C++'s verdict depends on the unspecified order of its two
      entries: a candidate for each orientation, converting or not,
      under which C++ accepts the pool, possibly none -/
  | unordered (cands : List PoolCandidate)

/-- What `balancePool` makes of a pool that it accepts. -/
private structure PoolResult where
  /-- the pool's postings, its elided posting replaced by the postings
      that complete it, or the bucket's postings added -/
  posts : List PostSpec
  /-- one candidate per admissible orientation of Phase 3, an
      orientation being admissible when C++ can take it and accept the
      pool, as the oracle models C++: a single candidate with no
      conversion and an empty residual when the pool balances exactly,
      through its elided posting or through the bucket; the candidates
      of `impliedExchange` when the implicit exchange accepts the pool
      or when its verdict depends on the order of the two entries; and
      otherwise a single candidate with no conversion, whose residual
      is the exact residual when the zero test or the per-unit cost
      allowance accepts it, and the residual of the second pass when
      that pass does. The allowance leaves the residual unadjusted,
      since C++ adds its adjustment for the rounding of per-unit costs
      only to the balance that Phase 8 tests, and changes no cost
      (xact.cc:898-929, regress/1125).

      The candidates that do not come from `impliedExchange` rest on the
      residuals of `balancePool`, which merge by commodity, or value,
      the lots that C++ keeps apart (annotate.h:120-125), and so they
      inherit the lot departures listed at `impliedExchange`. For a lot
      shape listed there as accepted here and rejected by C++, no
      orientation is admissible for C++, and the candidate records only
      the oracle's own acceptance: `10 A {$1}` against `-10 A` has the
      single empty candidate, while C++ rejects it. They include the
      candidate of an orientation that the top posting's key decides
      and in which Phase 3 makes no conversion, for which
      `impliedExchange` reports only `.declines`: under
      `format 1.00 A`, `0.004 A {$1}` against `-0.001 A` leaves
      `0.003 A` here, while C++ tests `0.004 A {$1}` and `-0.001 A`
      apart, and both pass.

      Each residual is the balance that Phase 8 tests. The `verify()`
      that follows an automated transaction (xact.cc:1040-1110,
      1683-1684) sums instead the costs that Phase 6 leaves, and these
      differ for an exchange of two lots priced in one commodity, whose
      converted posting has its cost rewritten into that commodity
      (xact.cc:764-774): `10 AAA {$5}` against `-5 BBB {$10}` leaves the
      empty residual here, and C++ accepts it, but beside an automated
      transaction that adds `Assets:X 1` and `Assets:Y -1` to the
      `AAA` posting C++ rejects it with the remainder `$-50` and
      `10 AAA {$5}` -/
  candidates : List PoolCandidate := [{}]
  /-- set when three conditions hold: the pool reaches the test of the
      implicit exchange, which it does only with no elided posting, a
      nonzero exact residual and no completion by the bucket; Phase 3's
      verdict there depends on the unspecified order of its two entries
      (`Exchange.unordered`); and `balancePool` accepts the pool, by the
      earlier rule that passes a residual in two commodities or by any
      other test. `candidates` then lists only the orientations under
      which C++ accepts the pool, possibly none, and in any other
      orientation C++ rejects the transaction. A pool that balances exactly keeps the
      single empty candidate and leaves this unset even where its lot
      keys make C++'s verdict depend on the order, one of the lot
      departures that `candidates` inherits: under `format 1.00 A`,
      `10 A {$1}` against `-10 A` beside bracket-virtual postings of
      `1 B {$1}` and `-1 B {$1}` is rejected by C++ with the lot first
      and accepted with the plain units first. -/
  orderDependent : Bool := false

/-- The implicit exchange of C++'s `finalize`, Phase 3
    (src/xact.cc:374-473 at 76b9dc2b2). With no null posting, a real
    balance of exactly two entries is converted at the rate it implies:
    with `x` the entry of the top posting's key and `y` the other,
    every must-balance posting of the commodity of `x` takes the
    computed cost in the commodity of `y`. The result is `.converts`
    when C++ makes that conversion and the balance it leaves passes
    Phase 8, `.fails` when C++ makes it and the transaction fails,
    `.declines` when C++ makes no conversion, and `.unordered` when the
    verdict depends on an order that C++ leaves unspecified; the last
    two leave the pool to the tests of `balancePool`, and `.unordered`
    carries the orientations, converting or not, under which C++
    accepts the pool. A failing verdict
    is the one C++ gives without `--permissive`, whose rescue of a
    computed balance assignment (xact.cc:941-952) the oracle does not
    model anywhere. `xact` is every posting of the transaction once
    assignments are resolved, and `pool` its real pool in posting order.

    C++ converts only when all of these hold, each from Phase 3 unless
    noted:
    - no posting of any kind carries an explicit cost (`saw_cost`,
      xact.cc:395-398); C++ computes no cost of its own before Phase 3;
    - the real balance, accumulated in posting order as C++ accumulates
      it (`CppSum`), is a balance of exactly two entries (xact.cc:380),
      neither of them exactly zero (the guard of issue #1789,
      xact.cc:413-421, test/regress/1789.test). Entries are keyed as
      C++ keys them, by the reduced commodity with its lot price per
      unit (`PostSpec.lotUnit`) and fixated flag (annotate.h:120-125),
      and an amount with no commodity has no lot (amount.cc:1908). A
      key that nets to zero before a second key arrives is dropped,
      but one that nets to zero later remains as a zero entry, and C++
      then makes no conversion;
    - the top posting, the last annotated must-balance posting with an
      amount, else the first (xact.cc:386-393), carries no fixated lot
      price (xact.cc:401-404);
    - `x` and `y` are not one base commodity with a lot price on `x`
      only (xact.cc:434-449, test/regress/1029.test).
    When the top posting's key is not an entry of the real balance, for
    instance because its commodity nets to zero or because it is a
    bracket-virtual posting, C++ takes the two entries in the
    unspecified order of an unordered map (balance.h:99) and swaps them
    when the first is not the top posting's (xact.cc:422-423). A
    verdict is then given only when both orientations give the same
    one, and otherwise the result is `.unordered`, for which
    `balancePool` keeps the rule that preceded this predicate: a real
    residual in exactly two commodities passes, whether its lots are
    ignored or valued.

    The conversion first reduces the amount of every posting
    (xact.cc:459), which throws for a posting with no amount
    (amount.cc:1153-1155), so that an elided bracket-virtual posting or
    an amountless paren-virtual one makes C++ reject the transaction.
    When `y` has no commodity and `x` has one, the rate `y/x` takes the
    commodity of `x` (amount.cc:814-815), and so does the cost of every
    converted posting (amount.cc:727-744), which Phase 6 then rejects
    as a cost in its posting's own commodity (xact.cc:679-681).
    Otherwise every must-balance posting of the key of `x`,
    bracket-virtual ones included, leaves the real balance and its cost
    of `|y/x|` times its quantity enters it (xact.cc:454-465). What
    remains of `y` is zero when the two sides have opposite signs and
    `2y` when they agree; what remains of `x` is zero unless the
    bracket-virtual postings of its key fail to net to zero. Phase 6
    then books a gain for each converted posting whose lot price is in
    a commodity `z` related to `y`, rounded at the display precision of
    `z` plus the decimals of the posting's quantity:
    - when `y` is `z` with no lot price, the gain is the lot basis less
      the computed cost (xact.cc:693-713), and it joins the entry of
      `y` even when it rounds to zero at display precision, since the
      test at xact.cc:696 is exact (amount.cc:1407);
    - when `y` carries a lot price in `z`, the gain is the lot value of
      the posting less the lot value of its cost (xact.cc:735-763), and
      it is booked in `z` only when it does not show as zero at display
      precision (xact.cc:762).
    Every entry must then pass the zero test of Phase 8 (xact.cc:898)
    at the display precision of its commodity. The gains are rounded
    one posting at a time, as C++ rounds them, and their sum can differ
    in either direction from the rounded gain of the whole. Phase 6
    runs only for a transaction with a date (`if (has_date())`,
    xact.cc:522), so for a periodic template, which has none
    (`periodic`), no gain is booked and Phase 8 tests the balance that
    the conversion leaves.

    Each orientation that converts and passes gives a candidate
    (`PoolCandidate`): its two entries, `x` first, and the entries that
    Phase 8 then tests, each with its remainder, exact zeros dropped:
    `x`, `y` together with a gain booked against it, and `z` with a gain
    between two lots. Each appears under its commodity, and two entries
    of one commodity that differ in their lots appear separately. An
    orientation in which C++ makes no conversion, `x` and `y` being one
    base with a lot price on `x` only, leaves both entries in the real
    balance, apart, and gives a candidate with no conversion when each
    entry passes the zero test of Phase 8 on its own; when the lot price
    of `x` is fixated, Phase 4 first replaces the entry of `x` by its
    cost in the lot price's commodity (xact.cc:475-518). `.converts`
    carries the candidate of the orientation that the top posting's key
    decides, or, when that key is not an entry and both orientations
    pass, the candidates of both, the second with `x` and `y` swapped;
    `.unordered` carries the candidates of the orientations, converting
    or not, under which C++ accepts the pool, possibly none.

    Known departures, each with the direction in which it fails:
    - the swap of issue #1130, which makes a COMMODITY_PRIMARY side the
      cost side `y` (xact.cc:425-431), is not modelled, because it
      depends on the history of price directives and earlier
      exchanges. It changes which side is doubled and whether a lot
      gain applies, and so can fail either way. A `C` directive, for
      one, registers a price that marks its smaller unit primary
      (textual_directives.cc:185-188, commodity.cc:73-75). Beside
      `C 1 Kb = 1024 b`, C++ accepts `1024 b {$1}` against `$-1000`
      without a gain, and it is rejected here (fail-closed); against a
      same-sign `0.001 EUR` shown to two decimals, C++ doubles the
      `1024 b` and rejects the transaction, while here the doubled
      `EUR` rounds away and it is accepted (fail-open);
    - C++ compares the top posting's commodity as written with the
      entries as reduced (xact.cc:333, 422), so a top posting in a unit
      that a commodity equivalence reduces matches neither entry, and
      C++ takes as `x` whichever entry the unspecified map order puts
      second. Here the top posting matches its reduced entry, which
      agrees with C++ only when that entry comes second, and so this
      can fail either way when the two orientations differ. Beside a
      `C` directive the swap above usually decides instead, since the
      directive marks the reduced unit primary; for the built-in units
      of time (session.cc:80-81), which register no price, the map
      order decides;
    - when the top posting's key is not an entry and the two
      orientations give different verdicts, the earlier rule that
      `balancePool` keeps passes every real residual in two
      commodities, and this can fail either way. The C++ builds
      measured take as `x` the entry whose key entered the balance
      first, but the order is unspecified (balance.h:99). After
      `5 GOOG` and `-5 GOOG`, which net to zero before a second key
      arrives, C++ doubles a same-sign `0.3 EUR` that follows `$0.001`,
      shows it as `1 EUR` under `format 1,000 EUR` and rejects the
      transaction, which is accepted here (fail-open); three postings
      of `1 A {$1.004}` against `-1 A {$3}`, under a bracket-virtual
      top posting of another commodity, each carry a gain of `$0.004`,
      which shows as zero and is not booked, so C++ accepts them, while
      here the residual is in one commodity, its lot values leave
      `$0.012`, and the transaction is rejected (fail-closed);
    - `[date]`, `(tag)` and `((value expression))` annotations do not
      split keys, and this can fail either way. Two dated lots of one
      commodity against cash are three keys to C++, which rejects
      them, and are accepted here (fail-open); a dated amount against
      a different quantity of plain units of its commodity is an
      exchange to C++, which accepts it, and is rejected here
      (fail-closed);
    - the fixated lot price that an `apply fixed` rate gives an amount
      (textual_xacts.cc:626-638) is not parsed, and this can fail
      either way. A fixed rate contradicted by the other side is
      accepted here (fail-open); a transaction of three keys that the
      fixed rate settles together with a fixated lot is rejected here
      (fail-closed);
    - the lot that C++ carries into the amount of a balance assignment
      `= AMT`, the target's own or else the account's single lot
      (textual_xacts.cc:843-862), is not modelled, and the amount is
      keyed with no lot; this can fail either way. With 10 `AAPL {$5}`
      held in `Assets:Broker`, a transaction that moves 4 of them to
      `Assets:Broker2` while `Assets:Broker = 0 AAPL` sells the other
      6 for `$30` has two keys for C++, which accepts it, and three
      here, where it is rejected (fail-closed); `Assets:Broker = 0
      AAPL` against `$60` alone is a sale at a lot gain for C++, which
      rejects it, and an exchange of plain units here, where it is
      accepted (fail-open);
    - a remainder that the bracket-virtual postings of the key of `x`
      leave in the real balance is tested here at display precision,
      but when it is not exactly zero C++ still holds two entries after
      Phase 3, so Phase 4 derives a cost from each fixated lot price
      that Phase 3 left without one and recomputes the balance without
      the bracket-virtual postings (xact.cc:475-518). Under
      `format 1 A`, `-20 B {=$2}` and `10 A {$4}` beside bracket-virtual
      postings of `0.004 A {$4}` and `-0.003 A {$4}` leave `-0.001 A`,
      which rounds away here, where the transaction is accepted, while
      C++ rejects it (fail-open);
    - a lot price written as a total, `{{T}}`, keys its amount by the
      exact quotient of `T` by the quantity, where C++ rounds the
      quotient (amount.cc:1909-1923). Three `A {{$100}}` and minus one
      `A {$33.333333}` are one key for C++ and two here, so beside a
      same-sign `0.001 B` that rounds away when doubled, C++ accepts
      the exchange and it is rejected here (fail-closed).
    Outside this predicate the first pass of `balancePool` values a lot
    only through the gain that `costVal` adds, outside a periodic
    template, to a cost in the lot price's commodity, and in the real
    pool the second pass values every lot, except that a periodic
    template keeps a cost where one is written. C++ values a lot only
    in Phase 4, for a fixated lot on a posting without a cost, and in
    Phase 6, for a lot whose posting has a cost, written or computed,
    in the lot price's commodity or whose cost itself carries a lot
    price in that commodity (xact.cc:475-518, 692-774); among postings
    with no cost written, that is a fixated lot and the lot of `x`.
    Seven lot shapes that C++ rejects are therefore still accepted
    here, each fail-open: a lot against plain units of its commodity,
    a fixated lot against plain units, a lot against a lot of its
    commodity at another price, three or more keys settled by
    unfixated lots, a fixated lot among other keys when it is not the
    top posting, a fixated lot as the top posting against an unfixated
    lot of another commodity priced in the same commodity, and, in a
    dated transaction, a lot whose posting has a cost in another
    commodity. The last is `10 AAA {5 EUR} @ $6` against `-50 EUR`,
    whose first pass leaves `$60` and `-50 EUR` and whose second pass
    settles it at the lot value, while C++ books no gain across the
    two commodities and leaves it unbalanced. In the other direction,
    when Phase 3 makes no conversion C++ keeps a lot and plain units of
    its commodity apart (annotate.h:120-125) and Phase 8 tests each
    entry on its own (xact.cc:898), while the first pass here merges
    them by commodity and the second values the lot. When the lot's
    posting is the top posting, as it is when no other posting that
    must balance carries an annotation, a lot against plain units of
    its commodity of which each rounds to zero, while their sum or the
    lot's value does not, is therefore accepted by C++ and rejected
    here (fail-closed): under `format 1.00 A` and `format $1.00`,
    `0.004 A {$100}` beside `0.004 A`, in either order. Under a
    bracket-virtual top posting of another commodity the
    order-dependent departure above applies instead: the same pair is
    accepted here in either order, and C++ accepts it with the lot
    first and rejects it with the plain units first.
    The bracket-virtual pool has no second pass, since C++ adds no lot
    value to the bracket-virtual balance (xact.cc:505-516, 712-713),
    but its first pass, which keys an amount without its lot, still
    accepts the first three shapes there, whose quantities net to zero
    when lots are ignored. The gain that `costVal` adds there is a
    further departure, which the comment beside `costVal` records. -/
private def impliedExchange (st : St) (xact pool : List PostSpec)
    (periodic : Bool := false) : Exchange :=
  let keyOf := fun (p : PostSpec) (a : Amount) => ((a.comm,
    if a.comm == "" then none else
      p.lotUnit.map fun lu => (lu.comm, lu.q, p.fixated)) : LotKey)
  let bal := pool.foldl (init := CppSum.null) fun s p =>
    match p.amount with
    | some a => s.add (keyOf p a) a.q
    | none => s
  let mustBal := xact.filter fun p => p.kind != .virtualUnbal && p.amount.isSome
  let top? := (mustBal.filter (·.annotated)).getLast? <|> mustBal.head?
  -- Phase 8 tests every entry at its display precision (xact.cc:898):
  -- the entries other than exact zeros when each of them passes
  let test := fun (left : List (String × ℚ)) =>
    if left.all (fun (c, q) => roundsToZero st c q) then
      some (left.filter fun (_, q) => q != 0)
    else none
  -- the verdict with `x` on the top posting's side
  let verdict := fun (x y : LotKey × ℚ) =>
    let ((cx, lx), qx) := x
    let ((cy, ly), qy) := y
    -- no conversion: one base, a lot price on `x` only (xact.cc:449,
    -- regress/1029). The two entries stay apart (annotate.h:120-125)
    -- and Phase 8 tests each, after Phase 4 has replaced a fixated lot
    -- by its cost in the lot price's commodity, which joins `y` when
    -- that is the commodity of `y` (xact.cc:475-518). Under
    -- `format 1.00 A`, `format $1.00` and a bracket-virtual top posting
    -- of another commodity, the C++ builds measured take as `x` the
    -- entry that entered the balance first, and with the lot first
    -- they reject `10 A {$1}` against `-10.004 A`, accept
    -- `0.004 A {$100}` beside `0.004 A`, accept `0.1 A {=$0.001}`
    -- beside `0.004 A`, whose lot Phase 4 prices at `$0.0001`, and
    -- reject `0.004 A {=$10}` beside `0.004 A` with the remainder
    -- `$0.04` and `40 A {=0.0001 A}` beside `0.004 A` with the
    -- remainder `0.01 A`
    if cx == cy && lx.isSome && ly.isNone then
      Verdict.declines (test (match lx with
        | some (z, px, true) =>
            if z == cy then [(cy, px * qx + qy)] else [(z, px * qx), (cy, qy)]
        | _ => [(cx, qx), (cy, qy)]))
    -- the conversion reduces the amount of every posting first, and an
    -- amountless posting throws (xact.cc:459, amount.cc:1153-1155)
    else if xact.any (·.amount.isNone) then .fails
    -- a rate `y/x` with no commodity in `y` takes the commodity of `x`
    -- (amount.cc:814-815), as do the costs (amount.cc:727-744), and
    -- Phase 6 throws for a cost in its posting's own commodity
    -- (xact.cc:679-681); in a periodic template, where Phase 6 does
    -- not run (xact.cc:522), the conversion leaves the entry of `y` in
    -- the balance and the zero test of Phase 8 rejects it (xact.cc:898,
    -- 960-965)
    else if cy == "" && cx != "" then .fails
    else
      -- every must-balance posting of the key of `x`, bracket-virtual
      -- ones included, moves into the real balance at the rate
      -- `|y/x|` in the commodity of `y` (xact.cc:454-465)
      let conv := mustBal.filterMap fun p => p.amount.bind fun a =>
        if keyOf p a == x.1 then some (p.amtDecs, a.q) else none
      let ratio := qy / qx
      let rate := if ratio < 0 then -ratio else ratio
      let moved := (conv.map (·.2)).sum
      let xLeft := qx - moved
      let yLeft := qy + rate * moved
      -- Phase 6: each converted posting's gain per unit `g` in `z`,
      -- rounded at the display precision of `z` plus the posting's
      -- decimals (xact.cc:708-711, 756-759); `dropShownZero` drops a
      -- rounded gain that shows as zero (xact.cc:762). A periodic
      -- template books no gain, since Phase 6 runs only for a
      -- transaction with a date (`if (has_date())`, xact.cc:522)
      let gains := fun (z : String) (g : ℚ) (dropShownZero : Bool) =>
        if periodic then (0 : ℚ) else
        conv.foldl (init := (0 : ℚ)) fun s (d, q) =>
          let r := roundAt ((st.precisions.lookup z).getD 0 + d) (g * q)
          if dropShownZero && roundsToZero st z r then s else s + r
      -- the entries that the conversion and the gains leave
      let left : List (String × ℚ) := (cx, xLeft) :: match lx, ly with
        | some (z, px, _), none =>
            -- a gain against a plain basis joins the entry of `y`; the
            -- test at xact.cc:696 is exact (amount.cc:1407)
            if cy == z then [(cy, yLeft + gains z (px - rate) false)]
            else [(cy, yLeft)]
        | some (z, px, _), some (zy, py, _) =>
            -- a gain between two lots priced in `z` (xact.cc:735-763)
            (cy, yLeft) :: (if zy == z then [(z, gains z (px - py * rate) true)]
              else [])
        | none, _ => [(cy, yLeft)]
      match test left with
      | some r => .passes r
      | none => .fails
  -- the candidate of an orientation under which C++ accepts the pool
  let candidate := fun (x y : LotKey × ℚ) (v : Verdict) => match v with
    | .passes r => [({ exchange := some (x, y), residual := r } : PoolCandidate)]
    | .declines (some r) => [{ residual := r }]
    | _ => []
  -- the exchange of the orientation that the top posting's key decides;
  -- a declining one leaves the pool, and its candidate, to `balancePool`
  -- (`PoolResult.candidates`)
  let ofVerdict := fun (x y : LotKey × ℚ) (v : Verdict) => match v with
    | .passes _ => Exchange.converts (candidate x y v)
    | .fails => .fails
    | .declines _ => .declines
  if xact.any (·.costVal.isSome) then .declines
  else match bal, top? with
    | .balance [x, y], some top =>
        if x.2 == 0 || y.2 == 0 || top.fixated then .declines
        else
          let tk := top.amount.map (keyOf top)
          if tk == some x.1 then ofVerdict x y (verdict x y)
          else if tk == some y.1 then ofVerdict y x (verdict y x)
          -- the order of the two entries decides (xact.cc:422-423,
          -- balance.h:99); only a verdict that both orders give is C++'s,
          -- and when both pass, each order is an admissible orientation
          else
            let v := verdict x y
            let v' := verdict y x
            let both := candidate x y v ++ candidate y x v'
            match v, v' with
            | .passes _, .passes _ => .converts both
            | .fails, .fails => .fails
            | .declines _, .declines _ => .declines
            | _, _ => .unordered both
    | _, _ => .declines

/-- Finalize a pending transaction into flows. With `periodic` the
    postings are those of a periodic template `~`: its UUID is not
    de-duplicated, its postings book no lot gain, a line beginning with
    `assert `, `check ` or `expr ` is a posting (`parsePosting`), and
    `flushPending` keeps only the verdict, discarding the state
    returned. -/
private def finalizeXact (st : St) (hline : Nat) (_header : String)
    (rawPosts : List (Nat × String)) (periodic : Bool := false) :
    Except String St := do
  -- UUID dedup: scan raw text (notes ride the raw lines); a periodic
  -- template is never registered by UUID (journal.cc:594-595, in
  -- add_xact, which the `~` directive never calls,
  -- textual_xacts.cc:316-318), so it is always checked
  let uuid? := if periodic then none else
    rawPosts.findSome? fun (_, r) => uuidOf r
  match uuid? with
  | some u =>
      if st.uuids.contains u then
        return st   -- duplicate transaction: dropped whole
      else pure ()
  | none => pure ()
  let st := match uuid? with
    | some u => { st with uuids := u :: st.uuids }
    | none => st
  -- parse postings, learning styles as we go; standalone comments
  -- after a posting append to ITS note (append_note, 783/2268), the
  -- ones before any posting to the transaction's
  let mut stv := st
  let mut posts : List PostSpec := []
  let mut leadNotes : List String := []
  for (ln, raw) in rawPosts do
    let rawT := trimS raw
    if rawT.startsWith ";" then
      match posts with
      | pl :: rest =>
          posts := { pl with note := pl.note ++ ";" ++ (rawT.drop 1).toString }
            :: rest
      | [] => leadNotes := leadNotes ++ [(rawT.drop 1).toString]
      continue
    let (p?, learned, comm?, decs, isExpr, teach) ←
      parsePosting stv ln raw periodic
    for (c, d) in teach do
      stv := bumpPrecision stv c d
    -- a style learned from a posting amount reaches its commodity, as
    -- C++ migrates it to a commodity that is not locked
    -- (amount.cc:1836-1837). Three departures are known. First, C++
    -- reads a bare amount with the style of the null commodity
    -- (amount.cc:1714-1715), which only the amount of a `D` directive
    -- changes (amount.cc:1850, textual_directives.cc:157), while a bare
    -- posting amount teaches it here: after `X 10,50` against an elided
    -- `Y`, C++ accepts a later bare `5.25`, which is rejected here as
    -- ambiguous (fail-closed). Second, C++ migrates no style to a
    -- commodity that a `D` directive or a `format` subdirective has
    -- locked (amount.cc:1836; textual_directives.cc:165, 875), while
    -- `lockPrecision` locks the precision alone and the style is
    -- learned here: after `D 1,000.00 EUR` and `X 10,50 EUR`, C++
    -- accepts a later `5.25 EUR`, which is rejected here as ambiguous
    -- (fail-closed), and after `D $1,000.00` and `X $1,5`, or after
    -- `commodity EUR` with `format 1,000.00 EUR` and `X 10,5 EUR`, C++
    -- reads a later `$1,500` or `1,500 EUR` as 1500, where it is read
    -- as 1.5 here (wrong rows). Third, an amount expression teaches no
    -- style here, since `parseAmount` reports none for it, while C++
    -- parses each literal of a posting expression with migration
    -- (textual_xacts.cc:585-587, token.cc:548-555), so that the
    -- literal's style reaches its commodity: after `X (10,50 EUR)`
    -- against an elided `Y`, C++ rejects a later `5.25 EUR`, which is
    -- accepted here (fail-open), and reads a later `1,500 EUR` as 1.5,
    -- where it is read as 1500 here (wrong rows)
    match learned with
    | some (c, b) =>
        stv := { stv with amt := { stv.amt with styles := (c, b) :: stv.amt.styles } }
    | none => pure ()
    -- the decimals of a posting amount reach its commodity, as C++
    -- migrates them (amount.cc:1836-1849). For an amount expression
    -- they are the largest number of decimals among its literals
    -- (`parseExprAmount`), while C++ parses each literal as an amount
    -- of its own, which migrates its precision to that literal's
    -- commodity alone, and to none for a bare literal
    -- (token.cc:540-555, amount.cc:1836), a known departure: after
    -- `X ($1 * 1.555)` against an elided `Y`, C++ prints X as `2 $`
    -- and no row for a later `(1/3 $)`, which show as 1.555 and 0.333
    -- here (wrong rows), and after `X (1.234 * $2)`
    -- against an elided `Y` it accepts a later `($1/3)` against
    -- `$-0.33`, which is rejected here (fail-closed)
    let _ := isExpr
    match comm? with
    | some c =>
        let c := (stv.commAliases.lookup c).getD c
        stv := bumpPrecision stv c decs
    | none => pure ()
    match p? with
    | some p =>
        -- canonicalize amounts through commodity equivalences. C++
        -- parses the amount unreduced (textual_xacts.cc:583) and reduces
        -- it in Phase 1 (xact.cc:333), dividing its lot price by the
        -- factor that scales the quantity (amount.cc:1153-1176, #512),
        -- and so the lot price per unit is divided here
        let scale := match p.amount with
          | some a =>
              (resolveEquiv stv.equivs ((stv.commAliases.lookup a.comm).getD a.comm)).1
          | none => 1
        let p := { p with
          amount := p.amount.map (canonAmt stv)
          costVal := p.costVal.map (canonAmt stv)
          lotVal := p.lotVal.map (canonAmt stv)
          lotUnit := p.lotUnit.map fun lu =>
            let c := canonAmt stv lu
            if scale == 0 then c else ⟨c.comm, c.q / scale⟩
          assignTarget := p.assignTarget.map (canonAmt stv) }
        posts := p :: posts
    | none => pure ()
  let ordered := posts.reverse
  -- assignments: sequential against running balance + this xact so far
  let mut resolved : List PostSpec := []
  -- intra-xact prior posts, keyed by (account, commodity, realOnly?)
  let mut intra : List ((String × String × Bool) × ℚ) := []
  let addIntra := fun (l : List ((String × String × Bool) × ℚ))
      (k : String × String) (isReal : Bool) dq =>
    let upd := fun (l : List ((String × String × Bool) × ℚ))
        (kk : String × String × Bool) =>
      match l.lookup kk with
      | some _ => l.map fun (k', v) => if k' = kk then (k', v + dq) else (k', v)
      | none => (kk, dq) :: l
    let l := upd l (k.1, k.2, false)
    if isReal then upd l (k.1, k.2, true) else l
  let xd := (headerDateF stv.dfmt stv.defaultYear _header).getD 0
  let balAsOf := fun (acct comm : String) (realOnly : Bool) =>
    stv.datedEvents.foldl (init := (0 : ℚ)) fun acc ((a, c), d, q, isReal) =>
      if a == acct && c == comm && d <= xd && (!realOnly || isReal)
      then acc + q else acc
  let hasRealPost := fun (acct comm : String) =>
    stv.datedEvents.any fun ((a, c), _, _, isReal) =>
      a == acct && c == comm && isReal
  for p in ordered do
    match p.assignTarget with
    | some target =>
        -- a REAL assignment measures the real-only balance when the
        -- account has prior real postings, else the combined balance
        -- (#543/#1699, compute_balance_diff); virtual assignments
        -- always measure the combined balance
        let realOnly := fun (c : String) =>
          p.kind == .real && hasRealPost p.account c
        if target.comm == "" && target.q == 0 then
          -- bare `=0`: zero the account across every commodity it
          -- holds (regress/1587)
          let comms := (stv.balances.filterMap fun ((acct, c), _) =>
            if acct == p.account then some c else none).eraseDups
          for c in comms do
            let key := (p.account, c)
            let cur := balAsOf p.account c (realOnly c)
              + ((intra.lookup (key.1, key.2, realOnly c)).getD 0)
            if cur != 0 then
              let q := -cur
              intra := addIntra intra key (p.kind == .real) q
              resolved := { p with amount := some ⟨c, q⟩
                                   assignTarget := none } :: resolved
        else
        let key := (p.account, target.comm)
        let cur := balAsOf p.account target.comm (realOnly target.comm)
          + ((intra.lookup (key.1, key.2, realOnly target.comm)).getD 0)
        let diff := target.q - cur
        let p := { p with amount := some ⟨target.comm, diff⟩
                          assignTarget := none }
        intra := addIntra intra key (p.kind == .real) diff
        resolved := p :: resolved
    | none =>
        match p.amount with
        | some a =>
            intra := addIntra intra (p.account, a.comm) (p.kind == .real) a.q
        | none => pure ()
        resolved := p :: resolved
  let rposts := resolved.reverse
  -- the final zero test of the real pool (Phase 8, xact.cc:868-898): a
  -- residual without a commodity is tested exactly (amount.cc:1378,
  -- 1429), and a cost commodity of display precision 0 is widened
  -- (`zeroTestPrec`, regress/1114). Once an automated transaction has
  -- added a posting that must balance, C++ runs `verify()`
  -- (xact.cc:1040-1110, 1683-1684), which applies the same test, with
  -- the same widening rule, to the single balance of real and
  -- bracket-virtual postings. It makes no allowance for the rounding of
  -- per-unit costs, and it widens by the cost of every posting of the
  -- extended transaction (xact.cc:1076-1091), the cost that a generated
  -- posting copies from its template posting included
  -- (xact.cc:1611-1612), while `zeroTestPrec` here reads only the
  -- postings from before the extension
  let settlesWide := fun (c : String) (s : ℚ) =>
    if c == "" then s == 0
    else roundsToZeroAt (zeroTestPrec stv rposts c) s
  -- Balancing runs per POOL: real (+deferred) postings balance among
  -- themselves, bracket-virtuals `[A]` among themselves (regress/563);
  -- paren-virtuals `(A)` are exempt. Each pool may have one elided
  -- posting. Structural decisions use EXACT residuals; the
  -- display-precision tolerance is only the final acceptance test.
  let balancePool : List PostSpec → Bool → Except String PoolResult :=
      fun pool isReal => do
    let sumsWith := fun (useLot : Bool) =>
      pool.foldl (init := ([] : List (String × ℚ))) fun acc p =>
        match p.amount with
        | some a =>
            -- in a periodic template a posting with a cost keeps it in
            -- both passes: Phase 1 sums the cost (xact.cc:325), Phase 4
            -- prices only a posting without one (xact.cc:486), and no
            -- Phase 6 turns it into the lot value (xact.cc:522)
            let v :=
              if useLot then
                if periodic then p.costVal.getD (p.lotVal.getD a)
                else p.lotVal.getD (p.costVal.getD a)
              else p.costVal.getD a
            match acc.lookup v.comm with
            | some _ => acc.map fun (c, s) => if c = v.comm then (c, s + v.q) else (c, s)
            | none => (v.comm, v.q) :: acc
        | none => acc
    let residualExact := (sumsWith false).filter fun (_, s) => s != 0
    -- the final zero test: `settlesWide` for the real pool; for a
    -- bracket-virtual pool the display precision (xact.cc:971-979), with
    -- a residual without a commodity tested exactly (amount.cc:1378,
    -- 1429)
    let settles := fun (c : String) (s : ℚ) =>
      if isReal then settlesWide c s
      else if c == "" then s == 0
      else roundsToZero stv c s
    let elided := pool.filter fun p => p.amount.isNone && p.assignTarget.isNone
    match elided with
    | [] =>
        if residualExact.isEmpty then pure { posts := pool }
        -- the `bucket` (`A`, account `default`) completes only a
        -- transaction of exactly ONE parsed posting of any kind,
        -- counted before a bare `=0` fans out and before automated
        -- postings; with two or more postings the residual is left to
        -- the implicit-exchange, rounding, second-pass lot-value and
        -- error cases below
        -- (xact.cc:368 `posts.size() == 1 && !balance.is_null()`, the
        -- second conjunct implied by a nonzero real residual;
        -- regress/coverage-bucket-single-post)
        else match (if isReal && ordered.length == 1 then st.bucket else none) with
          | some b =>
              -- bucket names were resolved when declared
              let comps := residualExact.map fun (c, s) =>
                { line := hline, inferred := true
                  account := b
                  kind := PostKind.real, amount := some ⟨c, -s⟩ : PostSpec }
              pure { posts := pool ++ comps }
          | none =>
              -- per-posting cost rounding may explain the residual
              -- (xact.cc phase 8, regress/1125). C++ adds the exact
              -- adjustment of rounding each per-unit cost of a real
              -- posting at its price's decimals (xact.cc:908-929);
              -- this tolerates instead half a unit in the last place of
              -- every cost in that commodity written with decimals,
              -- total costs included, and it does so also where the
              -- widened test of `zeroTestPrec` or the exact test of
              -- the null commodity rejects the residual. So
              -- `-0.5 FOO @ 1.00 EUR` twice with `1 BAR @@ 0.01 EUR`
              -- against `1.00 EUR`, the same with `@@ 0.50 EUR` for
              -- each `@ 1.00 EUR`, `0.5 FOO @ 0.5 EUR` twice with
              -- `(49/100 EUR)` against `-1 EUR`, and `1 FOO @ 0.333`
              -- against `(-1/3)` are accepted here and rejected by C++
              -- (fail-open). C++ then tests the residual plus its
              -- adjustment, at the widened precision of `zeroTestPrec`
              -- or at the display precision, where this accepts a
              -- residual only when it settles alone or lies within the
              -- tolerance: `0.5 FOO @ 1.005 EUR` with
              -- `1 BAR @@ 0.49696 EUR` against `-1 EUR`, which C++
              -- tests at the widened precision 4, and the same with
              -- `@@ 0.4921 EUR` against `-1.00 EUR`, which it tests at
              -- the display precision 2, are rejected here and accepted
              -- by C++ (fail-closed). The tolerance applies in the
              -- bracket-virtual pool as well, where C++ makes no
              -- adjustment (xact.cc:910 skips a virtual posting) and
              -- tests the balance at the display precision
              -- (xact.cc:973-979): the journal of regress/1125 with
              -- every posting bracket-virtual is accepted here and
              -- rejected by C++ (fail-open)
              let costTol := fun (c : String) =>
                pool.foldl (init := (0 : ℚ)) fun acc p =>
                  match p.costVal with
                  | some cv =>
                      if cv.comm == c && p.costDecs > 0 then
                        acc + 1 / (2 * ((10 ^ p.costDecs : ℕ) : ℚ))
                      else acc
                  | none => acc
              let unbalanced : Except String PoolResult :=
                err hline s!"unbalanced transaction (residual in {residualExact.length} commodities)"
              -- the implicit exchange of Phase 3, which converts only
              -- the real balance (xact.cc:380): `impliedExchange` gives
              -- C++'s verdict where C++ converts; where C++ makes no
              -- conversion, or where its verdict depends on the
              -- unspecified order of the two entries (balance.h:99,
              -- xact.cc:422-423), the tests below decide
              let exch :=
                if isReal then impliedExchange stv rposts pool periodic
                else .declines
              -- for an order-dependent verdict the oracle keeps its
              -- earlier rule, under which a residual in exactly two
              -- commodities passes in either pass; the docstring of
              -- `impliedExchange` gives a journal on which this departs
              -- from C++ in each direction
              let unordered := match exch with
                | .unordered _ => true
                | _ => false
              -- whether the pool settles by itself without a conversion:
              -- its exact residual under the zero test or the per-unit
              -- cost allowance (`alone1`), or, in the real pool, the
              -- residual of the second pass below (`alone2`)
              let residual2 := (sumsWith true).filter fun (_, s) => s != 0
              let alone1 := residualExact.all fun (c, s) =>
                settles c s || (s ≤ costTol c && -s ≤ costTol c)
              let alone2 := residual2.isEmpty || residual2.all fun (c, s) => settles c s
              -- a pool accepted without the implicit exchange: the
              -- candidates of an order-dependent verdict, or else the
              -- residual with which the pool settles by itself: the exact
              -- one when it settles, and otherwise the second pass's
              let accepted : Except String PoolResult :=
                pure { posts := pool, orderDependent := unordered
                       candidates := match exch with
                         | .unordered cs => cs
                         | _ => [{ residual :=
                             if alone1 then residualExact else residual2 }] }
              match exch with
              | .converts cs => pure { posts := pool, candidates := cs }
              | .fails => unbalanced
              | _ =>
                if (unordered && residualExact.length == 2) || alone1 then
                  accepted
                -- C++ adds no lot value to the bracket-virtual balance:
                -- Phase 1 sums it once, Phase 4's recompute skips its
                -- postings, Phase 6 adds their gain to the real balance,
                -- and Phase 8 tests it as it stands (xact.cc:505-516,
                -- 712-713, 973-979)
                else if !isReal then unbalanced
                -- second pass: substitute lot/fixated values
                -- (regress/coverage-wave3-fixated-price). The lot-valued
                -- residual must itself round to zero: C++ prices fixated
                -- lots in Phase 4, after Phase 3, and infers no exchange
                -- from what they leave (xact.cc:475-518, regress/1029)
                else if alone2 || (unordered && residual2.length == 2) then
                  accepted
                else unbalanced
    | [e] =>
        -- COST_PREC tagging: only when the inferred value fits the
        -- recovered price precision (set_cost_prec_if_needed, 2174)
        let pricePrec := fun (c : String) =>
          pool.foldl (init := (0 : Nat)) fun acc p =>
            match p.costVal with
            | some cv =>
                if cv.comm == c && p.costDecs > 0 then
                  max acc (if p.costDecs > p.amtDecs then
                    p.costDecs - p.amtDecs else p.costDecs)
                else acc
            | none => acc
        let comps := residualExact.map fun (c, s) =>
          let pp := pricePrec c
          let fits := pp > 0 && roundAt pp s == s
          { line := e.line, inferred := fits, note := e.note
            account := e.account, kind := e.kind
            amount := some ⟨c, -s⟩ : PostSpec }
        let kept := pool.filter fun p => !(p.amount.isNone && p.assignTarget.isNone)
        pure { posts := kept ++ comps }
    | _ => err hline "more than one elided posting in a balancing pool"
  let realPool := rposts.filter fun p => p.kind == .real || p.kind == .deferred
  let virtPool := rposts.filter fun p => p.kind == .virtualBal
  let exempt := rposts.filter fun p => p.kind == .virtualUnbal
  let realDone ← balancePool realPool true
  let virtDone ←
    if virtPool.isEmpty then pure { posts := [] }
    else balancePool virtPool false
  let completed := realDone.posts ++ virtDone.posts ++ exempt
  -- auto-xact extension (after balancing, as extend_xact does)
  let afterDate := stripStatus (trimS (String.ofList
    (_header.toList.dropWhile fun c => c != ' ')))
  let (hcode, hpayee) :=
    if afterDate.startsWith "(" then
      match takeBalanced '(' ')' afterDate.toList with
      | some (inner, rest) =>
          (String.ofList inner, trimS (String.ofList rest))
      | none => ("", afterDate)
    else ("", afterDate)
  let dateTok := String.ofList (_header.toList.takeWhile fun c =>
    c != ' ' && c != '=')
  let headerNote := (splitNote _header).2
  let xactNotes := headerNote ++ ";" ++ String.intercalate ";" leadNotes
  let (finalPosts, _autoBatches) :=
    applyAutos stv (headerDateF stv.dfmt stv.defaultYear _header)
      hpayee hcode dateTok xactNotes completed
  -- account payee-rules: an xact whose payee matches maps postings to
  -- the declared account's Unknown slot (cov4-directive-account-payee)
  let payee := hpayee
  let acctFor := fun (name : String) =>
    if name.endsWith ":Unknown" || name == "Unknown" then
      match stv.payeeAccountRules.find? fun (rx, _) => regexSearch rx payee with
      | some (_, target) => target
      | none => name
    else name
  -- flows: own amounts of every posting
  let flows := finalPosts.filterMap fun p =>
    p.amount.map fun a => (Account.mk (acctFor p.account) a.comm, a.q)
  -- running balances (dated, for date-ordered assignments — 1092)
  for p in finalPosts do
    match p.amount with
    | some a =>
        let nm := acctFor p.account
        stv := bumpBal stv nm a.comm a.q
        stv := bumpStat stv nm a.comm p.inferred
        stv := { stv with datedEvents :=
          ((nm, a.comm), xd, a.q, p.kind == .real) :: stv.datedEvents }
    | none => pure ()
  pure { stv with gens := flows :: stv.gens }

/-- Split on a separator word at paren/quote depth zero. -/
private partial def splitTopOn (sep : String) (s0 : String) : List String :=
  let sepL := sep.toList
  let rec go (cs : List Char) (cur : List Char) (acc : List String)
      (depth : Nat) (q : Option Char) : List String :=
    match cs with
    | [] => (String.ofList cur.reverse :: acc).reverse
    | c :: rest =>
        match q with
        | some qc =>
            if c == qc then go rest (c :: cur) acc depth none
            else go rest (c :: cur) acc depth q
        | none =>
            if c == '\'' || c == '"' then
              go rest (c :: cur) acc depth (some c)
            else if c == '(' || c == '[' || c == '{' then
              go rest (c :: cur) acc (depth + 1) none
            else if c == ')' || c == ']' || c == '}' then
              go rest (c :: cur) acc (depth - 1) none
            else if depth == 0 && sepL != [] && cs.take sepL.length == sepL then
              go (cs.drop sepL.length) [] (String.ofList cur.reverse :: acc) 0 none
            else go rest (c :: cur) acc depth none
  go s0.toList [] [] 0 none

private def unquoteAny (r : String) : String :=
  if r.length ≥ 2 && ((r.startsWith "'" && r.endsWith "'")
      || (r.startsWith "\"" && r.endsWith "\"")) then
    String.ofList ((r.drop 1).toString.toList.dropLast)
  else r

private def unslash (r : String) : String :=
  if r.length ≥ 2 && r.startsWith "/" && r.endsWith "/" then
    String.ofList ((r.drop 1).toString.toList.dropLast)
  else r

private def escLit (r : String) : String :=
  String.join (r.toList.map fun ch =>
    if "\\.*+?()[]|^$".toList.contains ch then
      String.ofList ['\\', ch]
    else String.ofList [ch])

/-- Compile one conjunction of predicate terms into a `PredSpec`. -/
private def compileConj (st : St) (n : Nat) (conj : List String) :
    Except String PredSpec := do
  let mut spec : PredSpec := {}
  for term0 in conj do
    let term := if term0.startsWith "expr " then
        trimS (term0.drop 5).toString else term0
    let term := unquoteAny term
    -- one layer of grouping parens around a term
    let term :=
      if term.startsWith "(" && term.endsWith ")" then
        trimS (String.ofList ((term.drop 1).toString.toList.dropLast))
      else term
    if term.isEmpty || term == "true" then
      continue
    if term.startsWith "@" then
      -- query-syntax payee term (feat-value-expr's `@XACT`)
      match compileRegex (escLit (trimS (term.drop 1).toString)) with
      | .ok rx =>
          spec := { spec with payeeRx := some rx }
          continue
      | .error e => err n e
    let term := if term.startsWith "~ " then
        trimS (term.drop 2).toString else term
    let term := if term.startsWith "any (" || term.startsWith "all (" then
        (term.take 3).toString ++ "(" ++ (term.drop 5).toString
      else term
    if term.startsWith "any(" || term.startsWith "all(" then
      let isAny := term.startsWith "any("
      let inner := trimS (String.ofList
        ((term.drop 4).toString.toList.dropLast))
      -- inner conjunction: `account =~ /rx/ [and R]`
      let parts := (splitTopOn " and " inner).map trimS
      let mut rxS := ""
      let mut realOnly := false
      for pt in parts do
        if pt == "R" || pt == "real" then
          realOnly := true
        else
          let alts := (splitTopOn " or " pt).map fun alt =>
            let alt := trimS alt
            let core := if alt.startsWith "account =~" then
                trimS (alt.drop "account =~".length).toString else alt
            unslash core
          rxS := if alts.length > 1 then
              "(" ++ String.intercalate ")|(" alts ++ ")"
            else alts.headD ""
      let rx ← match compileRegex rxS with
        | .ok r => pure r
        | .error e => err n e
      if isAny then
        spec := { spec with anyRx := some (rx, realOnly) }
      else
        spec := { spec with allRx := some rx }
      continue
    if term.startsWith "date =~" then
      let r := unslash (trimS (term.drop "date =~".length).toString)
      match compileRegex r with
      | .ok rx =>
          spec := { spec with dateRx := some rx }
          continue
      | .error e => err n e
    if term.startsWith "code =~" then
      let r := unslash (trimS (term.drop "code =~".length).toString)
      match compileRegex r with
      | .ok rx =>
          spec := { spec with codeRx := some rx }
          continue
      | .error e => err n e
    if term.startsWith "account(" then
      -- account("N").total CMP AMOUNT (2099): live balance test
      let inner := (term.drop "account(".length).toString
      let nameQ := String.ofList (inner.toList.takeWhile (· != ')'))
      let acctName := unquoteAny (trimS nameQ)
      let after := trimS (String.ofList
        ((inner.toList.dropWhile (· != ')')).drop 1))
      if after.startsWith ".total" then
        let r := trimS (after.drop ".total".length).toString
        let (cmp?, rest) :=
          if r.startsWith ">=" then (some AmtCmp.ge, r.drop 2)
          else if r.startsWith "<=" then (some AmtCmp.le, r.drop 2)
          else if r.startsWith ">" then (some AmtCmp.gt, r.drop 1)
          else if r.startsWith "<" then (some AmtCmp.lt, r.drop 1)
          else if r.startsWith "==" then (some AmtCmp.eq, r.drop 2)
          else (none, r.drop 0)
        match cmp? with
        | some cmp =>
            match parseAmount st.amt n (trimS rest.toString) with
            | .ok pr =>
                spec := { spec with
                  acctTotal := spec.acctTotal ++ [(acctName, cmp, pr.amount.q)] }
                continue
            | .error e => err n e
        | none => err n s!"out-of-scope account() predicate '{term.take 40}'"
      else err n s!"out-of-scope account() predicate '{term.take 40}'"
    -- `/A/ == /B/`: regex equality degenerates to the left match
    -- (cov6-xact-auto-eq-pred)
    let term :=
      match splitTopOn " == " term with
      | [l, r] =>
          if l.startsWith "/" && l.endsWith "/"
              && (trimS r).startsWith "/" then trimS l else term
      | _ => term
    let dTerm := if term.startsWith "date" then
        trimS (term.drop 4).toString else term
    if dTerm.startsWith ">=" || dTerm.startsWith "<=" ||
       dTerm.startsWith ">" || dTerm.startsWith "<" ||
       term.startsWith "d>=" || term.startsWith "d<=" ||
       term.startsWith "d>" || term.startsWith "d<" then
      let core := if term.startsWith "d" && !(term.startsWith "date") then
          (term.drop 1).toString else dTerm
      let (cmp, rest) :=
        if core.startsWith ">=" then (DateCmp.ge, core.drop 2)
        else if core.startsWith "<=" then (DateCmp.le, core.drop 2)
        else if core.startsWith ">" then (DateCmp.gt, core.drop 1)
        else (DateCmp.lt, core.drop 1)
      let ds := trimS rest.toString
      let ds := if ds.startsWith "[" && ds.endsWith "]" then
          String.ofList ((ds.drop 1).toString.toList.dropLast)
        else ds
      match headerDate st.defaultYear ds with
      | some d => spec := { spec with dateTerms := spec.dateTerms ++ [(cmp, d)] }
      | none => err n s!"malformed date in predicate '{ds}'"
    else if term.startsWith "amount" then
      let r := trimS (term.drop "amount".length).toString
      let (cmp, rest) :=
        if r.startsWith ">=" then (some AmtCmp.ge, r.drop 2)
        else if r.startsWith "<=" then (some AmtCmp.le, r.drop 2)
        else if r.startsWith ">" then (some AmtCmp.gt, r.drop 1)
        else if r.startsWith "<" then (some AmtCmp.lt, r.drop 1)
        else if r.startsWith "==" then (some AmtCmp.eq, r.drop 2)
        else (none, r.drop 0)
      match cmp with
      | none => err n s!"out-of-scope amount predicate '{term.take 30}'"
      | some cmp =>
          match parseAmount st.amt n (trimS rest.toString) with
          | .ok pr => spec := { spec with
              amountTerms := spec.amountTerms ++ [(cmp, pr.amount.q)] }
          | .error e => err n e
    else if term.startsWith "payee ==" then
      let r := unquoteAny (trimS (term.drop "payee ==".length).toString)
      match compileRegex ("^" ++ escLit r ++ "$") with
      | .ok rx => spec := { spec with payeeRx := some rx }
      | .error e => err n e
    else if term.startsWith "%" || term.startsWith "!%" then
      -- %TAG / %TAG=VALUE / %/re/ / !%TAG: tag requirements (1937,
      -- 783, 1984, auto_pedantic)
      let neg := term.startsWith "!%"
      let body := trimS (term.drop (if neg then 2 else 1)).toString
      let (nameS, val?) :=
        match body.splitOn "=" with
        | [n, v] => (trimS n, some (trimS v))
        | _ => (body, none)
      let rxSrc :=
        if nameS.startsWith "/" && nameS.endsWith "/" then unslash nameS
        else "^" ++ escLit nameS ++ "$"
      match compileRegex rxSrc with
      | .ok rx =>
          if neg then spec := { spec with negTag := some rx }
          else spec := { spec with tagReq := some (rx, val?) }
      | .error e => err n e
    else if term.startsWith "has_tag" then
      let inner := trimS (term.drop "has_tag".length).toString
      let inner := if inner.startsWith "(" && inner.endsWith ")" then
          trimS (String.ofList ((inner.drop 1).toString.toList.dropLast))
        else inner
      let inner := unquoteAny inner
      let rxSrc :=
        if inner.startsWith "/" && inner.endsWith "/" then unslash inner
        else "^" ++ escLit inner ++ "$"
      match compileRegex rxSrc with
      | .ok rx => spec := { spec with tagReq := some (rx, none) }
      | .error e => err n e
    else if term.startsWith "payee =~" then
      let r := unslash (trimS (term.drop "payee =~".length).toString)
      match compileRegex r with
      | .ok rx => spec := { spec with payeeRx := some rx }
      | .error e => err n e
    else if term.startsWith "comment =~" then
      let r := unslash (trimS (term.drop "comment =~".length).toString)
      match compileRegex r with
      | .ok rx => spec := { spec with commentRx := some rx }
      | .error e => err n e
    else if term.startsWith "commodity ==" then
      let r := unquoteAny (trimS (term.drop "commodity ==".length).toString)
      spec := { spec with commodityEq := some r }
    else if term.startsWith "account =~" then
      let r := unslash (trimS (term.drop "account =~".length).toString)
      match compileRegex r with
      | .ok rx => spec := { spec with accRxs := spec.accRxs ++ [rx] }
      | .error e => err n e
    else if term.startsWith "account ==" then
      let r := unquoteAny (trimS (term.drop "account ==".length).toString)
      match compileRegex ("^" ++ escLit r ++ "$") with
      | .ok rx => spec := { spec with accRxs := spec.accRxs ++ [rx] }
      | .error e => err n e
    else if term.startsWith "not " || term.startsWith "! " then
      let inner := trimS (String.ofList
        (term.toList.drop (if term.startsWith "not " then 4 else 2)))
      let inner := if inner.startsWith "expr " then
          trimS (inner.drop 5).toString else inner
      let inner := unquoteAny inner
      if inner.startsWith "has_tag" then
        let tg := trimS (inner.drop "has_tag".length).toString
        let tg := if tg.startsWith "(" && tg.endsWith ")" then
            trimS (String.ofList ((tg.drop 1).toString.toList.dropLast))
          else tg
        let tg := unquoteAny tg
        let rxSrc :=
          if tg.startsWith "/" && tg.endsWith "/" then unslash tg
          else "^" ++ escLit tg ++ "$"
        match compileRegex rxSrc with
        | .ok rx => spec := { spec with negTag := some rx }
        | .error e => err n e
      else
        let inner := if inner.startsWith "account =~" then
            trimS (inner.drop "account =~".length).toString else inner
        match compileRegex (unslash inner) with
        | .ok rx => spec := { spec with negRxs := spec.negRxs ++ [rx] }
        | .error e => err n e
    else
      match compileRegex (unslash term) with
      | .ok rx => spec := { spec with accRxs := spec.accRxs ++ [rx] }
      | .error e => err n e
  pure spec

/-- Compile a full auto-xact predicate into disjunctive branches:
    `A or B`, ternary `C ? T : E`, `and`/`&` conjunctions. -/
private def compilePred (st : St) (n : Nat) (predS : String) :
    Except String (List PredSpec) := do
  let predS := if predS.startsWith "expr " then
      trimS (predS.drop 5).toString else predS
  let predS := unquoteAny predS
  -- strip one layer of outer parens: `expr ( A & B )`
  let predS :=
    let pt := trimS predS
    if pt.startsWith "(" && pt.endsWith ")" then
      trimS (String.ofList ((pt.drop 1).toString.toList.dropLast))
    else pt
  -- ternary: C ? T : E  ≡  (C and T) or (not C and E)
  match splitTopOn " ? " predS with
  | [c, rest] =>
      match splitTopOn " : " rest with
      | [t, e] =>
          let bThen ← compileConj st n
            (((splitTopOn " and " c).map trimS) ++ ((splitTopOn " and " t).map trimS))
          let condSpec ← compileConj st n ((splitTopOn " and " c).map trimS)
          let negC ← compileConj st n ((splitTopOn " and " e).map trimS)
          let bElse := { negC with
            negRxs := negC.negRxs ++ condSpec.accRxs }
          pure [bThen, bElse]
      | _ => err n "malformed ternary predicate"
  | _ =>
  let orParts := (splitTopOn " or " predS).map trimS
  orParts.mapM fun branch => do
    let conj := ((splitTopOn "&" branch).flatMap
      (splitTopOn " and " ·)).map trimS
    compileConj st n conj

/-! ## Auto-rule block finalization -/

private def finalizeAuto (st : St) (rawPosts : List (Nat × String)) :
    Except String St := do
  match st.autoPred with
  | [] => .error "internal: auto block without predicate"
  | (branches, nm) :: rest => do
      let mut posts : List AutoPost := []
      let mut noteTag := ""
      for (ln, raw) in rawPosts do
        let rawT := trimS raw
        if rawT.startsWith ";" then
          noteTag := noteTag ++ ";" ++ (rawT.drop 1).toString
          continue
        let (content, _) := splitNote raw
        let content := stripStatus (trimS content)
        if content.isEmpty then continue
        if content.startsWith "assert " || content.startsWith "check "
            || content.startsWith "expr " || content.startsWith "eval "
            || content.startsWith "note " || content.startsWith "format " then
          continue  -- checks/eval/metadata: verified or report-time only
        let (acctField, amtField) := splitField content
        let (kind, name) ← accountKind ln acctField
        match amtField with
        | none =>
            -- amountless template mirrors the matched posting
            posts := ⟨name, kind, none, 1, none⟩ :: posts
        | some f =>
            let f := trimS f
            if f.startsWith "(" then
              -- expression template, evaluated per matched posting
              posts := ⟨name, kind, none, 1, some f⟩ :: posts
            else
            -- bare number = multiplier; otherwise fixed amount. C++
            -- multiplies by every template amount without a commodity
            -- (xact.cc:1546-1547), so one that is not a bare number,
            -- such as `1 @ $1` or `1 [2024/01/01]`, departs here: under
            -- `= /Assets:A/` with `Assets:X` and `Assets:Y` taking such
            -- an amount and its negation, applied to `10 AAA` against
            -- `-10 AAA`, C++ generates `10 AAA` and `-10 AAA`, and the
            -- oracle `1` and `-1`, whose balances differ
            let isBare := f.toList.all fun c =>
              c.isDigit || c == '.' || c == ',' || c == '-' || c == ' '
            if isBare then
              let (neg, cs) := match f.toList with
                | '-' :: r => (true, r.dropWhile (· == ' '))
                | cs => (false, cs)
              match readNumToken (some false) (cs.takeWhile fun c =>
                  c.isDigit || c == '.' || c == ',') with
              | some (q, _, _) =>
                  posts := ⟨name, kind, none, if neg then -q else q, none⟩ :: posts
              | none => err ln s!"malformed multiplier '{f}'"
            else do
              let r ← parseAmount st.amt ln f
              -- cost/lot annotations on template amounts parse and
              -- drop: extended posts flow at face value (2268)
              let _ ← annotLoop st.amt ln r.amount r.tail none none
              posts := ⟨name, kind, some r.amount, 1, none⟩ :: posts
      pure { st with
        autos := st.autos ++ [⟨branches, posts.reverse, nm, true, noteTag⟩]
        autoPred := rest }

/-! ## Directives -/

/-- Handle a top-level directive line; returns the new state and the
    pending-block mode it opens. Each ignored directive carries its
    justification. -/
private def defineDirective (st : St) (restS : String) :
    Except String St := do
  -- split at the FIRST `=` (bodies may contain more)
  match restS.splitOn "=" with
  | name :: rhsParts =>
      if rhsParts.isEmpty then pure st else
      let rhs := trimS (String.intercalate "=" rhsParts)
      let name := trimS name
      if name.toList.contains '(' then
        -- function definition: `f(a, b) = body`
        let fname := trimS (String.ofList (name.toList.takeWhile (· != '(')))
        let params := String.ofList
          ((name.toList.dropWhile (· != '(')).drop 1 |>.takeWhile (· != ')'))
        let ps := (params.splitOn ",").map trimS |>.filter (!·.isEmpty)
        pure { st with amt := { st.amt with
          funs := (fname, ps, rhs) :: st.amt.funs } }
      else
        match parseAmount st.amt 0 rhs with
        | .ok r =>
            pure { st with amt := { st.amt with
              defines := (name, r.amount) :: st.amt.defines } }
        | .error _ => pure st   -- non-amount define: report-time only
  | _ => pure st

private def handleDirective (st : St) (n : Nat) (t : String) :
    Except String St := do
  let word := trimS (String.ofList (t.toList.takeWhile (· != ' ')))
  let restS := trimS (t.drop word.length).toString
  match word with
  | "alias" =>
      match restS.splitOn "=" with
      | [from_, to_] =>
          pure { st with aliases := (trimS from_, trimS to_) :: st.aliases }
      | _ => err n s!"malformed alias '{restS}'"
  | "account-rewrite" =>
      let (from_, to_?) := splitField restS
      match to_? with
      | some to_ => do
          let rx ← match compileRegex from_ with
            | .ok r => pure r
            | .error e => err n e
          pure { st with rewrites := st.rewrites ++ [(rx, trimS to_)] }
      | none => err n s!"malformed account-rewrite '{restS}'"
  | "payee-rewrite" =>
      -- rewrites payees: labels only, no flows
      pure st
  | "apply" =>
      if restS.startsWith "account" then
        let acct := trimS (restS.drop "account".length).toString
        pure { st with applyStack := some acct :: st.applyStack }
      else
        -- apply tag: labels only (uuid tags never come from `apply`)
        pure { st with applyStack := none :: st.applyStack }
  | "end" =>
      -- `end`, `end apply ...`, `end account`, `end tag` all close
      -- the innermost apply; a stray `end test`/`end comment` does not
      if restS.isEmpty || restS.startsWith "apply"
          || restS.startsWith "account" || restS.startsWith "tag"
          || restS.startsWith "fixed" || restS.startsWith "year"
          || restS.startsWith "rate" then
        pure { st with applyStack := st.applyStack.drop 1 }
      else pure st
  | "bucket" =>
      -- default_account_directive resolves against the CURRENT apply
      -- stack (coverage-wave3-apply-directives)
      pure { st with bucket := some (resolveAccount st restS) }
  | "A" => pure { st with bucket := some (resolveAccount st restS) }
  | "include" =>
      -- `splice` in Driver.lean reads each include line outside a
      -- comment or test block (`opensCommentBlock`), splices each one
      -- it resolves, and leaves the rest here as a bare `include` (no
      -- argument) or `include ARG` (no file matched but the including
      -- one). C++ rejects a missing file (textual_directives.cc:458-459,
      -- regress/1670, coverage-error-include-not-found) and an include
      -- without an argument (textual_directives.cc:1034-1038,
      -- coverage-directive-no-arg). The reason names the argument as
      -- written, where C++ names the resolved path.
      if restS.isEmpty then err n "directive 'include' requires an argument"
      else err n s!"file to include was not found: {restS}"
  | "define" => defineDirective st restS
  | "def" => defineDirective st restS
  | "P" =>
      -- price observations: plain `bal` never converts, but an
      -- unseen price commodity picks up a TENTATIVE precision from
      -- the price literal (pool.cc: COMMODITY_PRECISION_FROM_PRICE).
      -- C++ grants it when the commodity's precision is 0 and the
      -- commodity is neither known nor locked (pool.cc:628-634), and
      -- the source commodity of a price directive becomes known
      -- (pool.cc:647), while this rule grants it only to a commodity
      -- for which no precision is recorded. Both halves of the
      -- difference are known departures. After `X $10` against an
      -- elided `Y` has taught `$` precision 0,
      -- `P 2024/01/01 EUR $1.2345` gives `$` four tentative places in
      -- C++ and none here, so that C++ prints a later `(1/3 $)` as
      -- `0.3333 $`, which rounds away here (wrong rows), and rejects a
      -- later `($3/10)` against `$0`, which is accepted here
      -- (fail-open). After `P 2024/01/01 EUR $1.2345` and
      -- `P 2024/01/01 FOO 1.25 EUR`, EUR is known in C++ and keeps
      -- precision 0, so that a later `(1/3 EUR)` prints no row there
      -- and 0.33 here (wrong rows)
      let toks := (restS.splitOn " ").filter (!·.isEmpty)
      match toks.reverse with
      | last :: _ =>
          (match parseAmount st.amt n last with
           | .ok r =>
               if r.amount.comm != ""
                   && (st.precisions.lookup r.amount.comm).isNone then
                 pure { st with
                   precisions := (r.amount.comm, r.decimals) :: st.precisions
                   tentativePrec := r.amount.comm :: st.tentativePrec }
               else pure st
           | .error _ =>
               -- SYM PRICE tail split across two tokens
               match toks.reverse with
               | amtTok :: symTok :: _ =>
                   (match parseAmount st.amt n (symTok ++ " " ++ amtTok) with
                    | .ok r =>
                        if r.amount.comm != ""
                            && (st.precisions.lookup r.amount.comm).isNone then
                          pure { st with
                            precisions := (r.amount.comm, r.decimals)
                              :: st.precisions
                            tentativePrec := r.amount.comm :: st.tentativePrec }
                        else pure st
                    | .error _ => pure st)
               | _ => pure st)
      | _ => pure st
  | "C" => do
      -- commodity equivalence: `C 1.00s = 100c`
      match restS.splitOn "=" with
      | [lhs, rhs] => do
          let l ← parseAmount st.amt n (trimS lhs)
          let r ← parseAmount st.amt n (trimS rhs)
          if l.amount.q == 0 then err n "zero left side in C directive"
          else
            -- the directive's literals teach display precision
            -- (`C 1.00s = 100c` gives s two decimals)
            let st := bumpPrecision st l.amount.comm l.decimals
            let st := bumpPrecision st r.amount.comm r.decimals
            -- a user redefinition of `s` supersedes the built-in time
            -- chain (C++ time units are internal, not commodity
            -- equivalences)
            let equivs :=
              if l.amount.comm == "s" || r.amount.comm == "s" then
                st.equivs.filter fun (u, f, b) =>
                  !((u == "h" && f == 3600 && b == "s")
                    || (u == "m" && f == 60 && b == "s"))
              else st.equivs
            let f := r.amount.q / l.amount.q
            if f == 1 then
              -- 1:1 equivalences canonicalize into the null
              -- commodity when either side is bare (2057,
              -- 1E192DF6), else into the left side
              if l.amount.comm == "" then
                pure { st with equivs := (r.amount.comm, 1, l.amount.comm) :: equivs }
              else if r.amount.comm == "" then
                pure { st with equivs := (l.amount.comm, 1, r.amount.comm) :: equivs }
              else
                pure { st with equivs := (r.amount.comm, 1, l.amount.comm) :: equivs }
            else
              pure { st with equivs := (l.amount.comm, f, r.amount.comm) :: equivs }
      | _ => err n s!"malformed C directive '{restS}'"
  | "D" => do
      -- default display format: declare the precision and the style,
      -- and LOCK the precision, as COMMODITY_STYLE_NO_MIGRATE does in
      -- C++ (textual_directives.cc:165; #761/#1054). C++ parses the
      -- directive's amount with migration and only then locks the
      -- commodity (textual_directives.cc:149-166), so that a higher
      -- precision learned earlier survives the directive
      -- (amount.cc:1847-1848), while `lockPrecision` sets the
      -- directive's own decimals. This known departure governs the rows
      -- printed and the zero test: after `A $500.12345` against an
      -- elided `B` and then `D $1,000.00`, C++ prints A as `$500.12345`
      -- and a later `($1/3)` as `$0.33333`, which show as 500.12 and
      -- 0.33 here (wrong rows),
      -- and it rejects a later `$1.001` against `$-1.00`, which is
      -- accepted here (fail-open). C++ locks the style with the same
      -- flag, which `lockPrecision` does not model; the style rule of
      -- `finalizeXact` records that departure
      match parseAmount st.amt n restS with
      | .ok r =>
          let st := lockPrecision st r.amount.comm r.decimals
          match r.learned with
          | some (c, b) =>
              pure { st with amt := { st.amt with styles := (c, b) :: st.amt.styles } }
          | none => pure st
      | .error _ => pure st
  | "N" => pure st       -- no-market flag: valuation reports only
  | "Y" =>
      pure { st with defaultYear := restS.toNat?.map Int.ofNat }
  | "year" =>
      pure { st with defaultYear := restS.toNat?.map Int.ofNat }
  | "assert" => pure st  -- checked by the C++ side; positive tests pass
  | "check" => pure st
  | "eval" => pure st    -- side-effect-free in the positive corpus
  | "value" => pure st   -- valuation expression: reports only
  | "import" => pure st  -- python import: only reachable in _py tests
  | "payee" => pure st   -- payee declarations: labels only
  | "capture" =>
      -- account capture rewrites: report-time account mapping
      let (to_, from_?) := splitField restS
      match from_? with
      | some from_ => do
          let rx ← match compileRegex (trimS from_) with
            | .ok r => pure r
            | .error e => err n e
          pure { st with rewrites := st.rewrites ++ [(rx, trimS to_)] }
      | none => err n s!"malformed capture '{restS}'"
  | _ =>
      if word.startsWith "Y" && (word.drop 1).toString.toList.all Char.isDigit then
        pure { st with defaultYear := (word.drop 1).toString.toNat?.map Int.ofNat }
      else if word.startsWith "--" then
        -- in-file option lines: apply the parse-semantic ones,
        -- ignore the report-time rest (the C++ reader accepts any)
        let base := (word.splitOn "=").headD word
        let val :=
          if (word.splitOn "=").length > 1 then
            String.intercalate "=" ((word.splitOn "=").drop 1)
          else restS
        if base == "--decimal-comma" then
          pure { st with amt := { st.amt with dcDefault := true } }
        else if base == "--recursive-aliases" then
          pure { st with recursiveAliases := true }
        else if base == "--input-date-format" then
          let order := (trimS val).toList.filterMap fun c =>
            if c == 'Y' || c == 'y' then some 'y'
            else if c == 'm' then some 'm'
            else if c == 'd' then some 'd'
            else none
          pure { st with dfmt := if order.isEmpty then none else some order }
        else if base == "--now" then
          match headerDate none (trimS val) with
          | some d => pure { st with nowSecs := some ((d * 86400 : Int) : ℚ) }
          | none => pure st
        else
          pure st
      else if word == "expr" || word == "eval" then
        pure st          -- evaluate-and-discard
      else
        -- unrecognized word directive: the C++ reader warns and
        -- skips it (and its indented block) under --permissive
        pure { st with errFlag := true }

/-! ## The engine -/

structure Result where
  gens : List (List (Account × ℚ))
  rewrites : List (Rx × String)
  equivs : List (String × ℚ × String)
  precisions : List (String × Nat)
  styles : List (String × Bool)
  flowStats : List ((String × String) × Nat × Nat)

private def flushPending (st : St) : Except String St := do
  match st.pending with
  | .xact ln h posts => finalizeXact { st with pending := .none } ln h posts.reverse
  | .auto posts => finalizeAuto { st with pending := .none } posts.reverse
  | .periodic ln h posts =>
      -- a `~` template must balance as a transaction without a date
      -- does: C++ finalizes it on parse (textual_xacts.cc:316) and
      -- throws from xact.cc:960-965 or 973-979, or from xact.cc:336-346
      -- for a second null posting. Witnesses, all rejected by C++:
      -- DDB54BB8, cov6-txact-period-unbalanced,
      -- cov9d-period-xact-unbalanced, coverage-periodic-unbalanced,
      -- coverage-textual-periodic-unbalanced, 5D92A5EB. Lot matching
      -- and the lot gains of Phases 5 and 6 run only for a transaction
      -- with a date (`if (has_date())`, xact.cc:522), so the postings
      -- of a template book no gain: `~ Monthly` over
      -- `Assets:Broker 10 AAPL {$10}` and `Assets:Cash $-150` balances,
      -- as does `-10 AAPL {$10} @ $15` against `$150`. The template is
      -- finalized against the state before it and its result is
      -- discarded: it contributes no flows to the balance report, since
      -- C++ keeps a template in `period_xacts` (textual_xacts.cc:318)
      -- and reports walk `xacts` (iterators.cc:53-54), and it teaches
      -- the oracle nothing. A template inherits the departures of a
      -- dated transaction, among them those that `impliedExchange` and
      -- `balancePool` record, value expressions that the reader cannot
      -- evaluate, such as `(abs($-10))`, and an empty or
      -- whitespace-only line among the postings, at which C++ ends them
      -- (textual_xacts.cc:945, 949-950), so that it finds the postings
      -- before the line unbalanced or refuses the indented line after
      -- it (textual.cc:289), while the reader skips the blank line
      -- (fail-open). Besides these, the following departures are known.
      -- C++ parses a template's postings before it balances them
      -- (textual_xacts.cc:312), and each posting amount migrates its
      -- display precision and style to its commodity there as in a
      -- dated transaction (amount.cc:1830-1864), so that a balanced
      -- template teaches C++ what the same amounts would teach in a
      -- dated one. A cost or a lot price, parsed without migration
      -- (textual_xacts.cc:691, 693-694; annotate.cc:187), teaches
      -- nothing on either side: after a template with
      -- `X 10 AAPL @ $1.2345` or `X 10 AAPL {$1.2345}` against an
      -- elided `Y`, neither prints a row for a later `(1/3 $)`. The
      -- oracle discards everything that a template teaches, since
      -- keeping it would carry into templates the departures of this
      -- reader's precision and style model for dated amounts, which are
      -- recorded beside the `D` and `P` directives, the style and
      -- precision rules of `finalizeXact` and the `alias` subdirective.
      -- What C++ learns governs the rows printed, the balancing verdict
      -- and the reading of later amounts, so this departure fails in
      -- either direction. In the rows printed: after a template with
      -- `X $500.1` against an elided `Y`, C++ prints a later `(1/3 $)`
      -- as `0.3 $`, which rounds away here (wrong rows), and after one
      -- with `X 1.000,50 EUR` it prints a later `1234 EUR` as
      -- `1.234,00 EUR`, where the oracle prints the same value but
      -- declares no `%% dc EUR` (a missing declaration). In the
      -- balancing verdict: after one with `X $1.000`, C++ rejects a
      -- later `A 3 X @ $0.333` against `B $-1.00`, which is accepted
      -- here (fail-open), and
      -- `zeroTestPrec` records a fail-closed effect on the zero test.
      -- In the reading of later amounts: after one with `X 10,50 EUR`,
      -- C++ rejects a later `5.25 EUR`, which is accepted here
      -- (fail-open), and after one with `X EUR 10,50` it accepts a
      -- later `EUR 1,500` against `EUR -1,5`, reading 1.5 in each,
      -- which is rejected here (fail-closed). Each of the following is
      -- rejected by C++ and accepted here (fail-open): a balance
      -- assertion or assignment `=` in a template, which C++ reads with
      -- no transaction (textual_xacts.cc:952), so that the `=` is never
      -- taken as one (textual_xacts.cc:743) and is refused as an
      -- unexpected character; an automated transaction whose postings
      -- unbalance a template, which C++ applies and checks again
      -- (textual_xacts.cc:317, xact.cc:1683-1684); and a period
      -- expression that C++ cannot read, or a note after it, which C++
      -- rejects (textual_xacts.cc:303, baseline/cmd-source.test) and
      -- which is not read here
      match finalizeXact { st with pending := .none } ln h posts.reverse
          (periodic := true) with
      | .ok _ => pure { st with pending := .none }
      | .error e => .error s!"periodic transaction: {e}"
  | _ => pure { st with pending := .none }

/-- A code point that C++ `read_line` drops from the end of a line
    once the trailing ASCII whitespace is gone (`is_unicode_whitespace`,
    textual.cc:136-163, applied at 203-226). -/
def isUnicodeWs (c : Char) : Bool :=
  [0x85, 0xA0, 0x1680, 0x2028, 0x2029, 0x202F, 0x205F, 0x3000].contains c.toNat
    || (0x2000 ≤ c.toNat && c.toNat ≤ 0x200A)

/-- A line as C++ `read_line` leaves it before any directive sees it
    (textual.cc:198-226): the trailing characters that `std::isspace`
    accepts (space, tab, line feed, vertical tab, form feed and carriage
    return) dropped, then the trailing Unicode whitespace (`isUnicodeWs`),
    and no ASCII whitespace after that. The engine's own view of a line
    in `run` keeps a trailing vertical tab, form feed or Unicode
    whitespace, so the tests that decide which lines C++ executes apply
    this first. -/
def readLineTrim (t : String) : String :=
  let ascii := t.toList.reverse.dropWhile fun c =>
    c == ' ' || c == '\t' || c == '\n' || c == '\x0B' || c == '\x0C' || c == '\r'
  String.ofList (ascii.dropWhile isUnicodeWs).reverse

/-- The directive word of a line and the argument after it, as C++
    finds them in `general_directive`: the first word, split at a space
    or a tab (`next_element`, utils.h:623-640), with at most two `@` or
    `!` prefixes dropped (textual.cc:321-324, textual_directives.cc:1031),
    and the rest of the line after the spaces and tabs that follow the
    word (`skip_ws`, utils.h:598-602). An indented line has an empty
    word. `t` is expected to have passed through `readLineTrim`. -/
def directiveWord (t : String) : String × String :=
  let isSep := fun (c : Char) => c == ' ' || c == '\t'
  let word := String.ofList (t.toList.takeWhile (!isSep ·))
  let arg := String.ofList ((t.toList.dropWhile (!isSep ·)).dropWhile isSep)
  let unprefix := fun (w : String) =>
    if w.startsWith "@" || w.startsWith "!" then (w.drop 1).toString else w
  (unprefix (unprefix word), arg)

/-- A line that opens a `comment` or `test` block, which the engine
    skips through the line that `closesCommentBlock` accepts. `t` is
    the engine's view of a line in `run` (the text before any carriage
    return, its trailing spaces and tabs dropped), which this test
    first trims as C++ `read_line` does (`readLineTrim`), so that a
    word followed by a form feed or by a no-break space opens a block
    as it does in C++. C++ opens a block
    on the directive word (`directiveWord`) `comment` or `test`
    whatever argument follows it (textual_directives.cc:1035-1036,
    1071-1072, 1124-1125), reads the block with `comment_directive`,
    and never executes a line inside it. An indented line has an empty
    word, so it opens nothing. `splice` in Driver.lean asks the same
    two questions, so that it resolves no include inside a block. -/
def opensCommentBlock (t : String) : Bool :=
  let w := (directiveWord (readLineTrim t)).1
  w == "comment" || w == "test"

/-- The line that ends a block opened by `opensCommentBlock`. C++
    `comment_directive` ends either kind of block at the first line
    that begins with `end comment` or `end test`, so leading whitespace
    keeps a line inside the block and text after the two words does not
    (textual_directives.cc:941-949). -/
def closesCommentBlock (t : String) : Bool :=
  t.startsWith "end comment" || t.startsWith "end test"

/-- Run the engine over (include-spliced) journal text. -/
def run (input0 : String) (dcDefault : Bool := false)
    (nowSecs : Option ℚ := none) (recAliases : Bool := false)
    (dfmtS : Option String := none) : Except String Result := do
  let dfmt := dfmtS.bind fun f =>
    let order := f.toList.filterMap fun c =>
      if c == 'Y' || c == 'y' then some 'y'
      else if c == 'm' then some 'm'
      else if c == 'd' then some 'd'
      else none
    if order.isEmpty then none else some order
  -- a leading BOM is transparent to the reader
  let input := if input0.startsWith "\uFEFF" then
      (input0.drop 1).toString else input0
  let mut st : St := { amt := { dcDefault }, nowSecs, dfmt
                       recursiveAliases := recAliases }
  let mut n : Nat := 0
  for line0 in input.splitOn "\n" do
    n := n + 1
    let line := (line0.splitOn "\r").headD ""
    let t := line.trimAsciiEnd.toString
    if st.inComment then
      if closesCommentBlock t then
        st := { st with inComment := false }
      continue
    if t.isEmpty
        || t.toList.all (fun c => c == ' ' || c == '\t' || c.toNat == 160) then
      continue   -- blank, including Unicode-whitespace-only (1091)
    let c := line.front
    if c == ' ' || c == '\t' then
      -- indented: belongs to the pending block; after a skipped
      -- (unrecognized) line, its indented continuation is skipped
      -- too, exactly as the permissive C++ reader does
      let danglingIndent :=
        st.errFlag && (match st.pending with | .none => true | _ => false)
      if danglingIndent then
        continue
      match st.pending with
      | .xact ln h posts =>
          let body := trimS t
          if body.isEmpty then continue
          if body.front == ';' then
            -- note line: keep for uuid detection via raw storage
            st := { st with pending := .xact ln h ((n, body) :: posts) }
          else
            st := { st with pending := .xact ln h ((n, t) :: posts) }
      | .periodic ln h posts =>
          let body := trimS t
          if body.isEmpty then continue
          -- a comment line in a template is dropped, not kept as a
          -- note: C++ collects its postings with parse_posts, which
          -- skips a line that begins with `;` (textual_xacts.cc:951)
          if body.front == ';' then continue
          st := { st with pending := .periodic ln h ((n, t) :: posts) }
      | .auto posts =>
          let body := trimS t
          if body.isEmpty then continue
          -- comment lines ride along: they are the rule's note tag
          st := { st with pending := .auto ((n, t) :: posts) }
      | .acctBlock frames =>
          let body := trimS t
          let ind := (line.toList.takeWhile fun c =>
            c == ' ' || c == '\t').length
          -- close frames at deeper-or-equal indentation
          let frames := frames.filter fun (i, _) => i < ind
          let name := ((frames.head?).map (·.2)).getD ""
          if body.startsWith "account " then
            let nm := trimS (body.drop "account ".length).toString
            let nm := (unquote nm).getD nm
            let full := if name.isEmpty then nm else name ++ ":" ++ nm
            st := { st with pending := .acctBlock ((ind, full) :: frames) }
            continue
          st := { st with pending := .acctBlock frames }
          if body.startsWith "alias " then
            let al := trimS (body.drop "alias ".length).toString
            let al := (unquote al).getD al
            st := { st with aliases := (al, name) :: st.aliases }
          else if body.startsWith "payee " then
            match compileRegex (trimS (body.drop "payee ".length).toString) with
            | .ok rx =>
                st := { st with payeeAccountRules :=
                  st.payeeAccountRules ++ [(rx, name)] }
            | .error _ => pure ()
          else if body == "default" then
            st := { st with bucket := some name }
          else if body.startsWith "assert " || body.startsWith "check "
              || body.startsWith "eval " || body.startsWith "note "
              || body.startsWith "format " then
            continue  -- verified or report-time only (953)
          -- note/payee/check/assert/eval/format subdirectives: labels
          -- or verified by the C++ side
          continue
      | .commBlock comm =>
          let body := trimS t
          if body.startsWith "alias " then
            -- the alias name now denotes the block's commodity
            -- (textual_directives.cc:844-849). Where the name already
            -- denoted a commodity of its own, C++ retires that
            -- commodity with the style it learned (pool.cc:150-173), so
            -- that a later amount written under the name reads with the
            -- style of the block's commodity, while the style learned
            -- under the name is kept here, a known departure: after
            -- `X 10,50 E` against an elided `Y` and then
            -- `commodity EUR` with `alias E`, C++ reads a later
            -- `1,500 E` as 1500 EUR, where it is read as 1.5 here
            -- (wrong rows), and accepts a later `5.25 E`, which is
            -- rejected here as ambiguous (fail-closed)
            let al := trimS (body.drop "alias ".length).toString
            let al := (unquote al).getD al
            st := { st with commAliases := (al, comm) :: st.commAliases }
            continue
          else if body.startsWith "format " then
            -- the format subdirective DECLARES the display precision
            -- and locks it against migration (opt-round, 1795, 628)
            let sample := trimS (body.drop "format ".length).toString
            match (parseAmount st.amt n sample) with
            | .ok r =>
                st := lockPrecision st
                  (if r.amount.comm == "" then comm else r.amount.comm)
                  r.decimals
                match r.learned with
                | some (c', b) =>
                    st := { st with amt := { st.amt with
                      styles := (c', b) :: st.amt.styles } }
                | none => pure ()
            | .error _ =>
                -- formats may show styles we infer elsewhere; the C++
                -- side still validates the journal itself
                pure ()
          let _ := comm
          continue
      | .ignoreBlock => continue
      | .none =>
          -- permissive: warn-and-skip (line-level), like the C++
          -- reader under --permissive
          st := { st with errFlag := true }
          continue
    else do
      st ← flushPending st
      st := { st with errFlag := false }
      if c.isDigit then
        st := { st with pending := .xact n t [] }
      else if t.startsWith "i " || t.startsWith "I " then
        let body := (splitNote (trimS (t.drop 2).toString)).1
        let dateS := String.ofList (body.toList.takeWhile (· != ' '))
        let rest1 := trimS (body.drop dateS.length).toString
        let timeS := String.ofList (rest1.toList.takeWhile (· != ' '))
        let rest2 := trimS (rest1.drop timeS.length).toString
        let (acct, payee?) := splitField rest2
        let secs ← parseDateTime n dateS timeS
        -- the account-block payee rules apply to timeclock payees too
        -- (regress/1211): an Unknown-ish account maps by payee
        let acct := resolveAccount st acct
        let acct := match payee? with
          | some pay =>
              if acct.endsWith ":Unknown" || acct == "Unknown" then
                match st.payeeAccountRules.find? fun (rx, _) =>
                    regexSearch rx pay with
                | some (_, target) => target
                | none => acct
              else acct
          | none => acct
        st := { st with clockIn := st.clockIn ++ [(secs, acct)] }
      else if t.startsWith "o " || t.startsWith "O " then
        let body := (splitNote (trimS (t.drop 2).toString)).1
        let dateS := String.ofList (body.toList.takeWhile (· != ' '))
        let rest1 := trimS (body.drop dateS.length).toString
        let timeS := String.ofList (rest1.toList.takeWhile (· != ' '))
        let rest2 := trimS (rest1.drop timeS.length).toString
        let (named, _desc) := splitField rest2
        let stop ← parseDateTime n dateS timeS
        -- clock_out_from_timelog: a single open entry closes no
        -- matter what account the o line names (723); with several,
        -- the account picks the entry
        let pick? :=
          match st.clockIn with
          | [only] => some only
          | _ =>
              if named.isEmpty then none
              else st.clockIn.find? fun (_, a) =>
                a == named || a == resolveAccount st named
        match pick? with
        | none => err n "timeclock check-out without check-in"
        | some (start, acct) =>
            -- create_timelog_xact: with a bucket account declared, C++
            -- adds a second posting of the negated duration to it, so
            -- the entry balances; with none the account's posting
            -- stands alone (timelog.cc:84-91, regress/1607). Neither
            -- is balance-checked, since a timelog posting need not
            -- balance (post.h:244-245)
            let flows := match st.bucket with
              | some b => [(Account.mk acct "s", stop - start),
                           (Account.mk b "s", start - stop)]
              | none => [(Account.mk acct "s", stop - start)]
            st := { st with gens := flows :: st.gens
                            clockIn := st.clockIn.filter fun (s0, a) =>
                              !(s0 == start && a == acct) }
            for (a, dq) in flows do
              st := bumpBal st a.name a.commodity dq
              st := bumpStat st a.name a.commodity false
              -- POST_IS_TIMELOG: visible to assignments' combined
              -- balance but never to the real-only side
              st := { st with datedEvents :=
                ((a.name, a.commodity), ((stop / 86400 : ℚ).floor : Int),
                 dq, false) :: st.datedEvents }
      else if t.startsWith "= " then
        -- auto-xact: compile predicate, collect template block;
        -- also `= NAME disable` / `= NAME enable` toggles
        let predS := trimS (t.drop 1).toString
        let toggle? :=
          let ws := predS.splitOn " "
          match ws.reverse with
          | last :: restRev =>
              if restRev.isEmpty then none
              else
                let nm := String.intercalate " " restRev.reverse
                if last == "disable" then some (nm, some false)
                else if last == "enable" then some (nm, some true)
                else if last == "delete" then some (nm, none)
                else none
          | _ => none
        let nameMatches := fun (nm : String) (r : AutoRule) =>
          let nm := unquoteAny nm
          match r.name with
          | some n =>
              n == nm ||
              (match compileRegex nm with
               | .ok rx => regexSearch rx n
               | .error _ => false)
          | none => false
        match toggle? with
        | some (nm, some on) =>
            st := { st with autos := st.autos.map fun r =>
              if nameMatches nm r then { r with active := on } else r }
        | some (nm, none) =>
            st := { st with autos := st.autos.filter fun r =>
              !(nameMatches nm r) }
        | none =>
        -- `= "name" :: PRED` names the rule
        let (ruleName, predS) :=
          match predS.splitOn "::" with
          | [nm, rest] =>
              let nm := trimS nm
              (some (unquoteAny nm), trimS rest)
          | _ => (none, predS)
        let branches ← compilePred st n predS
        st := { st with
          autoPred := (branches, ruleName) :: st.autoPred
          pending := .auto [] }
      else if t.startsWith "~" then
        -- periodic entries generate no postings in plain reports, but
        -- are balance-checked when the block closes (flushPending)
        st := { st with pending := .periodic n t [] }
      else if opensCommentBlock t then
        st := { st with inComment := true }
      else if t == "h" || t.startsWith "h " || t == "b"
          || t.startsWith "b " then
        continue  -- historical timelog compatibility: ignored
      else if t.startsWith "@account " || t.startsWith "!account " then
        let nm := trimS (t.drop "@account ".length).toString
        st := { st with pending := .acctBlock [(0, (unquote nm).getD nm)] }
      else if t.startsWith "@commodity " || t.startsWith "!commodity " then
        let nm := trimS (t.drop "@commodity ".length).toString
        st := { st with pending := .commBlock ((unquote nm).getD nm) }
      else if t.startsWith "account " || t.startsWith "account\t" then
        let nm := trimS (t.drop "account ".length).toString
        st := { st with pending := .acctBlock [(0, (unquote nm).getD nm)] }
      else if t.startsWith "commodity " || t.startsWith "commodity\t" then
        let nm := trimS (t.drop "commodity ".length).toString
        st := { st with pending := .commBlock ((unquote nm).getD nm) }
      else if t.startsWith "payee " || t.startsWith "tag " then
        st := { st with pending := .ignoreBlock }  -- label declarations
      else if t.startsWith "@" || t.startsWith "!" then
        -- historical directive prefixes
        st ← handleDirective st n (t.drop 1).toString
      else if isCommentStart c then
        continue
      else
        st ← handleDirective st n t
  st ← flushPending st
  -- dangling check-ins auto-close at the pinned `--now` instant
  match st.nowSecs with
  | some nowS =>
      -- future check-ins are dropped, not negatively closed (1689)
      for (start, acct) in st.clockIn do
        if start ≤ nowS then
          -- time_log_t::close checks each one out through the same
          -- create_timelog_xact, bucket posting included
          -- (timelog.cc:173-195, 84-91)
          let flows := match st.bucket with
            | some b => [(Account.mk acct "s", nowS - start),
                         (Account.mk b "s", start - nowS)]
            | none => [(Account.mk acct "s", nowS - start)]
          st := { st with gens := flows :: st.gens }
          for (a, dq) in flows do
            st := bumpBal st a.name a.commodity dq
            st := bumpStat st a.name a.commodity false
      st := { st with clockIn := [] }
  | none => pure ()
  pure ⟨st.gens.reverse, st.rewrites, st.equivs, st.precisions,
        st.amt.styles, st.flowStats⟩

/-- Apply report-time account rewrites (`account-rewrite`,
    `capture`) to a name. -/
def applyRewrites (rw : List (Rx × String)) (name : String) : String :=
  match rw.find? fun (rx, _) => regexSearch rx name with
  | some (_, to_) => to_
  | none => name

end Journal

end Ledger
