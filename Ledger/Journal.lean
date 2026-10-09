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
    precision as C++ prints an amount (`Parse.cppRoundAt`), widened in
    the real pool for a cost commodity shown without decimals
    (regress/1114), and asks for exact zero in the null commodity. A
    residual left to these tests passes when its part in each
    commodity passes the zero test or lies within the sum of half a
    unit in the last place of each cost written with decimals in that
    commodity. In either pool that allowance stands in for the
    per-unit cost rounding that C++ adjusts in the real pool alone
    (regress/1125, `costTol`).
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
  postings of the same transaction (regress/1005). A real assignment
  leaves out the virtual postings when its account has a real posting
  in an earlier transaction, in any commodity (#543, #1699). A target
  without a commodity is measured against every commodity that the
  account holds or that its earlier postings in the transaction bring;
  as in C++, a difference left in more than one commodity rejects the
  journal unless every amount left rounds to zero (balance.h:473-480),
  and otherwise the single amount left is posted, or a zero when what
  is left rounds to zero. With an amount present it is an assertion:
  positive tests pass their assertions by definition, so it is checked
  *by the C++ side* and dropped here.
- **Auto-xacts** `= /regex/`: template postings (fixed amounts or
  bare multipliers × the matched posting's amount) are appended per
  matching real posting of each later transaction — after balancing,
  as `extend_xact` does; templates may be virtual. C++ also matches
  virtual and deferred postings, a departure recorded at `applyAutos`.
  C++ matches as well every posting by which it completes an elided
  posting or the bucket's posting, and it can complete a commodity
  with one posting per annotated key, or with postings in a commodity
  that nets to zero, where the engine makes one posting or none;
  `applyAutos` refuses a rule whose effect depends on those postings,
  the check that C++ makes after it included, as out of scope, but for
  the departures that its docstring and that of `PoolResult.splitComms`
  record.
  After each rule that adds a posting that must balance, C++ checks
  the extended transaction once more (`verify()`, xact.cc:1040-1110,
  1683-1684), weighing a generated posting at the cost that its
  template writes or, when the matched posting has a cost, at the cost
  that C++ derives from the lot price of the generated amount, the
  template amount's own or the one copied from the matched posting;
  `verifyExtended` makes that check and lists its departures.
- **Timeclock** `i`/`o`: time postings (duration in canonical
  seconds), with the opposite amount posted to the bucket account
  when one is declared (regress/1607); no balance check.
- **UUID dedup**: a transaction in whose body `uuidOf` finds a UUID
  already seen is dropped whole but for the prices that its costs
  record, since C++ finalizes it before it drops it (C++ `journal.cc`
  semantics); it is the one documented non-flow-inert label. C++ reads
  the transaction's own `UUID` tag instead, a departure in the rows that
  the docstring of `uuidOf` records.
- **Periodic templates** `~`: finalized as a transaction without a
  date against the state before them, booking no lot gain and with no
  UUID de-duplication. As C++ `parse_posts` reads the postings, a line
  beginning with `;` is dropped and a line beginning with `assert `,
  `check ` or `expr ` is a posting. The result is discarded, together
  with the display precisions and amount styles that its amounts teach
  C++ and with the postings that automated transactions generate in
  it, which C++ gives to their accounts, two departures that
  `flushPending` records; an error in the template is reported with
  the prefix `periodic transaction: `.
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
  /-- the posting is a completion that `costTagged` in `balancePool`
      marks as C++ tags an inferred amount that fits the precision of a
      cost (BIGINT_COST_PREC); the comment on COST_PREC tagging beside it
      records the ways in which the mark departs from the tag, two tests
      of C++ that it weakens among them; `bumpStat` counts it for a lone
      inferred amount, and `finalizeXact` reads it for `St.lotFanout` -/
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
  /-- the factor by which a commodity equivalence reduced the amount,
      and by which `lotUnit` was divided, or 1 when none applies. C++
      parses the amount unreduced (textual_xacts.cc:583) and reduces it
      at the end of `finalize` for a transaction, but not for a
      periodic template (xact.cc:987-996), nor for a posting that an
      automated transaction generates afterwards. Where the amount stays
      unreduced, its price per unit, which C++ takes as the whole cost
      derived from a lot marked as a total (xact.cc:1617-1621), is
      `lotUnit` times this factor. -/
  lotScale : ℚ := 1
  assignTarget : Option Amount := none
  /-- the amount itself is annotated (`{lot}`, `[date]` or `(note)`
      before any cost or balance assertion): C++'s
      `amount.has_annotation()`, which picks the top posting of an
      implicit exchange (xact.cc:386-393). C++ discards the annotation
      of an amount with no commodity (amount.cc:1908), and so does
      this flag. `balancePool` reads it as well, for the weight of a
      posting without a cost (`PoolResult.splitComms`), and so does
      `applyAutos`, for the refusal that waits for `verifyExtended`,
      the second case of its docstring. The two departures recorded at
      `fixated` apply to this flag as well. -/
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
  /-- the cost amount carries an annotation of its own, a `{lot}`,
      `[date]` or `(note)` written after the cost and before any balance
      assertion, on a cost with a commodity. C++ parses the cost as an
      amount with its annotations (textual_xacts.cc:691), keeps them only
      on an amount with a commodity (amount.cc:1908), and sums the cost
      under its annotated commodity in Phase 1 of `finalize`
      (xact.cc:325-333). `balancePool` reads it, as it reads `annotated`
      for a posting without a cost, where it completes an elided posting
      or the bucket's posting (`PoolResult.splitComms`), and `applyAutos`
      reads both flags for the refusal that waits for `verifyExtended`,
      the second case of its docstring.

      For a posting whose own amount carries a lot price, Phase 6 books
      no gain of the usual kind on such a cost, since its annotated
      commodity is not the plain commodity of the basis (xact.cc:693,
      annotate.cc:343-355). It books instead a gain apart, plain, in the
      commodity of the lot price, of the basis less the cost times the
      price that annotates the cost, and only when that price is in the
      commodity of the lot price, whatever the commodity of the cost
      (xact.cc:735-774). `costVal` adds the gain of the usual kind, the
      basis less the cost (`gainVal`), to a cost in the commodity of the
      lot price, annotated or not, and no gain to a cost in another
      commodity; `balancePool` counts that gain as a weight of its own.
      Three departures follow, each of which gives wrong rows without
      any automated transaction:
      - where the annotation of the cost has no price in the commodity
        of the lot price, C++ books no gain:
        `Assets:S  10 c {$60} @ $5 (note)` completes an elided posting
        with `$-50 (note)` in C++ and with `$-600` here;
      - where that price is not one unit, the two gains differ:
        `Assets:T  10 AAPL {$50} @ $5 {$20}` completes an elided posting
        with `$500` and `$-50 {$20}` in C++ and with `$-500` here;
      - where the cost is in another commodity, C++ books a gain that
        the engine does not: `Assets:T  10 AAPL {$50} @ 5 EUR {$1}`
        completes an elided posting with `$-450` and `-50 EUR {$1}` in
        C++ and with `-50 EUR` here, and the commodity swap of
        baseline/feat-commodity_swap, `-100 BTC {$100} @ 2 ETH {$40}`
        beside `200 ETH {$40}`, with the amount of its
        `Expenses:Capital Loss` posting removed, completes that posting
        with `$2,000.00` in C++ and leaves it without an amount here. -/
  costAnnotated : Bool := false
  /-- the posting is one by which `balancePool` completes an elided
      posting, or the bucket's posting, in a commodity that C++ can
      complete with one posting per annotated commodity
      (`PoolResult.splitComms`); `applyAutos` reads it, and so does
      `finalizeXact`, for `St.lotFanout` -/
  splitRisk : Bool := false
  /-- the cost as Phase 6 of `finalize` hands it to the exchange of the
      commodity pool (xact.cc:688-690): a per-unit `@ P` times the
      amount, or a total `@@ T` signed as the amount
      (textual_xacts.cc:699-710), before any lot gain is added to it
      (`costVal`). `finalizeXact` reduces it through the commodity
      equivalences, as C++ reduces a cost when it parses it
      (textual_xacts.cc:691, amount.cc:1905-1906). `none` without a
      cost; `costPrice` derives from it the price that the exchange
      records -/
  rawCost : Option Amount := none
  /-- the precision of `rawCost` as `costPrec` counts it before the raise
      that Phase 6 makes after the exchange: the cost literal's decimals,
      plus the amount's precision for a per-unit `@`, with the
      departures for an expression that the docstring of `zeroTestPrec`
      records (`costPrice`) -/
  rawCostPrec : Nat := 0
  /-- the cost is virtual, `(@)` or `(@@)` (POST_COST_VIRTUAL,
      textual_xacts.cc:657-660), and so records no price (`costPrice`) -/
  costVirtual : Bool := false
  /-- the commodity of a lot price that annotates the cost itself, one
      written after the cost and before any balance assertion on a cost
      with a commodity, when that price has a commodity (`costPrice`) -/
  costLotComm : Option String := none
  /-- the precision that C++ gives the amount: its literal's decimals,
      or for an amount expression the approximation of
      `parseAmountField` (`costPrice`) -/
  amtPrec : Nat := 0
  /-- the amount as written, before `finalizeXact` reduces it through
      the commodity equivalences, its commodity named through the
      commodity aliases: C++ parses a posting amount unreduced
      (textual_xacts.cc:583) and exchanges it so (`costPrice`) -/
  rawAmount : Option Amount := none
  /-- the amount has a commodity and no annotation of its own, and an
      `apply fixed` or `apply rate` directive in force names that
      commodity (`St.fixatedComms`), so that C++ annotates the amount
      with the fixated price of the directive (textual_xacts.cc:626-638).
      `costPrice` reads it alone: the engine keeps no such annotation, a
      departure that the docstring of `impliedExchange` records -/
  rateFixed : Bool := false
  /-- the date that a note of the posting gives it, the last of its note
      lines that gives one (`noteDateOf`): `some (some d)` for the day
      `d`, and `some none` for a date that this reader does not read -/
  noteDate : Option (Option Int) := none
  deriving Repr

instance : Inhabited PostSpec :=
  ⟨{ line := 0, account := "", kind := .real }⟩

structure AutoPost where
  account : String
  kind : PostKind
  fixed : Option Amount
  mult : ℚ
  exprSrc : Option String := none
  /-- the cost written on a fixed template amount, `@ P` times the
      amount or `@@ T`, which C++ copies to every posting generated from
      the template (xact.cc:1611-1612) -/
  cost : Option Amount := none
  /-- the precision of `cost`, counted as `PostSpec.costPrec` counts it
      for a posting whose cost Phase 6 does not change -/
  costPrec : Nat := 0
  /-- the lot price per unit of a fixed template amount with a
      commodity, written before any cost, counted as `PostSpec.lotUnit`
      counts it. C++ keeps the annotation on the template amount
      (amount.cc:1908) and so on every posting generated from it, and
      derives that posting's cost from it when the matched posting has
      a cost and the template posting none (xact.cc:1613-1627) -/
  lotUnit : Option Amount := none
  /-- the lot price of `lotUnit` is written as a total, `{{T}}` or
      `{{=T}}`, as `PostSpec.lotTotal` records it -/
  lotTotal : Bool := false
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
  /-- `tag("K") == "V"`, the whole predicate of regress/842, read only
      within the bounds of `tagEqScan` (`tagEqHolds`) -/
  tagEq : Option (String × String) := none

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

/-- The kind of a posting recorded in `St.datedEvents`, as a balance
    assignment reads it (compute_balance_diff, textual_xacts.cc:398-438).
    A timelog posting (POST_IS_TIMELOG, timelog.cc:67, 86) never makes
    an account's balance real-only, yet stays in the real-only balance,
    from which C++ leaves out only virtual postings. A deferred posting
    is recorded as a virtual one, and a deferred assignment, or a
    deferred earlier posting of the assignment's transaction, is read as
    virtual as well. This departs from C++ in three ways. C++ holds a
    deferred posting back from its account until the whole journal is
    read (xact.cc:1001-1003, textual.cc:413), so that no assignment
    reads one from an earlier transaction; it reads a deferred
    assignment as a real one in choosing the real-only balance
    (textual_xacts.cc:399); and it subtracts an earlier deferred posting
    of the transaction from that balance (textual_xacts.cc:467-469).
    With `<Assets:A>  $10` before, `Assets:A  = 0` against `Assets:B`
    posts a zero in C++ and moves the `$10` to `Assets:B` here, and so
    does `Assets:A  = $0`; with `Assets:A  $5` and `(Assets:A)  $10`
    before, C++ posts `$-5` for `<Assets:A>  = 0`, and `$-15` is posted
    here (wrong rows); with `Assets:A  $10` before, `<Assets:A>  5 EUR`
    followed by `Assets:A  = 0` in one transaction is rejected by C++
    and accepted here (fail-open), and `<Assets:A>  $3` followed by
    `Assets:A  = 0` posts `$-13` in C++ and `$-10` here (wrong rows). -/
private inductive EvKind where
  | real | virt | timelog
  deriving DecidableEq

/-- A point of the dated price table: at the instant `secs`, one unit of
    `comm` is worth `price`. The instant counts seconds from 0000-03-01
    00:00, the origin of the day count of every date that the reader
    reads (`daysFromCivil`) and of the instant of `--now`. C++ keeps the
    table as an undirected graph of commodities whose edge between two
    of them maps each instant to the price last recorded at it, in
    either direction (`commodity_history_impl_t`, history.cc:114-120,
    351-369; history.h:77). Its instants are local times without a zone,
    read here as written. `St.priceLog` holds the points that the
    directives and the costs read so far write, `priceTable` resolves
    them into the table, and `pricesAt` reads the table as of an
    instant. -/
structure PricePoint where
  secs : Int
  comm : String
  price : Amount
  deriving Repr, DecidableEq

/-- The table that the log `log` of written points, the most recent
    first, leaves: the point written last at each instant on each two
    commodities, in either direction, in the order in which the points
    that remain were written. C++ keys the prices of an edge of its
    undirected graph (history.cc:114-120) by their instant alone, and
    `add_price` overwrites the entry that it already holds
    (history.cc:351-369): after `P 2024/01/01 EUR $1.10` and
    `P 2024/01/01 $ 0.90 EUR`, the table holds the second point alone.
    test/regress/coverage-iterators-dup-price.test repeats an equal
    price at one instant, which `pricedb` lists once whether or not the
    entry is overwritten (iterators.cc:144-161), so the replacement of a
    different or a reversed price rests on history.cc:358-368 alone. The
    log is resolved once, when the journal has been read (`run`), in time
    linear in its length, where replacing the point on each write would
    cost time quadratic in the number of prices. -/
private def priceTable (log : List PricePoint) : List PricePoint := Id.run do
  let mut seen : Std.HashSet (Int × String × String) := {}
  let mut table : List PricePoint := []
  for pt in log do
    let key := if pt.price.comm < pt.comm then (pt.secs, pt.price.comm, pt.comm)
      else (pt.secs, pt.comm, pt.price.comm)
    if !seen.contains key then
      seen := seen.insert key
      table := pt :: table
  return table

/-- The points of `pts` that C++ reads as of the instant `t`: those
    whose instant is not after it. C++ finds a price (`find_price`,
    history.cc:442, 503) through the latest price of each edge that is
    not after the reference time (history.cc:257-263) and lists the
    prices not after it (history.cc:418). The reference time that the
    Driver's `--now DATE` gives is 00:00 of that date, as C++ sets it
    (global.cc:483-493), so that a price recorded at 00:00 of the
    `--now` date is read and one recorded later that day is not. -/
def pricesAt (pts : List PricePoint) (t : Int) : List PricePoint :=
  pts.filter (·.secs ≤ t)

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
  /-- account aliases: name → target, the target named under the
      `apply account` stack when the directive was read -/
  aliases : List (String × String) := []
  rewrites : List (Rx × String) := []
  /-- one entry for each `apply` directive in force, the innermost first:
      the account of an `apply account` directive, and `none` for an
      `apply` of another kind. `pushApply` and `popApply` alone change it,
      and they change `fixatedComms` and `applyTags` with it, so that the
      three lists stay in step -/
  applyStack : List (Option String) := []
  /-- one entry for each entry of `applyStack`, the innermost first: the
      commodity of an `apply fixed` or `apply rate` directive, named
      through the commodity aliases, and `none` for an `apply` of another
      kind. C++ annotates a posting amount in that commodity that has no
      annotation of its own with the fixated price of the directive
      (textual_xacts.cc:626-638), which `PostSpec.rateFixed` records -/
  fixatedComms : List (Option String) := []
  /-- one entry for each entry of `applyStack`, the innermost first: the
      text of an `apply tag` directive as C++ keeps it, trimmed and, when
      it holds no `:`, wrapped in colons (textual_directives.cc:493-501,
      527), and `none` for an `apply` of another kind. C++ reads each
      such text into every transaction under it as it reads a note of
      the transaction (textual_xacts.cc:1167-1188), and so takes from it
      the date of the transaction, which dates the prices of its costs
      (`noteDateOf`, `finalizeXact`) -/
  applyTags : List (Option String) := []
  bucket : Option String := none
  autos : List AutoRule := []
  autoPred : List (List PredSpec × Option String) := []
  defaultYear : Option Int := none
  uuids : List String := []
  balances : List ((String × String) × ℚ) := []
  datedEvents : List ((String × String) × Int × ℚ × EvKind) := []
  gens : List (List (Account × ℚ)) := []   -- reversed
  pending : Pending := .none
  /-- open timelog check-ins: the time, the account named under the
      `apply account` stack before any alias expands, and the
      check-in's description (`timelogAccount`) -/
  clockIn : List (ℚ × String × String) := []
  nowSecs : Option ℚ := none
  recursiveAliases : Bool := false
  errFlag : Bool := false
  tentativePrec : List String := []
  lockedPrec : List String := []
  dfmt : Option (List Char) := none
  /-- (account, commodity) → (flows, inferred flows): drives the
      BIGINT_COST_PREC display rule for lone inferred balances -/
  flowStats : List ((String × String) × Nat × Nat) := []
  /-- (account, commodity, debit) → (flows, inferred flows): the flows
      of nonzero amount that `flowStats` counts, counted apart for the
      debit column, `true`, and the credit column (`bumpStat`) -/
  signStats : List ((String × String × Bool) × Nat × Nat) := []
  /-- set when a pool that its elided posting or the bucket's posting
      completes has a commodity listed in `PoolResult.splitComms` whose
      weights have both signs, or whose completion is tagged
      (`PostSpec.splitRisk` and `PostSpec.inferred`); `Result.lotFanout`
      gives its meaning, where it is set in excess and where it is
      missed -/
  lotFanout : Bool := false
  /-- every point that the price directives and the costs of the
      transactions read so far write, the most recent first, which
      `priceTable` resolves into the dated price table when the journal
      has been read (`priceDirective`, `costPrice`, `recordCostPoints`) -/
  priceLog : List PricePoint := []
  /-- the commodities that the price directives and the costs read so
      far mark primary, as far as this reader records them
      (`priceDirective`, `recordCostPoints`), kept for valuation:
      balancing does not read them. The list is partial; `Result.primary`
      names what it leaves out -/
  primary : List String := []
  /-- the price directives and the costs whose point the table does not
      hold, or holds at a date that a note or an `apply tag` gives, each
      as an issue and the commodity that it prices, empty where that is
      not read (`priceDirective`, `recordCostPoints`, `finalizeXact`), the
      most recent first -/
  priceIssues : List (String × String) := []
  /-- set by an in-file `--now` line, after which the current time of
      C++ is not known here: the option takes a time with its date
      (report.h:1059-1074 at 76b9dc2b2), and the end of an included file
      and `end apply year` restore the time that came before
      (textual_directives.cc:424-446, 593-595), while `nowSecs` takes the
      date alone and keeps it to the end of the journal
      (`priceDirective`) -/
  nowInFile : Bool := false
  /-- set where the year that C++ gives a date of a month and a day may
      differ from `defaultYear`: from the start in a journal into which
      files are spliced, since C++ restores its year where an included
      file ends (textual_directives.cc:424-446), and at an `apply year`
      directive, which sets that year (textual_directives.cc:464-476,
      543-559) where `defaultYear` stays as it was. `priceDay` then reads
      no such date, whether it is the date of a price directive
      (`priceDirective`), of a transaction with a cost
      (`recordCostPoints`) or of a note (`noteDateOf`) -/
  yearUnsure : Bool := false
  /-- set where an input date format is given, by `--input-date-format`
      or an in-file line of it: C++ then tries that format before its
      own readers of a date without a time, which no longer read `.` and
      `-` as `/` (times.cc:229-243, 319-327, 2499-2502), while
      `parse_datetime`, which reads a date with a time, still does
      (times.cc:429-432). `dfmt` does not record this: it keeps the
      order of the fields alone, and nothing for a format that names no
      field (`priceDay`) -/
  inputDateFormat : Bool := false
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

/-- Does `q` round to zero at `p` decimals? C++ `amount_t::is_zero`
    prints the quantity at the precision in question through
    `stream_out_mpq` and finds no nonzero digit (src/amount.cc:1417-1425
    at 76b9dc2b2), so the test rounds as a printed amount does
    (`cppRoundAt`): at precision 6 a residual of half a unit,
    `0.0000005`, is zero, and at precision 7 the residual `0.00000005`
    is not. -/
private def roundsToZeroAt (p : Nat) (q : ℚ) : Bool :=
  cppRoundAt p q == 0

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
    transaction's postings in order: for the final zero test of
    `finalizeXact`, before automated postings are added, and for
    `verifyExtended`, followed by the postings generated so far, whose
    copied template costs `verify()` reads as well (xact.cc:1076-1091).

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
      (textual_xacts.cc:952), from an `apply fixed` rate
      (textual_directives.cc:534-535), and from the amount literals of
      the value expressions that it parses with migration, each of
      which but a literal in braces teaches its commodity its decimals
      as C++ reads it (token.cc:317-322, 542-555). These are all the
      value expressions but those of a cost and of a balance assertion
      or assignment, which C++ parses with PARSE_NO_MIGRATE
      (textual_xacts.cc:691-694, 756-760), and that of a posting
      amount, whose literals this reader approximates (the precision
      rule of `finalizeXact`). Among them are a `define`
      (textual_directives.cc:1081), a typed metadata value
      (metadata.cc:194), a `Value:` tag (post.cc:1064-1076), a line of a
      transaction that begins with `assert`, `check` or `expr`, before
      or after its postings (textual_xacts.cc:1107-1125), the `eval`,
      `expr`, `assert`, `check` and `value` directives
      (textual_directives.cc:911-937), the predicate of an automated
      transaction (textual_xacts.cc:221), the `assert`, `check`, `eval`,
      `expr` and `value` subdirectives of `account`
      (textual_directives.cc:647-681, 739-740), the `assert` and `check`
      subdirectives of `tag` (textual_directives.cc:901-904) and the
      `value` subdirective of `commodity`
      (textual_directives.cc:852-853). Where C++ holds a positive
      precision from one of these it widens nothing, so after
      `= /^NEVER/` with `(Y) 0.50 EUR`, `~ Monthly` with `X 0.50 EUR`
      against an elided `Y`, `define x = 0.50 EUR`, `; X:: 0.50 EUR` or
      `apply fixed BAZ 0.50 EUR`, the transaction `1.0001 FOO @ 1 EUR`
      against `-1 BAR @ 1 EUR` is rejected here and accepted by C++
      (fail-closed). The same gaps reach the rows: after a transaction
      of `Assets:Cash  $10` against an elided `Equity` with the line
      `check amount < $0.001`, C++ prints a later `($1/3)` against an
      elided `Equity` as `$0.333`, where this reader prints no row for
      it (wrong rows). The comment on periodic templates in
      `flushPending` and the `apply fixed` entry of `impliedExchange`
      record what the same gaps do to the other tests, and `costPrice`
      what they do to the prices of costs. -/
private def zeroTestPrec (st : St) (posts : List PostSpec) (comm : String) :
    Nat :=
  match (st.precisions.lookup comm).getD 0 with
  | 0 => ((posts.find? fun q => q.costPrec > 0
            && q.costVal.any (·.comm == comm)).map (·.costPrec)).getD 0
  | p => p

private def lookupBal (st : St) (acct comm : String) : ℚ :=
  (st.balances.lookup (acct, comm)).getD 0

/-- Add a flow, inferred or not, to the counts of `k` in `m`, the
    flows and the inferred flows among them, as `bumpStat` keeps
    `St.flowStats` and `St.signStats`. -/
private def bumpCount {κ : Type} [DecidableEq κ] (m : List (κ × Nat × Nat))
    (k : κ) (inf : Bool) : List (κ × Nat × Nat) :=
  match m.lookup k with
  | some _ => m.map fun (k', t, i) =>
      if k' = k then (k', t + 1, i + (if inf then 1 else 0)) else (k', t, i)
  | none => (k, 1, if inf then 1 else 0) :: m

/-- Count a flow of `dq` in `comm` to `acct`, inferred or not: in
    `flowStats`, which the net row of `Driver` and the balance
    assignment of `finalizeXact` read for a lone inferred amount, and,
    when `dq` is not zero, in `signStats` under the column of its sign,
    the debit column for a positive amount and the credit column for a
    negative one. Under `--dc`, C++ gives each posting the pair
    `(amount > 0 ? amount : 0, amount < 0 ? amount : 0)`
    (src/report.h:751-754 at 76b9dc2b2, baseline/opt-dc), so that a
    posting of zero brings the integer 0 to both columns. C++ adds an
    integer to an amount with a commodity, or such an amount to an
    integer, by way of a balance, which ignores a zero (value.cc:572-575,
    591-594, 621-622, 1524-1525; balance.h:131; balance.cc:122-123), so
    that the zero leaves in its column the precision of a lone inferred
    amount, which a sum of two amounts drops (amount.cc:634-642), and it
    counts in neither column here. With `A  1 FOO @ $0.0004` against an
    elided `B`, a transaction of `B  $0` and `C  $0`, before it or after
    it, makes C++ print no row for `B` under `bal --flat` and still
    `$0.0004` in the credit column of `B` under `bal --dc --flat`. A
    zero whose amount carries an annotation departs from this in the
    net row: C++ adds it to the account's total by way of a balance as
    well, since its annotated commodity is not the plain one
    (value.cc:600-603), and so keeps the tag, while `flowStats` counts
    it here (wrong rows): with `B  $0 (n)` in place of `B  $0`, C++
    prints `$-0.0004` for `B` under `bal --flat`, and `Driver` prints no
    row for it. The flows counted are the engine's. Besides the
    departures of the balancing, each recorded where it arises, they
    depart from the postings of C++ where C++ completes one commodity
    with a posting for each annotated key (`Result.lotFanout`, set
    where that can change a column, but for the misses that its
    docstring records), and where the tag of an inferred amount departs
    from that of C++: on a completion (the comment on COST_PREC tagging
    in `balancePool`), and on a posting that an automated transaction
    generates from a tagged amount (the comment on `instantiate` in
    `applyAutos`). -/
private def bumpStat (st : St) (acct comm : String) (inf : Bool) (dq : ℚ) : St :=
  let st := { st with flowStats := bumpCount st.flowStats (acct, comm) inf }
  if dq = 0 then st
  else
    let skey := (acct, comm, decide (dq > 0))
    { st with signStats := bumpCount st.signStats skey inf }

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

/-- The alias expansion of an account name, or `none` when no alias
    fires (journal_t::expand_aliases, journal.cc:255-339). -/
private def expandAliases (st : St) (name : String) : Option String :=
  -- whole-name lookup first, else walk single components (first only
  -- unless --recursive-aliases); each alias expands at most once, and a
  -- component whose target already sits colon-aligned at that position
  -- is skipped (#3132); loop to fixpoint only under --recursive-aliases.
  -- Under that flag C++ rejects a cycle twice over, where the expansion
  -- stops here, a known departure (fail-open): a whole name that would
  -- expand a second time (journal.cc:272-274), so that with `alias A=B`
  -- and `alias B=A` a posting to `A` is rejected by C++ and accepted
  -- here (regress/coverage-error-circular-alias), and an expansion that
  -- ends at the name it began with (journal.cc:341-345), so that with
  -- the same aliases a posting to `A:X` is rejected by C++ and accepted
  -- here (regress/coverage-journal-alias)
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
        | some (used, n') => fix fuel (used :: seen) n'
        | none => n
  (expandOnce [] name).map fun (used, n') =>
    if st.recursiveAliases then fix 9 [used] n' else n'

/-- A name under the `apply account` stack (innermost last), as
    `top_account()->find_account` names it. -/
private def applyPrefixes (st : St) (name : String) : String :=
  (st.applyStack.filterMap id).foldl (fun acc p => s!"{p}:{acc}") name

/-- An account name as `account_t::find_account` reads it
    (account.cc:79-131): one trailing colon is dropped, and `none`
    marks a name with an empty component, which C++ rejects, so that
    `Bar:` names `Bar` while `Bar::`, `:Bar` and the empty name are
    rejected. -/
private def findAccountName (raw : String) : Option String :=
  let comps := raw.splitOn ":"
  let comps :=
    if comps.length > 1 && comps.getLast? == some "" then comps.dropLast
    else comps
  if comps.any (·.isEmpty) then none else some (String.intercalate ":" comps)

/-- Resolve an account name as `journal_t::register_account` does
    (journal.cc:169-177): an alias expansion when an alias fires,
    without a further `apply account` prefix, since the `alias`
    directive named its target under the stack when it was read;
    otherwise the name under the stack. With `alias Foo=Bar` and then
    `apply account Top`, a posting to `Foo` posts to `Bar`, and a
    posting to `Baz` to `Top:Baz`. C++ drops a trailing colon of any
    account name and rejects an empty component (account.cc:79-131),
    which is done here (`findAccountName`) only for an alias target and
    an `apply account` name, a known departure: a posting to `Foo:`
    posts to `Foo` in C++ and to `Foo:` here (wrong rows), and one to
    `Foo::Bar` is rejected by C++ and accepted here (fail-open). -/
private def resolveAccount (st : St) (name : String) : String :=
  match expandAliases st name with
  | some n => n
  | none => applyPrefixes st name

/-- The account to which `create_timelog_xact` books the hours of an
    entry whose check-in named `name`, which `clock_in_directive` gives
    under the `apply account` stack without expanding an alias
    (textual_directives.cc:110). C++ registers that full name when the
    entry is checked out (timelog.cc:76-77), so that the aliases in
    force at the check-out expand it, and an `Unknown` result maps
    through the account-block payee rules by the entry's payee
    (journal.cc:179-188, regress/1211), which is the check-in's
    description or, when that is empty, the check-out's
    (timelog.cc:49, 133-136). With `alias Foo=Bar` and then
    `apply account Top`, `i ... Foo` books its hours to `Top:Foo`, and
    with `alias Foo=Bar` between `i ... Foo` and its `o`, to `Bar`. -/
private def timelogAccount (st : St) (name payee : String) : String :=
  let acct := (expandAliases st name).getD name
  if acct.endsWith ":Unknown" || acct == "Unknown" then
    match st.payeeAccountRules.find? fun (rx, _) => regexSearch rx payee with
    | some (_, target) => target
    | none => acct
  else acct

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

/-- The UUID that this reader finds in the line `s` of the body of a
    transaction, any of its posting lines and note lines: the text after
    the first `uuid:`, in any case, up to a `,` or a `;`, trimmed and in
    lower case, and the first line that gives one prevails. C++ reads
    the `UUID` tag of the transaction alone (journal.cc:593), which the
    note of its header, its note lines before the first posting and an
    `apply tag` in force give it, matching the name of the tag in any
    case (metadata.cc:117) and keeping its value as written, a known
    departure that leaves the rows wrong both ways, measured on both C++
    binaries. Two transactions that post `$5` to `Assets:uuid:x`, or
    `$5` with `; UUID: abc` on the posting, against an elided `Equity`,
    or that buy `1 AAPL [2024/01/01] @ $5` with `; UUID: abc` on a note
    line after a posting, or with `; UUID: abc` on a note line before the
    postings of the one and `; UUID: ABC` on such a line of the other,
    are both kept by C++ and one of them is dropped here; and two that
    buy `1 AAPL {$4} @ $5` with `; UUID: abc` in the note of the header,
    or `1 AAPL [2024/01/01] @ $5` under `apply tag UUID: abc`, are
    reduced to one by C++ and both kept here.
    The prices that their costs record are the same in either reading,
    since C++ records them for a duplicate as well (the comment on `dup`
    in `finalizeXact`). -/
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
  /-- `PostSpec.costAnnotated` -/
  costAnnotated : Bool
  /-- `PostSpec.costLotComm` -/
  costLot : Option String
  /-- `PostSpec.costVirtual` -/
  costVirtual : Bool

/-- Consume the annotation/cost/assertion tail of an amount:
    `{lot} [date] (note) @ P / @@ T / = ASSERT` in any order. -/
private partial def annotLoop (ctx : AmtCtx) (line : Nat) (a : Amount)
    (tail : String) (lot : Option (Amount × Bool)) (cost : Option Amount)
    (teach : List (String × Nat) := []) (afterCost : Bool := false)
    (costDecs : Nat := 0) (afterAssert : Bool := false)
    (annotated : Bool := false) (fixated : Bool := false)
    (ownLot : Bool := false) (perUnit : Bool := false)
    (lotLit : Option (Nat × Bool) := none) (costAnnotated : Bool := false)
    (costLot : Option String := none) (costVirtual : Bool := false) :
    Except String AnnotTail := do
  -- `annotated`, `fixated` and `ownLot`: an annotation met before any
  -- cost or assertion belongs to the posting's own amount; after a
  -- cost it annotates the cost amount, after an assertion the
  -- assertion amount (textual_xacts.cc:756-757). `ownLot` says that
  -- the lot kept was met while `own` held. `costAnnotated`: one met
  -- after the cost and before any assertion, on a cost with a
  -- commodity, since C++ keeps no annotation on an amount without one
  -- (amount.cc:1908)
  let own := !afterCost && !afterAssert
  let onCost := afterCost && !afterAssert && cost.any (·.comm != "")
  let t := trimS tail
  if t.isEmpty || t == "." then
    pure { lot, cost, teach, costDecs, annotated, fixated, ownLot, perUnit,
           lotLit, costAnnotated, costLot, costVirtual }
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
    -- the lot price that annotates the cost itself, whose commodity
    -- `costPrice` compares with the amount's (regress/1217): the first,
    -- on a cost with a commodity, where the price has one
    let costLot' := if onCost && costLot.isNone && pr.amount.comm != "" then
        some pr.amount.comm
      else costLot
    -- while `own` holds, every lot taken so far is the posting's own
    annotLoop ctx line a (String.ofList rest) lot' cost teach afterCost costDecs
      (afterAssert := afterAssert) (annotated := annotated || own)
      (fixated := if own then lot'.any (·.2) else fixated)
      (ownLot := if own then lot'.isSome else ownLot) (perUnit := perUnit)
      (lotLit := lotLit') (costAnnotated := costAnnotated || onCost)
      (costLot := costLot') (costVirtual := costVirtual)
  else if t.startsWith "[" then
    match takeBalanced '[' ']' t.toList with
    | some (_, rest) =>
        annotLoop ctx line a (String.ofList rest) lot cost teach afterCost costDecs
          (afterAssert := afterAssert) (annotated := annotated || own)
          (fixated := fixated) (ownLot := ownLot) (perUnit := perUnit)
          (lotLit := lotLit) (costAnnotated := costAnnotated || onCost)
          (costLot := costLot) (costVirtual := costVirtual)
    | none => err line s!"unclosed lot date in '{t}'"
  else if t.startsWith "(" && !(t.startsWith "(@") then
    match takeBalanced '(' ')' t.toList with
    | some (_, rest) =>
        annotLoop ctx line a (String.ofList rest) lot cost teach afterCost costDecs
          (afterAssert := afterAssert) (annotated := annotated || own)
          (fixated := fixated) (ownLot := ownLot) (perUnit := perUnit)
          (lotLit := lotLit) (costAnnotated := costAnnotated || onCost)
          (costLot := costLot) (costVirtual := costVirtual)
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
      (perUnit := false) (lotLit := lotLit) (costAnnotated := costAnnotated)
      (costLot := costLot) (costVirtual := t.startsWith "(@@)")
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
      (perUnit := true) (lotLit := lotLit) (costAnnotated := costAnnotated)
      (costLot := costLot) (costVirtual := t.startsWith "(@)")
  else if t.startsWith "=" then
    -- assertion: the C++ side checks it; positive tests pass it, but
    -- the literal still teaches display precision (1699). C++ parses
    -- the assertion amount with its own annotations
    -- (textual_xacts.cc:756-757), so a later `{lot}`, `[date]` or
    -- `(note)` sets neither flag nor `ownLot`; the lot reading above
    -- still takes a lot written there as the posting's own for
    -- `lotVal`, a reading that no C++ test exercises (regress/2318
    -- writes the posting's lot first). C++ parses a literal with
    -- migration, which teaches its commodity its decimals however many
    -- they are, and an expression with PARSE_NO_MIGRATE, which teaches
    -- nothing (textual_xacts.cc:756-760), while here the amount teaches
    -- its decimals, a literal's or the approximation of an expression's
    -- (`parseAmount`), up to six alone, a known departure both ways:
    -- after `Assets:Cash  $1.00` against an elided `Equity` and
    -- `Assets:Cash  $0 = $1.0000000` against another, C++ prints a later
    -- `($1/3)` against an elided `Equity` as `$0.3333333`, and after
    -- `Assets:Cash  $1` and `Assets:Cash  $0 = ($1.00 * 1)` it prints no
    -- row for it, where it shows as 0.33 here after either (wrong rows).
    -- The assignment rule of `parseAmountField` shares both
    let pr ← parseAmount ctx line (trimS (t.drop 1).toString)
    let teach := if pr.decimals <= 6 then
        (pr.amount.comm, pr.decimals) :: teach else teach
    annotLoop ctx line a pr.tail lot cost teach afterCost costDecs
      (afterAssert := true) (annotated := annotated) (fixated := fixated)
      (ownLot := ownLot) (perUnit := perUnit) (lotLit := lotLit)
      (costAnnotated := costAnnotated) (costLot := costLot)
      (costVirtual := costVirtual)
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
  /-- `PostSpec.costAnnotated` -/
  costAnnotated : Bool := false
  /-- `PostSpec.rawCost`, the cost in the commodity in which it is
      written -/
  rawCost : Option Amount := none
  /-- `PostSpec.rawCostPrec` -/
  rawCostPrec : Nat := 0
  /-- `PostSpec.costVirtual` -/
  costVirtual : Bool := false
  /-- `PostSpec.costLotComm` -/
  costLotComm : Option String := none
  /-- `PostSpec.amtPrec` -/
  amtPrec : Nat := 0

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
    -- (the departure recorded at `PostSpec.fixated`). Its amount teaches
    -- as an assertion's does, with the departures recorded at the `=`
    -- branch of `annotLoop`: after `Assets:Cash  $1.00` against an elided
    -- `Equity` and `Assets:Cash  = $1.0000000` against another, C++
    -- prints a later `($1/3)` against an elided `Equity` as `$0.3333333`,
    -- where it shows as 0.33 here (wrong rows)
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
          lotLit, costAnnotated, costLot, costVirtual } ←
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
    -- the precision of the cost when Phase 6 exchanges it, before the
    -- raise below (`PostSpec.rawCostPrec`)
    let rawCostPrec := costPrec
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
    -- (fail-closed). Where an elided posting completes each pool, the
    -- gain passes from the real completion of C++ to the bracket-virtual
    -- one here (wrong rows): `[Assets:A]  -10 AAPL {$1} @ $5` against an
    -- elided `[Assets:B]`, beside an elided `Assets:D`, completes
    -- `[Assets:B]` with `$50` and `Assets:D` with `$-40` in C++, and
    -- `[Assets:B]` with `$10` and nothing in `Assets:D` here. When the
    -- two elided postings name one account, its net row agrees with C++
    -- and its debit and credit totals do not: with `[Assets:D]` elided
    -- in place of `[Assets:B]` and `Assets:C  $30` beside, C++ completes
    -- `[Assets:D]` with `$50` and `Assets:D` with `$-70`, whose columns
    -- hold `$50` and `$70`, where the engine's flows to `Assets:D` are
    -- `$10` and `$-30`; with `Assets:C  $-60 (n)` instead, C++ completes
    -- `Assets:D` with `$-40` and `$60 (n)`, a split of both signs that
    -- `St.lotFanout` misses (`Result.lotFanout`), and so does
    -- `applyAutos` (`PoolResult.splitComms`). C++ keeps no lot on an
    -- amount with no commodity (amount.cc:1908) and so adds no gain for
    -- it: `10 {$5} @ $6` against `-$50` is accepted here and rejected by
    -- C++ with a remainder of `$10` (fail-open), and against `-$60` it
    -- is rejected here and accepted by C++ (fail-closed). Three more, on
    -- a cost that carries an annotation of its own, give wrong rows; the
    -- docstring of `PostSpec.costAnnotated` records them
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
           fixated := hasComm && fixated, costPrec, costAnnotated
           rawCost := cost, rawCostPrec, costVirtual, costLotComm := costLot
           amtPrec }

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
                     costPrec := af.costPrec, costAnnotated := af.costAnnotated
                     rawCost := af.rawCost, rawCostPrec := af.rawCostPrec
                     costVirtual := af.costVirtual
                     costLotComm := af.costLotComm, amtPrec := af.amtPrec },
              af.learned, af.amount.map (·.comm), af.decimals, af.isExpr,
              af.teach)

/-! ## The tag equality of regress/842 -/

/-- A character of a tag name or value that the test `tag("K") == "V"`
    reads: an ASCII letter or digit, `_` or `-`. -/
private def tagEqChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '-'

/-- A non-empty run of `tagEqChar`. -/
private def tagEqWord (s : String) : Bool :=
  !s.isEmpty && s.toList.all tagEqChar

/-- One note line within the bounds of `tagEqScan`: `some none` for a
    line without `:`, which names no tag in C++ (metadata.cc:146-147),
    `some (some (Name, value))` for `Name: value` with blanks around
    the two words, and `none` for any other line with a `:`. C++ takes
    the first token of two or more characters as a name when it ends
    in `:`, and the rest of the line, its whitespace trimmed, as the
    value (metadata.cc:156-169, 181-197): `; Category: food` and
    `;Category:<TAB>food` name `Category` with the value `food`, while
    `; Category:food` names no tag. -/
private def tagEqLine (seg : String) : Option (Option (String × String)) :=
  if !seg.toList.contains ':' then some none
  else
    let isBlank := fun (c : Char) => c == ' ' || c == '\t'
    match seg.splitOn ":" with
    | [a, b] =>
        let nm := String.ofList (a.toList.dropWhile isBlank)
        let bs := b.toList
        let v := String.ofList
          ((bs.dropWhile isBlank).reverse.dropWhile isBlank).reverse
        if tagEqWord nm && (bs.head?.map isBlank).getD false && tagEqWord v then
          some (some (nm, v))
        else none
    | _ => none

/-- The tags of a note as the engine keeps it, the same-line note
    followed by `;` and each note line of its own (`finalizeXact`), in
    order. `none` outside the bounds of `tagEqScan`, under which the
    same-line note holds no `:` and `tagEqLine` reads each line. -/
private def tagEqMeta (note : String) : Option (List (String × String)) :=
  match note.splitOn ";" with
  | [] => some []
  | first :: own =>
      if first.toList.contains ':' then none
      else own.foldlM (fun acc seg => (tagEqLine seg).map (acc ++ ·.toList)) []

/-- The value of the tag `k` that C++ reads for a posting with the tags
    `pm` in a transaction with the tags `xm`: the posting's own, else
    the transaction's (post.cc:96-110), each the last that a note line
    sets, since a note line overwrites an earlier value
    (textual_xacts.cc:1100-1103, metadata.cc:132-133). -/
private def tagEqValue (k : String) (pm xm : List (String × String)) :
    Option String :=
  let last := fun (m : List (String × String)) =>
    ((m.filter (·.1 == k)).getLast?).map (·.2)
  last pm <|> last xm

/-- Whether `tag("K") == "V"` holds for a posting with the note `note`
    in a transaction with the notes `xactNotes`, within the bounds of
    `tagEqScan` and `tagEqGuard`. C++ compares the value that
    `tagEqValue` reads with `V` as a string (query.cc:412-460), so that
    under regress/842's `; Category: food` the test holds for both
    postings of the transaction, each of which generates a
    `(Budget:Food)` posting, and under `; Category: Food` it holds for
    neither. -/
private def tagEqHolds (k v xactNotes note : String) : Bool :=
  match tagEqMeta note, tagEqMeta xactNotes with
  | some pm, some xm => tagEqValue k pm xm == some v
  | _, _ => false

/-- Refuse a transaction that the rule `tag("K") == "V"` tests, before
    it is extended, where C++ reads the test or completes the
    transaction otherwise. Within the bounds of `tagEqScan` a note line
    is the only source of a tag, and every posting is real. C++ reads
    `K` as a pattern that ignores case and takes the first name it
    finds in an order that also ignores case (query.cc:446-460,
    mask.cc:365-367, metadata.cc:47-51, 97-108), so no name other than
    `K` that contains it may tag a posting (`posts`, as written) or its
    transaction: with `K` `Category`, `; category: food` or
    `; Categoryx: y` is refused.

    C++ tests every posting of the balanced transaction, the postings
    by which it completes an elided one included (xact.cc:1438-1447).
    It completes an elided posting from the sum of the written amounts
    (xact.cc:180-248, 829-844). While one commodity has entered the sum
    it is a single amount, whose negation the elided posting takes,
    zero or not; from the second commodity on it is a balance, which
    drops the first commodity if that has netted to zero by then
    (value.cc:600-607, balance.h:128-134) and keeps an entry for a
    commodity that nets to zero later (balance.cc:118-133), and the
    elided posting takes one posting per entry. A balance with no entry
    leaves the elided posting without an amount, and C++ then rejects
    the transaction (xact.cc:1012-1015). The engine completes an elided
    posting with one posting for each commodity that does not net to
    zero (`balancePool`), and `applyAutos` tests those. So a transaction
    with an elided posting is refused when the written amounts of some
    commodity in it net to zero, whether the test holds or not;
    otherwise C++ and the engine test the same postings. Beside
    `Expenses:C  3 EUR`, `Expenses:A  $5` and `Expenses:B  $-5`, C++
    completes an elided `Assets:Cash` with `$0` and `-3 EUR`, and under
    `; Category: food` the `$0` posting generates a `(Budget:Food)`
    posting of `$0`, while the engine completes it with `-3 EUR` alone;
    beside `Expenses:A  $5`, `Expenses:B  $-5` and `Expenses:C  0 EUR`,
    C++ rejects the transaction, which the engine reads. -/
private def tagEqGuard (hline : Nat) (k xactNotes : String)
    (posts : List PostSpec) : Except String Unit := do
  let refuse := fun (why : String) =>
    err (α := Unit) hline s!"out-of-scope tag() predicate: {why}"
  let some xm := tagEqMeta xactNotes
    | refuse "a note outside the form `; Name: value`"
  for p in posts do
    let some pm := tagEqMeta p.note
      | refuse "a note outside the form `; Name: value`"
    if ((pm ++ xm).map (·.1)).any fun nm =>
        nm != k && (nm.toLower.splitOn k.toLower).length > 1 then
      refuse s!"a tag name other than {k} that contains it"
  let written := posts.filterMap (·.amount)
  let netsToZero := fun (c : String) =>
    ((written.filter (·.comm == c)).map (·.q)).sum == 0
  if posts.any (·.amount.isNone) && written.any (netsToZero ·.comm) then
    refuse "an elided posting beside a commodity whose amounts net to zero"

/-! ## The dates of prices -/

/-- The fields of the date `s` of a price directive, each as its number
    and its count of digits, where `s` is fields of digits joined by
    single characters among `/`, `-` and `.`, and `none` otherwise. C++
    reads `.` and `-` in a date as `/`: `parse_datetime` always, for a
    date with a time (times.cc:429-432), and the readers of a date
    without a time unless an input date format is given
    (times.cc:239-243, `St.inputDateFormat`). -/
private def priceDateFields (s : String) : Option (List (Int × Nat)) :=
  (((s.splitOn "/").flatMap (·.splitOn "-")).flatMap (·.splitOn ".")).mapM
    fun p =>
      if !p.isEmpty && p.toList.all Char.isDigit then
        p.toNat?.map fun v => ((v : Int), p.length)
      else none

/-- Whether the year `y`, the month `m` and the day `d` name a day that
    C++ can hold: the gregorian dates of boost, which `ptime_from_tm` and
    `date_from_tm` build (times.cc:154-155, 181-182), span the years 1400
    to 9999 and refuse a day that the month lacks, so that
    `P 1399/12/31 EUR $1` and `P 2024/02/30 EUR $1` reject the journal on
    both C++ binaries. -/
private def priceDayValid (y m d : Int) : Bool :=
  let leap := (y % 4 == 0 && y % 100 != 0) || y % 400 == 0
  let days := if m == 2 then (if leap then 29 else 28)
    else if m == 4 || m == 6 || m == 9 || m == 11 then 30 else 31
  1400 ≤ y && y ≤ 9999 && 1 ≤ m && m ≤ 12 && 1 ≤ d && d ≤ days

/-- The day, counted as `daysFromCivil` counts it, of the date `dateS` of
    a price directive without a time, read as `parse_date` reads it,
    through readers that C++ tries in turn until one reads the date
    (pool.cc:565-567; times.cc:229-327, 2539-2544), with a year of four
    digits and a month and a day of one or two: `Y/M/D`
    (test/baseline/cmd-pricemap.test, test/baseline/opt-historical.test,
    test/regress/7C44010B.test), `Y/M`, which is the first day of the
    month (times.cc:2541), and `M/D` in the year of a `Y` or `year`
    directive (times.cc:175-182, 277-281;
    test/regress/coverage-wave2-textual.test). Any other date is `none`,
    and so is every date where an input date format is given
    (`St.inputDateFormat`), and `M/D` in two more cases. Where no year
    directive has been read, C++ takes the year of its current time and,
    for a month after the current one, the year before
    (times.cc:283-301). Where `St.yearUnsure` is set, C++ takes the year
    of an `apply year` directive, or in a journal with included files
    the year that it restores where an included file ends
    (textual_directives.cc:424-446, 464-476), neither of which
    `defaultYear` follows. `recordCostPoints` reads the date of a
    transaction with it, and `noteDateOf` the date that a note gives, for
    the prices of costs, since C++ reads both with `parse_date` as well
    (textual_xacts.cc:984-990, item.cc:96-102). -/
private def priceDay (st : St) (dateS : String) : Option Int := do
  guard !st.inputDateFormat
  match ← priceDateFields dateS with
  | [(y, 4), (m, lm), (d, ld)] =>
      if lm ≤ 2 && ld ≤ 2 && priceDayValid y m d then
        some (daysFromCivil y m d)
      else none
  | [(y, 4), (m, lm)] =>
      if lm ≤ 2 && priceDayValid y m 1 then some (daysFromCivil y m 1)
      else none
  | [(m, lm), (d, ld)] =>
      let y ← st.defaultYear
      if lm ≤ 2 && ld ≤ 2 && !st.yearUnsure && priceDayValid y m d then
        some (daysFromCivil y m d)
      else none
  | _ => none

/-- The date that the note line `note` gives the item that it annotates,
    read as `item_t::parse_tags` reads one (item.cc:66-104): after the
    blanks, tabs and `;` that begin the line, its first `[`, when a digit
    or `=` follows it, no `:` precedes it and a `]` closes it within 255
    characters, holds a date, an auxiliary date after `=`, or both, and
    C++ reads the date as `parse_date` reads the date of a price
    directive, as `priceDay` does. `none` where the line gives no date,
    or an auxiliary date alone, which dates no price; `some (some d)` for
    the day `d`; and `some none` for a date that this reader does not
    read. A note of a posting dates the posting, and one of its
    transaction dates the transaction, whose date a posting without one
    takes (`post_t::date`, post.cc:143-174), and of the note lines of an
    item the last that gives a date prevails. C++ reads the text of each
    `apply tag` in force into a transaction in the same way, after its
    notes (`St.applyTags`). -/
private def noteDateOf (st : St) (note : String) : Option (Option Int) := do
  let d := note.toList.dropWhile fun c => c == ' ' || c == '\t' || c == ';'
  let i ← d.findIdx? (· == '[')
  let inner := d.drop (i + 1)
  guard (inner.head?.any fun c => c.isDigit || c == '=')
  guard !((d.take i).contains ':')
  let j ← inner.findIdx? (· == ']')
  guard (j < 256)
  let primary := (inner.take j).takeWhile (· != '=')
  guard !primary.isEmpty
  pure (priceDay st (String.ofList primary))

/-- The date and the note of the header line `header` of a transaction,
    as `parse_xact` reads them (textual_xacts.cc:984-1074). The date is
    the first field, which ends at a blank or a tab (`next_element`,
    utils.h:623-631), up to the `=` of an auxiliary date. Past the blanks
    and tabs after it, C++ passes over a state mark, `*` or `!`, a code in
    parentheses and, when no mark precedes the code, a state mark after it
    (textual_xacts.cc:1019-1036), each with the blanks and tabs that
    follow it, and then reads the payee, which ends at the first
    `;` that a run of blanks and tabs holding a tab or two blanks
    precedes; the note is the text after that `;`, and there is none
    without it. A `;` that no such run precedes belongs to the payee, and
    so does one where the payee begins: under `2024/01/05 Buy ; [2024/01/09]`,
    `2024/01/05 ; [2024/01/09]` or `2024/01/05 *  ; [2024/01/09]`, both
    C++ binaries list the price of `1 AAPL @ $101` at 2024/01/05, and
    under `2024/01/05 Buy  ; [2024/01/09]` at 2024/01/09. `priceDay` reads
    the day of this date and `noteDateOf` the date that this note gives,
    for the prices of costs alone (`recordCostPoints`); the rest of the
    reader keeps the readings of `headerDateF` and `splitNote`, whose date
    ends at a blank or an `=` and whose note begins at the first `;` after
    a blank or a tab. -/
private def xactHeaderParts (header : String) : String × Option String :=
  let blank := fun (c : Char) => c == ' ' || c == '\t'
  let cs := header.toList
  let field := cs.takeWhile fun c => !blank c
  let date := String.ofList (field.takeWhile (· != '='))
  let mark := fun (l : List Char) => match l with
    | c :: r => if c == '*' || c == '!' then some (r.dropWhile blank) else none
    | [] => none
  let rec payee (spaces tabs : Nat) : List Char → Option String
    | [] => none
    | ' ' :: r => payee (spaces + 1) tabs r
    | '\t' :: r => payee spaces (tabs + 1) r
    | ';' :: r =>
        if tabs > 0 || spaces > 1 then some (String.ofList r) else payee 0 0 r
    | _ :: r => payee 0 0 r
  match cs.drop field.length with
  | [] => (date, none)
  | _ :: rest =>
      let next := rest.dropWhile blank
      let marked := mark next
      let next := marked.getD next
      -- C++ steps past the `(` of a code whether or not a `)` closes it
      let next := match next with
        | '(' :: r =>
            match r.findIdx? (· == ')') with
            | some i => (r.drop (i + 1)).dropWhile blank
            | none => r
        | _ => next
      let next := if marked.isSome then next else (mark next).getD next
      (date, payee 0 0 next)

/-! ## The prices that costs record -/

/-- The price that Phase 6 of `finalize` records for the cost of the
    posting `p` in a transaction with a date, as the commodity that it
    prices and its price per unit, or `none` where it records none.
    `st` holds the display precisions as this reader has learned them
    once the postings of the transaction are read, which is when C++
    reads them in Phase 6; where that learning departs from C++, the
    price departs with it, as the account of departures below records.

    Phase 6 hands each posting with a cost, of whatever kind, to
    `commodity_pool_t::exchange` (xact.cc:669-690), which takes the
    absolute value of the cost divided by the amount and records it as
    the price of the amount's commodity, its annotation set aside, at
    00:00 of the posting's date (pool.cc:390-397, 437, 488-493;
    xact.cc:688-690). A divided price in a commodity is rounded half away
    from zero at the precision of the amount, plus the display precision
    of the price's commodity, plus six (pool.cc:445-468, issue #2975):
    `12.00 EUR @@ 15.80 USD` records 1.31666667 USD where USD has no
    display precision yet (test/baseline/cmd-pricedb.test), and
    `3 AAPL @@ $100` records $33.33333333 once `$1.00` has taught `$` two
    places, of which `pricedb` prints six. A per-unit `@ P` is divided as
    well, since the cost is `P` times the amount by then
    (textual_xacts.cc:701-707), and so records `P` unless `P` has more
    places than that precision: `1 AAPL @ $0.12345678` records $0.123457.
    Where the amount is zero at the display precision of its commodity
    (`amount_t::is_zero`, amount.cc:1374-1430), the price is the cost
    itself, rounded at its own precision (`PostSpec.rawCostPrec`) or at
    the display precision of its commodity, the larger (pool.cc:437, 466;
    amount.cc:882-891), which leaves a written cost as it is:
    `(1/9 FOO) @ 200 EUR`, whose amount is zero at the precision 0 of
    FOO, records its cost of 200/9 EUR at the six places that the cost
    takes from the amount, 22.222222 EUR. A price without a commodity is
    not rounded (pool.cc:439-440, 460): `3 AAPL @@ 100` records 100/3. An
    amount without a commodity is priced as well, on the vertex of the
    null commodity, which `pricedb` does not list and through which a
    valuation can pass: after `Assets:A  10 @ $5`, `P 2024/01/01 X 5`
    values one X at $25 on both C++ binaries.

    No price is recorded (pool.cc:483-493) for a virtual cost, `(@)` or
    `(@@)`, which Phase 6 exchanges without adding a price
    (test/regress/999-a.test, test/regress/999-b.test,
    test/regress/1050.test); for a price that
    is exactly zero, a zero cost or one that rounds to zero; for an
    amount whose own lot price is fixated, `{=P}` or `{{=T}}`, or which
    an `apply fixed` rate annotates (`PostSpec.rateFixed`); for a cost
    whose own lot price is in the amount's commodity (issue #1217,
    test/regress/1217.test); and for a cost in the amount's commodity,
    which Phase 6 rejects for a plain amount (xact.cc:679-681). A fixated
    cost, `@ =P` or `@@ =T`, records its price, since Phase 6 fixates the
    lot price only after the exchange (xact.cc:816-819).

    The departures known are these, each measured on both C++ binaries.
    The precision of an amount expression is the approximation of
    `parseAmountField`, and the zero test of such an amount reads the
    display precision that the reader learns from it, the departure
    recorded beside the precision rule of `finalizeXact`, so that the
    price of a cost on such an amount can be rounded, or taken from the
    cost alone, otherwise than in C++: `(1.5 * 1.5 AAPL) @@ $10` records
    $4.44444444 in C++ and $4.4444444444444 here, and
    `(1.25/3 FOO) @ 1 EUR`, an amount that C++ takes as zero, records
    0.416667 EUR in C++ and 1 EUR here. The precision of a cost written
    as an expression is the approximation that the docstring of
    `zeroTestPrec` records, and so is the rounding of such a cost on an
    amount that is zero: `0 AAPL @@ ($100/3)` records $33.333333 in C++
    and $33 here.

    More widely, the price is rounded, and the zero test of its amount
    reads, at display precisions that this reader learns, and so the
    price inherits each departure of that learning. Those departures
    begin with the sources that this reader omits, which the docstring
    of `zeroTestPrec` gives: the postings of an automated transaction and
    of a periodic template, the latter recorded at `flushPending` as
    well, an `apply fixed` rate, and the amount literals of the value
    expressions that C++ parses with migration, but for that of a
    posting amount, such as a `define`, a typed metadata value, a `check`
    line of a transaction or an `eval` directive. The tentative precision
    of a price directive departs as the `P` arm of `handleDirective`
    records, and the precision that a `D` directive locks departs as the
    `D` arm records. The literals of an amount expression depart as the
    precision rule of `finalizeXact` records. The amount of a balance
    assertion or assignment teaches nothing here past six places, teaches
    here alone where it is an expression (the `=` branch of `annotLoop`),
    and teaches the commodity that it names as written (the rule on
    `teach` in `finalizeXact`). A transaction dropped for a UUID seen
    before teaches nothing here, while C++ learns from it as it reads it
    (the comment on `dup` in `finalizeXact`). After a transaction of
    `Assets:Cash  $10` against an elided `Equity` with the line
    `check amount < $0.001`, `3 AAPL @@ $100` records $33.333333333 in
    C++ and $33.333333 here. `3 AAPL @@ 100 EUR` records 33.33333333 EUR
    in C++ and 33.333333 EUR here after `~ Monthly` with `X  0.50 EUR`
    against an elided `Y`, and 33.333333333 EUR in C++ and 33.333333 EUR
    here beside `Assets:Cash  -100 EUR = -100.000 E` under
    `commodity EUR` with `alias E`. After `Assets:Cash  $1.2345` against
    an elided `Equity` and then `D $1.00`, `3 AAPL @@ $100` records
    $33.3333333333 in C++ and $33.33333333 here; after
    `Assets:A  0.0001 AAPL` against an elided `Equity` and then
    `D 1.00 AAPL`, `0.001 AAPL @@ $10` records $10000 in C++ and $10
    here, where its amount is zero at the two places of the directive.
    Beside `Assets:Cash  $-100 = $-100.0000000`, `3 AAPL @@ $100` records
    $33.3333333333333 in C++ and $33.333333 here, and `3 MSFT @@ $100`
    records $33.33333333 in C++ and $33.333333 here after a transaction
    with `UUID: abc` and `Assets:Cash  $-5` is repeated with `$-5.00`.

    The cost is read as the reader reads any amount, and so inherits the
    departures of its style model, of the `commodity` aliases and of a
    one-to-one `C` equivalence that the docstring of `priceDirective`
    records for a price: after a periodic template with `X  10,5 E`
    against an elided `Y`, which teaches C++ alone a decimal comma for
    `E` (the departure recorded at `flushPending`), `10 AAPL @ 1,500 E`
    records 1.5 E in C++ and 1500 E here, and beside `C 1 A = 1 B`,
    `10 X @ 5 A` records 5 B in C++ and 5 A here.

    An `apply fixed` or `apply rate` directive left open in an included
    file stays in force here to the end of the journal, the departure
    recorded at the `apply` arm of `handleDirective`, so that the table
    lacks the prices that C++ records for later costs on amounts in its
    commodity, and no issue stands in their place (fail-open): with
    `apply fixed AAPL $40` left open in an included file,
    `10 AAPL @ $50` after the `include` line records $50 in C++ and
    nothing here. -/
private def costPrice (st : St) (p : PostSpec) : Option (String × Amount) := do
  let a ← p.rawAmount
  let c ← p.rawCost
  -- the exclusion by `rateFixed` fails open where an `apply fixed` or
  -- `apply rate` left open in an included file annotates the amount here
  -- alone: the table then lacks the point that C++ records, and no issue
  -- stands in its place (the last paragraph above)
  guard (!p.costVirtual && !p.fixated && !p.rateFixed)
  guard (c.comm != a.comm && p.costLotComm != some a.comm)
  let prec := fun (k : String) => (st.precisions.lookup k).getD 0
  let ab := fun (x : ℚ) => if x < 0 then -x else x
  let zero := a.q == 0 || (a.comm != "" && p.amtPrec > prec a.comm
    && roundsToZeroAt (prec a.comm) a.q)
  let q := if zero then ab c.q else ab (c.q / a.q)
  let q := if c.comm == "" then q
    else if zero then roundAt (max p.rawCostPrec (prec c.comm)) q
    else roundAt (p.amtPrec + prec c.comm + 6) q
  guard (q != 0)
  pure (a.comm, ⟨c.comm, q⟩)

/-- The state `st` once the prices `points` that Phase 6 records for the
    costs of a transaction whose header line is `header` are written to
    the price log, each as the commodity that it prices, its price
    (`costPrice`) and the date that a note of its posting or of its
    transaction, or an `apply tag` in force, gives its posting
    (`noteDateOf`). A point is dated 00:00 of that date, with the issue
    `posting-date`, which stands alone where `priceDay` does not read
    that date, or else of the transaction's date as `priceDay` reads it
    (`xactHeaderParts`), failing which the issue `unread-price` stands in
    place of the point. C++ makes the commodity of each price primary
    (commodity.cc:72-78, commodity.h:237), as it is here whether the
    table holds the point or an issue stands in its place. -/
private def recordCostPoints (st : St) (header : String)
    (points : List (String × Amount × Option (Option Int))) : St :=
  let xactDay := priceDay st (xactHeaderParts header).1
  points.foldl (init := st) fun st (comm, price, noted) =>
    let st := if st.primary.contains price.comm then st
      else { st with primary := price.comm :: st.primary }
    match noted, xactDay with
    | some (some d), _ =>
        { st with priceLog := ⟨d * 86400, comm, price⟩ :: st.priceLog
                  priceIssues := ("posting-date", comm) :: st.priceIssues }
    | some none, _ =>
        { st with priceIssues := ("posting-date", comm) :: st.priceIssues }
    | none, some d =>
        { st with priceLog := ⟨d * 86400, comm, price⟩ :: st.priceLog }
    | none, none =>
        { st with priceIssues := ("unread-price", comm) :: st.priceIssues }

/-! ## Transaction finalization -/

/-- A completion that C++ can make and `balancePool` does not: a
    posting of the elided posting's account, or of the bucket's, in a
    commodity whose weights in the pool net to exactly zero. C++
    completes an elided posting with one posting for each entry of the
    sum that Phase 1 of `finalize` accumulates, keyed by annotated
    commodity (xact.cc:180-248, 829-863; annotate.h:120-125). An entry
    that nets to zero after a second key has entered stays in that sum
    (balance.cc:118-133), and while one key alone has entered, the sum
    is a single amount, zero or not (value.cc:600-607), so that C++ can
    complete the elided posting with postings that the engine,
    completing one posting per commodity of a nonzero residual, does not
    make. It adds the bucket's posting to a transaction of one posting
    whose sum is not null and completes it alike (xact.cc:368-372,
    `PoolResult.splitComms`): under `bucket Assets:Cash` and `= /Cash/`
    with `(Budget)  $10`, a transaction of `Expenses:Food  $0` alone
    gives `Assets:Cash` a posting of `$0`, and C++ books `$10`. Whether
    C++ keeps an entry that nets to zero depends on the order of the
    postings, since a key that has netted to zero when a second key
    enters is dropped (value.cc:1548, balance.h:128-134), and on the
    lot gains that Phase 6 adds afterwards (xact.cc:692-713, 763); this
    records the completion whenever the weights net to zero, which can
    only add refusals. -/
private structure ZeroCompletion where
  /-- the elided posting, or the bucket's posting, whose account and
      kind the completion takes -/
  post : PostSpec
  comm : String
  /-- the commodity is at risk of a split by annotation
      (`PoolResult.splitComms`), so that C++ can complete it with one
      posting per annotated key, of amounts that need not be zero;
      otherwise with at most one posting, of zero -/
  split : Bool

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
    on Phase 4 (the comment in the loop gives the C++ lines). A
    generated posting carries the cost written on its template posting
    (`AutoPost.cost`), which C++ copies to it before it would derive
    one (xact.cc:1611-1612), and the lot price of a fixed template
    amount (`AutoPost.lotUnit`), from which C++ derives one under the
    same condition on the matched posting (xact.cc:1613-1627). It
    returns as well the reason of a refusal that `finalizeXact` raises
    once `verifyExtended` has passed, the second of the cases below.

    Only real postings are matched here, while C++ matches every
    posting that an automated transaction did not generate, virtual and
    deferred ones included (xact.cc:1438-1447). Under `= /Food/` with
    `Assets:X 0.1`, C++ rejects `[Expenses:Food] 10.00 USD` against
    `[Assets:Cash]`, `(Expenses:Food) 10.00 USD` alone, and
    `<Expenses:Food> 10.00 USD` against an elided `Assets:Cash`, since
    the generated `Assets:X 1.00 USD` must balance; all three are
    accepted here (fail-open). With `Assets:Y -0.1` added, both C++ and
    the oracle accept the first and the third, and the balances of C++
    hold the two generated postings that these omit.

    C++ also matches each posting by which it completes an elided
    posting or the bucket's posting (xact.cc:1438-1447), and it can
    complete one commodity with several postings, one per annotated key,
    or with postings in a commodity whose weights net to zero, where
    `balancePool` makes one posting or none (`PoolResult.splitComms`,
    `ZeroCompletion`). A rule whose effect depends on those postings is
    refused as out of scope, with the line of the transaction: a
    template with a fixed amount or an expression books once per
    matched posting, a multiplier generates a posting from each, which
    the check that follows the rule (`verify()`, xact.cc:1040-1110,
    1683-1684) sums under its annotated key, a comparison of the amount
    tests each posting's own amount, and C++ tests each posting after
    the postings that the rule generated from those before it have
    joined the transaction and their accounts (xact.cc:1669-1671). None
    of these tests refuses a rule without template postings: C++ runs
    such a rule after every rule that has them (journal.cc:659-667), so
    that the note that it adds reaches no rule that generates a posting,
    and it changes no balance, whatever postings it matches. Under
    `= /Cash/` with only `; :Z:`, `Expenses:A  $5` and `Expenses:B  $-5`
    complete an elided `Assets:Cash` with `$0` in C++, which tags that
    posting and books nothing, and nothing is booked here. The engine
    runs such a rule in its place in the file, among the rules that
    generate postings, a departure (wrong rows): under `= /^Equity/`
    with only `; :SPLIT:`, followed by `= %SPLIT` with `(Budget)  1`,
    `Assets:Tajer  100 c` against `Equity:Gold  -100 c` books nothing in
    C++ and `-100 c` here. Any other rule is refused when one of its
    branches matches:
    - a completion of a commodity at risk (`PostSpec.splitRisk`), its
      amount comparisons dropped, since the amounts that C++ compares
      are not known here, when the rule has a template with a fixed
      amount or an expression, or the branch compares the amount, calls
      `all()` or reads `account("N").total`, which the postings
      generated from an earlier key can make fail for a later one. A
      rule whose templates only multiply stays accepted when its
      branches do none of these, unless the second case refuses it: a
      call of `any()` can only turn true as the rule generates postings,
      and every other condition reads the posting of each key as it
      reads the completion here, the posting of a key carrying the
      details of the posting completed (xact.cc:241-243) and a commodity
      condition reading the base commodity in C++ (post.cc:350-370), so
      that a rule that matched the posting of one key matches those of
      the keys after it. An expression whose value is linear in the
      amount, such as `(amount * 2)`, books on the postings of the keys
      what it would book on their sum, and it is refused all the same
      (fail-closed), as is a call of `all()` that the generated postings
      satisfy, a comparison of the amount or a total that every key
      passes as the completion does, or a template with a fixed amount
      when a call of `all()` or `any()`, or a comparison of the amount,
      lets a single key match, and C++ books once, as the engine does on
      its completion. Under `= /^Equity/` with `(Budget)  $10`,
      `Assets:Tajer  100 c (TAG)` and `Assets:Gruulmorg  200 c` complete
      an elided `Equity:Gold` with `-200 c` and `-100 c (TAG)` in C++,
      which books `$20`, and with `-300 c` here, which books `$10`, while
      with `(Budget)  0.1` in place of `$10` both book `-30 c`. Over the
      same transaction, under `= /^Equity/ and expr amount > -250` with
      `(Budget)  1`, C++ books `-300 c` and this books nothing; under
      `= /^Equity/ and expr amount < -150` with `(Budget)  $10`, the key
      of `-200 c` alone passes in C++, which books `$10`, as the engine
      does on its completion (fail-closed); under
      `= /^Equity/ and expr 'all(account =~ /Assets|Equity/)'` with
      `(Budget)  1`, C++ books `-200 c`, the generated posting failing
      `all()` for the second key, and this books `-300 c`; and after
      `(Budget)  10 c`, under `= expr account =~ /^Equity/ and
      account("Budget").total > -150 c` with `(Budget)  1`, C++ books
      `-200 c` and this `-300 c`. Under `bucket Assets:Cash` and
      `= /Cash/` with `(Budget)  $10`, a transaction of
      `Assets:T  10 AAPL {$50} @ $5 {$1}` alone gives `Assets:Cash` the
      postings `$-450` and `$-50 {$1}` in C++, which books `$20`, and
      the posting `$-500` here, which books `$10`. The argument by which
      a rule whose templates only multiply stays accepted runs from the
      first key, which C++ tests where the elided posting is written, as
      it tests there the posting that it makes of the commodity unsplit:
      a rule that matches the first key matches every later one. A rule
      that fails `any()` at the first key can still pass it at a later
      key, which C++ appends after the postings of the transaction, once
      the rule has generated postings from written postings that follow
      the elided posting; the split then changes what C++ books, and
      these tests do not refuse the rule. The engine tests its
      completion after the written postings, a departure that
      `PoolResult.posts` records, and so departs from C++ there with and
      without the split: under `= expr 'account =~
      /^Assets/ or account =~ /^Equity/ and any(account =~ /Budget/)'`
      with `(Budget)  1`, an elided `Equity:Gold` written before
      `Assets:Tajer  100 c (TAG)` and `Assets:Gruulmorg  200 c` makes C++
      book `200 c`, the first key, `-200 c`, failing `any()` and the
      appended `-100 c (TAG)` passing it, and `300 c` without `(TAG)`,
      while this books `0 c` in both. Likewise, the refusal of a branch
      that calls `all()` evaluates the call over the postings generated
      before the completion in the engine's order, so that where one of
      them has made `all()` false the completion is not refused, and the
      split can then decide what C++ books or whether it accepts the
      transaction. Under `= /^Equity|Assets:Tajer/ and expr
      'all(account =~ /Assets|Equity/)'` with `(Budget)  1`, an elided
      `Equity:Gold` written before `Assets:Tajer  100 c (TAG)` and
      `Assets:Gruulmorg  200 c` makes C++ book `-200 c`, and `-300 c`
      without `(TAG)`, while this books `100 c` in both, departing from
      C++ with and without the split. Under `= /^(Assets:C|Equity)/ and
      expr 'all(account =~ /Assets|Equity/)'` with `Budget  1`, an elided
      `Equity:Gold` written before `Assets:A  200 c (TAG)`,
      `Assets:B  100 c` and `Assets:C  -100 c` is completed in C++ with a
      zero where it is written and with `-200 c (TAG)` after the
      postings. The rule generates `Budget  0` from the zero, `all()`
      then failing for `Assets:C`, and C++ accepts the transaction, which
      it rejects without `(TAG)`, while this generates `Budget  -100 c`
      from `Assets:C` and rejects both for imbalance, departing from C++
      only with the split (fail-closed);
    - a completion of a commodity at risk, when the rule's templates
      only multiply, those of them that must balance do not cancel, and
      a written posting of the real pool that the rule does not match
      has an annotated weight in that commodity. C++ checks the
      transaction again after such a rule (`verify()`,
      xact.cc:1040-1110, 1683-1684), summing each annotated key apart:
      the postings that the rule generates from the keys of the
      completion and from the written postings that it matches leave
      unbalanced each key in which the written postings that it does not
      match fail to net to zero, while `verifyExtended`, which weighs
      the merged completion, passes wherever they net to zero in the
      commodity as a whole. Under `= /^(Assets:C|Equity)/` with
      `Budget  1`, C++ rejects `Assets:A  100 c (TAG)`,
      `Assets:B  -100 c` and `Assets:C  300 c` against an elided
      `Equity:Gold`, which it completes with `-200 c` and
      `-100 c (TAG)`, with the remainder `100 c` and `-100 c (TAG)`, and
      accepts them without `(TAG)`, while `verifyExtended` passes both;
      so it does with `[Budget]  1`, or with `Budget  2` and
      `Other  -1`, in place of `Budget  1`, and with a lot price or a
      lot date in place of the note, and under
      `= /^(Expenses:Rent|Liabilities:Card)/` with `Budget:Spent  1`
      it rejects `Expenses:Refund  -50 USD (refund)`,
      `Expenses:Refund  50 USD` and `Expenses:Rent  800 USD` against
      an elided `Liabilities:Card`, with the remainder `-50 USD` and
      `50 USD (refund)`. Templates that cancel, such as `Budget  1` and
      `Other  -1`, leave each key balanced, and C++ accepts the first
      of these journals with them. The refusal waits for
      `verifyExtended`, which `finalizeXact` runs after this function,
      so that a transaction that the engine's own check rejects keeps
      that reason: with `Assets:B  -50 c` in the first journal, both
      reject it. It over-approximates where the annotated weights of the
      written postings that the rule does not match net to zero in each
      key in C++ (fail-closed): with `(TAG)` on `Assets:B` as well, C++
      accepts the first journal, and so it does with `Assets:D  50 c {$2}`
      and `Assets:E  -50 c {$2}` added, two keys that each net to zero,
      showing in both the balances that the engine shows without the
      refusal. Every other refusal is raised at once, before
      `verifyExtended`, and so takes the place of the reason that this
      check gives where both it and C++ reject the transaction for
      imbalance. What the engine generates from a completion that C++
      splits or posts at zero need not be what C++ generates, and that
      check can find there an imbalance that C++ does not have: under
      `= /^Equity/ and expr amount < -250` with `Budget  1`, C++ accepts
      `Assets:Tajer  100 c (TAG)` and `Assets:Gruulmorg  200 c` against
      an elided `Equity:Gold`, completed with `-200 c` and
      `-100 c (TAG)`, neither of which passes the comparison, while the
      merged `-300 c` passes it here and `verifyExtended` would reject
      what the rule generates from it;
    - a completion at zero of a commodity at risk, its amount
      comparisons dropped. C++ books once for each of its postings, whose
      amounts need not be zero. A template with a fixed amount or an
      expression books on each; a rule whose templates only multiply
      fails the check that follows it (`verify()`) unless what it
      generates nets to zero in each key, as when those of its templates
      that must balance cancel, or when it matches as well the written
      postings whose weights the keys negate, and then, as when its
      templates are all virtual, it leaves every account's balance as it
      is, a case that this refusal does not tell apart (fail-closed):
      under `= /^(Assets|Equity)/` with `Budget  1`, C++ accepts
      `Assets:Tajer  100 c (TAG)` and `Assets:Gruulmorg  -100 c` against
      an elided `Equity:Gold`, which it completes with `100 c` and
      `-100 c (TAG)`, and shows the balances that the engine shows
      without the refusal. Under `= /Elided/` with `Budget  $10` and
      `Other  $-10`, `Assets:S  10 AAPL {$50}` and `Assets:T  -10 AAPL`
      complete an elided `Assets:Elided` with `10 AAPL` and
      `-10 AAPL {$50}` in C++, which books `$20` and `$-20`, and with
      nothing here, which books nothing; with `Budget  1` alone, C++
      rejects the transaction, the generated `10 AAPL` and
      `-10 AAPL {$50}` being two keys that `verify()` does not net;
    - any other completion at zero, at its zero amount, when the rule has
      a template with a fixed amount or an expression, a template
      posting that is not `(virtual)`, or a note. C++ completes such a
      commodity with at most one posting, of zero, on which a template
      with a fixed amount or an expression books as on any other: under
      `= /Cash/` with `(Budget)  $10`, `Expenses:C  3 EUR`,
      `Expenses:A  $5` and `Expenses:B  $-5` complete an elided
      `Assets:Cash` with `$0` and `-3 EUR` in C++, which books `$20`,
      and with `-3 EUR` here, which books `$10`. From that posting a
      multiplier generates a posting of zero, which changes no balance
      but which the engine does not make: one that is not virtual makes
      a later real balance assignment to its account measure the
      real-only balance (textual_xacts.cc:398-409), and one that must
      balance makes C++ check the transaction again (`verify()`). Under
      `= /Cash/` with `Budget  1` and `Other  -1`, `Expenses:A  $5` and
      `Expenses:B  $-5` complete an elided `Assets:Cash` with `$0`, and
      after a later `(Budget)  $10`, C++ reads `Budget  = $0` against
      the real-only balance and posts a zero, where `$-10` is posted
      here. A note written before the template postings tags the
      completion (xact.cc:1497-1503), for the rules after it to read. A
      rule whose templates are all `(virtual)` multipliers, and which
      carries no note, stays accepted, as regress/2482 requires of its
      completion at zero in `BTC`. The postings of zero that it
      generates change no balance, but each enters the sum by which C++
      shows its account, a sum that drops the precision that a lone
      inferred amount keeps (amount.cc:634-642), a departure
      (fail-open): under `= /Cash/` with `(Budget)  1`, when `Budget`
      holds a lone inferred `$-0.0004`, as an elided posting beside
      `Assets:B  1 FOO @ $0.0004` after `$1.00` elsewhere, the same
      completion makes C++ show `Budget` as zero, while it shows
      `$-0.0004` here.
    The functions `any()` and `all()` of C++ test every posting of the
    transaction (post.cc:653-700), its completions at zero included, so
    beside a completion at zero, of either pool, a rule with a branch
    that calls either is refused when the branch matches a real posting
    or a real completion at zero once its calls and amount comparisons
    are dropped: under `= /Assets:S/ and expr 'all(account =~
    /Assets:[ST]/)'` with `(Budget)  $10`, `Assets:S  10 AAPL {$50}` and
    `Assets:T  -10 AAPL` against an elided `Assets:Elided` make C++ book
    nothing, and this would book `$10`. A periodic
    template is tested alike, since C++ extends it as well
    (textual_xacts.cc:316-317) and gives each posting that a rule
    generates there to its account (xact.cc:1669-1671), while Phase 9
    gives the template's own postings to none (xact.cc:987-1010). A real
    posting so generated makes a later real balance assignment to its
    account measure the real-only balance (textual_xacts.cc:398-409):
    under `= /Cash/` with `Budget  1` and `Other  -1`, a template
    `~ Monthly` in which `Expenses:A  $5` and `Expenses:B  $-5` complete
    an elided `Assets:Cash` with `$0`, followed by `(Budget)  $10` and
    by `Budget  = $0` against an elided `Equity`, makes C++ post a zero,
    where `$-10` would be posted here. The refusal in a template can
    also fall on a journal that C++ reads as the engine does
    (fail-closed): under `= /^Equity/` with `(Budget)  $10`, a template
    of `Assets:Tajer  100 c (TAG)` and `Assets:Gruulmorg  200 c` against
    an elided `Equity:Gold` is refused, while C++ shows the balances
    that the engine shows without the refusal. That the engine
    gives no account the postings that a rule generates in a template
    is a departure that `flushPending` records, and so is the reading of
    `any()` and `all()` there, which C++ takes as false and true for a
    posting without a transaction. These tests read them as the engine
    does, so that a split that C++ makes in a template under a call of
    `all()` that is false here goes unrefused, its postings reaching
    accounts that the engine leaves as they are: under `= /^Equity/ and
    expr 'all(account =~ /Nothing/)'` with `(Budget)  $10`, a template
    of `Assets:Tajer  100 c (TAG)` and `Assets:Gruulmorg  200 c` against
    an elided `Equity:Gold`, followed by `(Budget)  $5` and, dated after
    the current date, by `Budget  = $0` against an elided `Equity`,
    makes C++ post `$-25`, and `$-15` without `(TAG)`, where `$-5` is
    posted here in both. These tests do not see the lot that C++
    carries into the amount of a balance assignment, a departure
    recorded at `PostSpec.fixated`, and do not refuse a split that it
    causes (fail-open): with `10 AAPL {$5}` held in `Assets:Broker`,
    under `= /^Equity/` with `(Budget)  $10`, `Assets:Broker  = 0 AAPL`
    beside `Assets:Other  4 AAPL` completes an elided `Equity:Gold` with
    `-4 AAPL` and `10 AAPL {$5}` in C++, which books `$20`, and with
    `6 AAPL` here, which books `$10`. Nor do they refuse a rule whose
    templates that must balance do not cancel where it matches a
    posting whose cost carries an annotation of its own: C++ derives the
    cost of the posting generated from it from the lot price of its
    amount, which lacks that annotation (xact.cc:1611-1627), so that the
    key of the annotated cost stays unbalanced in the check that follows
    the rule, a departure of `verifyExtended` that holds without a split
    (fail-open). Under `= /^(Assets|Equity)/` with `Budget  1`, C++
    rejects `Assets:Tajer  10 AAPL @ $5 (note)` against an elided
    `Equity:Gold`, which it completes with `$-50 (note)`, with the
    remainder `$50` and `$-50 (note)`, and it rejects as well the same
    posting beside `Assets:Gruulmorg  $20`, completed with `$-20` and
    `$-50 (note)`; it accepts both without `(note)`, while all four are
    accepted here.

    These tests read each branch as the engine reads it, so that a
    departure that makes the engine read a branch as false where C++
    reads it as true for the posting of some key hides the split, or
    the completion at zero, from them, as the departures above do for
    `any()` and `all()`. Others recorded beside their rules do the same:
    the balance that the engine reads for `account("N").total` before
    the transaction (`compileConj`), the place in which it runs a rule
    without template postings, the note written under a template posting
    that it gives to the matched posting, and the date of a posting that
    `dateOk` does not read: under `= /^Equity/ and expr date >=
    [2024/02/01]` with `(Budget)  $10`, `Assets:Tajer  100 c (TAG)` and
    `Assets:Gruulmorg  200 c` against an elided `Equity:Gold` that
    carries `; [2024/03/01]`, in a transaction dated 2024/01/01, make C++
    book `$20`, and `$10` without `(TAG)`, while this books nothing in
    both. -/
private def applyAutos (st : St) (hline : Nat) (xdate : Option Int)
    (payee : String) (code : String) (dateStr : String)
    (xactNotes : String) (posts : List PostSpec)
    (zeros : List ZeroCompletion) :
    Except String (List PostSpec × List (List (PostSpec × PostSpec × Bool))
      × Option String) :=
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
  -- the date of the transaction, while C++ reads the date of the posting
  -- tested (item.cc:149-150, 354-355; post.cc:143-174), which a note
  -- `; [DATE]` on the posting sets (item.cc:86-103), a departure (wrong
  -- rows): under `= /^Equity/ and expr date >= [2024/02/01]` with
  -- `(Budget)  $10`, `Assets:Tajer  100 c` and `Assets:Gruulmorg  200 c`
  -- against an elided `Equity:Gold` that carries `; [2024/03/01]`, in a
  -- transaction dated 2024/01/01, book `$10` in C++ and nothing here
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
      && (b.tagEq.all fun (k, v) => tagEqHolds k v xactNotes p.note)
  let instantiate := fun (xactNotes : String) (p : PostSpec) (a : Amount) =>
    fun (ap : AutoPost) =>
      -- C++ multiplies the matched amount by a template amount or an
      -- expression value without a commodity, and otherwise takes the
      -- template amount or the value as it stands (xact.cc:1533-1549), so
      -- that a posting generated from a tagged amount (`PostSpec.inferred`)
      -- keeps the tag, through the product, which amount_t::multiply
      -- leaves tagged (amount.cc:705-753), or through a value that is the
      -- matched amount, as that of `(amount)` is. The posting generated
      -- here is untagged, a departure (wrong rows): under `= /^C$/` with
      -- `(Budget)  1`, `(Budget)  (1)` or `(Budget)  (amount)`,
      -- `A  1 FOO @ $0.0004` against an elided `C` gives `Budget` the row
      -- `$-0.0004` and `$0.0004` in its credit column in C++, and no row
      -- here; with `(Budget)  $1` in a later transaction, the rows agree,
      -- and C++ still shows `$0.0004` in the credit column of `Budget`,
      -- where the counts of `bumpStat` give it no lone inferred amount
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
        -- the factor of a commodity equivalence, by which `canonAmt`
        -- reduces the generated amount and by which the template's lot
        -- price per unit is divided, as `finalizeXact` divides that of a
        -- written posting (amount.cc:1153-1176)
        let scale :=
          (resolveEquiv st.equivs ((st.commAliases.lookup amt.comm).getD amt.comm)).1
        let scale := if scale == 0 then 1 else scale
        { line := p.line, account := acct, kind := ap.kind
          amount := some (canonAmt st amt)
          costVal := ap.cost.map (canonAmt st), costPrec := ap.costPrec
          lotUnit := ap.lotUnit.map fun lu =>
            let c := canonAmt st lu
            ⟨c.comm, c.q / scale⟩
          lotTotal := ap.lotTotal, lotScale := scale
          : PostSpec }
  -- the refusals of completions that C++ splits or posts at zero (the
  -- docstring gives the rule and its witnesses): `loose` drops a
  -- branch's amount comparisons, `bare` its quantifiers as well
  let loose := fun (b : PredSpec) => { b with amountTerms := [] }
  let bare := fun (b : PredSpec) =>
    { b with amountTerms := [], anyRx := none, allRx := none }
  let splitWhy :=
    "out-of-scope automated transaction on a completion C++ splits by annotation"
  let zeroWhy :=
    "out-of-scope automated transaction on a completion C++ posts at zero"
  do
    let mut cand := posts.toArray
    let mut extra : List PostSpec := []
    let mut batches : List (List (PostSpec × PostSpec × Bool)) := []
    -- the reason of the refusal that waits for `verifyExtended` (the
    -- second case of the docstring)
    let mut pendingWhy : Option String := none
    for rule in st.autos do
      if !rule.active then
        batches := batches ++ [[]]
        continue
      -- a template with a fixed amount or an expression; whether the rule
      -- has template postings, without which C++ runs it after every rule
      -- that has them (journal.cc:659-667); and whether it does more on a
      -- completion at zero than add `(virtual)` postings of zero
      let shaped := rule.posts.any fun ap => ap.fixed.isSome || ap.exprSrc.isSome
      let generates := !rule.posts.isEmpty
      let marksZero := shaped || !rule.noteTag.isEmpty
        || rule.posts.any (·.kind != .virtualUnbal)
      if generates && !zeros.isEmpty then
        -- `bare` drops the quantifiers, which alone read the current set
        let tested : List (PostSpec × Amount) :=
          (cand.toList.filterMap fun p => match p.kind, p.amount with
            | PostKind.real, some a => some (p, a)
            | _, _ => none)
          ++ (zeros.filter (·.post.kind == .real)).map fun z =>
            (z.post, ⟨z.comm, 0⟩)
        if rule.branches.any fun b => (b.anyRx.isSome || b.allRx.isSome)
            && tested.any fun (p, a) => matchBranch xactNotes [] (bare b) p a then
          err hline (if zeros.any (·.split) then splitWhy else zeroWhy)
        let cur := cand.toList ++ extra
        for z in zeros do
          if z.post.kind == .real && (z.split || marksZero)
              && rule.branches.any fun b =>
                matchBranch xactNotes cur (if z.split then loose b else b) z.post
                  ⟨z.comm, 0⟩ then
            err hline (if z.split then splitWhy else zeroWhy)
      let mut batch : List (PostSpec × PostSpec × Bool) := []
      -- the commodities of the completions at risk that the rule matches,
      -- and the written postings of the real pool that it does not match,
      -- for the refusal that waits for `verifyExtended`
      let mut hit : List String := []
      let mut missed : List PostSpec := []
      for i in [0:cand.size] do
        let p : PostSpec := cand[i]!
        -- real postings only, neither virtual nor deferred ones, a
        -- departure that the docstring records. A deferred posting, never
        -- matched, counts among the postings of the real pool that the
        -- rule does not match, for the refusal that waits for
        -- `verifyExtended`
        match p.kind, p.amount with
        | PostKind.real, some a =>
            let cur := cand.toList ++ extra
            -- a completion at risk that a branch matches, its amount
            -- comparisons dropped, under a template with a fixed amount or
            -- an expression, or under a branch that compares the amount,
            -- calls `all()` or reads `account("N").total` (the first case
            -- of the docstring)
            if p.splitRisk && generates && rule.branches.any fun b =>
                (shaped || !b.amountTerms.isEmpty || b.allRx.isSome
                    || !b.acctTotal.isEmpty)
                  && matchBranch xactNotes cur (loose b) p a then
              err hline splitWhy
            if rule.branches.any fun b => matchBranch xactNotes cur b p a then
              if p.splitRisk then hit := a.comm :: hit
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
              -- the rule's note tags the matched posting, so later rules
              -- see it there (1984's :BUDGETED: guard, a note written
              -- before the template posting; xact.cc:1497-1503). C++
              -- gives a note written under a template posting only to the
              -- postings generated from that template (textual_xacts.cc:248,
              -- 274; xact.h:370-374; xact.cc:1658-1665), which no later
              -- rule with template postings matches (xact.cc:1443-1447),
              -- while `finalizeAuto` gathers every note line of the rule, a
              -- departure (wrong rows): under `= /Food/` with
              -- `(Budget)  $10` and `; :SEEN:` under it, and
              -- `= /Food/ and %SEEN` with `(Budget)  $10`,
              -- `Expenses:Food  $5` against `Assets:Cash  $-5` books `$10`
              -- in C++ and `$20` here. A rule without template postings tags
              -- here, in its place in the file, while C++ runs it after every
              -- rule that has them, a departure that the docstring records
              if !rule.noteTag.isEmpty then
                cand := cand.set! i { p with note := p.note ++ rule.noteTag }
            else if !p.splitRisk then
              missed := p :: missed
        | PostKind.deferred, some _ => missed := p :: missed
        | _, _ => pure ()
      -- a completion at risk that the rule matches, when its templates
      -- only multiply, those that must balance do not cancel, and a
      -- written posting of the real pool that it does not match has an
      -- annotated weight in that commodity (the second case of the
      -- docstring): `verify()` sums each annotated key apart
      -- (xact.cc:1040-1110, 1683-1684), which the engine's check of the
      -- merged completion does not
      let net := rule.posts.foldl (init := (0 : ℚ)) fun s ap =>
        if ap.kind != .virtualUnbal && ap.fixed.isNone && ap.exprSrc.isNone then
          s + ap.mult
        else s
      if net != 0 && missed.any fun p =>
          match p.costVal <|> p.amount with
          | some w => hit.contains w.comm
              && (if p.costVal.isSome then p.costAnnotated else p.annotated)
          | none => false then
        pendingWhy := some splitWhy
      batches := batches ++ [batch]
    pure (cand.toList ++ extra, batches, pendingWhy)

/-- A C++ balance key: the commodity, with the lot price (its
    commodity, its price per unit and its fixated flag) when the amount
    carries one. -/
private abbrev LotKey := String × Option (String × ℚ × Bool)

/-- The key under which C++ balances a posting's amount `a`: its
    commodity, with the posting's own lot price per unit
    (`PostSpec.lotUnit`) and fixated flag (annotate.h:120-125), and with
    no lot for an amount without a commodity (amount.cc:1908). -/
private def lotKeyOf (p : PostSpec) (a : Amount) : LotKey :=
  (a.comm, if a.comm == "" then none else
    p.lotUnit.map fun lu => (lu.comm, lu.q, p.fixated))

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
      order that C++ can take: one candidate per orientation, and
      beside them the candidate of the orientation that only the swap
      of issue #1130 takes, when that orientation converts and passes
      (`PoolResult.swapped`) -/
  | converts (cands : List PoolCandidate) (swapped : List PoolCandidate)
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
  /-- the pool's written postings, its elided posting left out, followed
      by the postings that complete the pool, if any, through its elided
      posting or through the bucket, in the reverse of the order in which
      their commodities first appear among the pool's weights. C++ fills
      the posting that it completes, the elided posting where it is
      written or the bucket's posting, which it adds after the postings
      of the transaction (xact.cc:368-372), with the first key of the
      sum, in the order in which it sorts the keys, and appends a posting
      for each further key after the postings of the transaction
      (xact.cc:234-246, 834-835; balance.cc:494-497, 509-521). This is a
      departure (wrong rows): a rule tests each posting after the
      postings that it generated from those before it have joined the
      transaction (xact.cc:1438-1447, 1669-1671), and `any()` and
      `all()` read them (post.cc:653-700). Under `= expr 'account =~
      /^Assets/ or account =~ /^Equity/ and any(account =~ /Budget/)'`
      with `(Budget)  1`, an elided `Equity:Gold` written before
      `Assets:Tajer  100 c` and `Assets:Gruulmorg  200 c` is tested first
      in C++, before any posting in `Budget` exists, and C++ books
      `300 c`, while here it is tested last and this books `0 c`; and
      under `= /Elided/ and expr 'all(account =~ /Assets/)'` with
      `(Budget)  1`, `Assets:S  $5` and `Assets:T  3 EUR` complete an
      elided `Assets:Elided` with `$-5` and then `-3 EUR` in C++, which
      books `$-5`, and in the opposite order here, which books
      `-3 EUR`. Where C++ splits the completion by annotation, this
      departure hides from the refusals of `applyAutos` a call of
      `any()` or `all()` that the split decides, as its docstring
      records. -/
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
  /-- the candidate of the orientation opposite to the one that the top
      posting's key decides, when the implicit exchange accepts the pool
      in that one, the two entries are of different commodities, and
      the opposite orientation converts and passes as well. C++ takes it
      when the swap of issue #1130 applies, that is when the top
      posting's commodity is COMMODITY_PRIMARY and the other is not
      (xact.cc:425-431), which depends on the price directives and the
      exchanges that precede the transaction, a history that balancing
      does not read (`St.primary` records the commodities that price
      directives and written costs mark, for valuation alone). Balancing
      does not read this candidate either, as the docstring of
      `impliedExchange` records; `verifyExtended` weighs the generated
      postings under it as under the orientations of `candidates`. -/
  swapped : List PoolCandidate := []
  /-- the commodities in which C++ can complete the pool with more than
      one posting, through its elided posting or through the bucket's
      posting, each with the weights that the engine sums in it, in
      posting order, whether its residual is zero or not; empty when
      neither completes the pool. C++ sums each posting that must
      balance at its cost, if it has one, and else at its amount, under
      its annotated commodity (xact.cc:325-333, annotate.h:120-125),
      adds the lot gains that Phase 6 books (xact.cc:692-713, 735-763),
      and completes the elided posting, or the bucket's, with one posting
      for each key of that sum (xact.cc:180-248, 368-372, 829-863), where
      `balancePool` completes it with one posting per commodity. The
      engine reads the lot price of an annotation and its fixation
      (`lotKeyOf`) but not its date, note or value expression, so it
      lists a commodity in which two or more weights fall, one of them
      annotated: an amount with `PostSpec.annotated` or a cost with
      `PostSpec.costAnnotated`. The gain that `costVal` adds to such a
      cost, the lot basis less the cost (`PostSpec.gainVal`), counts as a
      weight of its own, plain, for the gain that C++ books apart: under
      `= /Elided/` with `(Budget)  $10`,
      `Assets:T  10 AAPL {$50} @ $5 {$1}` completes an elided
      `Assets:Elided` with `$-450` and `$-50 {$1}` in C++, which books
      `$20`, and with `$-500` here, which books `$10`; with
      `bucket Assets:Cash`, the same posting alone gives `Assets:Cash`
      those postings in C++ and `$-500` here. The weights are the
      engine's, and they differ from those of C++ where `costVal`
      departs from it (`PostSpec.costAnnotated`): where C++ books no gain
      on such a cost, the gain counted here can list a commodity that C++
      keeps whole; where the price that annotates the cost is not one
      unit, the gain counted here differs from that of C++, and can
      differ in sign or be zero where that of C++ is not, so that a split
      that C++ makes goes unrefused (fail-open): under `= /Elided/` with
      `(Budget)  $10`, `Assets:T  10 AAPL {$5} @ $5 {$20}` completes an
      elided `Assets:Elided` with `$950` and `$-50 {$20}` in C++, which
      books `$20`, and with `$-50` here, which books `$10`; and the gain
      that C++ books on a cost in another commodity is not counted, so
      that a split that it causes goes unrefused as well (fail-open):
      under `= /Elided/` with `(Budget)  $10`,
      `Assets:T  10 AAPL {$50} @ 5 EUR {$1}` against an elided posting
      books `$20` in C++ and `$10` here. C++ adds the gain of a
      bracket-virtual posting to the real balance (xact.cc:712-713), which
      `costVal` weighs in the bracket-virtual pool (the comment beside
      it), so that a split of the real pool that the gain causes goes
      unrefused as well (fail-open): under `= /^Assets:D$/` with
      `(Budget)  $10`, `[Assets:A]  -10 AAPL {$1} @ $5` against an elided
      `[Assets:B]`, beside `Assets:C  $-60 (n)` and an elided `Assets:D`,
      completes `Assets:D` with `$-40` and `$60 (n)` in C++, which books
      `$20`, and with `$60` here, which books `$10`. The engine keeps
      neither of two annotations that C++ gives an amount
      (`PostSpec.fixated`), that of an `apply fixed` rate
      (textual_xacts.cc:626-638) and the lot that C++ carries into the
      amount of a balance assignment (textual_xacts.cc:843-862), so that
      a split that either causes can go unrefused (fail-open): under
      `= /Equity/` with `(Budget)  $10` and `apply fixed CAD $0.75`,
      `Assets:A  10 CAD` and `Assets:C  -1 FOO @ 4 CAD` complete an
      elided `Equity` with `4 CAD` and `-10 CAD {=$0.75}` in C++, which
      books `$20`, and with `-6 CAD` here, which books `$10`; under
      `= /Equity:Gold/` with `(Budget)  $10`, after `10 AAPL {$5}` in
      `Assets:Broker`, `Assets:Broker  = 0 AAPL` beside
      `Assets:Other  4 AAPL` completes an elided `Equity:Gold` with
      `-4 AAPL` and `10 AAPL {$5}` in C++, which books `$20`, and with
      `6 AAPL` here, which books `$10`. A commodity whose weights all
      carry one annotation is listed although C++ keeps it whole. A
      commodity listed in excess can only add refusals. `applyAutos`
      refuses the rules whose effect depends on the split
      (`PostSpec.splitRisk`, `ZeroCompletion.split`), and `finalizeXact`
      reads the weights for `St.lotFanout`. -/
  splitComms : List (String × List ℚ) := []
  /-- the completions at zero that C++ can make and `posts` lacks
      (`ZeroCompletion`), which `applyAutos` tests -/
  zeroCompletions : List ZeroCompletion := []

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
    or not, under which C++ accepts the pool, possibly none. When the
    top posting's key decides an orientation that converts and passes,
    and the two entries are of different commodities, `.converts` also
    carries the candidate of the opposite orientation if that one
    converts and passes, the orientation that the swap of issue #1130
    below would take.

    Known departures, each with the direction in which it fails:
    - the swap of issue #1130, which makes a COMMODITY_PRIMARY side the
      cost side `y` (xact.cc:425-431), is not modelled, because it
      depends on the history of price directives and earlier
      exchanges. The verdict here is that of the orientation that the
      top posting's key decides, and `verifyExtended` refuses a
      transaction whose verdict after an automated transaction depends
      on the orientation. The swap changes which side is doubled and
      whether a lot gain applies, and so the balancing verdict can fail
      either way. A `C` directive, for one, registers a price that marks
      its smaller unit primary (textual_directives.cc:185-188,
      commodity.cc:73-75). Beside `C 1 Kb = 1024 b`, C++ accepts
      `1024 b {$1}` against `$-1000` without a gain, and it is rejected
      here (fail-closed); against a same-sign `0.001 EUR` shown to two
      decimals, C++ doubles the `1024 b` and rejects the transaction,
      while here the doubled `EUR` rounds away and it is accepted
      (fail-open);
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
  let bal := pool.foldl (init := CppSum.null) fun s p =>
    match p.amount with
    | some a => s.add (lotKeyOf p a) a.q
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
        if lotKeyOf p a == x.1 then some (p.amtDecs, a.q) else none
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
  -- (`PoolResult.candidates`). A converting one carries beside its
  -- candidate that of the opposite orientation, which the swap of issue
  -- #1130 takes for two entries of different commodities
  -- (xact.cc:425-431), when that orientation converts and passes too
  -- (`PoolResult.swapped`)
  let ofVerdict := fun (x y : LotKey × ℚ) (v : Verdict) => match v with
    | .passes _ => Exchange.converts (candidate x y v)
        (if x.1.1 == y.1.1 then [] else match verdict y x with
          | .passes r => [{ exchange := some (y, x), residual := r }]
          | _ => [])
    | .fails => .fails
    | .declines _ => .declines
  if xact.any (·.costVal.isSome) then .declines
  else match bal, top? with
    | .balance [x, y], some top =>
        if x.2 == 0 || y.2 == 0 || top.fixated then .declines
        else
          let tk := top.amount.map (lotKeyOf top)
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
            | .passes _, .passes _ => .converts both []
            | .fails, .fails => .fails
            | .declines _, .declines _ => .declines
            | _, _ => .unordered both
    | _, _ => .declines

/-- The check that C++ makes once more after an automated transaction.
    `auto_xact_t::extend_xact` runs one rule at a time and, after a
    rule that generated a posting that must balance, calls `verify()`
    (src/xact.cc:1677-1684 and 1040-1110 at 76b9dc2b2). That sums the
    real and bracket-virtual postings of the extended transaction into
    one balance, each at its cost if it has one and else at its amount,
    with no implicit exchange and without the allowance that Phase 8
    makes for rounded per-unit costs (xact.cc:898-929), and tests the
    balance at display precision. As Phase 8 does (xact.cc:879-896), it
    first widens a cost commodity of display precision 0 to the
    precision of the first cost in it whose precision is positive, a
    derived cost excepted (xact.cc:1076-1091; `zeroTestPrec`). C++ also
    extends and checks a periodic template (textual_xacts.cc:316-317).
    Witness: under `= /Food/` with `Assets:Savings 0.1`, C++ rejects
    `Expenses:Food 10.00 USD` against an elided `Assets:Cash`, printing
    "Transaction does not balance" after "While applying automated
    transaction".

    `posts` are the transaction's postings before the extension,
    `real` and `bracket` what `balancePool` made of its two pools, and
    `batches` the triples of `applyAutos`, one list per rule. The
    balance before the extension is the residual of a candidate of the
    real pool, which is also what Phase 8 tests, together with the
    residual of the bracket-virtual pool. A generated posting weighs
    the cost written on its template posting, which C++ copies to it
    (xact.cc:1611-1612; regress/2268 and
    regress/coverage-auto-xact-post-cost are accepted only through it).
    Otherwise, when the matched posting has a cost, written or computed
    by Phase 3 in the orientation taken, and the generated amount
    carries a lot price, it weighs the cost that C++ derives from that
    price (xact.cc:1613-1627): the price per unit times the generated
    quantity, or, for a lot written `{{T}}`, the price per unit
    unscaled and negated for a negative quantity, since the annotation
    keeps ANNOTATION_PRICE_NOT_PER_UNIT after amount parsing divides
    the total by the quantity (amount.cc:1909-1923, `PostSpec.lotTotal`).
    The lot price is:
    - the template amount's own (`AutoPost.lotUnit`). C++ never reduces
      that amount, so the price per unit of a `{{T}}` lot is `lotUnit`
      times `lotScale`. Under `= /Food/` with `Assets:X 1 AAA {$5}` and
      `Assets:Y $-5`, C++ accepts `Expenses:Food 10 EUR @ $1.10` against
      an elided posting, deriving `$5` for `Assets:X`, and with
      `Assets:Y -1 AAA` it rejects the transaction;
    - else, when the generated amount copies the matched posting's
      annotation (the flag of `applyAutos`), the lot price that the
      matched posting writes. `finalize` reduces the matched amount at
      its end (xact.cc:987-996), so the price per unit of a `{{T}}` lot
      is `lotUnit` itself; a periodic template is not reduced, and
      there it is `lotUnit` times `lotScale`. Beside `C 1 Kb = 1024 b`,
      under `= /Food/` with `Assets:X 1` and `Assets:Y $-5`, C++ rejects
      `Expenses:Food 2 Kb {{$10}} @ $5` against an elided posting,
      deriving `$0.0048828125` for `Assets:X`, and accepts the same
      postings in a periodic template, deriving `$5`;
    - else, under the same flag in a transaction with a date, the
      per-unit cost with which Phase 6 annotates the matched amount
      (xact.cc:802-811, pool.cc:437, 508-522): the matched posting's
      written cost per unit, or the rate `|y/x|` of Phase 3 when the
      orientation converts that posting (xact.cc:454-465). A periodic
      template has no Phase 6 (xact.cc:522), and its matched amounts
      carry no such annotation.
    Otherwise it weighs its amount. Paren-virtual postings are exempt.
    A rule whose predicate matches only virtual or deferred postings
    generates nothing here and so is not checked, a departure that the
    docstring of `applyAutos` records.

    The check runs in each orientation that `real.candidates` admits and
    in the one of `real.swapped`, rule by rule over the weights of the
    generated postings so far. A transaction that passes in every
    orientation continues; one that fails in every orientation is
    rejected with a reason that begins, as the other balance rejections
    of `finalizeXact` do, `unbalanced transaction`; one whose verdict
    depends on the orientation is refused as out of scope. The check
    reads neither which commodities are COMMODITY_PRIMARY (the #1130
    entry of `impliedExchange`; `St.primary` records only those that
    price directives and written costs mark, for valuation) nor the
    order in which C++ takes two balance entries when neither is the
    top posting's key (balance.h:99, xact.cc:422-423), and each of
    these decides the orientation. Because the first is not read, the
    refusal also falls on a transaction before which no price
    directive, `C` directive or earlier exchange has marked any
    commodity primary, where C++ takes the orientation that the top
    posting's key decides. Under
    `= /Brokerage/` with `Expenses:Fees 0.01` and `Assets:Cash $-15.00`,
    C++ accepts `Assets:Brokerage 10 AAPL {$150.00}` against
    `Assets:Cash $-1500.00` as the first transaction of a journal, the
    generated `0.1 AAPL {$150.00}` deriving the cost `$15.00`; that
    orientation passes here and the opposite one fails, so the
    transaction is refused. Reading a full record of the commodities
    that C++ marks primary would narrow the refusal. A pool with no
    admissible orientation, which C++ rejects in every order while
    `balancePool` accepts it, is not checked again.

    Known departures, each with the direction in which it fails:
    - `verify()` keys every amount and cost as C++ keys it
      (annotate.h:120-125), an amount annotated with a lot price, a date
      or a note apart from plain units of its commodity, while the
      weights here merge by commodity. Under `= /Assets:A/` with
      `Assets:X 1` and `Assets:Y -10 AAA`, C++ rejects `10 AAA {$5}`
      against `-10 AAA {$5}`, and under `= /Food/` with
      `Assets:X 1 AAA {$5}` and `Assets:Y -1 AAA` it rejects
      `Expenses:Food $10.00` against an elided posting, as it does with
      `1 AAA [2026/01/01]` or `1 AAA (note)` in place of `1 AAA {$5}`;
      all of these are accepted here (fail-open). So is a transaction in
      which C++ derives the cost of a generated posting from the lot
      price of the matched amount while the matched cost carries an
      annotation of its own, which that lot price lacks
      (xact.cc:1611-1627): under `= /^(Assets|Equity)/` with `Budget  1`,
      `Assets:Tajer  10 AAPL @ $5 (note)` against an elided
      `Equity:Gold`, which C++ rejects with the remainder `$50` and
      `$-50 (note)`; the docstring of `applyAutos` gives the same
      posting beside a completion that C++ splits. Under
      `format 1.00 AAA`, with `Assets:Y 0.004 AAA`, it accepts
      `0.004 AAA {$1}` against `-0.004 AAA {$1}`, which is rejected here
      (fail-closed);
    - Phase 4, which gives every posting that must balance with a
      fixated lot price and no cost a cost while two or more entries
      remain after Phase 3 (xact.cc:475-518), is not modelled, so such
      a matched posting has no cost here and derives none for the
      postings generated from it. Under `= /Assets:A/`, C++ accepts
      `10 AAA {=$5}` against `$-50` with `Assets:X 0.5` and
      `Assets:Y $-25`, which is rejected here (fail-closed), and rejects
      it with `Assets:X 1` and `Assets:Y -10 AAA`, which is accepted
      here (fail-open);
    - Phase 6 rounds the per-unit cost of its annotation at the amount's
      precision, the cost commodity's display precision and six places
      more (pool.cc:460-468), where this keeps the exact quotient.
      Under `= /Expenses:Food/` with `Assets:X 3000000`, C++ rejects
      `3 FOO @@ $1.00` against an elided posting when
      `Assets:Y $-3000000.00` is added, which is accepted here
      (fail-open), and accepts it with `Assets:Y $-2999999.97`, which is
      rejected here (fail-closed). The per-unit price of a `{{T}}` lot is
      rounded in the same way (amount.cc:1909-1923) and enters a derived
      cost unscaled, so the two differ by less than a unit in the sixth
      place beyond the display precision that its commodity had when
      the lot was read; this could fail either way, and no journal is
      known on which it changes the verdict;
    - the flag of `applyAutos` also covers an amount expression whose
      value is in the matched commodity, which C++ annotates only when
      that value carries the annotation (xact.cc:1546-1549). Under
      `= /Energy/` with `Assets:Rebate (100 kWh)`, C++ rejects
      `100 kWh @@ 72.00 EUR` against an elided posting when
      `Income:Rebate -72.00 EUR` is added, which is accepted here
      (fail-open), and accepts it with `Income:Rebate -100 kWh`, which
      is rejected here (fail-closed);
    - the residual of a candidate is the balance that Phase 8 tests,
      while `verify()` sums the costs that Phase 6 leaves, and these
      differ for an exchange of two lots priced in one commodity: the
      shape that the docstring of `PoolResult.candidates` gives is
      accepted here and rejected by C++ (fail-open). They differ as well
      where a posting with a lot price has a cost written with a price
      of its own in the commodity of that lot price, a cost that Phase 6
      rewrites into the basis of the lot (xact.cc:735-774,
      `PostSpec.costAnnotated`): under `= /Assets:Y/` with `Budget  1`
      and `Other  -1`, C++ rejects `Assets:U  5 AAPL {$40} @ $5 {$1}`,
      `Assets:X  $-25 {$1}` and `Assets:Y  $-175` with the remainder
      `$25` and `$-25 {$1}`, and accepts them without the rule, while
      both are accepted here (fail-open);
    - `PostSpec.lotTotal` stands in for the mark that C++ keeps on the
      interned commodity, and its docstring gives a journal on which
      this departs in each direction;
    - the display precision read here omits what the amounts of an
      automated transaction teach C++ (`zeroTestPrec`), and this can
      fail either way. Under `= /Food/` with `Assets:Savings $0.001`,
      C++ rejects `Expenses:Food $10.00` against an elided posting,
      which is accepted here (fail-open). Under `= /Food/` with
      `Assets:X 0.1` and `Assets:Y -0.33 XYZ`, C++ accepts
      `Expenses:Food 10 EUR @ 0.333 XYZ` against an elided posting,
      since `-0.33 XYZ` gives `XYZ` a display precision of 2 and so
      `verify()` widens nothing, while here the written cost widens
      `XYZ` to three places and the remainder `0.003 XYZ` rejects it
      (fail-closed);
    - `verify()` also rejects a posting whose cost is in the commodity
      of its own amount (xact.cc:1064-1070), which is not checked here
      (fail-open). Under `= /Food/` with `Assets:X 1 USD @ 1 USD` and
      `Assets:Y -1 USD`, C++ rejects `Expenses:Food 10.00 USD` against
      an elided posting. A template amount without a commodity, such as
      `1 @ $1`, meets the same rejection beside a matched amount in `$`
      through the multiplication that the template parser does not
      model (`finalizeAuto`). Phase 6 makes the same check on a written
      posting with a cost (xact.cc:679-681), and `finalizeXact` does
      not make it either, so `A $10 @ $1` against `B` is accepted here
      (fail-open). -/
private def verifyExtended (st : St) (hline : Nat) (posts : List PostSpec)
    (real bracket : PoolResult)
    (batches : List (List (PostSpec × PostSpec × Bool)))
    (periodic : Bool) : Except String Unit :=
  let absQ := fun (q : ℚ) => if q < 0 then -q else q
  -- the weight of a generated posting `g` under the orientation `o`,
  -- `m` being the posting it was generated from and `d` the flag of
  -- `applyAutos`
  let weight := fun (o : PoolCandidate) (t : PostSpec × PostSpec × Bool) =>
    let (m, g, d) := t
    g.amount.map fun ga =>
      -- the cost derived from the lot price `lu` per unit; for a lot
      -- marked as a total, the price per unit of the amount as C++
      -- holds it is `lu` times `scale`
      let ofLot := fun (lu : Amount) (total : Bool) (scale : ℚ) =>
        (lu.comm, if !total then lu.q * ga.q
          else if ga.q < (0 : ℚ) then -(lu.q * scale) else lu.q * scale)
      let derived : Option (String × ℚ) := do
        let ma ← m.amount
        -- the matched posting has a cost: written, or computed by
        -- Phase 3 in this orientation
        let converted := match o.exchange with
          | some ((kx, _), _) => lotKeyOf m ma == kx
          | none => false
        guard (m.costVal.isSome || converted)
        match g.lotUnit with
        | some lu => pure (ofLot lu g.lotTotal g.lotScale)
        | none =>
          guard (d && ma.comm != "")
          match m.lotUnit, m.costVal, o.exchange with
          | some lu, _, _ =>
              pure (ofLot lu m.lotTotal (if periodic then m.lotScale else 1))
          | none, some cv, _ =>
              guard (!periodic)
              pure (cv.comm, absQ (cv.q / ma.q) * ga.q)
          | none, none, some ((_, qx), ((cy, _), qy)) =>
              guard (!periodic)
              pure (cy, absQ (qy / qx) * ga.q)
          | none, none, none => none
      ((g.costVal.map fun c => (c.comm, c.q)) <|> derived).getD (ga.comm, ga.q)
  let merge := fun (es : List (String × ℚ)) =>
    es.foldl (init := ([] : List (String × ℚ))) fun acc (c, q) =>
      if acc.any (·.1 == c) then
        acc.map fun (c', s) => (c', if c' == c then s + q else s)
      else acc ++ [(c, q)]
  let virt := (bracket.candidates.head?.map (·.residual)).getD []
  -- under `o`, the remainder of the first check that fails, if one does;
  -- the widening reads the costs of the postings generated so far
  let failure := fun (o : PoolCandidate) => Id.run do
    let mut gens : List PostSpec := []
    let mut ws : List (String × ℚ) := []
    for batch in batches do
      gens := gens ++ batch.map (·.2.1)
      let mb := batch.filter fun (_, g, _) => g.kind != .virtualUnbal
      if mb.isEmpty then continue
      ws := ws ++ mb.filterMap (weight o)
      let r := (merge (o.residual ++ virt ++ ws)).filter fun (_, s) => s != 0
      unless r.all (fun (c, s) => if c == "" then s == 0
          else roundsToZeroAt (zeroTestPrec st (posts ++ gens) c) s) do
        return some r
    return none
  let failures := (real.candidates ++ real.swapped).map failure
  match failures.filterMap id with
  | [] => pure ()
  | r :: _ =>
      if failures.all (·.isSome) then
        err hline (s!"unbalanced transaction after automated transaction " ++
          s!"(residual in {r.length} commodities)")
      else
        err hline ("out-of-scope automated posting weighed through an implicit " ++
          "exchange whose orientation depends on commodity primacy (#1130) or on " ++
          "the order of the balance entries")

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
  -- a transaction whose UUID has been seen is dropped whole but for the
  -- prices of its costs, for which its postings are still read: C++
  -- finalizes a transaction before it looks its UUID up and drops it
  -- (journal.cc:573-596), so that Phase 6 records those prices, at the
  -- date of the duplicate (`costPrice`). That date can differ from the
  -- earlier transaction's, since C++ compares the amounts of the two
  -- with the annotations that Phase 6 gives them (journal.cc:547-555,
  -- 624-639), which carry the date of the exchange only where the amount
  -- has no lot price and no lot date of its own (xact.cc:684-692,
  -- 803-812; pool.cc:508-522): with `-1 AAPL {$4} @ $5`, or
  -- `1 AAPL [2024/01/01] @ $5`, under `UUID: abc` on 2024/01/03 and again
  -- on 2024/01/10, `pricedb` lists AAPL at $5 on 2024/01/10 on both C++
  -- binaries. The duplicate teaches nothing here, while C++ learns from
  -- it as it reads it, a departure that the docstring of `costPrice`
  -- records. C++ rejects the journal where the postings of the two are
  -- not equivalent (journal.cc:624-639), which is not checked here
  -- (fail-open): `1 AAPL @ $5` under `UUID: abc` on 2024/01/03 and again
  -- on 2024/01/10 is rejected by both C++ binaries and read here. A
  -- duplicate with a posting that `parsePosting` does not read is dropped
  -- whole without an error, and the issue `unread-price`, with no
  -- commodity, stands in place of its points (`Result.priceIssues`):
  -- C++ reads `Assets:Cash  $-5 = (abs($-5) * -1)` in the duplicate of
  -- the purchase with a lot date above, skipping the check of a
  -- duplicate's assertion (textual_xacts.cc:787-809,
  -- test/regress/1771.test), and lists AAPL at $5 on 2024/01/10, while
  -- `parsePosting` does not read `abs`
  let dup := uuid?.any st.uuids.contains
  let st := match uuid? with
    | some u => if dup then st else { st with uuids := u :: st.uuids }
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
          posts := { pl with note := pl.note ++ ";" ++ (rawT.drop 1).toString
                             noteDate := noteDateOf stv (rawT.drop 1).toString
                               <|> pl.noteDate }
            :: rest
      | [] => leadNotes := leadNotes ++ [(rawT.drop 1).toString]
      continue
    let (p?, learned, comm?, decs, isExpr, teach) ←
      match parsePosting stv ln raw periodic with
      | .ok r => pure r
      | .error e =>
          if dup then
            return { st with priceIssues := ("unread-price", "") :: st.priceIssues }
          else throw e
    -- the decimals of a balance assertion or assignment reach the
    -- commodity named as written, while C++ names it through the
    -- commodity aliases as it parses the amount (pool.cc:121-127,
    -- 150-154), as the rule for a posting amount below does, a known
    -- departure: under `commodity EUR` with `alias E`, after
    -- `Assets:Cash  0 EUR = 0.000 E` against an elided `Equity`, C++
    -- prints a later `(1/3 EUR)` against an elided `Equity` as 0.333 EUR,
    -- where it leaves no row here (wrong rows)
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
        -- what `costPrice` reads: the amount unreduced and the cost
        -- reduced, each commodity named through the aliases, as C++
        -- parses them (textual_xacts.cc:583, 691), and the date that the
        -- posting's own note gives it
        let named := fun (c : String) => (stv.commAliases.lookup c).getD c
        let rawAmount : Option Amount :=
          p.amount.map fun a => ⟨named a.comm, a.q⟩
        let p := { p with
          amount := p.amount.map (canonAmt stv)
          costVal := p.costVal.map (canonAmt stv)
          lotVal := p.lotVal.map (canonAmt stv)
          lotUnit := p.lotUnit.map fun lu =>
            let c := canonAmt stv lu
            if scale == 0 then c else ⟨c.comm, c.q / scale⟩
          lotScale := if scale == 0 then 1 else scale
          assignTarget := p.assignTarget.map (canonAmt stv)
          rawAmount := rawAmount
          rawCost := p.rawCost.map (canonAmt stv)
          costLotComm := p.costLotComm.map named
          rateFixed := rawAmount.any fun a => a.comm != "" && !p.annotated
            && stv.fixatedComms.contains (some a.comm)
          noteDate := noteDateOf stv p.note }
        posts := p :: posts
    | none => pure ()
  let ordered := posts.reverse
  -- the prices that Phase 6 records for the costs of a transaction with
  -- a date (`costPrice`), read here, once its postings have taught this
  -- reader the display precisions that C++ reads when Phase 6 runs, and
  -- written to the price log once the transaction is balanced
  -- (`recordCostPoints`), each with the date that a note gives its
  -- posting, the posting's own or else its transaction's (`noteDateOf`).
  -- C++ reads the dates of a transaction in turn, each replacing the one
  -- before: the note of the header (`xactHeaderParts`), the note lines
  -- before the first posting, and then the text of each `apply tag` in
  -- force, the innermost first, so that the outermost prevails (Phase 7
  -- of `parse_xact`, textual_xacts.cc:1167-1188; `St.applyTags`). Under
  -- `apply tag [2024/02/01] x:y` around `apply tag [2024/03/01] z:w`,
  -- both C++ binaries list the price of `1 AAPL @ $5` in a transaction
  -- of 2024/01/03, whose header note is `; [2024/01/09]`, at 2024/02/01.
  -- A `~` template's costs record no price: C++ runs the lot matching
  -- and exchange phases of finalize, where exchange() records prices,
  -- only for a dated transaction (xact.cc:522-822, `if (has_date())`),
  -- and a template has no date. After `~ Monthly` with
  -- `Assets:Broker  10 AAPL @ $150`, `pricedb` lists no AAPL price and
  -- `bal -X $` leaves a later AAPL holding unvalued, on 3.4.1 and on
  -- 76b9dc2b2 alike
  let xactNoteDate := ((xactHeaderParts _header).2.toList ++ leadNotes
      ++ st.applyTags.filterMap id).foldl
    (fun acc n => noteDateOf stv n <|> acc) none
  let costPoints : List (String × Amount × Option (Option Int)) :=
    if periodic then []
    else ordered.filterMap fun p => (costPrice stv p).map fun (c, pr) =>
      (c, pr, p.noteDate <|> xactNoteDate)
  -- a transaction whose UUID has been seen writes these points alone, to
  -- the state before it (the comment on `dup`)
  if dup then return recordCostPoints st _header costPoints
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
  -- the account's balance as of this transaction's date (#1092,
  -- textual_xacts.cc:430-438). The real-only balance leaves out only
  -- the virtual postings, so a timelog posting stays in it
  -- (textual_xacts.cc:435, and account.cc:868 in file order). C++
  -- compares the date of each earlier posting itself (`post_t::date`,
  -- post.cc:143-174), which a posting note `; [DATE]` sets, while every
  -- event here carries the date of its transaction, a known departure:
  -- with `20 EUR` and `$10  ; [2024/12/01]` posted to `Assets:A` on
  -- 2024/01/01, C++ reads only the euros for `Assets:A  = 0` on
  -- 2024/06/01 and posts `-20 EUR`, which is rejected here
  -- (fail-closed), and for `Assets:A  = $0` it posts a zero, where the
  -- dollars are moved out here (wrong rows). An assignment also reads
  -- its account as written, while C++ reads it after a payee rule has
  -- mapped an `Unknown` account (journal_t::register_account,
  -- journal.cc:179-188), and the balances here are kept under the mapped
  -- name (`acctFor` below), a further departure: under
  -- `account Expenses:Food` with `payee Grocer`, after `$10` and `20 EUR`
  -- posted to `Expenses:Unknown` by the payee `Grocer`, C++ rejects
  -- `Expenses:Unknown  = 0` in a later transaction of that payee, which
  -- is accepted here (fail-open)
  let balAsOf := fun (acct comm : String) (realOnly : Bool) =>
    stv.datedEvents.foldl (init := (0 : ℚ)) fun acc ((a, c), d, q, k) =>
      if a == acct && c == comm && d <= xd && (!realOnly || k != .virt)
      then acc + q else acc
  for p in ordered do
    match p.assignTarget with
    | some target =>
        -- a REAL assignment measures the real-only balance when the account
        -- has a prior real posting, else the combined balance (#543/#1699);
        -- virtual assignments always measure the combined balance. C++
        -- makes this choice once for the account, from its postings in
        -- every commodity and on every date, whether or not they have an
        -- amount (an elided posting that the balancing leaves without one
        -- is recorded below), and a timelog posting does not count as real
        -- in it (compute_balance_diff, textual_xacts.cc:398-409): with
        -- `$10` in `Assets:A` and `(Assets:A)  20 EUR` before,
        -- `Assets:A  = 0` measures `$10` and no euros, and posts `$-10`.
        -- A deferred assignment always measures the combined balance here,
        -- a departure recorded at `EvKind`
        let realOnly := p.kind == .real && stv.datedEvents.any
          fun ((a, _), _, _, k) => a == p.account && k == .real
        let curOf := fun (c : String) => balAsOf p.account c realOnly
          + ((intra.lookup (p.account, c, realOnly)).getD 0)
        if target.comm == "" then
          -- a target without a commodity (textual_xacts.cc:817-871). C++
          -- subtracts from the target the account's balance and the
          -- account's earlier postings in this transaction, with lot
          -- annotations stripped, so that the lots of one commodity count
          -- as one (compute_balance_diff, textual_xacts.cc:390-479), and
          -- every exact zero leaves the difference (balance.cc:162-170).
          -- When every amount left rounds to zero at its display precision
          -- (textual_xacts.cc:842; an amount without a commodity only when
          -- it is exactly zero, amount.cc:1374-1430), C++ posts a zero
          -- without a commodity and leaves the account as it is
          -- (textual_xacts.cc:866). Otherwise it posts the difference
          -- converted to an amount by `balance_t::to_amount`, which throws
          -- "Cannot convert a balance with multiple commodities to an
          -- amount" when more than one commodity is left
          -- (textual_xacts.cc:851-858, balance.h:473-480). With `$10` and
          -- `20 EUR` in `Assets:A`, `Assets:A  = 0` against an elided
          -- `Assets:B` is rejected by C++ and here, and so are
          -- `Assets:A  = 5` when `Assets:A` holds `$10` alone, and
          -- `Assets:A  = 0` after `Assets:A  5 EUR` in the same transaction
          -- when it holds `$10` before. With `5` and `$10` in `Assets:A`,
          -- `Assets:A  = 5` posts `$-10`. Over a single commodity,
          -- `Assets:A  = 0` posts the negated balance and so zeroes the
          -- account (regress/1587), but over `($1 / 3)` alone, which shows
          -- as `$0`, it posts a zero, so that a later `($1 / 3)` makes the
          -- account show `$1`. An amount that the account holds in a
          -- commodity as a single inferred amount, one that C++ tags with
          -- the precision of the cost that it balances (BIGINT_COST_PREC,
          -- xact.cc:211-226), keeps the tag in the difference unless an
          -- earlier posting of the transaction in that commodity is
          -- subtracted from it, since a sum drops it (amount.cc:634-642,
          -- 677-681). C++ then takes it as zero only when it is exactly
          -- zero if the display precision is 0 or if the amount rounds to
          -- zero there with `in_place_roundto`, half away from zero as
          -- `roundAt` rounds, and otherwise tests it at display precision
          -- as it tests any amount (amount.cc:1384-1402, 1072-1100, issue
          -- #1692); the account's flows are counted as `Driver` counts
          -- them for a lone inferred balance (`flowStats`). After `$1.00`
          -- in `Assets:C` and `Assets:B  1 FOO @ $0.0004` against an
          -- elided `Assets:A` (the cost shape), `Assets:A  = 0` posts
          -- `$0.0004` and so zeroes the account, and with
          -- `Assets:B  1 BAR @ 0.0004 EUR` beside the `FOO`, it is rejected
          -- by C++ and here. With `@ $0.005` in the cost shape, the
          -- difference of exactly half a unit is zero, since its binary
          -- expansion rounds down (`cppRoundAt`), so that `Assets:A  = 0`
          -- posts a zero and a later `Assets:A  $0.01` leaves the account
          -- at `$0.005`, which shows as zero in C++ and here. The commodities
          -- considered are those of the account's balance and of its
          -- earlier postings in this transaction. Six departures are
          -- known, in the precision or the commodities of the difference.
          -- First, the display precision is the one learned from every
          -- posting of the transaction, while C++ has learned it only from
          -- the amounts before the assignment, so that a later posting that
          -- widens it makes a difference that C++ takes as zero be rejected
          -- here when it is left in more than one commodity (fail-closed),
          -- and be posted here when it is left in one (wrong rows): over
          -- `($1 / 3)` and `(1 EUR / 3)`, `Assets:A  = 0` followed by
          -- `Assets:C  $0.0001` is accepted by C++, and over `($1 / 3)`
          -- alone C++ leaves `$0.3333` in `Assets:A`, which is zeroed here.
          -- Second, the precision can be narrower here, since a periodic
          -- template and the postings of an automated transaction teach C++
          -- the precision of their amounts and the oracle nothing (see
          -- `flushPending`, and `zeroTestPrec` for the other sources that
          -- the oracle does not read): after a template with
          -- `Assets:Z  $0.001`, or after `= /^NEVER/` with
          -- `(Assets:Z)  $0.001`, C++ rejects `Assets:A  = 0` over
          -- `($1 / 3)` and `(1 EUR / 3)`, which is accepted here
          -- (fail-open). Third,
          -- C++ has not yet reduced the amounts of this transaction through
          -- commodity equivalences (textual_xacts.cc:583-587; they are
          -- reduced in finalize, xact.cc:996), while the reader reduces
          -- each as it reads it (`canonAmt`), so that two units of one
          -- equivalence are two commodities there and one here: under
          -- `C 1 EUR = 100 CENT`, with `1 EUR` in `Assets:A` from before,
          -- `Assets:A  1 EUR` followed by `Assets:A  = 0` in one
          -- transaction is rejected by C++ and accepted here (fail-open).
          -- Fourth, the flows that decide a tag are counted here on every
          -- date and of every kind, while C++ reads only those of the
          -- balance it measures, so that a single inferred amount beside a
          -- later posting in its commodity, or beside a virtual one when the
          -- real-only balance is measured, is read here at display
          -- precision: after the cost shape, `Assets:A  (1 EUR / 3)`, and
          -- `Assets:A  $1.00` dated after the assignment, C++ rejects
          -- `Assets:A  = 0`, which is accepted here (fail-open). A posting of
          -- exactly zero, which C++ neither adds to a balance nor subtracts
          -- from one (balance.cc:122-123, 162-163), counts here as well, as
          -- a flow or as an earlier posting of the transaction: after the
          -- cost shape and `Assets:A  (1 EUR / 300)`, `Assets:A  $0` followed
          -- by `Assets:A  = 0` in one transaction is rejected by C++ and
          -- accepted here (fail-open), and so is the same `$0` posted in an
          -- earlier transaction. Fifth, the amount that C++ posts keeps the
          -- tag (balance.h:477-478), and the posting that balances the
          -- assignment takes it over (xact.cc:234-237), so that after the
          -- cost shape C++ shows `$-0.0004` in the `Assets:D` that balances
          -- `Assets:A  = 0`, which shows as zero here (wrong rows, as before
          -- this rule, and with a target of `$0` as well). Sixth, the price
          -- precision that tags an amount is recovered here from the
          -- postings of its own balancing pool alone, a departure recorded
          -- at `pricePrec`
          let comms := ("" :: (stv.balances.filterMap fun ((acct, c), _) =>
              if acct == p.account then some c else none)
            ++ intra.filterMap fun ((acct, c, _), _) =>
              if acct == p.account then some c else none).eraseDups
          let left := comms.filterMap fun c =>
            let d := (if c == "" then target.q else 0) - curOf c
            if d == 0 then none else some (c, d)
          let tagged := fun (c : String) =>
            stv.flowStats.lookup (p.account, c) == some (1, 1)
              && (intra.lookup (p.account, c, realOnly)).isNone
          let shownZero := fun ((c, d) : String × ℚ) =>
            let prec := (stv.precisions.lookup c).getD 0
            c != "" && roundsToZero stv c d
              && (!tagged c || (prec != 0 && roundAt prec d != 0))
          if left.length > 1 && !left.all shownZero then
            err p.line (s!"balance assignment without a commodity leaves " ++
              s!"a balance in {left.length} commodities")
          let amt : Amount := match left with
            | [(c, d)] => if shownZero (c, d) then ⟨"", 0⟩ else ⟨c, d⟩
            | _ => ⟨"", 0⟩
          intra := addIntra intra (p.account, amt.comm) (p.kind == .real) amt.q
          resolved := { p with amount := some amt
                               assignTarget := none } :: resolved
        else
        let key := (p.account, target.comm)
        let diff := target.q - curOf target.comm
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
  -- (xact.cc:1611-1612). This test reads only the postings from before
  -- the extension, and `verifyExtended` reads the generated postings
  -- as well
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
    -- COST_PREC tagging: an inferred amount is tagged only when it fits
    -- the price precision recovered from a cost in its commodity
    -- (set_cost_prec_if_needed, xact.cc:195-231). Four departures are
    -- known. First, C++ scans every posting of the transaction
    -- (xact.cc:210) and this scans the pool alone: after `$1.00` in
    -- another account, with `Assets:B  1 FOO @ $0.0004` against an elided
    -- `Assets:C`, and `[Assets:E]  ($1 / 2500)` against an elided
    -- `[Assets:A]`, C++ shows `$-0.0004` in `Assets:A`, which shows as
    -- zero here (wrong rows), and with `(Assets:A)  (1 EUR / 300)` later,
    -- C++ rejects `Assets:A  = 0`, which is accepted here (fail-open).
    -- Second, C++ recovers the precision only from a cost in the plain
    -- commodity of the amount that it tags (xact.cc:213), and so not from
    -- a cost that keeps an annotation of its own
    -- (`PostSpec.costAnnotated`), while such a cost counts here (wrong
    -- rows): `A  1 FOO @ $0.0004 (n)` completes an elided `C` with an
    -- untagged `$-0.0004 (n)` in C++, which it prints as `$-0 (n)` and
    -- which leaves no row for `C`, and with a tagged `$-0.0004` here, a
    -- lone inferred balance that `Driver` shows unrounded. Third, C++
    -- applies the test to each of the postings by which it completes a
    -- commodity, one for each annotated key (xact.cc:234-247, 824-863),
    -- and a sum of two of them drops the tag (amount.cc:634-642), while
    -- this applies it to the single completion of the commodity (wrong
    -- rows): `A  1 FOO @ $0.0001` and `B  $5 (n)` complete an elided `C`
    -- with a tagged `$-0.0001` and an untagged `$-5 (n)` in C++, which
    -- shows `$-5` in `C` and `$5` in its credit column, and with a tagged
    -- `$-5.0001` here, which `Driver` shows unrounded. Fourth, C++ tags
    -- an amount only when the recovered precision exceeds the precision
    -- of its commodity at that point (xact.cc:217), a test that this
    -- makes as though that precision were 0, so that where that
    -- precision later falls below the recovered one, as a `format`
    -- subdirective or an amount that replaces a precision taken from a
    -- price directive can make it fall (textual_directives.cc:871-874,
    -- amount.cc:1839-1846), an amount that C++ leaves untagged can be
    -- tagged here and shown unrounded (wrong rows): after `X  $1.0000`
    -- against an elided `Y`, `A  1 FOO @ $0.0001` completes an elided
    -- `C` with an untagged `$-0.0001` in C++ and with a tagged one here,
    -- so that a later `commodity $` with `format $1.00` leaves no row for
    -- `C` in C++, while `Driver` shows the lone inferred balance
    -- unrounded, and `P 2024/01/01 FOO $0.0001` in place of the first
    -- transaction, with `X  $1.00` after the transaction of `C` in place
    -- of the directive, does the same. Each of the four reaches the debit
    -- and credit counts of `bumpStat` as well; `Result.lotFanout` is set
    -- for the third, where a tagged completion is in a commodity that
    -- `PoolResult.splitComms` lists. This omits as well the test by which
    -- C++ tags only an amount with digits after the point
    -- (xact.cc:222-226). That omission cannot change how an amount shows,
    -- since a whole amount shows alike at any precision, and it sets
    -- `Result.lotFanout` in excess where such an amount completes a
    -- commodity that `PoolResult.splitComms` lists
    let pricePrec := fun (c : String) =>
      pool.foldl (init := (0 : Nat)) fun acc p =>
        match p.costVal with
        | some cv =>
            if cv.comm == c && p.costDecs > 0 then
              max acc (if p.costDecs > p.amtDecs then
                p.costDecs - p.amtDecs else p.costDecs)
            else acc
        | none => acc
    let costTagged := fun (c : String) (s : ℚ) =>
      let pp := pricePrec c
      pp > 0 && roundAt pp s == s
    -- the weights that stand here for what C++ sums, in posting order,
    -- each with whether it is annotated, and the commodities in which
    -- C++ can complete the pool with one posting per annotated key
    -- (`PoolResult.splitComms`). A cost that carries an annotation of its
    -- own weighs twice when `costVal` holds a lot gain: C++ sums the cost
    -- under its annotated commodity in Phase 1, and Phase 6 can add a
    -- gain apart, plain (xact.cc:735-763), which the gain of `costVal`
    -- stands for with the departures recorded at `PostSpec.costAnnotated`
    let weights : List (Amount × Bool) := pool.flatMap fun p =>
      match p.amount, p.costVal with
      | none, _ => []
      | some a, none => [(a, p.annotated)]
      | some _, some cv =>
          let g : ℚ := match p.gainVal.map (canonAmt stv) with
            | some ga => if !periodic && p.costAnnotated && ga.comm == cv.comm then ga.q
                else 0
            | none => 0
          if g == 0 then [(cv, p.costAnnotated)]
          else [(⟨cv.comm, cv.q - g⟩, true), (⟨cv.comm, g⟩, false)]
    let weightsIn := fun (c : String) => weights.filter (·.1.comm == c)
    let atRisk := fun (c : String) =>
      (weightsIn c).length ≥ 2 && (weightsIn c).any (·.2)
    -- for a pool that its elided posting or the bucket's posting
    -- completes: the commodities of the weights, those at risk with their
    -- weights, and for each commodity whose weights net to zero the
    -- completion that C++ can still make (`ZeroCompletion`)
    let comms := (weights.map (·.1.comm)).eraseDups
    let splitComms := (comms.filter atRisk).map fun c =>
      (c, (weightsIn c).map (·.1.q))
    let zeroComps := fun (e : PostSpec) =>
      (comms.filter fun c => !residualExact.any (·.1 == c)).map fun c =>
        ({ post := e, comm := c, split := atRisk c } : ZeroCompletion)
    -- the bucket's account where the bucket completes the pool (the
    -- comment below gives the condition), and the completions at zero
    -- that C++ can make through the posting that it adds there
    let bucket? := if isReal && ordered.length == 1 then st.bucket else none
    let bucketZeros := fun (b : String) =>
      zeroComps { line := hline, account := b, kind := .real }
    match elided with
    | [] =>
        if residualExact.isEmpty then
          -- C++ adds the bucket's posting to a transaction of one posting
          -- whose sum is not null, a zero one included, and completes it
          -- with that sum (xact.cc:368-372, 829-844; `ZeroCompletion`)
          match bucket? with
          | some b => pure { posts := pool, splitComms, zeroCompletions := bucketZeros b }
          | none => pure { posts := pool }
        -- the `bucket` (`A`, account `default`) completes only a
        -- transaction of exactly ONE parsed posting of any kind,
        -- counted before automated postings; with two or more postings
        -- the residual is left to the implicit-exchange, rounding,
        -- second-pass lot-value and error cases below
        -- (xact.cc:368 `posts.size() == 1 && !balance.is_null()`, the
        -- second conjunct implied by a nonzero real residual;
        -- regress/coverage-bucket-single-post)
        else match bucket? with
          | some b =>
              -- bucket names were resolved when declared. C++ adds a null
              -- posting to the bucket (xact.cc:368-372), which it fills as
              -- it fills an elided one, so that it tags the amount only
              -- under the cost rule above (xact.cc:829-837, 234-237): after
              -- `$1.00` in `Assets:Y`, `Assets:X  ($1/1000)` alone leaves an
              -- untagged `$-0.001` in the bucket, which shows as zero and
              -- which a later balance assignment reads at display precision.
              -- It fills it per annotated key as well (xact.cc:829-863), so
              -- that the bucket's posting can split (`PostSpec.splitRisk`)
              let comps := residualExact.map fun (c, s) =>
                { line := hline, inferred := costTagged c s
                  account := b
                  kind := PostKind.real, amount := some ⟨c, -s⟩
                  splitRisk := atRisk c : PostSpec }
              pure { posts := pool ++ comps, splitComms, zeroCompletions := bucketZeros b }
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
              | .converts cs sw =>
                  pure { posts := pool, candidates := cs, swapped := sw }
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
        let comps := residualExact.map fun (c, s) =>
          { line := e.line, inferred := costTagged c s, note := e.note
            account := e.account, kind := e.kind
            amount := some ⟨c, -s⟩, splitRisk := atRisk c : PostSpec }
        let kept := pool.filter fun p => !(p.amount.isNone && p.assignTarget.isNone)
        -- the completions follow the postings kept, while C++ fills the
        -- elided posting where it is written (xact.cc:234-246), a
        -- departure that the docstring of `PoolResult.posts` records
        pure { posts := kept ++ comps, splitComms, zeroCompletions := zeroComps e }
    | _ => err hline "more than one elided posting in a balancing pool"
  let realPool := rposts.filter fun p => p.kind == .real || p.kind == .deferred
  let virtPool := rposts.filter fun p => p.kind == .virtualBal
  let exempt := rposts.filter fun p => p.kind == .virtualUnbal
  let realDone ← balancePool realPool true
  let virtDone ←
    if virtPool.isEmpty then pure { posts := [] }
    else balancePool virtPool false
  let completed := realDone.posts ++ virtDone.posts ++ exempt
  -- C++ completes the elided posting of a pool, or the bucket's posting,
  -- with one posting for each annotated key of the sum that Phase 1
  -- accumulates and Phase 6 extends with the lot gains that it books
  -- (xact.cc:180-248, 368-372, 692-713, 735-763, and Phase 7 at
  -- 824-863), where `balancePool` completes it with one posting per
  -- commodity, and it tags those of the postings that fit the precision
  -- of a cost, under the tests that the comment on COST_PREC tagging in
  -- `balancePool` records, a tag that the sum of two of them drops
  -- (amount.cc:634-642). The flag is set where this can change the debit
  -- or credit totals of the completed account, or how they show: where
  -- two of the weights that `PoolResult.splitComms` lists for a
  -- commodity have opposite signs (regress/1638), and where the
  -- completion of a commodity that it lists is tagged. Elsewhere those
  -- totals are those of C++, except where the balancing departs from
  -- C++, as the comments beside it record, and where `Result.lotFanout`
  -- records a miss: the gain of a bracket-virtual posting, for one (the
  -- comment beside `costVal`), leaves the net row of an account that
  -- elided postings of both pools complete as in C++ and changes its
  -- debit and credit totals
  if (realDone.splitComms ++ virtDone.splitComms).any (fun (_, ws) =>
        ws.any (· > 0) && ws.any (· < 0))
      || (realDone.posts ++ virtDone.posts).any (fun p => p.splitRisk && p.inferred) then
    stv := { stv with lotFanout := true }
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
  -- a transaction that the rule `tag("K") == "V"` tests is refused
  -- where `tagEqGuard` finds that C++ reads the test or completes the
  -- transaction otherwise
  for rule in stv.autos do
    if rule.active then
      for b in rule.branches do
        if let some (k, _) := b.tagEq then
          tagEqGuard hline k xactNotes rposts
  let (finalPosts, autoBatches, pendingWhy) ←
    applyAutos stv hline (headerDateF stv.dfmt stv.defaultYear _header)
      hpayee hcode dateTok xactNotes completed
      (realDone.zeroCompletions ++ virtDone.zeroCompletions)
  verifyExtended stv hline rposts realDone virtDone autoBatches periodic
  -- the refusal that `applyAutos` defers until the check that follows each
  -- rule has passed here, so that a rejection for imbalance keeps its reason
  if let some why := pendingWhy then err hline why
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
        stv := bumpStat stv nm a.comm p.inferred a.q
        stv := { stv with datedEvents :=
          ((nm, a.comm), xd, a.q, if p.kind == .real then .real else .virt)
            :: stv.datedEvents }
    | none => pure ()
  -- C++ adds every posting that is not deferred to its account, with or
  -- without an amount (xact.cc:1001-1005), and so an elided real posting
  -- that the balancing leaves at zero (xact.cc:829-842), which is dropped
  -- here, still makes a later real assignment to its account measure the
  -- real-only balance (textual_xacts.cc:399-406); an event of no amount,
  -- recorded for every elided real posting, stands for it: with
  -- `Assets:A` elided against `$10` and `$-10`, and `(Assets:A)  $10` and
  -- `(Assets:A)  20 EUR` after, `Assets:A  = 0` reads no balance and posts
  -- a zero. The bucket's posting, which C++ adds as well to a transaction
  -- of one posting whose sum is zero (xact.cc:368-372, `ZeroCompletion`),
  -- has no such event, a departure (wrong rows): with
  -- `bucket Assets:Cash`, after `Expenses:Food  $0` alone and
  -- `(Assets:Cash)  $10`, `Assets:Cash  = $0` against `Equity` posts a
  -- zero in C++ and `$-10` here
  for p in rposts do
    if p.kind == .real && p.amount.isNone then
      stv := { stv with datedEvents :=
        ((acctFor p.account, ""), xd, 0, .real) :: stv.datedEvents }
  -- the points of `costPoints`, written now that the transaction is
  -- balanced, since Phase 6 follows the implicit exchange of Phase 3
  stv := recordCostPoints stv _header costPoints
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
      -- account("N").total CMP AMOUNT (2099): live balance test. The
      -- engine reads the balance that the account held before the
      -- transaction, the quantities of all its commodities summed, and
      -- drops the commodity of the bound, while C++ reads the account's
      -- total (account.cc:884-900), with the postings of the transaction
      -- that have joined the account (xact.cc:987-1010) and those that
      -- rules generated before (xact.cc:1669-1671), and fails with
      -- "Cannot convert a balance with multiple commodities to an
      -- amount" when that total is held in more than one commodity, or
      -- under more than one annotation of one. Two departures follow:
      -- under `= expr account =~ /^Equity/ and account("Budget").total
      -- > 5 c` with `(Budget)  1`, `Budget  10 c` against an elided
      -- `Equity` books `-10 c` to `Budget` in C++, whose total is
      -- already `10 c`, and nothing here (wrong rows); and with
      -- `(Budget)  10 c` and `(Budget)  3 EUR` before, under the bound
      -- `-150 c`, C++ rejects `Assets:A  100 c` against an elided
      -- `Equity`, which is accepted here (fail-open), and so it does
      -- with `3 c (TAG)` in place of `3 EUR`
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
          -- every note line of the rule, wherever it stands, while C++
          -- gives the matched posting only those before the first
          -- template posting, a departure recorded in `applyAutos`
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
        -- the template keeps its account as written. C++ registers it
        -- when the rule is read, under the `apply account` stack and
        -- through the aliases then in force (textual_xacts.cc:271, 571),
        -- and registers the full name again, through the aliases in
        -- force, when the rule is applied (xact.cc:1655-1656), a known
        -- departure (wrong rows): with `alias Foo=Bar` and a rule
        -- `= /Food/` posting `Foo 1` and `Cash -1`, a posting of `$10`
        -- to `Expenses:Food` generates `$10` in `Bar` in C++ and in
        -- `Foo` here, and the same rule read under `apply account Top`
        -- without the alias generates them in `Top:Foo` and `Top:Cash`
        -- in C++ and in `Foo` and `Cash` here
        let (kind, name) ← accountKind ln acctField
        match amtField with
        | none =>
            -- amountless template mirrors the matched posting. C++ instead
            -- rejects a matched template posting with neither an amount
            -- nor an amount expression, "Automated transaction's posting
            -- has no amount" (xact.cc:1529-1531, regress/716,
            -- regress/coverage-xact-auto-noamount). Those two files were
            -- accepted here; `verifyExtended` now rejects them as
            -- unbalanced, a different reason, since the mirrored posting
            -- must balance. Under `= /Food/` with `Assets:X` and
            -- `Assets:Y -1`, C++ rejects `Expenses:Food 10.00 USD` against
            -- an elided posting, and the generated postings balance here,
            -- so it is accepted (fail-open)
            posts := { account := name, kind, fixed := none, mult := 1 } :: posts
        | some f =>
            let f := trimS f
            if f.startsWith "(" then
              -- expression template, evaluated per matched posting
              posts := { account := name, kind, fixed := none, mult := 1
                         exprSrc := some f } :: posts
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
                  posts := { account := name, kind, fixed := none
                             mult := if neg then -q else q } :: posts
              | none => err ln s!"malformed multiplier '{f}'"
            else do
              let r ← parseAmount st.amt ln f
              -- extended posts flow at face value (2268). The cost of a
              -- template amount is kept, as C++ keeps it on the template
              -- posting (textual_xacts.cc:699-710), and so is its own lot
              -- price, which C++ keeps on an amount with a commodity
              -- (amount.cc:1908). `verifyExtended` weighs a generated
              -- posting by the cost (regress/2268) or by the cost that
              -- C++ derives from the lot price (xact.cc:1613-1627)
              let ann ← annotLoop st.amt ln r.amount r.tail none none
              let ownLot := ann.ownLot && r.amount.comm != ""
              posts := { account := name, kind, fixed := some r.amount, mult := 1
                         cost := ann.cost
                         costPrec := if ann.perUnit then ann.costDecs + r.decimals
                           else ann.costDecs
                         lotUnit := if ownLot then ann.lot.map (·.1) else none
                         lotTotal := ownLot && ann.lotLit.any (·.2) } :: posts
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

/-- The seconds into its day of the time `s` of a price directive, read
    as strptime reads `%H:%M:%S` for `parse_datetime` (times.cc:154-155,
    2530-2531): an hour, a minute and a second of one or two digits
    each, after which C++ leaves the rest of the field unread, so that
    `10:00:00.5` and `12:00:00:00` read as `10:00:00` and `12:00:00` on
    both C++ binaries. A second of 60, which strptime admits, is the
    next minute, as `ptime_from_tm` makes it (`10:00:60` reads as
    `10:01:00`). Any other field is `none`: among them `25:00:00`,
    `10:00` and `10:00:61`, which both C++ binaries reject, and a second
    of more than two digits, whose reading depends on the C library. -/
private def priceTime (s : String) : Option Int := do
  let num := fun (cs : List Char) =>
    let ds := cs.takeWhile Char.isDigit
    if ds.isEmpty || ds.length > 2 then none
    else (String.ofList ds).toNat?.map fun v => ((v : Int), cs.drop ds.length)
  let (h, r) ← num s.toList
  let ':' :: r := r | none
  let (m, r) ← num r
  let ':' :: r := r | none
  let (sec, _) ← num r
  if h ≤ 23 && m ≤ 59 && sec ≤ 60 then some (h * 3600 + m * 60 + sec)
  else none

/-- The instant, in seconds from 0000-03-01 (`daysFromCivil`), of a
    price directive whose date field is `dateS` and whose time field is
    `timeS`, read as `parse_datetime` reads `DATE TIME`
    (pool.cc:559-564, times.cc:421-442): the date as `Y/M/D` or, failing
    that, as `M/D/Y` (times.cc:2530-2531), with a year of four digits
    and a month and a day of one or two, and the time of `priceTime`
    (test/regress/1202.test, test/regress/1130.test). Any other date is
    `none`. -/
private def priceInstant (dateS timeS : String) : Option Int := do
  let tod ← priceTime timeS
  let (y, m, d) ← match ← priceDateFields dateS with
    | [(y, 4), (m, lm), (d, ld)] | [(m, lm), (d, ld), (y, 4)] =>
        if lm ≤ 2 && ld ≤ 2 then some (y, m, d) else none
    | _ => none
  if priceDayValid y m d then some (daysFromCivil y m d * 86400 + tod)
  else none

/-- Whether C++ skips the character `c` as white space before a symbol
    or an amount (`peek_next_nonws`, utils.h:644-651, which asks
    `std::isspace`): a blank, a tab, a line feed, a carriage return, a
    vertical tab or a form feed. -/
private def cppSpace (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r' || c.toNat == 11 || c.toNat == 12

/-- Whether C++ ends a commodity symbol written without quotes at the
    character `c` (`invalid_chars`, commodity.cc:331-349): a digit, a
    blank, a tab, a line feed, a carriage return, DEL or one of
    `!&()*+,-./:;<=>?@[]^{|}~`. Any other character continues the
    symbol, a double quote, a backslash and every character beyond
    ASCII among them. -/
private def cppSymbolEnds (c : Char) : Bool :=
  c.isDigit || c.toNat == 127 || " \t\n\r!&()*+,-./:;<=>?@[]^{|}~".toList.contains c

/-- The characters of a commodity symbol written without quotes at the
    front of `cs`, as `commodity_t::parse_symbol` reads them
    (commodity.cc:417-426): those before the first at which
    `cppSymbolEnds`, a backslash standing for the character after it,
    whatever that is, and `none` for a backslash at the end, at which
    C++ throws. -/
private def cppBareSymbol : List Char → Option (List Char)
  | '\\' :: c :: r => (cppBareSymbol r).map (c :: ·)
  | ['\\'] => none
  | c :: r => if cppSymbolEnds c then some [] else (cppBareSymbol r).map (c :: ·)
  | [] => some []

/-- The characters of a commodity symbol between double quotes, `cs`
    being the text after the opening quote, as `READ_INTO` reads them
    for `commodity_t::parse_symbol` (commodity.cc:409-415,
    utils.h:660-697): those before the closing quote, a backslash
    standing for the character after it, or for a backspace, a form
    feed, a line feed, a carriage return, a tab or a vertical tab after
    it as `b`, `f`, `n`, `r`, `t` or `v`, and `none` where no quote
    closes the symbol, at which C++ throws. -/
private def cppQuotedSymbol : List Char → Option (List Char)
  | '\\' :: c :: r =>
      let e := match c with
        | 'b' => Char.ofNat 8 | 'f' => Char.ofNat 12 | 'n' => '\n'
        | 'r' => '\r' | 't' => '\t' | 'v' => Char.ofNat 11 | c => c
      (cppQuotedSymbol r).map (e :: ·)
  | '"' :: _ => some []
  | c :: r => if c == '\\' then none else (cppQuotedSymbol r).map (c :: ·)
  | [] => none

/-- The commodity symbol that `commodity_t::parse_symbol` reads from the
    front of `cs` (commodity.cc:404-436), after white space: the symbol
    of `cppQuotedSymbol` after a double quote, and otherwise that of
    `cppBareSymbol`, which is no symbol where it is a reserved word of
    the expression language (`is_reserved_token`, commodity.cc:359-381):
    `and`, `div`, `else`, `false`, `if`, `not`, `or` or `true`. `none`
    stands for a symbol at which C++ throws. -/
private def cppSymbolOf (cs : List Char) : Option String :=
  match cs.dropWhile cppSpace with
  | '"' :: r => (cppQuotedSymbol r).map String.ofList
  | r => (cppBareSymbol r).map fun s =>
      let s := String.ofList s
      if ["and", "div", "else", "false", "if", "not", "or", "true"].contains s then ""
      else s

/-- The commodity of the price `s` of a price directive as C++ reads it
    (`amount_t::parse`, amount.cc:1617-1659), empty for a price in no
    commodity, and `none` where C++ throws in reading the symbol. After
    white space and a sign, a price that begins with a digit or `.`
    begins with its number, which `parse_quantity` reads
    (amount.cc:1550-1580): the digits and the marks `.`, `,` and `'`
    that follow, less the marks that end them, of which a `.` is read
    again; the commodity is then what `cppSymbolOf` reads after the
    number, and none at the end of the text. Any other price begins
    with its commodity, which `cppSymbolOf` reads. -/
private def cppPriceComm (s : String) : Option String :=
  let cs := s.toList.dropWhile cppSpace
  let cs := match cs with
    | '-' :: r | '+' :: r => r.dropWhile cppSpace
    | r => r
  match cs with
  | c :: _ =>
      if c.isDigit || c == '.' then
        let tok := cs.takeWhile fun c => c.isDigit || c == '.' || c == ',' || c == '\''
        let num := (tok.reverse.dropWhile fun c => !c.isDigit).reverse
        let r := cs.drop num.length
        let r := if !num.isEmpty && r.head? == some '.' then r.drop 1 else r
        if r.isEmpty then some "" else cppSymbolOf r
      else cppSymbolOf cs
  | [] => some ""

/-- The state `st` once the price directive `P DATE [TIME] SYMBOL PRICE`,
    whose text after `P` is `rest`, has written its point to the price
    log, the directive read as `parse_price_directive` reads it
    (pool.cc:548-652), or once an issue stands in place of that point.
    `handleDirective` passes the text after a `P` that the first field
    follows directly, as in `P2024/01/02 EUR $1.10`, as well.

    - A field ends at a space or a tab (`next_element`,
      utils.h:623-640). When the second field begins with a digit it is
      a time, read with the date by `priceInstant` (pool.cc:559-564).
      Otherwise, when the first field begins with a digit, it is a date,
      read at 00:00 by `priceDay` (pool.cc:565-567).
    - When neither begins with a digit the directive has no date: its
      first field is the symbol, and C++ records the price at its current
      time (pool.cc:568-572; `CURRENT_TIME`, times.h:127-128), which is
      the instant of `--now` where one is given, and otherwise the instant
      at which the run began, which C++ fixes before it reads any file
      (global.cc:76), so that a `Y`, `year` or `apply year` directive
      does not move it (textual_directives.cc:561-567). The point is
      recorded here at the instant of the Driver's `--now`, and the issue
      `undated-price` stands in its place without that `--now` and after
      an in-file `--now` line (`St.nowInFile`).
    - The symbol of a dated directive is the next field, or the text
      between double quotes, after which C++ skips one character
      (`commodity_t::parse_symbol`, commodity.cc:438-455), so that the
      price of `"AAPL"$7` is 7 with no commodity. An alias of a
      commodity names the commodity that it denotes, on either side
      (pool.cc:121-127, 150-173).
    - A price that begins with `(` is an expression, which C++ evaluates
      (pool.cc:589-615, test/regress/1101.test) and which is not
      evaluated here: the issue `price-expr` stands in place of its
      point, and the primary commodities stay as they were, although C++
      marks the commodity of a result in one commodity primary
      (pool.cc:615, 646).
    - Any other price is an amount, read in the journal's style as
      `--decimal-comma` and the styles learned so far read an amount, with
      no `define`d name read as its value, since C++ reads a name there as
      a commodity and rejects `P 2024/01/01 EUR x` after `define x=5`
      (amount.cc:1665). Its commodity must be the one that C++ reads
      (`cppPriceComm`). C++ ends a symbol written without quotes at
      characters that `parseAmount` keeps in it, reads a backslash in a
      symbol as an escape and a reserved word as no symbol
      (commodity.cc:331-349, 359-381, 404-436), and reads no symbol
      after a number that a `,` begins or ends (amount.cc:1550-1580,
      1617-1659), so that it reads `P 2024/01/01 EUR 5 A!B` as a price
      of 5 A, `P 2024/01/01 EUR 5 and` and `P 2024/01/01 EUR 5, USD` as
      prices of 5 in no commodity, and `P 2024/01/01 EUR 5 A\ B` as a
      price in the commodity `A B`, where `parseAmount` reads the
      commodities `A!B`, `and`, `USD` and `A\`. The read itself teaches
      the commodity of the price neither a style nor a precision
      (PARSE_NO_MIGRATE, pool.cc:617, amount.cc:1832-1835); the
      tentative precision that C++ grants afterwards (pool.cc:628-634)
      is the rule of the `P` arm of `handleDirective`. C++ reduces the
      price through the commodity equivalences (amount.cc:1905-1906), as
      `canonAmt` does but for the departure below, so that
      `P 2024/01/01 BAR 1.5h` is a price of 5400 s. Text after the price
      is ignored, so that `P 2024/01/01 EUR $1.10 ; note` is a price of
      $1.10, except text that begins with `{`, `[` or `(`, which C++
      reads as an annotation of the commodity of the price
      (amount.cc:1636-1657, annotate.cc:147-271) and which the table does
      not model. A price of zero is a point (test/regress/1085.test).
    - C++ rejects a price in the commodity that it prices
      (pool.cc:639-642, test/regress/1940.test), so that the graph holds
      no edge from a commodity to itself (history.cc:353), and such a
      directive records nothing here.
    - The commodity of the price becomes primary (pool.cc:646,
      commodity.cc:72-78) where the point is recorded and where the issue
      `undated-price` stands in its place.

    Where a directive is not read as C++ reads it, the issue
    `unread-price` stands in place of its point: a date or a time that
    `priceDay` or `priceInstant` does not read, a symbol that is missing
    or whose quote is not closed, and a price that `parseAmount` does not
    read, that carries an annotation or whose commodity C++ reads
    otherwise. C++ rejects the journal at most such directives
    (pool.cc:551-552, 561-562; textual_directives.cc:195-200), and the
    journal is read on here as before the table was kept (fail-open), so
    that the issue changes no comparison; C++ reads the others, as it
    reads `P 01/15 EUR $1.10` under no year directive and
    `P 2024/01/01 EUR 5 A!B`, and there the issue marks the point that
    the table lacks.
    Three departures are known, and in each the table holds a point that
    C++ does not record, or lacks one that it does, with no issue. A `C`
    directive records the price of its larger unit at 1970-01-01 00:00,
    which the table does not hold, and marks both of its units primary,
    which `Result.primary` does not record (textual_directives.cc:174-191,
    amount.cc:1983-1985). Where it declares a one-to-one equivalence, C++
    reduces a price to its right side while `canonAmt` names the side
    that the rule of the `C` arm of `handleDirective` chooses: beside
    `C 1 A = 1 B`, `P 2024/01/01 X 5 A` is a price of 5 B in C++ and of
    5 A here. `Result.equivs` names such directives.
    When an `alias` subdirective gives a commodity a name that a posting,
    a price or another `alias` has already given to a commodity of its
    own, C++ retires that commodity and gives its vertex of the price
    graph, with the prices recorded on it, to the commodity that the
    alias names, which no longer reads the vertex that it held before or
    any price recorded there (pool.cc:150-173, history.cc:336-349; the
    comment at history.cc:347 that this vertex had no edges does not
    hold where a price was recorded on it). The amounts read before the
    alias keep the retired commodity, which reads the vertex that the two
    now share. The table keeps each point under the commodities that its
    directive named, and so departs in two directions. It lacks, for each
    of the two, the points that C++ reads for it through the shared
    vertex and that a directive gave the other: for the commodity that
    the alias names, those recorded before the alias for the retired one,
    and for the retired one, those recorded after it, so that `pricedb`
    can list one price twice where the table holds one point (a missing
    point). After `P 2018-08-30 $ 68.1451 RUB` and then `commodity ₽`
    with `alias RUB`, `pricedb` lists that one price both as `$` in `RUB`
    and as `₽` in `RUB` (test/regress/1678.test), and after a posting of
    `10 RUB` and the same block it lists a later `P 2024/01/02 RUB $0.01`
    both for `RUB` and for `₽`. It also keeps the points recorded before
    the alias for the commodity that the alias names, which C++ no longer
    reads (a wrong point): after `P 2024/01/01 E $1`,
    `P 2024/01/01 EUR $3` and then `commodity EUR` with `alias E`,
    `pricedb` lists `EUR` at `$1` alone and `-X $` values a later posting
    of `10 EUR` at $10 on both C++ binaries, where the table holds `E` at
    `$1` and `EUR` at `$3`. The price is read in the style that this
    reader has learned, and so inherits the departures of the reader's
    style model that the style rule of `finalizeXact`, the `D` arm of
    `handleDirective` and `flushPending` record: where C++ has the other
    style for the commodity of the price, or for the null commodity where
    the price has none, a number that reads differently in the two
    styles is a point at a value that C++ does not hold (a wrong point).
    After `D $1,000.00` and a posting of `$1,5`, `P 2024/01/04 Z $1,500`
    is a price of $1500 in C++ and of $1.5 here, and after a periodic
    template with a posting of `1.000,50 EUR`, `P 2024/01/04 Z 1,234 EUR`
    is a price of 1.234 EUR in C++ and of 1234 EUR here. -/
private def priceDirective (st : St) (n : Nat) (rest : String) : St := Id.run do
  let blank := fun (c : Char) => c == ' ' || c == '\t'
  let field := fun (s : String) => String.ofList (s.toList.takeWhile (!blank ·))
  let after := fun (s : String) =>
    String.ofList ((s.toList.dropWhile (!blank ·)).dropWhile blank)
  let digitFirst := fun (s : String) => s.toList.head?.any Char.isDigit
  let issue := fun (i c : String) =>
    { st with priceIssues := (i, c) :: st.priceIssues }
  let dateS := field rest
  let rest1 := after rest
  if rest1.isEmpty then return issue "unread-price" ""
  -- the instant of the directive, `none` where it is not read or not
  -- known, whether it has a date, and the text that holds the symbol
  -- and the price, after the date and the time
  let timeS := field rest1
  let (instant, dated, symPrice) :=
    if digitFirst timeS then (priceInstant dateS timeS, true, after rest1)
    else if digitFirst dateS then
      ((priceDay st dateS).map (· * 86400), true, rest1)
    else
      (if st.nowInFile then none else st.nowSecs.map (·.floor), false, rest1)
  let symP : Option (String × String) :=
    if !dated then some (dateS, symPrice)
    else
      match symPrice.toList with
      | '"' :: cs =>
          (cs.findIdx? (· == '"')).map fun i =>
            (String.ofList (cs.take i), String.ofList (cs.drop (i + 2)))
      | _ => some (field symPrice, after symPrice)
  let some (sym, priceS) := symP | return issue "unread-price" ""
  if sym.isEmpty then return issue "unread-price" ""
  let comm := (st.commAliases.lookup sym).getD sym
  if dated && instant.isNone then return issue "unread-price" comm
  let priceT := trimS priceS
  if priceT.startsWith "(" then return issue "price-expr" comm
  match parseAmount { st.amt with defines := [] } n priceT with
  | .error _ => return issue "unread-price" comm
  | .ok r =>
      if r.tail.startsWith "{" || r.tail.startsWith "[" || r.tail.startsWith "(" then
        return issue "unread-price" comm
      -- the commodity of the price must be the one that C++ reads
      -- (commodity.cc:331-349, 359-381, 404-436; amount.cc:1550-1580,
      -- 1617-1659): it reads `5 A!B` as 5 A, and `5 and` and `5, USD` as
      -- 5 in no commodity
      if cppPriceComm priceT != some r.amount.comm then
        return issue "unread-price" comm
      let price := canonAmt st r.amount
      if price.comm == comm then return st
      let primary :=
        if st.primary.contains price.comm then st.primary
        else price.comm :: st.primary
      match instant with
      | some t =>
          return { st with priceLog := ⟨t, comm, price⟩ :: st.priceLog, primary }
      | none =>
          return { st with
            priceIssues := ("undated-price", comm) :: st.priceIssues, primary }

/-- The state `st` with an `apply` directive pushed, as the innermost,
    onto the three lists that hold one entry for each `apply` directive in
    force: the account of an `apply account` onto `St.applyStack`, the
    commodity of an `apply fixed` or `apply rate` onto `St.fixatedComms`
    and the text of an `apply tag` onto `St.applyTags`, each `none` for a
    directive of another kind. -/
private def pushApply (st : St) (acct fixed tag : Option String) : St :=
  { st with applyStack := acct :: st.applyStack
            fixatedComms := fixed :: st.fixatedComms
            applyTags := tag :: st.applyTags }

/-- The state `st` with the innermost `apply` directive removed from the
    three lists that `pushApply` extends. -/
private def popApply (st : St) : St :=
  { st with applyStack := st.applyStack.drop 1
            fixatedComms := st.fixatedComms.drop 1
            applyTags := st.applyTags.drop 1 }

private def handleDirective (st : St) (n : Nat) (t : String) :
    Except String St := do
  -- general_directive ends the directive word at the first space or tab
  -- (next_element, textual_directives.cc:1028-1029, utils.h:623-640), as
  -- `directiveWord` does, so that `alias<TAB>Foo=Bar` is an alias
  let word := trimS (String.ofList
    (t.toList.takeWhile fun c => c != ' ' && c != '\t'))
  let restS := trimS (t.drop word.length).toString
  match word with
  | "alias" =>
      -- alias_directive (textual_directives.cc:716-728): the name ends
      -- at the first `=` and a line without one is ignored; the target
      -- is named under the `apply account` stack when the directive is
      -- read, by find_account, which rejects an empty component and
      -- drops a trailing colon (account.cc:79-131); and
      -- account_alias_directive rejects a name equal to that target
      -- (textual_directives.cc:701-714, baseline/dir-alias-fail). So
      -- `alias A=B=C` makes `A` denote `B=C`, `alias Foo=` is rejected,
      -- and under `apply account Top`, `alias Foo=Bar` makes `Foo` denote
      -- `Top:Bar` while `alias Top:Foo=Foo` is illegal. A bare `alias`
      -- lacks the argument that general_directive requires
      -- (textual_directives.cc:1034-1038,
      -- regress/coverage-wave11-directive-noarg)
      if restS.isEmpty then err n "directive 'alias' requires an argument"
      else
        match restS.splitOn "=" with
        | [] | [_] => pure st
        | al :: rhs =>
            let al := trimS al
            let raw := trimS (String.intercalate "=" rhs)
            match findAccountName raw with
            | none =>
                err n s!"alias target '{raw}' has an empty sub-account name"
            | some t =>
                let target := applyPrefixes st t
                if al == target then err n s!"illegal alias {al}={target}"
                else pure { st with aliases := (al, target) :: st.aliases }
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
      -- C++ keeps the `apply` directives of each file on a stack of its
      -- own, which ends with the file, an included file reading the
      -- stacks of the files that include it after its own
      -- (textual_internal.h:138-176; textual_directives.cc:402, 428-430),
      -- while the reader splices included files into one text (`splice`
      -- in Driver.lean) with one stack, so that an `apply` left open in an
      -- included file stays in force here to the end of the journal, a
      -- known departure: with `apply account Sub` left open in an included
      -- file, C++ posts a later `Assets:B  $5` against an elided `Equity`
      -- to `Assets:B` and `Equity`, where this reader posts it to
      -- `Sub:Assets:B` and `Sub:Equity` (wrong rows), and with
      -- `apply fixed AAPL $40` left open there, `10 AAPL @ $50` after the
      -- `include` line records the price $50 in C++ and none here, with no
      -- issue in its place (fail-open, `costPrice`)
      if restS.startsWith "account" then
        let acct := trimS (restS.drop "account".length).toString
        -- apply_account_directive requires a name and finds it under
        -- the stack with find_account (textual_directives.cc:464-487),
        -- which drops a trailing colon and rejects an empty component
        -- (`findAccountName`): under `apply account Top:`, a posting to
        -- `Baz` posts to `Top:Baz`, and a bare `apply account` is
        -- rejected (regress/coverage-wave11-apply-account-noarg)
        if acct.isEmpty then
          err n "directive 'apply account' requires an argument"
        else
          match findAccountName acct with
          | none =>
              err n s!"apply account '{acct}' has an empty sub-account name"
          | some a => pure (pushApply st (some a) none none)
      else
        -- `apply tag` gives labels, which bring no flows, with two
        -- exceptions. A date that its text gives, read as a note's
        -- (`noteDateOf`), becomes the date of each transaction under it
        -- and so of the prices of their costs (`St.applyTags`): under
        -- `apply tag [2024/02/01] x:y`, both C++ binaries list the price
        -- of `1 AAPL @ $5` in a transaction of 2024/01/03 at 2024/02/01,
        -- where the table holds it with the issue `posting-date`; left
        -- open in an included file, the same directive leaves that price
        -- at 2024/01/03 in C++, the scope departure above, and the table
        -- holds it at 2024/02/01 with that issue. A `UUID` tag that its
        -- text gives is the transaction's own in C++, which `uuidOf` does
        -- not read (the departure recorded there).
        -- `apply year` sets the year that C++ gives a date of a month and
        -- a day (textual_directives.cc:464-476, 543-559), which
        -- `defaultYear` does not follow, so that `priceDay` no longer reads
        -- such a date (`St.yearUnsure`): where a price directive or a
        -- transaction with a cost carries one, the issue `unread-price`
        -- stands in place of the point, and where a note gives one, the
        -- issue `posting-date` stands alone. Under `Y 2024` and
        -- `apply year 2024`, both C++ binaries list the price of
        -- `1 AAPL @ $5` in a transaction of `01/03` at 2024/01/03
        let kw := String.ofList
          (restS.toList.takeWhile fun c => c != ' ' && c != '\t')
        let yearUnsure := st.yearUnsure || kw == "year"
        -- `apply fixed` and `apply rate` read their argument as a price
        -- directive without a date (textual_directives.cc:473-474,
        -- 530-540; pool.cc:548-572), whose first field names the
        -- commodity, through the commodity aliases, and which needs a
        -- price after it (`St.fixatedComms`)
        let arg := trimS (restS.drop kw.length).toString
        let sym := String.ofList
          (arg.toList.takeWhile fun c => c != ' ' && c != '\t')
        let fixed :=
          if (kw == "fixed" || kw == "rate") && !sym.isEmpty
              && sym.length < arg.length then
            some ((st.commAliases.lookup sym).getD sym)
          else none
        let tag := if kw != "tag" then none
          else if arg.contains ':' then some arg else some s!":{arg}:"
        pure { pushApply st none fixed tag with yearUnsure }
  | "end" =>
      -- `end`, `end apply ...`, `end account`, `end tag` all close
      -- the innermost apply; a stray `end test`/`end comment` does not
      if restS.isEmpty || restS.startsWith "apply"
          || restS.startsWith "account" || restS.startsWith "tag"
          || restS.startsWith "fixed" || restS.startsWith "year"
          || restS.startsWith "rate" then
        pure (popApply st)
      else pure st
  | "bucket" =>
      -- default_account_directive resolves against the CURRENT apply
      -- stack (coverage-wave3-apply-directives) unless an alias fires,
      -- as register_account resolves a posting's account
      -- (textual_directives.cc:168-171): with `alias S=Suspense`,
      -- `bucket S` under `apply account Top` makes `Suspense` the bucket
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
      -- and 0.33 here (wrong rows). The rule takes the price to be the
      -- last field, or the last two, and so finds none where text
      -- follows it: `P 2024/01/01 EUR $1.2345 ; note` gives an unseen `$`
      -- four tentative places in C++ and none here, so that a later
      -- `($1/3)` against an elided posting shows as `$0.3333` in C++ and
      -- leaves no row here (wrong rows). The point of the directive, or
      -- the issue that stands in its place, is recorded first, by
      -- `priceDirective`, whose docstring records where its reading
      -- departs from that of C++; the two touch different parts of the
      -- state, so their order is immaterial
      let st := priceDirective st n restS
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
      -- accepted here (fail-open). The departure reaches the prices of
      -- costs as well, which are rounded at that precision and whose
      -- amounts are tested for zero at it (`costPrice`): after
      -- `Assets:Cash  $1.2345` against an elided `Equity` and then
      -- `D $1.00`, `3 AAPL @@ $100` records $33.3333333333 in C++ and
      -- $33.33333333 here. C++ locks the style with the same flag, which
      -- `lockPrecision` does not model; the style rule of `finalizeXact`
      -- records that departure
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
          pure { st with dfmt := if order.isEmpty then none else some order
                         inputDateFormat := true }
        else if base == "--now" then
          -- `headerDate` reads a date of three fields alone, where C++
          -- also reads a time after the date, or a period
          -- (report.h:1059-1074 at 76b9dc2b2), and where the end of an
          -- included file or `end apply year` restores the time that came
          -- before (textual_directives.cc:424-446, 593-595), so that a
          -- price directive without a date is no longer read
          -- (`St.nowInFile`)
          let st := { st with nowInFile := true }
          match headerDate none (trimS val) with
          | some d => pure { st with nowSecs := some ((d * 86400 : Int) : ℚ) }
          | none => pure st
        else
          pure st
      else if word == "expr" || word == "eval" then
        pure st          -- evaluate-and-discard
      else if word.startsWith "P" then
        -- C++ reads a line that begins with `P` and holds no word
        -- directive as a price directive, from the first character after
        -- the `P` that is not a blank (textual.cc:329, 363-364;
        -- textual_directives.cc:195-200), so that `P2024/01/02 EUR $1.10`
        -- is a price of EUR on 2024/01/02. Its point is recorded
        -- (`priceDirective`), but the line is otherwise skipped as an
        -- unrecognized one, so that the tentative precision of the `P`
        -- arm is not granted, a known departure with the consequences
        -- that the `P` arm describes (wrong rows, fail-open)
        pure { priceDirective st n (trimS (t.drop 1).toString) with errFlag := true }
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
  /-- the counts of `St.signStats`: the flows of nonzero amount that
      `flowStats` counts, kept apart for the debit and the credit column
      of each account (`bumpStat`) -/
  signStats : List ((String × String × Bool) × Nat × Nat)
  /-- some transaction has a balancing pool whose completion, through its
      elided posting or through the bucket's posting, can give the
      completed account debit or credit totals other than the engine's,
      or show them otherwise. C++ completes such a posting with one
      posting for each annotated key of the sum that Phase 1 accumulates
      and Phase 6 extends with the lot gains that it books
      (xact.cc:180-248, 368-372, 692-713, 735-763, and Phase 7 at
      824-863; annotate.h:120-125), each negating the weights that fall
      in its key, where the engine completes it with one posting per
      commodity or with none. When no two weights of a commodity have
      opposite signs, no two of those postings have opposite signs
      either, and the debit and credit totals of the completed account
      are those of the engine's single posting. When the weights have
      both signs, the postings can have both, and both totals then
      exceed the engine's: in regress/1638, C++ completes the elided
      `Income:Currency` of the transaction `Buy food` with `40 USD` and
      `-40 USD {=1.30 CAD}`, which add `40 USD` to each column of that
      account, while the engine makes no posting in `USD` there. C++
      also tags those of the postings that fit the precision of a cost,
      under the tests that the comment on COST_PREC tagging in
      `balancePool` records, and the sum of two of them in one column
      drops the tag (amount.cc:634-642), so that a column that C++ fills
      with two postings of one sign shows at display precision, where
      the engine's single tagged posting, alone in its column, counts in
      `signStats` as a lone inferred amount:
      `A  1 FOO @ $0.0001` and `B  $5 (n)` complete an elided `C` with
      `$-0.0001` and `$-5 (n)` in C++, which shows `$5` in the credit
      column of `C`, and with a tagged `$-5.0001` here. The flag is set
      when the weights that `PoolResult.splitComms` lists for a
      commodity include one above zero and one below, whether the
      commodity's residual is zero or not, and when the completion of a
      commodity that it lists is tagged (`PostSpec.inferred`).

      It is set in excess where C++ keeps all the weights of the
      commodity under one key, or where its keys net to one sign, in
      either case where the completion is not tagged, so that the totals
      of the completed account are the engine's and show as the engine's
      do; where a tagged completion shares its column with another flow;
      where the tag cannot change how the column shows, since C++ widens
      the display of a tagged amount only in a commodity of display
      precision 0 or where the amount rounds to zero at that precision
      (amount.cc:2041-2054), a precision known only once the journal is
      read, and since a whole amount, which C++ leaves untagged
      (xact.cc:222-226), shows alike at any precision; and where the
      commodity is listed only for a weight of zero, which C++ adds to no
      key (balance.h:131, balance.cc:122-123). In regress/1217 the cost
      `0.00160 ETH {334.51 EUR} [2017-06-13]` and the amount
      `-0.00160 ETH {334.51 EUR} [2017-06-13]` fall under one key, and C++
      completes the elided `Assets:Current:Kraken` with `-334.51 EUR` and
      a posting of zero in that key; `Assets:A  10 AAA (x)` and
      `Assets:B  -5 AAA (x)` complete an elided `Equity` with `-5 AAA (x)`
      alone in C++, and with `Assets:C  3 AAA` beside them with `-3 AAA`
      and `-5 AAA (x)`; after the transaction of `C` above, a later
      `C  $-1` against an elided `D` brings the credit column of `C` to
      `$6` in C++ and here; after `X  $1.0000` against `Y`, the
      transaction of `C` shows `$5.0001` in the credit column of `C` in
      C++ and here; `A  10 FOO @ $5.00` and `B  $10 (n)` complete an
      elided `C` with `$-50` and `$-10 (n)` in C++, neither tagged, and
      with a tagged `$-60` here, each showing `$60` in the credit column
      of `C`; and `A  1 FOO @ $0.0001` beside `B  $0 (n)` completes an
      elided `C` with `$-0.0001` alone in C++ and here, each showing
      `$0.0001` in the credit column of `C`.

      It is missed where the weights that `PoolResult.splitComms` lists
      depart from those of C++, as its docstring and that of
      `PostSpec.costAnnotated` record, among them where C++ adds the gain
      of a bracket-virtual posting to the real balance (xact.cc:712-713),
      which the engine weighs in the bracket-virtual pool (the comment
      beside `costVal`), and where C++ gives an amount an annotation that
      the engine does not keep (`PostSpec.fixated`); the totals then
      differ (wrong rows). With an elided `[Assets:D]` and an elided
      `Assets:D`, `[Assets:A]  -10 AAPL {$1} @ $5` beside
      `Assets:C  $-60 (n)` completes `[Assets:D]` with `$50` and
      `Assets:D` with `$-40` and `$60 (n)` in C++, whose columns then
      hold `$110` and `$40`, and with `$10` and `$60` here, which leave
      `$70` in the debit column alone, the net row of `Assets:D` being
      `$70` on both sides. C++ carries into the amount of a balance
      assignment the lot of its target, or else the account's single lot
      (textual_xacts.cc:843-862): with `10 AAPL {$5}` in `Assets:Broker`,
      `Assets:Broker  = 0 AAPL` beside `Assets:Other  4 AAPL` completes
      an elided `Equity:Gold` with `-4 AAPL` and `10 AAPL {$5}` in C++,
      whose columns then hold `10 AAPL` and `4 AAPL`, and with `6 AAPL`
      here; in a journal of its own, `Assets:Broker  = 10 AAPL {$5}`
      beside `Assets:Other  -10 AAPL` completes an elided `Equity:Gold`
      with `10 AAPL` and `-10 AAPL {$5}` in C++, whose columns then hold
      `10 AAPL` each, and with no posting here. An `apply fixed` rate
      annotates an amount (textual_xacts.cc:626-638): under
      `apply fixed CAD $0.75`, `Assets:A  10 CAD` beside
      `Assets:C  -1 FOO @ 4 CAD` completes an elided `Equity` with
      `4 CAD` and `-10 CAD {=$0.75}` in C++, whose columns then hold
      `4 CAD` and `10 CAD`, and with `-6 CAD` here.

      The flag does not cover the other departures of the tag of an
      inferred amount, the first, second and fourth that the comment on
      COST_PREC tagging in `balancePool` records and that of a posting
      generated from a tagged amount (the comment on `instantiate` in
      `applyAutos`). Each can reach the net rows, and it can reach a
      column alone where the account holds a flow of the other sign:
      `A  1 FOO @ $0.0004 (n)` against an elided `C`, then `C  $1`
      against an elided `D`, give `C` the row `$1` in C++ and here, and
      C++ shows zero in the credit column of `C`, where the engine's
      tagged `$-0.0004`, alone in that column, counts in `signStats` as a
      lone inferred amount. A periodic
      template, whose result `flushPending` discards, and a transaction
      dropped for its UUID leave the flag as it was. -/
  lotFanout : Bool
  /-- the dated price table that the price directives and the costs
      written on the postings of transactions with a date record, in the
      order in which its points were last written (`priceDirective`,
      `costPrice`, `recordCostPoints`, `priceTable`); `pricesAt` reads it
      as of an instant -/
  prices : List PricePoint
  /-- the commodities that the price directives and the costs mark
      primary, as far as this reader records them, kept for valuation
      alone: balancing does not read them (the #1130 entry of
      `impliedExchange`). Apart from the departures that `costPrice`
      records, under which the price of a cost can round to zero here
      alone or in C++ alone, the list holds the commodity of the price of
      each point that a directive records, of each directive with the
      issue `undated-price`, and of each price that C++ records for a
      written cost, whether the table holds its point or an issue that
      names its commodity stands in its place (commodity.cc:72-78,
      commodity.h:237). After a periodic template with `X  $0.50`
      against an elided `Y`, which teaches C++ alone the two places of
      `$`, `10 AAPL @@ $0.000001` records $0.0000001 in C++, which marks
      `$` primary, and here a price that rounds to zero at six places,
      which records nothing. The same holds after `Assets:A  $1.0000001`
      against an elided `Equity` and then `D $1.00`, after which `$` keeps
      seven places in C++ and has two here: `10 AAPL @@ $0.00000001`
      records $0.000000001 in C++ and nothing here.

      The list leaves out five kinds of commodity that C++ marks. The
      first is the commodity of a price expression whose result is in one
      commodity (pool.cc:615, 646). The second is the commodity of the
      price of a directive with the issue `unread-price`, with those of
      the prices of a transaction dropped for its UUID for which that
      issue stands. The third is each unit of a `C` directive: the smaller
      through the price that the directive records
      (textual_directives.cc:185-188, commodity.cc:73-75), and the larger
      through `parse_conversion`, which gives it the flags of the smaller
      (textual_directives.cc:191, amount.cc:1983-1985). The fourth is the
      commodity of a cost that Phase 3 of `finalize` computes for an
      implicit exchange, which Phase 6 exchanges as it does a written
      one, with that of the lot price that it records beside it
      (xact.cc:425-465, 669-690, 782-800). The fifth is the commodity of
      the price that C++ records for a cost on an amount that an
      `apply fixed` left open in an included file annotates here alone, of
      which the table holds neither the point nor an issue (the departure
      that `costPrice` records). The list is therefore complete, apart
      from the departures of `costPrice` under which a price rounds to
      zero on one side alone, for a journal whose `priceIssues` holds no
      `price-expr` or `unread-price` entry and which has no `C` directive,
      no transaction that an implicit exchange balances and no
      `apply fixed` or `apply rate` left open in an included file -/
  primary : List String
  /-- the price directives and the written costs whose point the table
      does not hold, or holds at a date that a note or an `apply tag`
      gives, in the order in which they are read, each as an issue and
      the commodity that it prices, empty where that is not read. The
      issue `price-expr` stands for a price that is an expression, and
      `undated-price` for a directive without a date whose instant is not
      known here. The issue `unread-price` stands for a directive that is
      not read as C++ reads it (`priceDirective`) and for a cost in a
      transaction whose date `priceDay` does not read; with no commodity,
      it stands for a transaction dropped for a UUID seen before with a
      posting that `parsePosting` does not read (`finalizeXact`). The
      issue `posting-date` stands for a cost whose price C++ records at
      the date that a note of its posting or of its transaction, or an
      `apply tag` in force, gives (`noteDateOf`, `St.applyTags`), and the
      table holds the point if `priceDay` reads that date. Where an
      `apply tag` is left open in an included file, which ends it in C++
      alone (the departure recorded at the `apply` arm of
      `handleDirective`), that issue also stands for a later cost whose
      price C++ records at the date of its transaction.
      Apart from the departures that `priceDirective` and `costPrice`
      record, among them a price read in a style other than the one in
      which C++ reads it, a cost whose price is rounded at a display
      precision that this reader learns otherwise than C++, and a cost on
      an amount that an `apply fixed` left open in an included file
      annotates here alone, a price directive or a written cost of a
      journal that C++ reads either writes to the table the point that
      C++ records or has an entry here -/
  priceIssues : List (String × String)

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
      -- unexpected character; and a period expression that C++ cannot
      -- read, or a note after it, which C++ rejects
      -- (textual_xacts.cc:303, baseline/cmd-source.test) and which is
      -- not read here. C++ applies the automated transactions to a
      -- template and checks it again (textual_xacts.cc:316-317,
      -- xact.cc:1683-1684), and `verifyExtended` does the same, with no
      -- lot price from Phase 6 on a matched posting, since Phase 6 runs
      -- only for a transaction with a date (xact.cc:522). C++ reads each
      -- posting of a template as one without a transaction, for which
      -- `any()` is false and `all()` true (textual_xacts.cc:490,
      -- post.cc:653-700), while `applyAutos` tests both over the postings
      -- of the template and those generated before, a departure in either
      -- direction: under `= /^Equity/ and expr 'any(account =~ /Tajer/)'`
      -- with `Budget  1`, a template of `Assets:Tajer  100 c` against an
      -- elided `Equity:Gold` is accepted by C++ and rejected here
      -- (fail-closed), and under
      -- `= /^Equity/ and expr 'all(account =~ /Nothing/)'` with
      -- `Budget  1` it is rejected by C++ and accepted here (fail-open).
      -- C++ also gives each posting that a rule generates in a template to
      -- its account (xact.cc:1669-1671), while Phase 9 gives the template's
      -- own postings to none (xact.cc:987-1010). Such a posting belongs to
      -- no transaction (textual_xacts.cc:490, xact.cc:93-100) and so takes
      -- the current date, that of `--now` when it is given
      -- (post.cc:163-174). A real one makes a later real balance
      -- assignment to its account measure the real-only balance
      -- (textual_xacts.cc:398-409), and an assignment dated on or after
      -- the current date sums its amount as well
      -- (textual_xacts.cc:430-439). The oracle keeps only the verdict and
      -- so gives those postings to no account, a departure (wrong rows):
      -- under `= /Expenses:Food/` with `Budget  1` and `Other  -1`, after
      -- a template `~ Monthly` of `Expenses:Food  $100` against an elided
      -- `Assets:Cash` and a later `(Budget)  $10`, `Budget  = $0`
      -- against an elided `Equity` posts a zero in C++, which leaves
      -- `$10` in `Budget`, and `$-10` here, which leaves `$10` in
      -- `Equity`; with the assignment dated after the current date, C++
      -- posts `$-100` for it, which leaves `$-90` in `Budget` and `$100`
      -- in `Equity`. The refusals of `applyAutos` on a completion that C++
      -- splits or posts at zero hold in a template as well
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

/-- `tag("K") == "V"` exactly, with one space on each side of `==`,
    double quotes, and `K` and `V` runs of `tagEqChar`: the predicate
    of test/regress/842.test, which the engine reads, as a test of the
    value of a tag, only within the bounds of `tagEqScan`. -/
private def tagEqForm (predS : String) : Option (String × String) :=
  if predS.startsWith "tag(\"" then
    match (predS.drop 5).toString.splitOn "\") == \"" with
    | [k, rest] =>
        if rest.endsWith "\"" then
          let v := String.ofList rest.toList.dropLast
          if tagEqWord k && tagEqWord v then some (k, v) else none
        else none
    | _ => none
  else none

/-- Whether `s` calls `tag(`, `meta(` or `data(`, written where no ASCII
    letter, digit or `_` precedes it, so that `has_tag(` does not. -/
private def callsMetaFn (s : String) : Bool :=
  let calls := ["tag(", "meta(", "data("].map String.toList
  let rec go (afterWord : Bool) : List Char → Bool
    | [] => false
    | c :: rest =>
        (!afterWord && calls.any (·.isPrefixOf (c :: rest)))
          || go (c.isAlphanum || c == '_') rest
  go false s.toList

/-- An account name of words of `tagEqChar` joined by single spaces and
    colons. -/
private def tagEqAccount (acct : String) : Bool :=
  (acct.splitOn ":").all fun part => (part.splitOn " ").all tagEqWord

/-- A line that `tagEqScan` admits in the rule `tag("K") == "V"`: a
    virtual posting `(A)`, `A` a `tagEqAccount` whose last part is not
    `Unknown`, with an integer multiplier and nothing after it. The
    bound on `Unknown` is precautionary: C++ moves a posting generated
    for an account whose last part is `Unknown` to the account that an
    `account` block's `payee` line maps the payee to
    (xact.cc:1641-1656), and no directive lies within the bounds. -/
private def tagEqTemplate (body : String) : Bool :=
  match splitField body with
  | (acct, some amt) =>
      let inner := String.ofList (acct.toList.drop 1).dropLast
      let ds := if amt.startsWith "-" then (amt.drop 1).toString else amt
      acct.startsWith "(" && acct.endsWith ")" && tagEqAccount inner
        && (inner.splitOn ":").getLast? != some "Unknown"
        && !ds.isEmpty && ds.toList.all Char.isDigit
  | _ => false

/-- A transaction header that `tagEqScan` admits: a date `YYYY/MM/DD`
    that C++ accepts, a year from 1400 to 9999 and a day of its month,
    and a payee of words of `tagEqChar` joined by single spaces. -/
private def tagEqHeader (t : String) : Bool :=
  let num := fun (s : String) (w : Nat) =>
    if s.length == w && s.toList.all Char.isDigit then s.toNat? else none
  match t.splitOn " " with
  | date :: payee =>
      payee.all tagEqWord &&
        match date.splitOn "/" with
        | [y, m, d] =>
            match num y 4, num m 2, num d 2 with
            | some y, some m, some d =>
                let leap := y % 4 == 0 && (y % 100 != 0 || y % 400 == 0)
                let days := if m == 2 then (if leap then 29 else 28)
                  else if m == 4 || m == 6 || m == 9 || m == 11 then 30
                  else 31
                1400 ≤ y && y ≤ 9999 && 1 ≤ m && m ≤ 12 && 1 ≤ d && d ≤ days
            | _, _, _ => false
        | _ => false
  | [] => false

/-- A posting amount that `tagEqScan` admits: ASCII digits with an
    optional fraction after `.`, written after `$`, `$-` or `-$`, or
    with an optional `-` before them and a space and a commodity of
    uppercase ASCII letters after them. -/
private def tagEqAmount (s : String) : Bool :=
  let digits := fun (t : String) => !t.isEmpty && t.toList.all Char.isDigit
  let num := fun (t : String) =>
    match t.splitOn "." with
    | [i] => digits i
    | [i, f] => digits i && digits f
    | _ => false
  let unsign := fun (t : String) =>
    if t.startsWith "-" then (t.drop 1).toString else t
  if s.startsWith "$" then num (unsign (s.drop 1).toString)
  else if s.startsWith "-$" then num (s.drop 2).toString
  else match (unsign s).splitOn " " with
    | [q, c] => num q && !c.isEmpty && c.toList.all Char.isUpper
    | _ => false

/-- A posting line, without its indentation, that `tagEqScan` admits: a
    `tagEqAccount`, alone or followed by a `tagEqAmount` after two spaces
    or a tab, whose first word is not `assert`, `check` or `expr`, which
    begin a line that C++ evaluates (textual_xacts.cc:1107-1125). -/
private def tagEqPosting (body : String) : Bool :=
  let w := String.ofList (body.toList.takeWhile fun c => c != ' ' && c != '\t')
  !["assert", "check", "expr"].contains w &&
    match splitField body with
    | (acct, none) => tagEqAccount acct
    | (acct, some amt) => tagEqAccount acct && tagEqAmount amt

/-- The text after `;` of a note line that `tagEqScan` admits: words of
    `tagEqChar` and blanks, which C++ reads as neither a tag nor a date
    (metadata.cc:146-147, item.cc:86-88), or `Name: value` (`tagEqLine`)
    with a name other than `Value`, which C++ parses as an expression
    (post.cc:1064-1078). -/
private def tagEqNote (txt : String) : Bool :=
  match tagEqLine txt with
  | some none => txt.toList.all fun c => tagEqChar c || c == ' ' || c == '\t'
  | some (some (nm, _)) => nm.toLower != "value"
  | none => false

/-- What an indented line continues as `tagEqScan` follows the
    journal: no block, the rule `tag("K") == "V"`, or a transaction. -/
private inductive TagEqBlock where
  | closed | rule | xact

/-- The bounds within which the engine reads the predicate of
    test/regress/842.test, `= tag("K") == "V"` (`tagEqForm`). C++ lexes
    `tag`, `meta` and `data` alike as a metadata test and reads
    `tag(K) == V` as `tag(/K/) == "V"`, a name pattern that ignores case
    and a value compared as a string (query.cc:262-276, 412-460,
    628-643). The whole journal is checked before a line is read. The
    result is `none` when no line holds the rule and no line falls
    under (R1), and the line of the rule when the journal lies within
    the bounds; any other journal is refused, fail-closed, as an
    out-of-scope `tag()` predicate.

    - (R1) A line outside a `comment` or `test` block that begins with
      `=`, other than the rule, and that calls `tag(`, `meta(` or
      `data(` (`callsMetaFn`) is refused, whether the rule is present
      or not. The test is on the whole line as C++ reads it
      (textual.cc:167-232), before the predicate is split and past any
      carriage return, so that no quoting, `expr`, negation,
      parenthesis, conjunction or carriage return escapes it:
      `= /Expenses/ and not tag("Category") == "food"` is refused, and
      so is `= /Expenses/<CR> and tag("Category") == "food"`, which C++
      reads whole and the engine only up to the carriage return.
      `has_tag(` passes (regress/872, 2268, 1182_3, 1894_1), and the
      spellings in which no parenthesis directly follows the name, such
      as `tag ("Category") == "food"`, `tag Category==food` and
      `%Category==food`, keep their reading, as does
      `%("Category") == "food"`, in which no name precedes the
      parenthesis.
    - (R2) When the rule is present, every line that C++ reads must be
      blank, a comment (a line that begins with one of `;#%*|`, or a
      `comment` or `test` block), the rule followed by its template
      lines (`tagEqTemplate`), or a transaction after the rule: a
      header (`tagEqHeader`) followed by postings (`tagEqPosting`) and
      note lines (`tagEqNote`), with no `uuid:` and no carriage return
      within a line; and no file may be spliced into the journal
      (`spliced`). Any other journal is refused. C++ was measured to
      read each kind below otherwise, as its shape shows; any other
      spelling outside the admitted forms, such as a date written with
      `-`, punctuation in a payee or an account, a thousands separator
      or a commodity in lowercase, is refused because the bounds admit
      only the forms whose reading was measured:
      - another line that begins with `=`: rules read each other's
        notes, which C++ formats, places and orders otherwise
        (xact.cc:1497-1502, 1658-1664; journal.cc:655-667), so that
        after `= /Groc/` with `(Budget:X)  1` and `; Category: dining`
        C++ tags the generated posting, not the matched one;
      - a line of the rule other than a virtual posting with an integer
        multiplier, a note included: C++ rejects the multiplier `0.5`
        under `--decimal-comma` (amount.cc:1732-1734), which the engine
        reads;
      - a directive: `apply tag Category: food` tags each transaction in
        C++ (textual_xacts.cc:1167-1187) and none here, and
        `account-rewrite budget:food  Budget:Other` moves the generated
        postings in C++ alone (textual_directives.cc:791-804,
        mask.cc:365-367);
      - an included file: the scan reads the text that `splice` in
        Driver.lean makes, in which a block can continue into the first
        line of an included file or past its last, while C++ reads each
        file with a reader of its own (textual_directives.cc:428-431)
        and rejects an indented line that continues no block of its file
        (textual.cc:284-290): after the template line
        `(Budget:Food)  -1`, `include t.inc`, where t.inc holds
        `    (Budget:Other)  1`, gives the rule a second template line
        here and is rejected by C++;
      - a transaction before the rule, which the rule does not test and
        `tagEqGuard` does not check: there, `Assets:Cash` elided beside
        `Expenses:A  $5`, `Expenses:B  $-5` and `Expenses:C  0 EUR` makes
        C++ reject the journal (xact.cc:1012-1015), which the engine
        reads;
      - a header with an auxiliary date, a state, a code or a note, or
        with a date that C++ rejects: `2024/01/01 Shop ; Category: food`
        leaves the note in the payee in C++ (textual_xacts.cc:1038-1066),
        while the engine keeps it as the transaction's note, and C++
        alone rejects `2024/02/30 Shop`;
      - a posting with a note, a cost, a lot, a balance assertion or
        assignment, or an expression, or a line that begins with
        `assert`, `check` or `expr`: `expr ACategory = "dining"` under a
        posting tags it in C++ (textual_xacts.cc:1107-1125,
        item.cc:280-292), and the test then reads that name in place of
        `Category`, while the engine drops the line;
        `Assets:A  10 AAA @ $1.005` gives an elided posting the cost's
        precision in C++ (xact.cc:195-238), which a posting generated
        from it keeps there and not here; and `Budget:Food  = $0` reads
        the generated postings, which C++ dates by the matched posting
        and rounds at display precision (xact.cc:1603-1610;
        textual_xacts.cc:430-438, 842-866);
      - a note line other than words or `Name: value`, or one that names
        `Value`: `; [2024/05/01]` dates the posting in C++
        (item.cc:86-104), which here keeps the date of its transaction,
        and C++ alone rejects `; Value: x--`;
      - a line that holds `uuid:`: with `; UUID: abc` under a posting of
        each of two transactions, C++ keeps both, since the tag is not
        the transaction's (journal.cc:593-596), and `uuidOf` drops the
        second;
      - an indented line that continues no block: after a blank line,
        C++ rejects `    ; Category: food` (textual.cc:284-290), which
        the engine adds to the notes of the transaction above;
      - a carriage return within a line: C++ reads the value `food<CR>x`
        in `; Category: food<CR>x` (textual.cc:167-232), and the engine,
        which ends the line at the carriage return, `food`.

    In a journal within these bounds the rule tests every transaction,
    and `tagEqGuard` then checks each of them. -/
private def tagEqScan (input : String) (spliced : Bool) :
    Except String (Option Nat) := do
  let mut inComment := false
  let mut block := TagEqBlock.closed
  let mut rule : Option Nat := none
  let mut fault : Option (Nat × String) := none
  let mut n : Nat := 0
  for line0 in input.splitOn "\n" do
    n := n + 1
    let line := (line0.splitOn "\r").headD ""
    let t := line.trimAsciiEnd.toString
    if inComment then
      if closesCommentBlock t then inComment := false
      continue
    let mut why : Option String :=
      if line0.toList.dropLast.contains '\r' then
        some "a carriage return within a line"
      else if containsUUID t then some "a line that holds `uuid:`"
      else none
    if t.toList.all fun c => c == ' ' || c == '\t' then
      block := .closed
    else if line.front == ' ' || line.front == '\t' then
      let body := trimS t
      match block with
      | .closed =>
          why := why <|> some "an indented line that continues no block"
      | .rule =>
          unless tagEqTemplate body do
            why := why <|> some "a line of the rule other than `(A)  N`"
      | .xact =>
          if body.startsWith ";" then
            unless tagEqNote (body.drop 1).toString do
              why := why <|>
                some "a note other than words or `Name: value`, or `Value`"
          else
            unless tagEqPosting body do
              why := why <|> some "a posting other than `A  AMOUNT` or `A`"
    else
      block := .closed
      if line.front == '=' then
        let predS := trimS (t.drop 1).toString
        if t.startsWith "= " && (tagEqForm predS).isSome then
          if rule.isNone then
            rule := some n
            block := .rule
          else why := why <|> some "another automated transaction"
        else if callsMetaFn (readLineTrim line0) then
          let raw := (readLineTrim line0).map fun c =>
            if c == '\r' then ' ' else c
          let shown := (trimS (raw.drop 1).toString).take 40
          err n s!"out-of-scope tag() predicate '{shown}'"
        else why := why <|> some "another automated transaction"
      else if isCommentStart line.front then pure ()
      else if opensCommentBlock t then inComment := true
      else if line.front.isDigit then
        block := .xact
        unless tagEqHeader t do
          why := why <|> some "a header other than `YYYY/MM/DD PAYEE`"
        if rule.isNone then
          why := why <|> some "a transaction before the rule"
      else why := why <|> some "a directive"
    if let some w := why then
      fault := fault <|> some (n, w)
  match rule, fault with
  | some ln, some (m, w) =>
      err ln s!"out-of-scope tag() predicate: {w} at line {m}"
  | some ln, none =>
      if spliced then err ln "out-of-scope tag() predicate: an included file"
      else pure (some ln)
  | none, _ => pure none

/-- Run the engine over (include-spliced) journal text; `spliced` is
    set when `splice` in Driver.lean spliced a file into it, which the
    bounds of `tagEqScan` and `St.yearUnsure` read. -/
def run (input0 : String) (dcDefault : Bool := false)
    (nowSecs : Option ℚ := none) (recAliases : Bool := false)
    (dfmtS : Option String := none) (spliced : Bool := false) :
    Except String Result := do
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
  -- the bounds of `tag("K") == "V"` (regress/842), before any line
  let tagEqRule ← tagEqScan input spliced
  let mut st : St := { amt := { dcDefault }, nowSecs, dfmt
                       recursiveAliases := recAliases
                       yearUnsure := spliced
                       inputDateFormat := dfmtS.isSome }
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
          -- account_directive_body reads a comment line as the account's
          -- metadata tags (textual_directives.cc:631-635), and any other
          -- line as a keyword that ends at the first space or tab
          -- (next_element) and the argument after it, which every
          -- keyword but `default` requires (textual_directives.cc:637-641,
          -- regress/coverage-account-subdir-no-arg): a bare `alias`,
          -- `payee` or `account` line in a block is rejected
          let tagLine := body.startsWith ";" || body.startsWith "#"
            || body.startsWith "*" || body.startsWith "|"
          let kw := String.ofList
            (body.toList.takeWhile fun c => c != ' ' && c != '\t')
          let arg := trimS (body.drop kw.length).toString
          if !tagLine && arg.isEmpty && kw != "default" then
            err n s!"account directive '{kw}' requires an argument"
          if kw == "account" then
            let nm := (unquote arg).getD arg
            -- a nested block registers its name under the enclosing
            -- account, which the nested dispatch passes as the parent
            -- (textual_directives.cc:651-655, regress/877), unless an
            -- alias fires (textual_directives.cc:611, journal.cc:169-177):
            -- with `alias X=Y`, `account X` nested in `account A` names
            -- `Y`
            let full := (expandAliases st nm).getD
              (if name.isEmpty then nm else name ++ ":" ++ nm)
            st := { st with pending := .acctBlock ((ind, full) :: frames) }
            continue
          st := { st with pending := .acctBlock frames }
          if kw == "alias" then
            let al := (unquote arg).getD arg
            -- account_alias_directive rejects an alias equal to the
            -- block's resolved name (textual_directives.cc:701-714,
            -- regress/coverage-wave11-account-alias-self); under
            -- `apply account Top`, `account Foo` with `alias Top:Foo` is
            -- illegal
            if al == name then err n s!"illegal alias {al}={name}"
            st := { st with aliases := (al, name) :: st.aliases }
          else if kw == "payee" then
            match compileRegex arg with
            | .ok rx =>
                st := { st with payeeAccountRules :=
                  st.payeeAccountRules ++ [(rx, name)] }
            | .error _ => pure ()
          else if kw == "default" then
            -- account_default_directive ignores any argument
            -- (textual_directives.cc:649-650)
            st := { st with bucket := some name }
          -- tag lines and the note, value, assert, check, eval and expr
          -- subdirectives: labels, report-time only, or verified by the
          -- C++ side (953)
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
        -- the entry keeps the account as `clock_in_directive` names it,
        -- under the `apply account` stack, and its payee; the aliases
        -- and the payee rules apply when it is checked out
        -- (`timelogAccount`). time_log_t::clock_in rejects a second
        -- check-in to an account already checked in, comparing the
        -- accounts so named (timelog.cc:201-207,
        -- regress/coverage-timelog-double-checkin): with `alias Foo=Bar`,
        -- `i ... Foo` and then `i ... Bar` are two entries
        let acct := applyPrefixes st acct
        if st.clockIn.any fun (_, a, _) => a == acct then
          err n "cannot double check-in to the same account"
        st := { st with
          clockIn := st.clockIn ++ [(secs, acct, payee?.getD "")] }
      else if t.startsWith "o " || t.startsWith "O " then
        let body := (splitNote (trimS (t.drop 2).toString)).1
        let dateS := String.ofList (body.toList.takeWhile (· != ' '))
        let rest1 := trimS (body.drop dateS.length).toString
        let timeS := String.ofList (rest1.toList.takeWhile (· != ' '))
        let rest2 := trimS (rest1.drop timeS.length).toString
        let (named, desc?) := splitField rest2
        let stop ← parseDateTime n dateS timeS
        -- clock_out_from_timelog: a single open entry closes no
        -- matter what account the o line names (723); with several,
        -- the entry is the one whose check-in named the account that
        -- `clock_out_directive` names under the `apply account` stack,
        -- before any alias expands (textual_directives.cc:139,
        -- timelog.cc:112-122, regress/coverage-timelog-nomatch): with
        -- `alias Foo=Bar` and entries for `Foo` and `Baz` open,
        -- `o ... Bar` matches neither, and under `apply account Top`
        -- with entries for `Foo` and `Baz`, `o ... Top:Foo` names
        -- `Top:Top:Foo` and matches neither
        let pick? :=
          match st.clockIn with
          | [only] => some only
          | _ =>
              if named.isEmpty then none
              else st.clockIn.find? fun (_, a, _) => a == applyPrefixes st named
        match pick? with
        | none => err n "timeclock check-out without check-in"
        | some (start, name, pay) =>
            let acct := timelogAccount st name
              (if pay.isEmpty then desc?.getD "" else pay)
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
                            clockIn := st.clockIn.filter fun (s0, a, _) =>
                              !(s0 == start && a == name) }
            for (a, dq) in flows do
              st := bumpBal st a.name a.commodity dq
              st := bumpStat st a.name a.commodity false dq
              -- POST_IS_TIMELOG (timelog.cc:67, 86): it never makes an
              -- account's balance real-only, yet stays in the real-only
              -- balance, from which C++ leaves out only virtual postings
              -- (textual_xacts.cc:398-409, 435)
              st := { st with datedEvents :=
                ((a.name, a.commodity), ((stop / 86400 : ℚ).floor : Int),
                 dq, .timelog) :: st.datedEvents }
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
        -- test/regress/842.test: `tag("K") == "V"` is read within the
        -- bounds of `tagEqScan`, which approved this line
        let branches ← match tagEqForm predS with
          | some kv =>
              if tagEqRule == some n then pure [{ tagEq := some kv }]
              else err n "out-of-scope tag() predicate"
          | none => compilePred st n predS
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
        -- named as `account` names it, below
        let nm := trimS (t.drop "@account ".length).toString
        let nm := resolveAccount st ((unquote nm).getD nm)
        st := { st with pending := .acctBlock [(0, nm)] }
      else if t.startsWith "@commodity " || t.startsWith "!commodity " then
        let nm := trimS (t.drop "@commodity ".length).toString
        st := { st with pending := .commBlock ((unquote nm).getD nm) }
      else if t.startsWith "account " || t.startsWith "account\t" then
        -- account_directive registers the block's name under the
        -- `apply account` stack, unless an alias fires
        -- (textual_directives.cc:602-611, journal.cc:169-177), so that
        -- its `alias`, `payee` and `default` subdirectives name the
        -- resolved account: under `apply account Top`, `account Suspense`
        -- with `default` makes `Top:Suspense` the bucket
        let nm := trimS (t.drop "account ".length).toString
        let nm := resolveAccount st ((unquote nm).getD nm)
        st := { st with pending := .acctBlock [(0, nm)] }
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
      for (start, name, pay) in st.clockIn do
        if start ≤ nowS then
          -- time_log_t::close checks each one out through the same
          -- create_timelog_xact, bucket posting included
          -- (timelog.cc:173-195, 84-91)
          let acct := timelogAccount st name pay
          let flows := match st.bucket with
            | some b => [(Account.mk acct "s", nowS - start),
                         (Account.mk b "s", start - nowS)]
            | none => [(Account.mk acct "s", nowS - start)]
          st := { st with gens := flows :: st.gens }
          for (a, dq) in flows do
            st := bumpBal st a.name a.commodity dq
            st := bumpStat st a.name a.commodity false dq
      st := { st with clockIn := [] }
  | none => pure ()
  pure ⟨st.gens.reverse, st.rewrites, st.equivs, st.precisions,
        st.amt.styles, st.flowStats, st.signStats, st.lotFanout,
        priceTable st.priceLog, st.primary.reverse, st.priceIssues.reverse⟩

/-- Apply report-time account rewrites (`account-rewrite`,
    `capture`) to a name. -/
def applyRewrites (rw : List (Rx × String)) (name : String) : String :=
  match rw.find? fun (rx, _) => regexSearch rx name with
  | some (_, to_) => to_
  | none => name

end Journal

end Ledger
