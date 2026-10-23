import Ledger.Oracle
import Ledger.Register
import Ledger.Journal

/-!
# The oracle driver (differential-comparison side)

Reads `.dat` files, splices `include`s (so the pure engine never does
IO), runs the journal engine (`Journal.lean`), constructs the L2 term,
with one generator per effective transaction and the journal as their
tensor, and evaluates the executable oracle `netFlow` at every touched
account, printing one canonical line per nonzero balance:

    COMMODITY|AMOUNT|ACCOUNT

sorted; report-time account rewrites are applied (merging flows) at
output, and canonical-second time totals are displayed in the largest
fitting unit (h/m/s) rounded to two decimals, as the C++ ledger does
but for the minute, a departure that `displayAmount` records.

Run through the **interpreter** (never a `lean_exe`):

    lake env lean --run Ledger/Driver.lean [FLAGS] FILE ...

Flags apply to the next file only (mirroring a test's own flags) and
reset after it: `--decimal-comma`, `--recursive-aliases`,
`--now DATE`, `--input-date-format FORMAT`, and the opt-in output
flags `--gross` and `--exchange COMM`. `--gross` adds `>> dr ROW` and
`>> cr ROW` lines of gross totals, summed posting by posting, after
the net rows, or, in place of those lines, the single line
`?? gross lot-annotated-completion` (`grossRows`). `--exchange COMM`
adds, after the net and gross lines, `>> value ROW` lines that give
the holdings of each account valued in `COMM` at the prices in effect
at 00:00 of the `--now` date, each computed through `netValueAt`, or,
in place of those lines, the single line `?? exchange REASON`, with
the commodity concerned after the reason where there is one, for a
file that the oracle cannot value as C++ does (`exchangeRows`). Each
file's block starts with `== PATH`; a rejection prints `!! ERROR ...`
for that file (fail-closed, never silent), and a `??` line is never a
rejection. A file given without an output flag prints exactly the
default protocol that the README describes.
-/

namespace Ledger

namespace Driver

open Parse Journal GenSpec

/-- Render an exact rational canonically: minimal decimal when the
    denominator divides a power of ten, else `p/q`. -/
def ratToCanonical (q : ℚ) : String :=
  let den := q.den
  let rec findK : Nat → Option Nat
    | 0 => none
    | k + 1 =>
        match findK k with
        | some r => some r
        | none => if (10 ^ k) % den == 0 then some k else none
  match findK 31 with
  | none => s!"{q.num}/{q.den}"
  | some k =>
      let scale := (10 ^ k) / den
      let m := q.num.natAbs * scale
      let intPart := m / 10 ^ k
      let frac := m % 10 ^ k
      let sign := if q.num < 0 then "-" else ""
      if k == 0 || frac == 0 then
        s!"{sign}{intPart}"
      else
        let fracStr := toString frac
        let padded := String.ofList (List.replicate (k - fracStr.length) '0') ++ fracStr
        let trimmed := String.ofList (padded.toList.reverse.dropWhile (· == '0')).reverse
        s!"{sign}{intPart}.{trimmed}"

abbrev roundAt := Parse.roundAt

/-- Display a base-commodity total in the largest fitting equivalent
    unit (built-in time chain and `C` directives alike), rounded at
    the unit's learned precision (default 2 for converted units, the
    learned/0 precision for the base itself) as C++ prints an amount,
    through `stream_out_mpq` (src/amount.cc:2055 and 208-245 at
    76b9dc2b2, `cppRoundAt`): a total exactly half-way between two
    displayable values rounds as its binary expansion decides, so that
    at precision 1 a total of `0.35` shows as `0.3` and one of `0.45`
    as `0.5`. The default of 2 departs from C++ for the minute, which C++
    shows at the one place that its built-in conversion `1.0m` gives it
    (session.cc:80 at 76b9dc2b2) unless an amount raises that precision
    (amount.cc:1847-1848): after `Assets:Time  100s` against an elided
    posting, `bal --flat` shows `1.7m` for `Assets:Time` on both C++
    binaries, where this shows 1.67 (wrong rows). No journal of the
    corpus shows it. -/
def displayAmount (equivs : List (String × ℚ × String))
    (precisions : List (String × Nat)) (comm : String) (q : ℚ) :
    String × ℚ :=
  let a := if q < 0 then -q else q
  -- candidate units resolving to this base, largest factor first
  let units := (equivs.filterMap fun (u, _, _) =>
      let (f, base) := Journal.resolveEquiv equivs u
      if base == comm then some (u, f) else none)
    |>.toArray.qsort (fun x y => x.2 > y.2) |>.toList
  match units.find? fun (_, f) => a ≥ f && f != 1 with
  | some (u, f) =>
      let p := max ((precisions.lookup u).getD 2) 2
      (u, cppRoundAt p (q / f))
  | none =>
      if comm == "" then (comm, q)   -- bare amounts: full precision
      else
        let p := (precisions.lookup comm).getD 0
        (comm, cppRoundAt p q)

/-- The generator specification of an evaluated journal. -/
def specFor (arr : Array (List (Account × ℚ))) : GenSpec where
  Gen := Fin arr.size
  dom i := ((arr[i].filter fun p => p.2 < 0).map Prod.fst : List Account)
  cod i := ((arr[i].filter fun p => p.2 > 0).map Prod.fst : List Account)

/-- The journal as a single L2 term: the tensor of its generators. -/
def journalTerm (S : GenSpec) : (ts : List S.Gen) → Σ A B : Object, S.FreeMor A B
  | [] => ⟨0, 0, .id 0⟩
  | t :: rest =>
      let ⟨A, B, f⟩ := journalTerm S rest
      ⟨S.dom t + A, S.cod t + B, .tensor (.gen t) f⟩

/-- Per-generator flows, read off the engine's output. -/
def flowsFor (arr : Array (List (Account × ℚ)))
    (i : Fin arr.size) (a : Account) : ℚ :=
  (arr[i].filter fun p => p.1 = a).foldl (fun s p => s + p.2) 0

/-- The row `COMMODITY|AMOUNT|ACCOUNT` of a total `v` at the account
    `a`, displayed as C++ displays it, or none when the total shows as
    zero. `stat` counts the flows that the total sums and the inferred
    ones among them. The total is displayed by `displayAmount`, except
    that a lone inferred amount renders at its recovered precision when
    the commodity has none, or when it would otherwise show as zero
    (BIGINT_COST_PREC, issues #1692/#1773); sums drop the widening.
    C++ asks whether it shows as zero with `in_place_roundto`, which
    rounds half away from zero as `roundAt` does, not as the row is
    printed (src/amount.cc:2041-2053, 1072-1100): `A 1 FOO @ $0.005`
    against an elided `B`, with `$` shown at two places, is not
    widened, prints as zero, and leaves no row. -/
def displayRow (res : Journal.Result) (stat : Nat × Nat) (a : Account)
    (v : ℚ) : Option String :=
  let (dispComm, dispQ) := displayAmount res.equivs res.precisions a.commodity v
  let (tot, inf) := stat
  let prec := (res.precisions.lookup a.commodity).getD 0
  if tot == 1 && inf == 1 && dispComm == a.commodity
      && a.commodity != ""
      && (prec == 0 || roundAt prec v == 0) then
    -- at the widened precision C++ tests the exact value
    -- (`amount_t::is_zero`, src/amount.cc:1388-1408 at 76b9dc2b2)
    if v = 0 then none
    else some s!"{a.commodity}|{ratToCanonical v}|{a.name}"
  else
  -- a total that shows as zero leaves no row: C++ displays an account
  -- only when its display total is nonzero
  -- (`format_accounts::mark_accounts`, src/output.cc:325 at
  -- 76b9dc2b2), and prints an amount of a balance only when it is
  -- nonzero (`print_amount_from_balance`, src/balance.cc:561), each
  -- time by `amount_t::is_zero`, which reads the amount as it prints
  -- at its display precision, the rounding `cppRoundAt` reproduces
  -- (src/amount.cc:1374-1430). For a value that `exchangeRows` computes,
  -- C++ reads the exact value instead where the precision that the value
  -- carries is not above the display precision (src/amount.cc:1407-1408),
  -- and the reason `rounds-to-zero` stands wherever the two can differ
  if dispQ = 0 then none
  else some s!"{dispComm}|{ratToCanonical dispQ}|{a.name}"

/-- The gross rows of an evaluated journal `res`, whose generators are
    `arr`, whose term is `term`, and whose flows touch the accounts
    `accts`, for the opt-in flag `--gross`. For each account after the
    report-time rewrites, the line `>> dr ROW` carries the total of the
    positive amounts posted to it, and the line `>> cr ROW` the total of
    the magnitudes of its negative amounts, each summed posting by
    posting over the term (`GenSpec.debitTotal` and
    `GenSpec.creditTotal`), as the debit and credit columns of C++
    `bal --dc --flat` are (src/report.h:751-754 at 76b9dc2b2;
    test/baseline/opt-dc.test). The debit total less the credit total
    is the account's net flow (`GenSpec.gross_foot`). Each total is
    displayed by `displayRow`, as a net row is, with the counts that
    `Journal.Result.signStats` keeps for its own column: under `--dc`
    C++ adds into a column only the amounts of that column's sign, the
    other postings bringing a zero that the sum ignores
    (src/value.cc:572-575 and 591-594, src/balance.cc:122-123), so
    that a lone inferred amount in one column keeps its recovered
    precision there (BIGINT_COST_PREC in src/amount.cc;
    test/regress/1692.test) while a net row that sums it with other
    postings drops it: after `A  2 X @ 0.2 Y` against an elided `B`,
    and `B  1 Y` against an elided `Equity`, `bal --dc --flat` shows
    `1 Y` for the balance of `B` and `0.4 Y` in its credit column, and
    so do the net row and the `>> cr` line of `B` here. The lines are
    sorted. Where the engine's postings can give an account columns
    other than those of C++, or show them otherwise, because C++
    completes an elided posting with a posting for each annotated key
    of a commodity (src/xact.cc:180-248, and Phase 7 at 824-863, at
    76b9dc2b2; test/regress/1638.test, 1998.test and
    coverage-wave7-xact-edge.test), `Journal.Result.lotFanout` holds,
    and the single line `?? gross lot-annotated-completion` replaces
    the gross lines. The docstring of that field records the two
    conditions that set it and, each with a journal, where it holds in
    excess and where it is missed. -/
def grossRows (res : Journal.Result) (arr : Array (List (Account × ℚ)))
    {A B : Object} (term : (specFor arr).FreeMor A B)
    (accts : List Account) : List String :=
  if res.lotFanout then ["?? gross lot-annotated-completion"] else
  let posts : Fin arr.size → List (Account × ℚ) := fun i => arr[i]
  -- per-account debit and credit totals, then report-time rewrites
  -- (merging)
  let totals : List (Account × ℚ × ℚ) := accts.foldl (init := []) fun acc a0 =>
    let a := Account.mk (Journal.applyRewrites res.rewrites a0.name) a0.commodity
    let d := GenSpec.debitTotal posts term a0
    let c := GenSpec.creditTotal posts term a0
    match acc.lookup a with
    | some _ => acc.map fun (a', d', c') =>
        if a' = a then (a', d' + d, c' + c) else (a', d', c')
    | none => (a, d, c) :: acc
  let colStat := fun (name comm : String) (debit : Bool) =>
    res.signStats.foldl (init := ((0 : Nat), (0 : Nat)))
      fun (t, i) ((a, c, dr), t', i') =>
        if Journal.applyRewrites res.rewrites a == name && c == comm
            && dr == debit then
          (t + t', i + i')
        else (t, i)
  let rows := totals.flatMap fun (a, d, c) =>
    ((displayRow res (colStat a.name a.commodity true) a d).map
        (">> dr " ++ ·)).toList
      ++ ((displayRow res (colStat a.name a.commodity false) a c).map
        (">> cr " ++ ·)).toList
  (rows.toArray.qsort (· < ·)).toList

/-- The edges of the price graph that C++ searches at an instant, from
    the points `pts` of the dated price table that are not after that
    instant (`Journal.pricesAt`): one edge for each two commodities that
    a point links, in either direction, which carries the latest of
    those points. C++ keeps the prices of two commodities on one edge of
    an undirected graph (history.cc:114-120, 351-369) and reads, of an
    edge, the latest price that is not after the instant
    (`recent_edge_weight`, history.cc:257-263). The table holds one
    point at each instant on each two commodities
    (`Journal.Result.prices`), so that the latest is unique. A point that
    would link a commodity to itself, which C++ never records
    (pool.cc:639-642, history.cc:353), is left out. -/
def priceEdges (pts : List Journal.PricePoint) : List Journal.PricePoint :=
  pts.foldl (init := []) fun acc pt =>
    if pt.comm == pt.price.comm then acc else
    let same := fun (e : Journal.PricePoint) =>
      (e.comm == pt.comm && e.price.comm == pt.price.comm)
        || (e.comm == pt.price.comm && e.price.comm == pt.comm)
    match acc.find? same with
    | some e =>
        if pt.secs > e.secs then acc.map fun r => if same r then pt else r
        else acc
    | none => acc ++ [pt]

/-- The commodities that an edge of `es` links to `c`, each with that
    edge. -/
def priceNeighbors (es : List Journal.PricePoint) (c : String) :
    List (String × Journal.PricePoint) :=
  es.filterMap fun e =>
    if e.comm == c then some (e.price.comm, e)
    else if e.price.comm == c then some (e.comm, e)
    else none

/-- The tree of a breadth-first search of the edges `es` from the
    commodity `s`: each commodity that it reaches, other than `s`, with
    the commodity and the edge by which it is first reached. Each round
    reaches the commodities one edge further, so that as many rounds as
    there are edges, and one more, reach every commodity that a path of
    `es` links to `s`. -/
def priceTree (es : List Journal.PricePoint) (s : String) :
    List (String × String × Journal.PricePoint) := Id.run do
  let mut seen : List String := [s]
  let mut frontier : List String := [s]
  let mut tree : List (String × String × Journal.PricePoint) := []
  for _ in [0:es.length + 1] do
    let mut next : List String := []
    for u in frontier do
      for (v, e) in priceNeighbors es u do
        if !seen.contains v then
          seen := v :: seen
          next := next ++ [v]
          tree := tree ++ [(v, u, e)]
    frontier := next
  return tree

/-- The hops of the path from `s` to `t` in the tree `tree` that
    `priceTree` grows from `s`, each as the commodity that it leaves, the
    commodity that it reaches and its edge, in order from `s`, or none
    when the tree does not reach `t`. -/
def treePath (tree : List (String × String × Journal.PricePoint))
    (s t : String) : Option (List (String × String × Journal.PricePoint)) :=
  let rec back : Nat → String → List (String × String × Journal.PricePoint) →
      Option (List (String × String × Journal.PricePoint))
    | 0, _, _ => none
    | n + 1, v, acc =>
        if v == s then some acc
        else match tree.find? (·.1 == v) with
          | some (_, u, e) => back n u ((u, v, e) :: acc)
          | none => none
  back (tree.length + 1) t []

/-- What the price graph of the edges `es` gives the commodity `c` in
    the target `t` (`chainVerdict`). -/
inductive ChainVerdict where
  /-- the rate `q` of the only chain, through the commodities `via` -/
  | rate (q : ℚ) (via : List String)
  /-- no chain links `c` to `t` -/
  | noPath
  /-- more than one chain links `c` to `t` -/
  | alternative
  /-- the only chain crosses a price of zero against its direction -/
  | zeroInverse

/-- The rate at which the edges `es` value one unit of the commodity
    `c` in the target `t`, when a single chain of edges links the two.
    The oracle admits only a commodity whose path of prices to the target
    is unique, since it does not model the choice that C++ makes among
    several paths, the one whose oldest price is the most recent
    (Dijkstra's search with `f_max`, history.cc:538-544). A breadth-first
    search finds a path (`priceTree`, `treePath`), and the path is the
    only one exactly when every hop of it is a bridge, an edge without
    which its two commodities are no longer linked. The rate is the
    product of the rates of the hops, each the price of its edge or,
    against the direction of the edge, the price inverted, as C++
    multiplies the prices along the path that `find_price` finds
    (history.cc:503-617) with exact rationals, rounding none
    (amount.cc:705-751, 909-917). A single chain is the path that C++'s
    search returns, whatever the ages of its prices. -/
def chainVerdict (es : List Journal.PricePoint) (c t : String) : ChainVerdict :=
  match treePath (priceTree es c) c t with
  | none => .noPath
  | some hops =>
      let bridge := fun (u v : String) (e : Journal.PricePoint) =>
        !((priceTree (es.filter (· != e)) u).any (·.1 == v))
      if hops.any (fun (u, v, e) => !bridge u v e) then .alternative
      else
        let step := fun (r : ℚ) (hop : String × String × Journal.PricePoint) =>
          let (u, _, e) := hop
          if e.comm == u then some (r * e.price.q)
          else if e.price.q == 0 then none
          else some (r / e.price.q)
        match hops.foldlM step 1 with
        | some q => .rate q (hops.map (·.2.1))
        | none => .zeroInverse

/-- The value rows of an evaluated journal `res`, whose generators are
    `arr`, whose term is `term`, whose flows touch the accounts `accts`,
    whose net totals after the report-time rewrites are `merged`, and
    whose net rows `displayRow` shows with the counts `stats`, for the
    opt-in flag `--exchange target` with the Driver's `--now` at the
    instant `terminus` (00:00 of its date), as C++ `bal --flat -X target`
    values each account (src/report.h:904-909 and 1035-1039, the
    `value_date` of src/report.cc:2157 being the terminus, at 76b9dc2b2;
    `value_t::exchange_commodities`, src/value.cc:1924-1937, and
    `balance_t::value`, src/balance.cc:291-305). Each commodity other
    than the target is valued at the rate of its single chain of prices
    at the terminus (`priceEdges`, `chainVerdict`), the target at 1, and
    for each account after the rewrites the line `>> value ROW` carries
    the sum, over the account names that the rewrites merge into it, of
    `netValueAt`, its flows times those rates, displayed in the target by
    `displayRow` as a net row is. C++ shows a value in the target itself,
    never in a larger unit (`report_t::display_value`,
    src/report.cc:815-821), as `displayRow` shows a total in every target
    but the second, which it shows in the largest unit that fits, a case
    that the reason `time-unit` refuses, whose comment also gives the
    precisions at which C++ shows the minute and the hour. The list of
    accounts `accts` has no duplicates and holds every account at which a
    flow is nonzero, so that each sum is Ellerman's value of the account's
    property vector at a price vector (p. 498), as
    `netValueAt_eq_valueHom` in `Ledger/Market.lean` proves. A lone
    inferred amount in the target keeps its recovered precision where
    nothing else is added to it, as C++ copies an amount of the target
    unvalued (amount.cc:1279-1280) and drops the mark of that precision
    from a sum (amount.cc:634-642). The lines are sorted.

    Where the oracle cannot value a file as C++ does, the single line
    `?? exchange REASON`, with the commodity concerned after the reason
    where there is one, replaces the value lines, the first reason that
    applies in the order of the branches below, each with the witness
    that forced it. Such a file is not rejected: its net rows still
    print.

    No reason covers the known departures that the value rows inherit
    from what they are computed from, and a value row can then depart
    from C++ (fail-open): those of the net totals and of their display;
    those of the dated price table where no issue stands in place of a
    point; and those of the display precisions that the reader learns,
    but for the precision that a price directive grants, which the
    reason `price-precision` refuses. The comments of the reader and of
    `displayRow` record departures of the first kind, the docstrings of
    `Journal.Result.priceIssues`, `priceDirective`, `costPrice` and
    `exchangePoints` departures of the second, and the docstring of
    `costPrice` lists departures of the third, but these records are
    incomplete: some known departures of the net totals, among them
    shapes that C++ rejects and the reader accepts, are recorded beside
    no rule, so that a value row can depart from C++ where no comment
    says so. A departure of the precision learned for the target reaches
    every value row, which shows at that precision, so that a value row
    can depart where the net rows agree: after
    `Assets:Cash  $10` against an elided `Equity`, an automated
    transaction `= /^NEVER/` with `(Budget)  $0.49`,
    `P 2024/01/01 X $2` and `Assets:A  1.25 X` against an elided
    `Equity`, `bal -X $` shows $2.50 for `Assets:A` on both C++
    binaries, where the value row is $2, since the template teaches C++
    alone two places for `$`. Among the departures of the dated price
    table, `exchangePoints` records a price that the precision of an
    amount expression rounds otherwise than C++: after
    `Assets:Cash  $1.00` against an elided posting,
    `Assets:A  (1.5 * 1.5 EUR)` against `Assets:B  $-10.00` and then
    `Assets:C  1000000000 EUR` against an elided posting, `bal -X $`
    shows $4444444444.40 for `Assets:C` on both C++ binaries, where the
    value row is $4444444444.44. Four more shapes depart in the same
    way. A journal line that sets a report option other than `--now`,
    such as `--amount 7` or `--exchange EUR`, or a session option that
    takes effect only once C++ has read the journal, changes what C++
    shows while the reader ignores it (the in-file option branch of
    Journal `handleDirective`), so that the value rows depart, with the
    net rows or alone: `--download` makes C++ value through prices that
    it fetches (src/global.cc:270-279, src/report.cc:193-205), and with
    `--getquote` naming a script that quotes AAPL at $7, `bal -X $`
    shows $70 for `10 AAPL` priced at $2 on both C++ binaries, where the
    value row is $20. A price read in a style other than the one in
    which C++ reads it is a point at a value that C++ does not hold
    (`Journal.Result.priceIssues`): after `D $1,000.00` and a posting of
    `$1,5`, `P 2024/01/04 Z $1,500` makes `bal -X $` show $1,500.00 for
    a later `1 Z` on both C++ binaries, where the value row is $1.5. An
    assignment in an expression that C++ evaluates as it reads the
    journal, as in `check market(a, d, t) = 7` or in the note
    `; Foo:: market(a, d, t) = 7`, defines a function that its valuation
    calls, which `Journal.Result.valueExprAll` does not record (its
    docstring lists the places): `bal -X $` then shows 7 for every
    account on both C++ binaries. And an expression that C++ evaluates as
    it reads the journal and that values a commodity at the terminus
    leaves in the cache of prices that C++ keeps for that commodity
    (`commodity_t::find_price`, src/commodity.cc:171-224) a price that the
    report reads in place of the graph, though a later price of another
    commodity on its chain changes it, since a new price clears the cache
    of the commodity that it prices alone (src/commodity.cc:85): after
    `P 2024/01/01 AAPL 100 EUR`, `P 2024/01/01 EUR $1`,
    `Assets:Broker  3 AAPL` against an elided `Equity` with the line
    `check market(1 AAPL, [2026/08/26], "$") > 0`, and then
    `P 2024/01/03 EUR $2`, `bal -X $ --now 2026/08/26` shows $300 for
    `Assets:Broker` on both C++ binaries, where the value row is $600. -/
def exchangeRows (res : Journal.Result) (arr : Array (List (Account × ℚ)))
    {A B : Object} (term : (specFor arr).FreeMor A B) (accts : List Account)
    (merged : List (Account × ℚ)) (stats : String → String → Nat × Nat)
    (target : String) (terminus : Option Int) : List String :=
  let issue := fun (kind : String) =>
    (res.priceIssues.find? (·.1 == kind)).map (·.2)
  -- the commodities other than the target in which an account holds a
  -- nonzero total, and those of a nonzero flow
  let held := (((merged.filter fun (a, v) => v != 0 && a.commodity != target).map
    (·.1.commodity)).eraseDups.toArray.qsort (· < ·)).toList
  let flowComms := ((res.gens.flatten.filter fun (a, q) =>
    q != 0 && a.commodity != target).map (·.1.commodity)).eraseDups
  -- the graph at the terminus; without a terminus there is none, and the
  -- branch no-terminus refuses first
  let edges := match terminus with
    | some t => priceEdges (Journal.pricesAt res.prices t)
    | none => []
  let verdicts := held.map fun c => (c, chainVerdict edges c target)
  let firstWith := fun (pick : ChainVerdict → Bool) =>
    (verdicts.find? (pick ·.2)).map (·.1)
  let refusal : Option (String × String) :=
    -- no-terminus: the rows value at 00:00 of the Driver's `--now`
    -- date, as C++ sets its terminus from `--now` (report.h:1059-1074
    -- at 76b9dc2b2; `Journal.pricesAt`). Without it the oracle has no
    -- terminus, a limitation of the oracle's input rather than a rule
    -- of C++, which then values at the current time (times.h:127-128).
    -- A journal line that sets `--now`, spelled `--now`, `--now_` or
    -- `--now-`, moves C++'s terminus to the date that it gives, at the
    -- time of day that it gives where it has one (report.h:1065, 1070 at
    -- 76b9dc2b2; `Journal.Result.nowInFile`), and the issue
    -- `undated-price` stands for a price directive without a date, which
    -- C++ dates at its current time (pool.cc:568-572) and which the
    -- reader records only without the Driver's `--now` or after such a
    -- line (`Journal.Result.nowInFile`), so that the branch refuses all
    -- three, an oracle limitation each time
    (if terminus.isNone || res.nowInFile || (issue "undated-price").isSome then
      some ("no-terminus", "") else none)
    -- price-expr: a price directive whose price is an expression, which
    -- C++ evaluates and, for a result in several commodities, makes the
    -- value expression of the commodity (pool.cc:589-615,
    -- test/regress/1101.test), is not evaluated here and leaves no
    -- point in the table; an oracle limitation
    <|> (issue "price-expr").map ("price-expr", ·)
    -- unread-price: a price directive, a cost or a lot price that the
    -- reader does not read as C++ reads it, whose point the table lacks
    -- (`Journal.Result.priceIssues`; the reader cascade of
    -- times.cc:229-327, commodity.cc:331-349 and amount.cc:1617-1659 for
    -- a directive), and, without a commodity, a journal line
    -- `--decimal_comma` read where the reader does not read amounts with
    -- a decimal comma already, after which C++ reads every amount with a
    -- decimal comma (session.h:233, amount.cc:1714-1715), so that the
    -- points and the display precisions that the reader takes from the
    -- amounts read after it can depart
    -- (`Journal.St.decimalCommaUnapplied`); an oracle limitation
    <|> (issue "unread-price").map ("unread-price", ·)
    -- exchange-order: the costs of an implicit exchange whose sides the
    -- order of the two entries of the balance decides (xact.cc:386-393;
    -- `Journal.Result.priceIssues`), whose points the table lacks; an
    -- oracle limitation
    <|> (issue "exchange-order").map ("exchange-order", ·)
    -- value-expression: C++ values an amount through a value
    -- expression before it consults the price graph: that of the
    -- annotation of its commodity (annotate.cc:417-418, for a `((EXPR))`
    -- lot), that of the commodity (commodity.cc:163-207), and the one
    -- that `extend_post` gives a posting from its `Value` tag, its
    -- account or the journal (post.cc:1040-1075); bare where an
    -- expression can value any commodity (`Journal.Result.valueExprAll`),
    -- and otherwise for the first commodity of
    -- `Journal.Result.valueExprComms` in which a flow is nonzero
    <|> (if res.valueExprAll then some ("value-expression", "") else none)
    <|> (res.valueExprComms.find? flowComms.contains).map ("value-expression", ·)
    -- posting-date: a cost, or a lot price recorded beside one, whose
    -- price C++ records at the date that a note of its posting or of its
    -- transaction, or an `apply tag`, gives (xact.cc:688-690, which
    -- exchanges at `post->date()`): `2024/01/05 Buy` with
    -- `Assets:Broker  1 AAPL @ $101  ; [2024/01/07]` records its price at
    -- 2024/01/07. The table holds the point only where the reader reads
    -- that date (`Journal.Result.priceIssues`), and the issue does not
    -- say which, so that the branch refuses in excess where it does
    <|> (issue "posting-date").map ("posting-date", ·)
    -- fixated-lot: an amount whose lot price is fixated is valued at
    -- that price, bypassing the price graph (annotate.cc:381-418,
    -- ANNOTATION_PRICE_FIXATED at 403-405; amount.cc:1269-1273;
    -- test/baseline/feat-fixated-prices.test), for the first commodity of
    -- `Journal.Result.fixatedLotComms` in which a flow is nonzero. That
    -- record is conservative for a posting of which C++ fixates the
    -- amount alone or the completion in the commodity of the cost alone
    -- (`Journal.PostSpec.fixatedMark`), so that the commodity named can be
    -- one that C++ values through the graph: for `10 AAPL @ 5 EUR {=$2}`
    -- against an elided posting, with `P 2024/02/01 AAPL $170`, the branch
    -- names AAPL, which `bal -X $` values at $1700 on both C++ binaries
    <|> (res.fixatedLotComms.find? flowComms.contains).map ("fixated-lot", ·)
    -- equivalence: a `C` directive declares an equivalence that C++
    -- applies while it parses (`price_conversion_directive`,
    -- textual_directives.cc:174-191) and through which it records a
    -- price that the table does not hold, valuing a commodity without a
    -- price through its larger units (amount.cc:1301-1320); not
    -- modelled, so any `C` directive refuses, the most recent one named
    <|> (if res.equivs != ({} : Journal.St).equivs then
          some ("equivalence", (res.equivs.head?.map (·.1)).getD "") else none)
    -- commodity-alias: an `alias` subdirective of a `commodity` block
    -- after a point that names the alias or the block's commodity
    -- (`Journal.Result.aliasPrices`), where C++ can retire a commodity
    -- and move its prices to the block's commodity (pool.cc:150-173,
    -- history.cc:336-349): after `P 2024/01/01 E $1`,
    -- `P 2024/01/01 EUR $3` and then `commodity EUR` with `alias E`,
    -- `bal -X $` values a later `10 EUR` at $10 on both C++ binaries,
    -- where the table's point of `EUR` gives $30; an oracle limitation,
    -- refused in excess where C++ retires nothing
    <|> (if res.aliasPrices then some ("commodity-alias", "") else none)
    -- price-precision: C++ grants the commodity of the price of a price
    -- directive the decimals of the price where the commodity's
    -- precision is 0 and it is neither known nor locked
    -- (pool.cc:628-634), a commodity becoming known at the places that
    -- the docstring of `Journal.St.knownComms` lists, among them the
    -- source of a price directive (pool.cc:645-647), while the reader
    -- grants a precision only to a commodity for which none is recorded
    -- (the `P` arm of Journal `handleDirective`). Where the two grants
    -- from the precision recorded before the directive differ
    -- (`Journal.Result.pricePrecisionComms`, the first commodity named),
    -- the target can show at another precision, and a cost can record
    -- its price at another one, since Phase 6 rounds the price at the
    -- precision of the commodity of the cost (Journal `costPrice`): after
    -- `Assets:Cash  $1000` against an elided posting, `3 AAPL @ $170`
    -- against `Assets:Cash` and then `P 2024/02/01 AAPL $170.25`,
    -- `bal -X $` shows $510.75 for the AAPL account on both C++
    -- binaries, where the value row would be $511. A difference in any
    -- commodity refuses, in excess where it shows in no value row; a
    -- precision that the reader learns otherwise than C++ before the
    -- directive is among the inherited departures of the docstring above
    <|> (res.pricePrecisionComms.head?).map ("price-precision", ·)
    -- null-commodity: C++ never values an amount without a commodity
    -- (`has_commodity()`, amount.cc:1263) and shows it unvalued, so
    -- that a target without one, or an account that holds a nonzero
    -- total without one, has no value row in the target: after
    -- `Assets:A  10` against an elided posting, `bal -X $` shows `10`
    -- for `Assets:A` on both C++ binaries
    <|> (if target == "" || held.contains "" then some ("null-commodity", "")
          else none)
    -- percent: C++ multiplies by an amount in `%` as by a hundredth of
    -- it (amount.cc:727-740), when it values an amount in `%`
    -- (amount.cc:1324-1325) and when a chain multiplies by a price in
    -- `%` (history.cc:589-596), so that the target `%`, a holding in it
    -- and a chain through it are refused
    <|> (if target == "%" || held.contains "%"
            || verdicts.any (fun (_, v) => match v with
                | .rate _ via => via.contains "%" | _ => false) then
          some ("percent", "") else none)
    -- time-unit: a target that the built-in chain of time units names,
    -- the second, the minute or the hour (session.cc:80-81 at
    -- 76b9dc2b2), which, any `C` directive being refused above, are the
    -- units of `Journal.Result.equivs`. C++ shows a value in the target
    -- itself, since under `-X` it does not convert what it shows to a
    -- larger unit (`report_t::display_value`, src/report.cc:815-821),
    -- while `displayRow` shows a total in `s` in the largest unit that
    -- fits it: after `Assets:Time  2h` against an elided posting,
    -- `bal -X s` shows `7200s` for `Assets:Time` on both C++ binaries,
    -- where the value row would show 2h. And C++ shows a value in the
    -- minute or the hour at the precision that the built-in conversions
    -- `1.0m` and `1.00h` give those units, one place and two, unless an
    -- amount raises it (amount.cc:1847-1848), while `displayRow` shows a
    -- total in either at the precision recorded for it, which is zero
    -- where no amount sets one: with `P 2024/01/01 h 7 EUR` and
    -- `Assets:Euro  10 EUR` against an elided posting, `bal -X h` shows
    -- `1.43h` for `Assets:Euro` on both C++ binaries, where the value row
    -- would show 1h
    <|> (if res.equivs.any (fun (u, _, b) => u == target || b == target) then
          some ("time-unit", "") else none)
    -- no-price-path: no chain of prices at the terminus links the
    -- commodity to the target, and C++ shows the holding unvalued,
    -- unless it values the commodity through a larger unit
    -- (amount.cc:1301-1320) or the account's total is one annotated
    -- amount, which it values at its lot price where that price is in
    -- the target (`report_t::fn_market`, src/report.cc:953-970 at
    -- 76b9dc2b2): after `Assets:A  10 AAPL {$150}` against an elided
    -- posting, with no price, `bal -X $` shows $1500 for `Assets:A` on
    -- both C++ binaries; an oracle limitation stated as a refusal
    <|> (firstWith (· matches .noPath)).map ("no-price-path", ·)
    -- alternative-price-path: more than one chain links the commodity to
    -- the target, a cycle or a diamond, and C++ takes the one whose
    -- oldest price is the most recent (Dijkstra's search with `f_max`,
    -- history.cc:538-544), which the oracle does not model, admitting a
    -- single chain alone (`chainVerdict`); an oracle limitation
    <|> (firstWith (· matches .alternative)).map ("alternative-price-path", ·)
    -- zero-inverse-price: the chain crosses a price of zero against its
    -- direction, which C++ leaves at zero where it has no inverse
    -- (`in_place_invert`, amount.cc:909-917): with
    -- `P 2024/01/01 EUR $0.00` and `Assets:Checking  $100` against an
    -- elided posting, `bal -X EUR` shows nothing on both C++ binaries.
    -- test/regress/1085.test crosses the same price in its direction,
    -- under `-X '$'`, which the chain multiplies by zero
    <|> (firstWith (· matches .zeroInverse)).map ("zero-inverse-price", ·)
  match refusal with
  | some (reason, comm) =>
      [s!"?? exchange {reason}" ++ (if comm.isEmpty then "" else s!" {comm}")]
  | none =>
    let p : Commodity → ℚ := fun c =>
      if c == target then 1
      else match verdicts.lookup c with
        | some (.rate q _) => q
        | _ => 0
    let names := (accts.map (·.name)).eraseDups
    -- each account after the rewrites with its value and its row
    let values := (names.map (Journal.applyRewrites res.rewrites ·)).eraseDups.map
      fun n =>
        let v := ((names.filter (Journal.applyRewrites res.rewrites · == n)).map
          fun m => netValueAt (flowsFor arr) accts p m term).sum
        -- the counts of the target's net row, where nothing else adds to
        -- it: nothing does where every holding in another commodity is
        -- valued at exactly zero, since C++ adds no amount of exactly zero
        -- to a balance (`balance_t::operator+=`, src/balance.cc:122-123
        -- at 76b9dc2b2), so that a lone inferred amount in the target keeps
        -- its mark beside a holding priced at zero
        let others := merged.any fun (a, w) =>
          a.name == n && a.commodity != target && w * p a.commodity != 0
        let stat := if others then (0, 0) else stats n target
        (v, displayRow res stat (Account.mk n target) v)
    -- rounds-to-zero: an account whose value is not zero but shows as
    -- zero in the target. C++ shows an account by `amount_t::is_zero`,
    -- which reads a value exactly where the precision that the value
    -- carries is not above that of the target, and as it prints
    -- otherwise (src/amount.cc:1374-1429 at 76b9dc2b2), a precision that
    -- adds those of the prices and of the amount (amount.cc:705-751,
    -- 909-917) and that the oracle does not model; and under `--flat` it
    -- shows the total of a parent account none of whose children it
    -- shows (`format_accounts::mark_accounts`, src/output.cc:312-330).
    -- After `Assets:Cash  $10.00` against an elided posting,
    -- `P 2024/01/01 $ 150 JPY` and `Assets:Yen  0.5 JPY` against an
    -- elided posting, `bal -X $` shows `$0.00` for `Assets:Yen` on both
    -- C++ binaries; and after `P 2024/01/01 AAPL $155.00`,
    -- `Expenses:Food:Groceries  $50.00` and `Expenses:Auto:Gas  $35.00`,
    -- each against an elided `Assets:Cash`, `bal --flat -X AAPL` shows
    -- `AAPL1` for `Expenses` on both, where no value row would show
    -- either account; an oracle limitation, refused in excess where C++
    -- hides the account as well
    if values.any (fun (v, row) => v != 0 && row.isNone) then
      ["?? exchange rounds-to-zero"]
    else
      ((values.filterMap (·.2.map (">> value " ++ ·))).toArray.qsort (· < ·)).toList

/-- Balances of an (include-spliced) journal text; `spliced` says that
    a file was spliced into it (`splice`), `gross` adds the gross rows
    (`grossRows`) after the net rows, and `exchange` the value rows in
    that commodity (`exchangeRows`) after them. -/
def balancesOf (decimalComma : Bool) (nowSecs : Option ℚ)
    (recAliases : Bool) (dfmt : Option String) (input : String)
    (spliced : Bool := false) (gross : Bool := false)
    (exchange : Option String := none) :
    Except String (List String) := do
  let res ← Journal.run input decimalComma nowSecs recAliases dfmt spliced
  let arr := res.gens.toArray
  let S := specFor arr
  let ⟨_, _, term⟩ := journalTerm S (List.finRange arr.size)
  let accts := (res.gens.flatten.map Prod.fst).eraseDups
  -- per-account oracle totals, then report-time rewrites (merging)
  let totals := accts.filterMap fun a =>
    let v := netFlow (flowsFor arr) term a
    -- a total of exactly zero leaves no row, dropped here before the
    -- merge as `displayRow` would drop it after: C++ forms the total of
    -- an account by addition alone (`post_t::add_to_value` and
    -- `account_t::total`, src/post.cc:977-1014 and
    -- src/account.cc:884-900 at 76b9dc2b2), and an addition to a
    -- balance ignores an amount of exactly zero and never erases an
    -- entry (`balance_t::operator+=`, src/balance.cc:118-133), so a
    -- commodity whose amounts net to exactly zero has no entry or an
    -- entry of value zero, and neither prints a row (`displayRow`)
    if v = 0 then none
    else some (Account.mk (Journal.applyRewrites res.rewrites a.name) a.commodity, v)
  let merged : List (Account × ℚ) := totals.foldl (init := []) fun acc (a, v) =>
    match acc.lookup a with
    | some _ => acc.map fun (a', v') => if a' = a then (a', v' + v) else (a', v')
    | none => (a, v) :: acc
  let statFor := fun (name comm : String) =>
    res.flowStats.foldl (init := ((0 : Nat), (0 : Nat)))
      fun (t, i) ((a, c), t', i') =>
        if Journal.applyRewrites res.rewrites a == name && c == comm then
          (t + t', i + i')
        else (t, i)
  let rows := merged.filterMap fun (a, v) =>
    displayRow res (statFor a.name a.commodity) a v
  let styleRows := res.styles.filterMap fun (c, dc) =>
    if dc then some (if c == "" then "%% dc *" else s!"%% dc {c}") else none
  let net := styleRows ++ (rows.toArray.qsort (· < ·)).toList
  let grossLines := if gross then grossRows res arr term accts else []
  let valueLines := match exchange with
    | some c => exchangeRows res arr term accts merged statFor c (nowSecs.map (·.floor))
    | none => []
  pure (net ++ grossLines ++ valueLines)

end Driver

end Ledger

namespace Ledger.Driver

/-- The deepest include nesting C++ allows: `include_directive`
    counts the files that include the current one and refuses an
    include in a file that more than this many files include
    (textual_directives.cc:343-347, "Maximum include depth exceeded
    (100)"). -/
def maxIncludeDepth : Nat := 100

/-- The components of the path of a file after C++ `resolve_path`
    (utils.cc:833-852), which ends in `lexically_normal`: an empty or
    `.` component drops, a name followed by `..` drops with it, and a
    trailing separator survives as an empty last component, which
    matches no directory entry. A `..` with no name before it drops
    directly under the root of an absolute path, and stays at the head
    of a relative one (`rel`). -/
def normalComps (comps : List String) (rel : Bool := false) : List String :=
  let rec go : List String → List String → Bool → List String × Bool
    | [], acc, trail => (acc, trail)
    | c :: rest, acc, _ =>
        if c == "" || c == "." then go rest acc rest.isEmpty
        else if c == ".." then
          if rel && (acc.isEmpty || acc.head? == some "..") then
            go rest (c :: acc) false
          else go rest acc.tail (rest.isEmpty && !acc.isEmpty)
        else go rest (c :: acc) false
  let (acc, trail) := go comps [] false
  if trail && !acc.isEmpty then ("" :: acc).reverse else acc.reverse

/-- The name that C++ gives the file named `p` on the command line,
    `context.pathname` from `open_for_reading` (context.h:144-146,
    157): `p` normalized by `resolve_path`, which keeps the leading
    `..` of a relative path, and a relative result joined to the
    current directory with no second normalization. Every file that an
    include reaches is named in normal form (`globPaths`), so when `p`
    begins with `..` no match equals the top file, and a glob in it
    includes it once more, as in C++ (textual_directives.cc:395-399). -/
def topPathname (p : String) : IO System.FilePath := do
  if p.startsWith "/" then
    return ⟨"/" ++ "/".intercalate (normalComps (p.splitOn "/"))⟩
  let cwd := (← IO.currentDir).toString
  let cwd := if cwd.endsWith "/" then cwd else cwd ++ "/"
  return ⟨cwd ++ "/".intercalate (normalComps (p.splitOn "/") (rel := true))⟩

/-- C++ `expand_path` (utils.cc:789-831) for a path that begins with
    `~`: a bare `~` or `~/...` takes its prefix from `HOME`. The
    password database that C++ consults for `~user/...`, or when
    `HOME` is unset, is out of the oracle's reach, so such a path, like
    one under a `HOME` that is not absolute, stays unresolved, and the
    include is rejected as not found. -/
def expandHome (p : String) : IO (Option String) := do
  let rest := (p.drop 1).toString
  if !(rest.isEmpty || rest.startsWith "/") then return none
  match ← IO.getEnv "HOME" with
  | some home =>
      if !home.startsWith "/" then return none
      if rest.isEmpty then return some home
      let home := if home.endsWith "/" then home else home ++ "/"
      return some (home ++ (rest.drop 1).toString)
  | none => return none

end Ledger.Driver

/-- Resolve an include pattern as C++ `include_directive` does
    (textual_directives.cc:365-392). A pattern that begins with `/` is
    taken as written, one that begins with `~` is expanded by
    `expandHome`, and any other is joined to `dir`, the directory of
    the including file. The path is normalized (`normalComps`) and
    matched from the root one component at a time against the entries
    of each directory, as `expand_glob_path` does
    (textual_directives.cc:270-305), and case-sensitively, so that a
    name that differs only in case does not match on a
    case-insensitive filesystem either (regress/1660). Only a
    directory continues the walk, and only a regular file is a final
    match (textual_directives.cc:298-302).

    The matching of a single component departs from C++ in four known
    ways, which this function keeps. C++ compiles every component,
    glob or not, with `mask_t::assign_glob` (textual_directives.cc:280,
    mask.cc:379-423), which leaves `^` and `$` as anchors of the
    regular expression, takes a backslash as escaping the character
    after it, and copies a bracket expression into the regular
    expression as written, through its closing `]` (mask.cc:390-395).
    Here a component without `*`, `?` or `[` must equal an entry
    exactly; `^` and `$` in a glob component match themselves; `splice`
    has already dropped every backslash; and every character inside a
    bracket is translated as it is outside one, so that `[^a]` is a
    class of `^` and `a` rather than a negated class, and `x[*].dat`
    does not match a file named `x*.dat`, nor `x[?].dat` one named
    `x?.dat`. C++
    also takes a pattern that begins with a backslash as written,
    against the working directory of the process
    (textual_directives.cc:370), where here it is joined to `dir`. For
    a name that holds `^` or `$`, a pattern that holds a backslash, or
    a bracket expression that holds `^`, `*` or `?`, the oracle and C++
    can therefore read different files. -/
partial def globPaths (dir : System.FilePath) (pat : String) :
    IO (List System.FilePath) := do
  let full? ←
    if pat.startsWith "/" then pure (some pat)
    else if pat.startsWith "~" then Ledger.Driver.expandHome pat
    else pure (some (dir.toString ++ "/" ++ pat))
  let some full := full? | return []
  let isGlob := fun (c : String) =>
    c.toList.any fun ch => ch == '*' || ch == '?' || ch == '['
  let globRx := fun (c : String) => String.join (c.toList.map fun ch =>
    if ch == '*' then "[^/]*"
    else if ch == '?' then "."
    else if ch == '.' then "\\."
    else if ch == '[' then "["
    else if ch == ']' then "]"
    else if ch == '+' || ch == '(' || ch == ')' || ch == '|'
         || ch == '^' || ch == '$' then String.ofList ['\\', ch]
    else String.ofList [ch])
  let isFile := fun (p : System.FilePath) => do
    match ← p.metadata.toBaseIO with
    | .ok m => pure (m.type == .file)
    | .error _ => pure false
  -- `base` is a directory path without a trailing separator; "" is the root
  let rec walk (base : String) : List String → IO (List System.FilePath)
    | [] => pure []
    | c :: rest => do
        let baseP : System.FilePath := ⟨if base.isEmpty then "/" else base⟩
        if !(← baseP.isDir) then return []
        let names := (← baseP.readDir).map (·.fileName)
        let matched : Array String :=
          if !(isGlob c) then (if names.contains c then #[c] else #[])
          else match Ledger.Parse.compileRegex ("^" ++ globRx c ++ "$") with
            | .error _ => #[]
            | .ok rx =>
                (names.filter (Ledger.Parse.regexSearch rx ·)).qsort (· < ·)
        let mut acc : List System.FilePath := []
        for nm in matched do
          let p := base ++ "/" ++ nm
          if rest.isEmpty then
            if ← isFile ⟨p⟩ then acc := acc ++ [⟨p⟩]
          else if ← System.FilePath.isDir ⟨p⟩ then
            acc := acc ++ (← walk p rest)
        pure acc
  walk "" (Ledger.Driver.normalComps (full.splitOn "/"))

/-- Splice the `include` lines of `text`, the contents of the file
    `self` in the directory `dir`, which `parents` files include;
    `self` is the name that C++ gives the file (`topPathname`,
    `globPaths`). A line is an include as C++ reads one, once its
    trailing whitespace, Unicode whitespace included, is dropped as
    `read_line` drops it (Journal `readLineTrim`): it begins in column
    0, since an indented line belongs to the construct above it
    (textual.cc:284-290); its directive word, the first word after at
    most two `@` or `!` prefixes (Journal `directiveWord`), is
    `include`; and it is not inside a `comment` or `test` block, whose
    lines C++ never executes (Journal `opensCommentBlock` and
    `closesCommentBlock`). A leading byte order mark is dropped as C++
    drops it from the first line of every file (textual.cc:191-195).
    Balanced quotes around the argument are stripped
    (textual_directives.cc:353-359), and backslashes in it are dropped,
    which departs from C++ (see `globPaths`); `globPaths` resolves it,
    and a match equal to `self` is skipped, as `include_directive`
    skips the including file (textual_directives.cc:395-399). An
    include with no argument, or with no other match, is left for the
    engine as a bare `include` or as `include ARG`, which the engine
    rejects by name (Journal `handleDirective`). An include in a file
    that more than `maxIncludeDepth` files include throws the C++
    error. The result is the spliced text, and whether a file was
    spliced into it, which the engine's bounds of `tag("K") == "V"`
    read (Journal `run`). -/
partial def splice (self : System.FilePath) (dir : System.FilePath)
    (text : String) (parents : Nat) : IO (String × Bool) := do
  let text := if text.startsWith "\uFEFF" then (text.drop 1).toString else text
  let mut out : Array String := #[]
  let mut inComment := false
  let mut spliced := false
  for line in text.splitOn "\n" do
    -- the engine's view of the line (Journal `run`)
    let t := ((line.splitOn "\r").headD "").trimAsciiEnd.toString
    if inComment then
      if Ledger.Journal.closesCommentBlock t then inComment := false
      out := out.push line
      continue
    if Ledger.Journal.opensCommentBlock t then
      inComment := true
      out := out.push line
      continue
    -- the directive word and argument of the line as C++ `read_line`
    -- leaves it (textual.cc:198-226)
    let (word, arg) := Ledger.Journal.directiveWord (Ledger.Journal.readLineTrim t)
    if word != "include" then
      out := out.push line
      continue
    if arg.isEmpty then
      -- C++ refuses it before `include_directive` runs, so before
      -- the depth test (textual_directives.cc:1034-1038)
      out := out.push "include"
      continue
    if parents > Ledger.Driver.maxIncludeDepth then
      throw (IO.userError
        s!"maximum include depth exceeded ({Ledger.Driver.maxIncludeDepth})")
    let pat :=
      if arg.length ≥ 2 && ((arg.startsWith "\"" && arg.endsWith "\"")
          || (arg.startsWith "'" && arg.endsWith "'")) then
        String.ofList ((arg.drop 1).toString.toList.dropLast)
      else arg
    let pat := String.ofList (pat.toList.filter (· != '\\'))
    let paths ← globPaths dir pat
    let paths := paths.filter fun p => p.toString != self.toString
    if paths.isEmpty then
      out := out.push s!"include {arg}"
    else
      for path in paths do
        -- C++ opens a matched file without checking the stream
        -- (context.h:144-157), so it reads a file that it finds but
        -- cannot open as empty; here the read error propagates, and
        -- `main` rejects the journal on one `!! ERROR` line instead
        let sub ← IO.FS.readFile path
        out := out.push (← splice path (path.parent.getD dir) sub (parents + 1)).1
        spliced := true
  -- C++ reads a block no further than the end of its own file
  -- (textual_directives.cc:941-949), so the block that an included
  -- file leaves open closes where that file ends
  if inComment && parents > 0 then out := out.push "end comment"
  return (String.intercalate "\n" out.toList, spliced)

namespace Ledger.Driver

/-- The text of the file `arg` with its includes spliced, and whether a
    file was spliced into it. -/
def readSpliced (arg : String) : IO (String × Bool) := do
  let txt ← IO.FS.readFile arg
  let self ← topPathname arg
  splice self (self.parent.getD "/") txt 0

end Ledger.Driver

def main (args : List String) : IO Unit := do
  let mut dc := false
  let mut rec_ := false
  let mut now : Option ℚ := none
  let mut nowPending := false
  let mut dfmt : Option String := none
  let mut dfmtPending := false
  let mut gross := false
  let mut exch : Option String := none
  let mut exchPending := false
  -- A flag that takes a value takes the next argument that the tests
  -- before its own pending test do not claim, so that `--exchange --gross
  -- FILE` applies `--gross` and takes FILE as the target, reading no file;
  -- `--input-date-format` and `--now` take their values in the same way.
  -- A caller passes each value right after its flag.
  for arg in args do
    if arg == "--decimal-comma" then
      dc := true
    else if arg == "--recursive-aliases" then
      rec_ := true
    else if arg == "--gross" then
      gross := true
    else if arg == "--exchange" then
      exchPending := true
    else if exchPending then
      exchPending := false
      exch := some arg
    else if arg == "--input-date-format" then
      dfmtPending := true
    else if dfmtPending then
      dfmtPending := false
      dfmt := some arg
    else if arg == "--now" then
      nowPending := true
    else if nowPending then
      nowPending := false
      now := Ledger.Journal.headerDate none arg |>.map fun d =>
        ((d * 86400 : Int) : ℚ)
    else do
      IO.println s!"== {arg}"
      match ← (Ledger.Driver.readSpliced arg).toBaseIO with
      | .error e =>
        -- the text of an IO error can continue on a second line
        -- ("  file: PATH"); the protocol gives a rejection one line
        let lines := ((toString e).splitOn "\n").map (·.trimAscii.toString)
        IO.println s!"!! ERROR {" ".intercalate (lines.filter (!·.isEmpty))}"
      | .ok (text, spliced) =>
        match Ledger.Driver.balancesOf dc now rec_ dfmt text spliced gross exch with
        | .error e => IO.println s!"!! ERROR {e}"
        | .ok rows => for r in rows do IO.println r
      dc := false
      rec_ := false
      now := none
      dfmt := none
      gross := false
      exch := none
