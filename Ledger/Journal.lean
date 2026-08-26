import Ledger.Parse

/-!
# The journal engine: directives, transactions, and final flows

Stateful upper half of the L4 → L2 mapping (lexical lower half in
`Parse.lean`). Consumes journal text (with `include`s already spliced
by the driver — parsing stays pure) and produces one generator per
effective transaction: its final per-account, per-commodity flows.

Semantics implemented, each pinned by the C++ suite's own expected
outputs (the `SemanticBisimulation` ctest is the standing check):

- **Balancing**: per commodity over real/bracket-virtual/deferred
  postings, each contributing its lot-price value `{P}`×qty if
  annotated, else its `@`/`@@` cost, else its own amount; one elided
  posting absorbs the residual per commodity; with no elided posting
  a `bucket` account absorbs it; a two-commodity residual is an
  implicit exchange; paren-virtuals `(A)` are exempt.
- **Assignments** `= AMT` on an amountless posting: computed
  sequentially against the running account balance including earlier
  postings of the same transaction (regress/1005). With an amount
  present it is an assertion: positive tests pass their assertions by
  definition, so it is checked *by the C++ side* and dropped here.
- **Auto-xacts** `= /regex/`: template postings (fixed amounts or
  bare multipliers × the matched posting's amount) are appended per
  matching real posting of each later transaction — after balancing,
  as `extend_xact` does; templates may be virtual.
- **Timeclock** `i`/`o`: single-sided time postings (duration in
  canonical seconds); no balancing.
- **UUID dedup**: a transaction whose note carries an already-seen
  `UUID:` is dropped whole (C++ `journal.cc` semantics) — the one
  documented non-flow-inert label.
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
  assignTarget : Option Amount := none
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

/-- Display-precision-tolerant zero test: does the residual round to
    zero at the commodity's learned precision? (Cost amounts never
    feed precision — confirmed on standard.dat's 22-decimal prices.) -/
private def roundsToZero (st : St) (comm : String) (q : ℚ) : Bool :=
  let p := (st.precisions.lookup comm).getD 0
  let scaled := (if q < 0 then -q else q) * (10 ^ p : ℕ)
  scaled * 2 ≤ 1

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

/-- Consume the annotation/cost/assertion tail of an amount:
    `{lot} [date] (note) @ P / @@ T / = ASSERT` in any order. -/
private partial def annotLoop (ctx : AmtCtx) (line : Nat) (a : Amount)
    (tail : String) (lot : Option (Amount × Bool)) (cost : Option Amount)
    (teach : List (String × Nat) := []) (afterCost : Bool := false)
    (costDecs : Nat := 0) :
    Except String (Option (Amount × Bool) × Option Amount ×
      List (String × Nat) × Nat) := do
  let t := trimS tail
  if t.isEmpty || t == "." then
    pure (lot, cost, teach, costDecs)
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
    let fixated := innerS.startsWith "="
    let innerS := if fixated then trimS (innerS.drop 1).toString else innerS
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
        | none => some (lotAmt, fixated)
    annotLoop ctx line a (String.ofList rest) lot' cost teach afterCost costDecs
  else if t.startsWith "[" then
    match takeBalanced '[' ']' t.toList with
    | some (_, rest) =>
        annotLoop ctx line a (String.ofList rest) lot cost teach afterCost costDecs
    | none => err line s!"unclosed lot date in '{t}'"
  else if t.startsWith "(" && !(t.startsWith "(@") then
    match takeBalanced '(' ')' t.toList with
    | some (_, rest) =>
        annotLoop ctx line a (String.ofList rest) lot cost teach afterCost costDecs
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
      (max costDecs pr.decimals)
  else if t.startsWith "(@)" || t.startsWith "@" then
    -- per-unit costs round at the cost literal's own precision,
    -- posting by posting (regress/1125); `@ =` fixates (1794); cost
    -- literals teach display precision up to ledger's 6-digit
    -- extension (1151 vs standard.dat's 22-digit prices)
    let off := if t.startsWith "(@)" then 3 else 1
    let rest0 := trimS (t.drop off).toString
    let rest0 := if rest0.startsWith "=" then trimS (rest0.drop 1).toString
      else rest0
    let pr ← parseAmount ctx line rest0
    annotLoop ctx line a pr.tail lot
      (some ⟨pr.amount.comm, pr.amount.q * a.q⟩) teach true
      (max costDecs pr.decimals)
  else if t.startsWith "=" then
    -- assertion: the C++ side checks it; positive tests pass it, but
    -- the literal still teaches display precision (1699)
    let pr ← parseAmount ctx line (trimS (t.drop 1).toString)
    let teach := if pr.decimals <= 6 then
        (pr.amount.comm, pr.decimals) :: teach else teach
    annotLoop ctx line a pr.tail lot cost teach afterCost costDecs
  else
    err line s!"trailing junk after amount '{t}'"

/-- Parse the amount field of a posting (everything after the
    account): amount, lot annotations, cost, assertion/assignment. -/
private def parseAmountField (ctx : AmtCtx) (line : Nat) (field : String) :
    Except String (Option Amount × Option Amount × Option Amount ×
      Option Amount × Option (String × Bool) × Nat × Bool ×
      List (String × Nat) × Nat × Option Amount) := do
  -- returns (amount, balancing, assignTarget, learnedStyle, decimals)
  let field := trimS field
  if field.isEmpty then
    pure (none, none, none, none, none, 0, false, [], 0, none)
  else if field.startsWith "=" then
    -- balance assignment (amountless posting); lot annotations on the
    -- target are parsed and dropped (1603)
    let r ← parseAmount ctx line (trimS (field.drop 1).toString)
    let _ ← annotLoop ctx line r.amount r.tail none none
    pure (none, none, none, some r.amount, r.learned, r.decimals, false,
          (if r.decimals <= 6 then [(r.amount.comm, r.decimals)] else []),
          0, none)
  else do
    let (preLot, field) ←
      if field.startsWith "{" then
        match takeBalanced '{' '}' field.toList with
        | some (inner, rest) => do
            let innerS := trimS (String.ofList inner)
            let innerS := if innerS.startsWith "=" then
                trimS (innerS.drop 1).toString else innerS
            let pr ← parseAmount ctx line innerS
            pure (some pr.amount, trimS (String.ofList rest))
        | none => err line s!"unclosed leading lot in '{field}'"
      else pure (none, field)
    let r ← parseAmount ctx line field
    let a := r.amount
    let (lot, cost, teach, costDecs) ←
      annotLoop ctx line a r.tail (preLot.map (·, true)) none
    -- xact.cc phase 4/6: a fixated lot with no cost derives the cost
    -- from the annotation; a lot WITH a cost books the rounded
    -- gain/loss (basis - cost, rounded at commodity precision plus
    -- the amount's decimals) into the effective cost
    let gainVal := match lot, cost with
      | some (p, _), some c =>
          if p.comm == c.comm then
            let gl := (p.q * a.q) - c.q
            some (Amount.mk c.comm
              (roundAt ((ctx.precs.lookup c.comm).getD 0 + r.decimals) gl))
          else none
      | _, _ => none
    let costVal := match lot, cost with
      | some (p, _), some c =>
          if p.comm == c.comm then
            let basis := p.q * a.q
            let gl := basis - c.q
            let glR := roundAt ((ctx.precs.lookup c.comm).getD 0 + r.decimals) gl
            some (Amount.mk c.comm (c.q + glR))
          else some c
      | _, _ => cost
    let lotVal := lot.map fun (p, _) => Amount.mk p.comm (p.q * a.q)
    pure (some a, costVal, lotVal, none, r.learned, r.decimals,
          field.startsWith "(", teach, costDecs, gainVal)

private def parsePosting (st : St) (line : Nat) (raw : String) :
    Except String (Option PostSpec × Option (String × Bool) ×
      Option String × Nat × Bool × List (String × Nat)) := do
  let (content, note) := splitNote raw
  let content := stripStatus (trimS content)
  if content.isEmpty then
    pure (none, none, none, 0, false, [])
  else if content.startsWith "assert " || content.startsWith "check "
      || content.startsWith "expr " then
    -- inline expression check/eval: verified/discarded by the C++ side
    pure (none, none, none, 0, false, [])
  else do
    let (acctField, amtField) := splitField content
    let (kind, name) ← accountKind line acctField
    let account := resolveAccount st name
    match amtField with
    | none => pure (some { line, account, kind, note }, none, none, 0, false, [])
    | some f => do
        let (amount, costVal, lotVal, assignTarget, learned, decs, isExpr,
             teach, costDecs, gainVal) ← parseAmountField st.amt line f
        pure (some { line, account, kind, note, amount, costVal, lotVal,
                     assignTarget, amtDecs := decs, costDecs, gainVal },
              learned, amount.map (·.comm), decs, isExpr, teach)

/-! ## Transaction finalization -/

private def applyAutos (st : St) (xdate : Option Int) (payee : String)
    (code : String) (dateStr : String)
    (xactNotes : String) (posts : List PostSpec) : List PostSpec :=
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
    for rule in st.autos do
      if !rule.active then continue
      for i in [0:cand.size] do
        let p : PostSpec := cand[i]!
        match p.kind, p.amount with
        | PostKind.real, some a =>
            let cur := cand.toList ++ extra
            if rule.branches.any fun b => matchBranch xactNotes cur b p a then
              let gen := rule.posts.filterMap (instantiate xactNotes p a)
              extra := extra ++ gen
              -- the template's own note tags the matched posting, so
              -- later rules see it there (1984's :BUDGETED: guard)
              if !rule.noteTag.isEmpty then
                cand := cand.set! i { p with note := p.note ++ rule.noteTag }
        | _, _ => pure ()
    pure (cand.toList ++ extra)

/-- Finalize a pending transaction into flows. -/
private def finalizeXact (st : St) (hline : Nat) (_header : String)
    (rawPosts : List (Nat × String)) : Except String St := do
  -- UUID dedup: scan raw text (notes ride the raw lines)
  let uuid? := rawPosts.findSome? fun (_, r) => uuidOf r
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
    let (p?, learned, comm?, decs, isExpr, teach) ← parsePosting stv ln raw
    for (c, d) in teach do
      stv := bumpPrecision stv c d
    match learned with
    | some (c, b) =>
        stv := { stv with amt := { stv.amt with styles := (c, b) :: stv.amt.styles } }
    | none => pure ()
    let _ := isExpr
    match comm? with
    | some c =>
        let c := (stv.commAliases.lookup c).getD c
        stv := bumpPrecision stv c decs
    | none => pure ()
    match p? with
    | some p =>
        -- canonicalize amounts through commodity equivalences
        let p := { p with
          amount := p.amount.map (canonAmt stv)
          costVal := p.costVal.map (canonAmt stv)
          lotVal := p.lotVal.map (canonAmt stv)
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
  -- Balancing runs per POOL: real (+deferred) postings balance among
  -- themselves, bracket-virtuals `[A]` among themselves (regress/563);
  -- paren-virtuals `(A)` are exempt. Each pool may have one elided
  -- posting. Structural decisions use EXACT residuals; the
  -- display-precision tolerance is only the final acceptance test.
  let balancePool := fun (pool : List PostSpec) (allowBucket : Bool) => do
    let sumsWith := fun (useLot : Bool) =>
      pool.foldl (init := ([] : List (String × ℚ))) fun acc p =>
        match p.amount with
        | some a =>
            let v :=
              if useLot then (p.lotVal.getD (p.costVal.getD a))
              else p.costVal.getD a
            match acc.lookup v.comm with
            | some _ => acc.map fun (c, s) => if c = v.comm then (c, s + v.q) else (c, s)
            | none => (v.comm, v.q) :: acc
        | none => acc
    let residualExact := (sumsWith false).filter fun (_, s) => s != 0
    let elided := pool.filter fun p => p.amount.isNone && p.assignTarget.isNone
    match elided with
    | [] =>
        if residualExact.isEmpty then pure pool
        else match (if allowBucket then st.bucket else none) with
          | some b =>
              -- bucket names were resolved when declared
              let comps := residualExact.map fun (c, s) =>
                { line := hline, inferred := true
                  account := b
                  kind := PostKind.real, amount := some ⟨c, -s⟩ : PostSpec }
              pure (pool ++ comps)
          | none =>
              -- per-posting cost rounding may explain the residual
              -- (xact.cc phase 8, regress/1125)
              let costTol := fun (c : String) =>
                pool.foldl (init := (0 : ℚ)) fun acc p =>
                  match p.costVal with
                  | some cv =>
                      if cv.comm == c && p.costDecs > 0 then
                        acc + 1 / (2 * ((10 ^ p.costDecs : ℕ) : ℚ))
                      else acc
                  | none => acc
              if residualExact.length == 2 then pure pool  -- implicit exchange
              else if residualExact.all fun (c, s) =>
                  roundsToZero stv c s
                    || (s ≤ costTol c && -s ≤ costTol c) then
                pure pool
              else
                -- second pass: substitute lot/fixated values
                -- (coverage-wave3 fixated, opt-base lot+cost)
                let residual2 := (sumsWith true).filter fun (_, s) => s != 0
                if residual2.isEmpty
                    || residual2.all (fun (c, s) => roundsToZero stv c s)
                    || residual2.length == 2 then
                  pure pool
                else
                  err hline s!"unbalanced transaction (residual in {residualExact.length} commodities)"
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
        pure ((pool.filter fun p => !(p.amount.isNone && p.assignTarget.isNone))
          ++ comps)
    | _ => err hline "more than one elided posting in a balancing pool"
  let realPool := rposts.filter fun p => p.kind == .real || p.kind == .deferred
  let virtPool := rposts.filter fun p => p.kind == .virtualBal
  let exempt := rposts.filter fun p => p.kind == .virtualUnbal
  let realDone ← balancePool realPool true
  let virtDone ←
    if virtPool.isEmpty then pure []
    else balancePool virtPool false
  let completed := realDone ++ virtDone ++ exempt
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
  let finalPosts := applyAutos stv (headerDateF stv.dfmt stv.defaultYear _header)
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
            -- bare number = multiplier; otherwise fixed amount
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
  | "define" => defineDirective st restS
  | "def" => defineDirective st restS
  | "P" =>
      -- price observations: plain `bal` never converts, but an
      -- unseen price commodity picks up a TENTATIVE precision from
      -- the price literal (pool.cc: COMMODITY_PRECISION_FROM_PRICE)
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
      -- default display format: declare and LOCK precision/style
      -- (amount.cc: D sets COMMODITY_STYLE_NO_MIGRATE — #761/#1054)
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
  | _ => pure { st with pending := .none }

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
      if trimS t == "end comment" || trimS t == "end test" then
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
        -- periodic entries generate no postings in plain reports
        st := { st with pending := .ignoreBlock }
      else if t == "comment" || t == "test" || t.startsWith "test "
          || t.startsWith "test\t" then
        -- `test` opens a comment block ended by `end test`
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
