import Mathlib.Data.Rat.Defs
import Ledger.Basic

/-!
# Lexical layer: numbers, commodities, amounts, regexes

The lower half of the journal engine (`Journal.lean` holds the
stateful upper half). Everything here is context-passed and pure:

- **Numbers** are lexed as a token (digits, `.`, `,`) and then read
  under the commodity's *style*: dot-decimal (default) or
  decimal-comma. When the style is unknown it is inferred by the C++
  rules exercised in regress/1138: with both separators present the
  last one is the decimal; a comma with a non-3-digit group or a zero
  integer part is a decimal; inference is reported upward so the
  journal engine can *learn* the commodity's style, exactly as
  `textual.cc` does.
- **Time commodities** `s`/`m`/`h` canonicalize to seconds
  (commodity `"s"`); display back in the largest fitting unit happens
  in the driver.
- **Amount expressions** `(...)` support `+ - * /`, parentheses,
  numeric literals with commodities, and `define`d variables.
- **Regexes** (auto-xact predicates, `account-rewrite`) are a small
  backtracking engine: literals, `. * + ? ^ $ [..] (..) |` and
  escapes; anything else fails closed.
-/

namespace Ledger

namespace Parse

/-- An amount: commodity (possibly `""`) and exact quantity. -/
structure Amount where
  comm : String
  q : ℚ
  deriving Repr, DecidableEq

private def err {α} (line : Nat) (msg : String) : Except String α :=
  .error s!"line {line}: {msg}"

/-! ## Regex engine -/

inductive Rx where
  | empty
  | lit (c : Char)
  | any
  | cls (neg : Bool) (cs : List Char)
  | seq (a b : Rx)
  | alt (a b : Rx)
  | star (a : Rx)
  | plus (a : Rx)
  | opt (a : Rx)
  | bol
  | eol

private partial def parseAtom (parseAlt : List Char → Except String (Rx × List Char)) :
    List Char → Except String (Rx × List Char)
  | [] => .error "regex: empty atom"
  | '(' :: rest => do
      let (r, rest) ← parseAlt rest
      match rest with
      | ')' :: rest => pure (r, rest)
      | _ => .error "regex: unclosed group"
  | '[' :: rest => do
      let (neg, rest) := match rest with
        | '^' :: r => (true, r)
        | r => (false, r)
      let rec collect (acc : List Char) : List Char → Except String (List Char × List Char)
        | ']' :: r => pure (acc.reverse, r)
        | '\\' :: c :: r => collect (c :: acc) r
        | a :: '-' :: b :: r =>
            if b == ']' then collect ('-' :: a :: acc) (b :: r)
            else
              let lo := a.toNat; let hi := b.toNat
              let range := (List.range (hi + 1 - lo)).map fun i => Char.ofNat (lo + i)
              collect (range.reverse ++ acc) r
        | c :: r => collect (c :: acc) r
        | [] => .error "regex: unclosed class"
      let (chars, rest) ← collect [] rest
      pure (.cls neg chars, rest)
  | '\\' :: c :: rest => pure (.lit c, rest)
  | '.' :: rest => pure (.any, rest)
  | '^' :: rest => pure (.bol, rest)
  | '$' :: rest => pure (.eol, rest)
  | c :: rest =>
      if c == '*' || c == '+' || c == '?' || c == ')' || c == '|' then
        .error s!"regex: unexpected '{c}'"
      else pure (.lit c, rest)

private partial def parseAltRx : List Char → Except String (Rx × List Char) :=
  fun cs => do
    let rec parsePostfix (r : Rx) : List Char → (Rx × List Char)
      | '*' :: rest => parsePostfix (.star r) rest
      | '+' :: rest => parsePostfix (.plus r) rest
      | '?' :: rest => parsePostfix (.opt r) rest
      | rest => (r, rest)
    let rec parseSeq (acc : Rx) (cs : List Char) : Except String (Rx × List Char) :=
      match cs with
      | [] => pure (acc, [])
      | ')' :: _ => pure (acc, cs)
      | '|' :: _ => pure (acc, cs)
      | _ => do
          let (a, rest) ← parseAtom parseAltRx cs
          let (a, rest) := parsePostfix a rest
          parseSeq (.seq acc a) rest
    let (a, rest) ← parseSeq .empty cs
    match rest with
    | '|' :: rest => do
        let (b, rest) ← parseAltRx rest
        pure (.alt a b, rest)
    | _ => pure (a, rest)

/-- Compile a regex source string (fail-closed). -/
def compileRegex (src : String) : Except String Rx := do
  let (r, rest) ← parseAltRx src.toList
  if rest.isEmpty then pure r
  else .error s!"regex: trailing '{String.ofList rest}'"

private partial def matchRx (r : Rx) (cs : List Char) (atStart : Bool) :
    List (List Char) :=
  match r with
  | .empty => [cs]
  | .lit c => match cs with
    | c' :: rest => if c == c' then [rest] else []
    | [] => []
  | .any => match cs with
    | _ :: rest => [rest]
    | [] => []
  | .cls neg set => match cs with
    | c :: rest => if (set.contains c) != neg then [rest] else []
    | [] => []
  | .seq a b =>
      (matchRx a cs atStart).flatMap fun rest =>
        matchRx b rest (atStart && rest.length == cs.length)
  | .alt a b => matchRx a cs atStart ++ matchRx b cs atStart
  | .star a =>
      let one := (matchRx a cs atStart).filter (·.length < cs.length)
      cs :: one.flatMap fun rest => matchRx (.star a) rest false
  | .plus a => matchRx (.seq a (.star a)) cs atStart
  | .opt a => cs :: matchRx a cs atStart
  | .bol => if atStart then [cs] else []
  | .eol => if cs.isEmpty then [cs] else []

/-- Unanchored regex search. -/
partial def regexSearch (r : Rx) (s : String) : Bool :=
  let rec go (cs : List Char) (atStart : Bool) : Bool :=
    if !(matchRx r cs atStart).isEmpty then true
    else match cs with
      | [] => false
      | _ :: rest => go rest false
  go s.toList true

/-! ## Lexical helpers -/

def isCommentStart (c : Char) : Bool :=
  c == ';' || c == '#' || c == '%' || c == '|' || c == '*'

/-- Split off a trailing note (`;` preceded by whitespace):
    (content-trimmed-right, note). -/
def splitNote (s : String) : String × String :=
  let cs := s.toList
  let rec go (prevWs : Bool) (acc : List Char) : List Char → List Char × List Char
    | [] => (acc.reverse, [])
    | ';' :: rest =>
        if prevWs then (acc.reverse, rest) else go false (';' :: acc) rest
    | c :: rest => go (c == ' ' || c == '\t') (c :: acc) rest
  let (content, note) := go true [] cs
  ((String.ofList content).trimAsciiEnd.toString, String.ofList note)

/-- Split at the first tab or double-space. -/
def splitField (s : String) : String × Option String :=
  let cs := s.toList
  let rec go (acc : List Char) : List Char → String × Option String
    | [] => ((String.ofList acc.reverse).trimAsciiEnd.toString, none)
    | '\t' :: rest =>
        ((String.ofList acc.reverse).trimAsciiEnd.toString,
         some ((String.ofList rest).trimAscii.toString))
    | ' ' :: ' ' :: rest =>
        ((String.ofList acc.reverse).trimAsciiEnd.toString,
         some ((String.ofList rest).trimAscii.toString))
    | c :: rest => go (c :: acc) rest
  go [] cs

def trimS (s : String) : String := s.trimAscii.toString

/-! ## Numbers under commodity styles -/

private def digitsVal (cs : List Char) : ℕ :=
  cs.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0

private def validGroups (groups : List (List Char)) : Bool :=
  match groups with
  | [] => false
  | [_] => true
  | g₀ :: rest =>
      1 ≤ g₀.length && g₀.length ≤ 3 && rest.all fun g => g.length == 3

private def splitOnChar (c : Char) (cs : List Char) : List (List Char) :=
  let rec go (cur : List Char) (acc : List (List Char)) : List Char → List (List Char)
    | [] => ((cur.reverse) :: acc).reverse
    | x :: rest =>
        if x == c then go [] (cur.reverse :: acc) rest
        else go (x :: cur) acc rest
  go [] [] cs

/-- Read a numeric token (digits/`.`/`,` only) under a style.
    `style`: `none` = infer, `some true` = decimal-comma,
    `some false` = dot-decimal. Returns the value and, when inference
    settled a style, the style to learn. -/
def readNumToken (style : Option Bool) (tok0 : List Char) :
    Option (ℚ × Nat × Option Bool) :=
  -- Exact port of amount_t::parse's separator scan (amount.cc):
  -- right-to-left; a comma with a non-3 tail, a >3 tail, or a zero
  -- integer part is the decimal; a later period retroactively makes
  -- a tentative thousands-comma the decimal; apostrophes are always
  -- 3-digit group marks; commodity/global style forces decimal-comma.
  let dc0 := style == some true
  let n := tok0.length
  -- state: (decOff, noC, noP, dc, prec, lastComma?, lastPeriod?, ok)
  let step := fun (st : Nat × Bool × Bool × Bool × Nat × Option Nat ×
        Option Nat × Bool) ((idx : Nat), (ch : Char)) =>
    let (decOff, noC, noP, dc, prec, lastC, lastP, ok) := st
    if !ok then st
    else if ch == '.' then
      if noP then (decOff, noC, noP, dc, prec, lastC, lastP, false)
      else if dc then
        if decOff % 3 != 0 then (decOff, noC, noP, dc, prec, lastC, lastP, false)
        else (decOff, true, noP, dc, prec, lastC, lastP.orElse (fun _ => some idx), ok)
      else
        match lastC with
        | some lc =>
            -- retroactive: the comma to the right was the decimal
            if decOff % 3 != 0 then (decOff, noC, noP, dc, prec, lastC, lastP, false)
            else (decOff, true, noP, true, n - 1 - lc,
                  lastC, lastP.orElse (fun _ => some idx), ok)
        | none => (0, noC, true, dc, decOff, lastC, some idx, ok)
    else if ch == ',' then
      if noC then (decOff, noC, noP, dc, prec, lastC, lastP, false)
      else if dc then
        match lastP with
        | some _ => (decOff, noC, noP, dc, prec, lastC, lastP, false)
        | none => (0, true, noP, dc, decOff, lastC.orElse (fun _ => some idx), lastP, ok)
      else
        let intZero := lastC.isNone && idx > 0 &&
          (List.range idx).all fun i =>
            (tok0[i]?.getD '0') == '0' || (i == 0 && (tok0[i]?.getD ' ') == '-')
        if decOff % 3 != 0 || (lastC.isNone && decOff > 3) || intZero then
          if lastC.isSome || lastP.isSome then
            (decOff, noC, noP, dc, prec, lastC, lastP, false)
          else (0, true, noP, true, decOff, some idx, lastP, ok)
        else
          -- thousands group; a second comma blocks later periods
          (decOff, noC, lastC.isSome || noP, dc, prec,
           lastC.orElse (fun _ => some idx), lastP, ok)
    else if ch == '\'' then
      if decOff % 3 != 0 then (decOff, noC, noP, dc, prec, lastC, lastP, false)
      else (decOff, noC, noP, dc, prec, lastC, lastP, ok)
    else
      (decOff + 1, noC, noP, dc, prec, lastC, lastP, ok)
  let init : Nat × Bool × Bool × Bool × Nat × Option Nat × Option Nat × Bool :=
    (0, false, false, dc0, 0, none, none, true)
  let scanned := (tok0.zipIdx.reverse.map fun (c, i) => (i, c)).foldl step init
  let (_, _, _, dcF, prec, _, _, ok) := scanned
  if !ok || tok0.isEmpty then none
  else
    let digits := tok0.filter Char.isDigit
    if digits.isEmpty then none
    else
      let v : ℚ := ((digitsVal digits : ℕ) : ℚ) / ((10 ^ prec : ℕ) : ℚ)
      some (v, prec, if dcF && !dc0 then some true else none)

/-- Round half-away-from-zero at `p` decimals. -/
def roundAt (p : Nat) (q : ℚ) : ℚ :=
  let f : ℚ := ((10 ^ p : ℕ) : ℚ)
  let scaled := q * f
  let n : Int :=
    if scaled ≥ 0 then (scaled + 1/2).floor
    else -((-scaled + 1/2).floor)
  (n : ℚ) / f

/-! ## Commodities -/

def isForbiddenComm (c : Char) : Bool :=
  c == '@' || c == '=' || c == '(' || c == ')' || c == '{' || c == '}'
    || c == '[' || c == ']'

def validCommodity (s : String) : Bool :=
  !s.isEmpty && s.toList.all fun c =>
    !c.isDigit && !isForbiddenComm c && c != ' ' && c != '\t' && c != '-'
      && c != ',' && c != '"' && c != ';' && c != '.'

def unquote (s : String) : Option String :=
  match s.toList with
  | '"' :: rest =>
      if rest.length ≥ 1 && rest.getLast? == some '"' then
        some (String.ofList rest.dropLast)
      else none
  | _ => none

/-- Time-unit commodities canonicalize to seconds. -/
def timeFactor (s : String) : Option ℚ :=
  if s == "s" then some 1
  else if s == "m" then some 60
  else if s == "h" then some 3600
  else none

def resolveCommodity (line : Nat) (raw : String) : Except String String := do
  match unquote raw with
  | some inner =>
      if inner.toList.any (· == '"') then
        err line s!"malformed quoted commodity '{raw}'"
      else pure inner
  | none =>
      if validCommodity raw then pure raw
      else err line s!"malformed commodity '{raw}'"

/-! ## Amounts -/

/-- Style/definition context threaded through amount parsing. -/
structure AmtCtx where
  /-- commodity → decimal-comma? (learned styles) -/
  styles : List (String × Bool) := []
  /-- `--decimal-comma` in force (from the test's own flags) -/
  dcDefault : Bool := false
  /-- `define`d variables -/
  defines : List (String × Amount) := []
  /-- `define f(a, b) = body` functions: name → (params, body src) -/
  funs : List (String × List String × String) := []
  /-- current commodity display precisions (`truncated` uses them) -/
  precs : List (String × Nat) := []

def AmtCtx.styleFor (ctx : AmtCtx) (comm : String) : Option Bool :=
  match ctx.styles.lookup comm with
  | some b => some b
  | none => if ctx.dcDefault then some true else none

/-- Result of an amount parse: the amount, the unconsumed tail, and a
    style newly learned for a commodity (to fold into the state). -/
structure AmtResult where
  amount : Amount
  tail : String
  learned : Option (String × Bool) := none
  /-- fractional digits of the literal (display-precision evidence) -/
  decimals : Nat := 0

private def isNumStart (c : Char) : Bool := c.isDigit || c == '.' || c == ','

private def numTokenOf (cs : List Char) : List Char × List Char :=
  let tok := cs.takeWhile fun c => c.isDigit || c == '.' || c == ',' || c == '\''
  -- trailing separators belong to the tail (guards `100,` + ` EUR`)
  let tok' := (tok.reverse.dropWhile fun c => c == '.' || c == ',' || c == '\'').reverse
  (tok', cs.drop tok'.length)

/-- Where a commodity word ends (suffix position). -/
private def commWordOf (cs : List Char) : List Char :=
  match cs with
  | '"' :: rest =>
      let inner := rest.takeWhile (· != '"')
      if rest.length > inner.length then '"' :: inner ++ ['"'] else []
  | _ => cs.takeWhile fun c =>
      c != ' ' && c != '\t' && !isForbiddenComm c && c != ';'

/-- A prefix commodity symbol: stops at digits, sign, space. -/
private def prefixSymOf (cs : List Char) : List Char :=
  match cs with
  | '"' :: _ => commWordOf cs
  | _ => cs.takeWhile fun c =>
      !c.isDigit && c != ' ' && c != '\t' && c != '-' && c != '+'
        && !isForbiddenComm c && c != ';' && c != ','

/-! Expression amounts `( ... )`: mutual arithmetic evaluator. -/

private def combineAmt (line : Nat) (op : Char) (a b : Amount) :
    Except String Amount := do
  -- multiplying by N% divides by 100 ($1000 * 19% = $190); dividing
  -- by N% multiplies by 100 ($1190 / 19% = $6263.16); the result
  -- keeps the left commodity, gaining "%" only from a bare left side
  if op == '*' && b.comm == "%" then
    pure ⟨if a.comm == "" then "%" else a.comm, a.q * b.q / 100⟩
  else if op == '/' && b.comm == "%" then
    if b.q == 0 then err line "division by zero in amount expression"
    else pure ⟨a.comm, a.q / b.q * 100⟩
  else do
    let comm ←
      if a.comm == b.comm then pure a.comm
      else if a.comm == "" then pure b.comm
      else if b.comm == "" then pure a.comm
      else err line s!"mixed commodities '{a.comm}'/'{b.comm}' in expression"
    match op with
    | '+' => pure ⟨comm, a.q + b.q⟩
    | '-' => pure ⟨comm, a.q - b.q⟩
    | '*' => pure ⟨comm, a.q * b.q⟩
    | _ =>
        if b.q == 0 then err line "division by zero in amount expression"
        else pure ⟨comm, a.q / b.q⟩

mutual

private partial def exprPrimary (ctx : AmtCtx) (line : Nat) :
    List Char → Except String (Amount × Nat × List Char)
  | cs => do
    match cs.dropWhile (· == ' ') with
    | [] => err line "empty amount expression"
    | '(' :: rest => do
        let (a, d, rest) ← exprTop ctx line rest
        match rest.dropWhile (· == ' ') with
        | ')' :: rest => pure (a, d, rest)
        | _ => err line "unclosed parenthesis in amount expression"
    | '-' :: rest => do
        let (a, d, rest) ← exprPrimary ctx line rest
        pure (⟨a.comm, -a.q⟩, d, rest)
    | cs@(c :: _) =>
        if isNumStart c then
          let (tok, rest) := numTokenOf cs
          match readNumToken (ctx.styleFor "") tok with
          | none => err line "malformed number in expression"
          | some (q, d, _) =>
              let sp := rest.dropWhile (· == ' ')
              let w := commWordOf sp
              let wS := String.ofList w
              if !wS.isEmpty && !w.isEmpty && (validCommodity wS || (unquote wS).isSome)
                  && !"+-*/".toList.contains (wS.toList.headD ' ') then do
                let comm ← resolveCommodity line wS
                let rest := sp.drop w.length
                pure (⟨comm, q⟩, d, rest)
              else pure (⟨"", q⟩, d, rest)
        else if c.isAlpha then
          let name := String.ofList (cs.takeWhile fun c => c.isAlphanum || c == '_')
          let rest := cs.drop name.length
          match rest.dropWhile (· == ' ') with
          | '(' :: argCs =>
              -- function application: evaluate comma-separated args
              let rec readArgs (cs : List Char) (acc : List Amount) :
                  Except String (List Amount × List Char) := do
                let (a, _, rest) ← exprTop ctx line cs
                match rest.dropWhile (· == ' ') with
                | ',' :: more => readArgs more (a :: acc)
                | ')' :: more => pure ((a :: acc).reverse, more)
                | _ => err line s!"malformed arguments to '{name}'"
              let (args, rest) ← readArgs argCs []
              if name == "roundto" then
                match args with
                | [x, n] => pure (⟨x.comm, roundAt n.q.num.toNat x.q⟩, 0, rest)
                | _ => err line "roundto expects two arguments"
              else if name == "truncated" then
                match args with
                | [x] =>
                    let p := (ctx.precs.lookup x.comm).getD 0
                    pure (⟨x.comm, roundAt p x.q⟩, 0, rest)
                | _ => err line "truncated expects one argument"
              else
                match ctx.funs.lookup name with
                | some (params, body) =>
                    let binds := params.zip args
                    let ctx' := { ctx with defines := binds ++ ctx.defines }
                    let (v, d, _) ← exprTop ctx' line body.toList
                    pure (v, d, rest)
                | none => err line s!"unknown function '{name}'"
          | _ =>
            match ctx.defines.lookup name with
            | some a => pure (a, 0, rest)
            | none => err line s!"unknown variable '{name}' in amount expression"
        else do
          let symCs := prefixSymOf cs
          if symCs.isEmpty then err line "malformed amount expression" else
          let sym ← resolveCommodity line (String.ofList symCs)
          let rest := (cs.drop symCs.length).dropWhile (· == ' ')
          let (neg, rest) := match rest with
            | '-' :: r => (true, r.dropWhile (· == ' '))
            | r => (false, r)
          let (tok, rest) := numTokenOf rest
          match readNumToken (ctx.styleFor sym) tok with
          | none => err line s!"malformed number after '{sym}'"
          | some (q, d, _) =>
              let q := if neg then -q else q
              pure (⟨sym, q⟩, d, rest)

private partial def exprFactor (ctx : AmtCtx) (line : Nat) (cs : List Char) :
    Except String (Amount × Nat × List Char) := do
  let (a, d, rest) ← exprPrimary ctx line cs
  exprFactorLoop ctx line a d rest

private partial def exprFactorLoop (ctx : AmtCtx) (line : Nat) (a : Amount)
    (d : Nat) (cs : List Char) : Except String (Amount × Nat × List Char) :=
  match cs.dropWhile (· == ' ') with
  | '*' :: rest => do
      let (b, d', rest) ← exprPrimary ctx line rest
      let c ← combineAmt line '*' a b
      exprFactorLoop ctx line c (max d d') rest
  | '/' :: rest => do
      let (b, d', rest) ← exprPrimary ctx line rest
      let c ← combineAmt line '/' a b
      exprFactorLoop ctx line c (max d d') rest
  | _ => pure (a, d, cs)

private partial def exprTop (ctx : AmtCtx) (line : Nat) (cs : List Char) :
    Except String (Amount × Nat × List Char) := do
  let (a, d, rest) ← exprFactor ctx line cs
  exprTopLoop ctx line a d rest

private partial def exprTopLoop (ctx : AmtCtx) (line : Nat) (a : Amount)
    (d : Nat) (cs : List Char) : Except String (Amount × Nat × List Char) :=
  match cs.dropWhile (· == ' ') with
  | '+' :: rest => do
      let (b, d', rest) ← exprFactor ctx line rest
      let c ← combineAmt line '+' a b
      exprTopLoop ctx line c (max d d') rest
  | '-' :: rest => do
      let (b, d', rest) ← exprFactor ctx line rest
      let c ← combineAmt line '-' a b
      exprTopLoop ctx line c (max d d') rest
  | _ => pure (a, d, cs)

end

/-- Expression amount `( ... )`; returns the max literal decimals as
    display-precision evidence (matches C++'s VSGBX 0.01 display in
    divzero.dat). -/
def parseExprAmount (ctx : AmtCtx) (line : Nat) (cs : List Char) :
    Except String (Amount × Nat × List Char) := do
  match cs.dropWhile (· == ' ') with
  | '(' :: rest => do
      let (a, d, rest) ← exprTop ctx line rest
      match rest.dropWhile (· == ' ') with
      | ')' :: rest => pure (a, d, rest)
      | _ => err line "unclosed parenthesis in amount expression"
  | _ => err line "expected '(' expression amount"

/-- Parse one amount (simple or expression) from the front of `s`;
    the tail may hold costs, assertions, or annotations. -/
def parseAmount (ctx : AmtCtx) (line : Nat) (s : String) :
    Except String AmtResult := do
  let cs := s.toList
  let (neg1, cs) := match cs with
    | '-' :: rest => (true, rest.dropWhile (· == ' '))
    | '+' :: rest => (false, rest.dropWhile (· == ' '))
    | cs => (false, cs)
  let finish (a : Amount) (tail : List Char) (learned : Option (String × Bool))
      (decs : Nat) : Except String AmtResult := do
    let a := if neg1 then Amount.mk a.comm (-a.q) else a
    pure ⟨a, trimS (String.ofList tail), learned, decs⟩
  match cs with
  | [] => err line "empty amount"
  | c :: _ =>
    if c == '(' then
      let (a, d, rest) ← parseExprAmount ctx line cs
      finish a rest none d
    else if c.isAlpha
        && (ctx.defines.lookup
              (String.ofList (cs.takeWhile fun c => c.isAlphanum || c == '_'))).isSome then
      -- a defined variable heads the amount: evaluate as expression
      let (a, d, rest) ← exprTop ctx line cs
      finish a rest none d
    else if isNumStart c then
      -- suffix form: NUMBER [commodity-word]
      let (tok, rest) := numTokenOf cs
      if tok.isEmpty then err line s!"malformed number in '{s}'" else
      let rest := match rest with
        | c :: r =>
            if (c == '.' || c == ',')
                && (r.isEmpty || (r.headD ' ') == ' ') then r
            else rest
        | _ => rest
      let commCs := commWordOf (rest.dropWhile (· == ' '))
      let commRaw := String.ofList commCs
      if commRaw.isEmpty then
        match readNumToken (ctx.styleFor "") tok with
        | some (q, d, learn) =>
            let rest := match rest with
              | c :: r =>
                  if (c == '.' || c == ',')
                      && (r.isEmpty || (r.headD ' ') == ' ') then r
                  else rest
              | _ => rest
            finish ⟨"", q⟩ rest (learn.map fun b => ("", b)) d
        | none => err line s!"ambiguous number '{String.ofList tok}'"
      else if commRaw == "%" then
        let restAfter := (rest.dropWhile (· == ' ')).drop commCs.length
        match readNumToken (ctx.styleFor "%") tok with
        | some (q, d, _) => finish ⟨"%", q⟩ restAfter none d
        | none => err line s!"ambiguous number '{String.ofList tok}'"
      else do
        let comm ← resolveCommodity line commRaw
        let restAfter :=
          (rest.dropWhile (· == ' ')).drop commCs.length
        match readNumToken (ctx.styleFor comm) tok with
        | none => err line s!"ambiguous number '{String.ofList tok}' for '{comm}'"
        | some (q, d, learn) =>
            let learned := learn.map fun b => (comm, b)
            finish ⟨comm, q⟩ restAfter learned d
    else do
      -- prefix form: SYMBOL [spaces] [-] NUMBER
      let symCs := prefixSymOf cs
      if symCs.isEmpty then err line s!"malformed amount '{s}'" else
      let sym ← resolveCommodity line (String.ofList symCs)
      let rest1 := (cs.drop symCs.length).dropWhile (· == ' ')
      let (neg2, rest2) := match rest1 with
        | '-' :: r => (true, r.dropWhile (· == ' '))
        | '+' :: r => (false, r.dropWhile (· == ' '))
        | r => (false, r)
      let (tok, rest3) := numTokenOf rest2
      if tok.isEmpty then err line s!"malformed number in '{s}'" else
      match readNumToken (ctx.styleFor sym) tok with
      | none => err line s!"ambiguous number '{String.ofList tok}' for '{sym}'"
      | some (q, d, learn) =>
          let q := if neg2 then -q else q
          let learned := learn.map fun b => (sym, b)
          finish ⟨sym, q⟩ rest3 learned d

end Parse

end Ledger
