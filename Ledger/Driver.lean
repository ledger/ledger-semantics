import Ledger.Oracle
import Ledger.Journal

/-!
# The oracle driver (differential-comparison side)

Reads `.dat` files, splices `include`s (so the pure engine never does
IO), runs the journal engine (`Journal.lean`), constructs the L2 term
— one generator per effective transaction, the journal as their
tensor — and evaluates the executable oracle `netFlow` at every
touched account, printing one canonical line per nonzero balance:

    COMMODITY|AMOUNT|ACCOUNT

sorted; report-time account rewrites are applied (merging flows) at
output, and canonical-second time totals are displayed in the largest
fitting unit (h/m/s) rounded to two decimals, as the C++ ledger does.

Run through the **interpreter** (never a `lean_exe`):

    lake env lean --run Ledger/Driver.lean [FLAGS] FILE ...

Flags apply to the next file only (mirroring a test's own flags) and
reset after it: `--decimal-comma`, `--recursive-aliases`,
`--now DATE`, `--input-date-format FORMAT`. Each file's block starts
with `== PATH`; a rejection prints `!! ERROR ...` for that file
(fail-closed, never silent).
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
    learned/0 precision for the base itself). -/
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
      (u, roundAt p (q / f))
  | none =>
      if comm == "" then (comm, q)   -- bare amounts: full precision
      else
        let p := (precisions.lookup comm).getD 0
        (comm, roundAt p q)

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

/-- Balances of an (include-spliced) journal text. -/
def balancesOf (decimalComma : Bool) (nowSecs : Option ℚ)
    (recAliases : Bool) (dfmt : Option String) (input : String) :
    Except String (List String) := do
  let res ← Journal.run input decimalComma nowSecs recAliases dfmt
  let arr := res.gens.toArray
  let S := specFor arr
  let ⟨_, _, term⟩ := journalTerm S (List.finRange arr.size)
  let accts := (res.gens.flatten.map Prod.fst).eraseDups
  -- per-account oracle totals, then report-time rewrites (merging)
  let totals := accts.filterMap fun a =>
    let v := netFlow (flowsFor arr) term a
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
    let (dispComm, dispQ) := displayAmount res.equivs res.precisions a.commodity v
    -- a lone inferred balance renders at its recovered precision when
    -- the commodity has none, or when it would otherwise show as zero
    -- (BIGINT_COST_PREC, issues #1692/#1773); sums drop the widening
    let (tot, inf) := statFor a.name a.commodity
    if tot == 1 && inf == 1 && dispComm == a.commodity
        && a.commodity != ""
        && (((res.precisions.lookup a.commodity).getD 0) == 0
            || dispQ == 0) then
      if v = 0 then none
      else some s!"{a.commodity}|{ratToCanonical v}|{a.name}"
    else
    if dispQ = 0 then none
    else some s!"{dispComm}|{ratToCanonical dispQ}|{a.name}"
  let styleRows := res.styles.filterMap fun (c, dc) =>
    if dc then some (if c == "" then "%% dc *" else s!"%% dc {c}") else none
  pure (styleRows ++ (rows.toArray.qsort (· < ·)).toList)

end Driver

end Ledger

/-- Expand a (possibly glob) include pattern against `dir`:
    `*`, `?`, and `[..]` in any path component. -/
partial def globPaths (dir : System.FilePath) (pat : String) :
    IO (List System.FilePath) := do
  let comps := pat.splitOn "/"
  let isGlob := fun (c : String) =>
    c.toList.any fun ch => ch == '*' || ch == '?' || ch == '['
  let rec walk (base : System.FilePath) : List String → IO (List System.FilePath)
    | [] => pure [base]
    | c :: rest => do
        if !(isGlob c) then
          walk (base / c) rest
        else
          let rxSrc := String.join (c.toList.map fun ch =>
            if ch == '*' then "[^/]*"
            else if ch == '?' then "."
            else if ch == '.' then "\\."
            else if ch == '[' then "["
            else if ch == ']' then "]"
            else if ch == '+' || ch == '(' || ch == ')' || ch == '|'
                 || ch == '^' || ch == '$' then String.ofList ['\\', ch]
            else String.ofList [ch])
          match Ledger.Parse.compileRegex ("^" ++ rxSrc ++ "$") with
          | .error _ => pure []
          | .ok rx => do
              if !(← base.pathExists) then pure [] else
              let entries ← base.readDir
              let names := (entries.map (·.fileName)).qsort (· < ·)
              let mut acc : List System.FilePath := []
              for nm in names do
                if Ledger.Parse.regexSearch rx nm then
                  acc := acc ++ (← walk (base / nm) rest)
              pure acc
  let res ← walk dir comps
  res.filterM (·.pathExists)

/-- Splice `include` lines (resolved against `dir`), depth-limited;
    like `include_directive`, the file never includes itself, quotes
    are stripped, and backslash escapes in the pattern are literal. -/
partial def splice (self : System.FilePath) (dir : System.FilePath)
    (text : String) (depth : Nat) : IO String := do
  if depth == 0 then
    return text
  let mut out : Array String := #[]
  for line in text.splitOn "\n" do
    let t := line.trimAscii.toString
    let t := if t.startsWith "@" then (t.drop 1).toString else t
    let incl? :=
      if t.startsWith "include " then some (t.drop "include ".length).toString
      else if t.startsWith "!include " then some (t.drop "!include ".length).toString
      else none
    match incl? with
    | some fname =>
        let pat := Ledger.Parse.trimS fname
        let pat :=
          if pat.length ≥ 2 && ((pat.startsWith "\"" && pat.endsWith "\"")
              || (pat.startsWith "'" && pat.endsWith "'")) then
            String.ofList ((pat.drop 1).toString.toList.dropLast)
          else pat
        let pat := String.ofList (pat.toList.filter (· != '\\'))
        let paths ← globPaths dir pat
        let paths := paths.filter fun p => p.toString != self.toString
        if paths.isEmpty then
          out := out.push line   -- unresolved: engine reports it, named
        else
          for path in paths do
            let sub ← IO.FS.readFile path
            let subDir := path.parent.getD dir
            out := out.push (← splice path subDir sub (depth - 1))
    | none => out := out.push line
  return String.intercalate "\n" out.toList

def main (args : List String) : IO Unit := do
  let mut dc := false
  let mut rec_ := false
  let mut now : Option ℚ := none
  let mut nowPending := false
  let mut dfmt : Option String := none
  let mut dfmtPending := false
  for arg in args do
    if arg == "--decimal-comma" then
      dc := true
    else if arg == "--recursive-aliases" then
      rec_ := true
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
      let txt ← IO.FS.readFile arg
      let self := System.FilePath.mk arg
      let dir := self.parent.getD "."
      let spliced ← splice self dir txt 8
      match Ledger.Driver.balancesOf dc now rec_ dfmt spliced with
      | .error e => IO.println s!"!! ERROR {e}"
      | .ok rows => for r in rows do IO.println r
      dc := false
      rec_ := false
      now := none
      dfmt := none
