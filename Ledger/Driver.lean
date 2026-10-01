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
    error. -/
partial def splice (self : System.FilePath) (dir : System.FilePath)
    (text : String) (parents : Nat) : IO String := do
  let text := if text.startsWith "\uFEFF" then (text.drop 1).toString else text
  let mut out : Array String := #[]
  let mut inComment := false
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
        out := out.push (← splice path (path.parent.getD dir) sub (parents + 1))
  -- C++ reads a block no further than the end of its own file
  -- (textual_directives.cc:941-949), so the block that an included
  -- file leaves open closes where that file ends
  if inComment && parents > 0 then out := out.push "end comment"
  return String.intercalate "\n" out.toList

namespace Ledger.Driver

/-- The text of the file `arg` with its includes spliced. -/
def readSpliced (arg : String) : IO String := do
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
      match ← (Ledger.Driver.readSpliced arg).toBaseIO with
      | .error e =>
        -- the text of an IO error can continue on a second line
        -- ("  file: PATH"); the protocol gives a rejection one line
        let lines := ((toString e).splitOn "\n").map (·.trimAscii.toString)
        IO.println s!"!! ERROR {" ".intercalate (lines.filter (!·.isEmpty))}"
      | .ok spliced =>
        match Ledger.Driver.balancesOf dc now rec_ dfmt spliced with
        | .error e => IO.println s!"!! ERROR {e}"
        | .ok rows => for r in rows do IO.println r
      dc := false
      rec_ := false
      now := none
      dfmt := none
