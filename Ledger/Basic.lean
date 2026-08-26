/-!
# Basic types

Account names, commodities, and the atomic `Account` pair. These are
deliberately thin: an account×commodity pair is an *identifier*, not a
container of value. Value lives in valuations (`Valuation.lean`), flow
lives in morphisms (`Groupoid.lean`).
-/

namespace Ledger

/-- A commodity identifier (USD, EUR, shares of AAPL, etc.). -/
abbrev Commodity : Type := String

/-- An account name (e.g. "Assets:Cash:Checking"). -/
abbrev AccountName : Type := String

/-- An account×commodity pair — the atomic unit of an object in 𝕋. -/
structure Account where
  name : AccountName
  commodity : Commodity
  deriving BEq, DecidableEq, Hashable, Repr, Inhabited

end Ledger
