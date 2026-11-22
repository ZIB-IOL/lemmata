module

/-! # Integer tables written as strings

The witness data are stored as one comma-separated string per row, parsed by the
computable functions below. A malformed entry would parse as `0`; the witness modules
check that every entry parses. -/

@[expose] public section

namespace Lemmata.GrothendieckLowerBounds

/-- Parse one comma-separated row of integers. -/
def parseRow (s : String) : Array Int := (s.splitOn ",").toArray.map fun t => t.toInt?.getD 0

/-- Every entry of the row is an integer literal. -/
def rowWellFormed (s : String) : Bool := (s.splitOn ",").all fun t => t.toInt?.isSome

/-- Parse a table, one string per row. -/
def table (rows : Array String) : Array (Array Int) := rows.map parseRow

/-- Entry `(i, j)` of a parsed table, `0` outside it. -/
def entry (t : Array (Array Int)) (i j : Nat) : Int := (t[i]?.getD #[])[j]?.getD 0

end Lemmata.GrothendieckLowerBounds
