module

public import Lemmata.ModifiedE8Bell.Compute.Raw
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Rat.Cast.Order

@[expose] public section

namespace Lemmata.ModifiedE8Bell

open scoped BigOperators

abbrev Setting := Fin 120
abbrev Coordinate := Fin 8
abbrev Signing := Setting → Bool
abbrev Vector := Coordinate → ℤ

/-- `true` denotes the output +1; `false` denotes -1. -/
def sign (b : Bool) : ℤ := if b then 1 else -1

/-- Doubled canonical E₈ roots: the 56 integral lines followed by the
64 even-parity half-root lines. The order is specified in the entry. -/

def root (i : Setting) (j : Coordinate) : ℤ := (rootRows[i.val]?.getD #[])[j.val]?.getD 0

/-- Four times the integer Bell matrix `3 V Vᵀ - 13 I`, where `V = root / 2`. -/
def fourMatrix (i j : Setting) : ℤ :=
  3 * (∑ k, root i k * root j k) - if i = j then 52 else 0

/-- Four times the value on a deterministic pair of output lists. -/
def fourBell (a b : Signing) : ℤ :=
  ∑ i, ∑ j, sign (a i) * sign (b j) * fourMatrix i j

/-- The Bell value, with its original normalization. -/
def bell (a b : Signing) : ℚ := (fourBell a b : ℚ) / 4

/-- The classical bound is 6104 and is attained by deterministic outputs. -/
def ExactClassicalValue : Prop :=
  (∀ a b : Signing, |bell a b| ≤ 6104) ∧
  ∃ a b : Signing, bell a b = 6104

end Lemmata.ModifiedE8Bell
