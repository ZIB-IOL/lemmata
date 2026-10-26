module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Tactic.FinCases

@[expose] public section

set_option Elab.async false

namespace Lemmata.CocubicCovering
abbrev Field := ZMod 2
abbrev Vector (n : Nat) := Fin n → Field
end Lemmata.CocubicCovering
