module

public import Lemmata.TensorRank.Def.Tensor
public import Lemmata.TensorRank.Def.Rank
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.Choose.Basic

@[expose] public section

set_option autoImplicit false

namespace Lemmata.TensorRank

abbrev Neighbors {k : ℕ} (i : Fin k) := {j : Fin k // j ≠ i}

abbrev GraphCoordinate (k n : ℕ) (i : Fin k) := Neighbors i → Fin n

/-- Each edge carries the same index at its two endpoints. -/
noncomputable def completeGraph (k n : ℕ) :
    Tensor ℂ (Fin k) (GraphCoordinate k n) := by
  classical
  exact fun x => if ∀ (i j : Fin k) (h : i ≠ j),
    x i ⟨j, h.symm⟩ = x j ⟨i, h⟩ then 1 else 0

noncomputable def graphExponent (k : ℕ) : ℝ := by
  classical
  exact ⨅ d : {n : ℕ // 2 ≤ n},
    Real.log (Tensor.rank (completeGraph k d.val)) / Real.log d.val

noncomputable def edgeExponent (k : ℕ) : ℝ :=
  graphExponent k / (k.choose 2 : ℝ)

end Lemmata.TensorRank
