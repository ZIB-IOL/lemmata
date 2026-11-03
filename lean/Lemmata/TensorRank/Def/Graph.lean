module

/-
Copyright (c) 2026 Kirill Khoruzhii. Licensed under Apache-2.0.
Modified for the arbitrary-field tensor-rank formalization; namespace and imports
adapted for Lemmata. See docs/tensor-rank/NOTICE.txt for upstream attribution
and modification notices, and docs/tensor-rank/LICENSE.txt for the license.
-/

public import Lemmata.TensorRank.Def.Tensor
public import Lemmata.TensorRank.Def.Rank
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.Choose.Basic

@[expose] public section

set_option autoImplicit false

namespace Lemmata.TensorRank

variable {𝕜 : Type*} [Field 𝕜]

abbrev Neighbors {k : ℕ} (i : Fin k) := {j : Fin k // j ≠ i}

abbrev GraphCoordinate (k n : ℕ) (i : Fin k) := Neighbors i → Fin n

/-- Each edge carries the same index at its two endpoints. -/
noncomputable def completeGraph (k n : ℕ) :
    Tensor 𝕜 (Fin k) (GraphCoordinate k n) := by
  classical
  exact fun x => if ∀ (i j : Fin k) (h : i ≠ j),
    x i ⟨j, h.symm⟩ = x j ⟨i, h⟩ then 1 else 0

noncomputable def graphExponent (k : ℕ) : ℝ := by
  classical
  exact ⨅ d : {n : ℕ // 2 ≤ n},
    Real.log (Tensor.rank (completeGraph (𝕜 := 𝕜) k d.val)) / Real.log d.val

noncomputable def edgeExponent (k : ℕ) : ℝ :=
  graphExponent (𝕜 := 𝕜) k / (k.choose 2 : ℝ)

end Lemmata.TensorRank
