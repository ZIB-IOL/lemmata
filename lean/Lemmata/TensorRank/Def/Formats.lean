module

/-
Copyright (c) 2026 Kirill Khoruzhii. Licensed under Apache-2.0.
Modified for the arbitrary-field tensor-rank formalization; namespace and imports
adapted for Lemmata. See docs/tensor-rank/NOTICE.txt for upstream attribution
and modification notices, and docs/tensor-rank/LICENSE.txt for the license.
-/

public import Lemmata.TensorRank.Def.Asymptotic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Data.Fintype.Pi

@[expose] public section

set_option autoImplicit false

open Classical

noncomputable section

namespace Lemmata.TensorRank

variable {𝕜 : Type*} [Field 𝕜]

abbrev Cubical (k n : ℕ) := Tensor 𝕜 (Fin k) (fun _ => Fin n)

def cubicalRanks (k n : ℕ) : Set ℝ :=
  {x | ∃ T : Cubical (𝕜 := 𝕜) k n, Tensor.asymptoticRank T = x}

def balancedMatrix (r n : ℕ) (T : Cubical (𝕜 := 𝕜) (r + r) n) :
    Matrix (Fin r → Fin n) (Fin r → Fin n) 𝕜 :=
  fun a b => T (Fin.addCases a b)

def balancedDiagonal (r n : ℕ) : Cubical (𝕜 := 𝕜) (r + r) n :=
  fun x => if (fun j : Fin r => x (j.castAdd r)) = (fun j : Fin r => x (j.natAdd r))
    then 1 else 0

end Lemmata.TensorRank
