module

public import Lemmata.TensorRank.Def.Asymptotic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Data.Fintype.Pi

@[expose] public section

set_option autoImplicit false

open Classical

noncomputable section

namespace Lemmata.TensorRank

abbrev Cubical (k n : ℕ) := Tensor ℂ (Fin k) (fun _ => Fin n)

def cubicalRanks (k n : ℕ) : Set ℝ :=
  {x | ∃ T : Cubical k n, Tensor.asymptoticRank T = x}

def balancedMatrix (r n : ℕ) (T : Cubical (r + r) n) :
    Matrix (Fin r → Fin n) (Fin r → Fin n) ℂ :=
  fun a b => T (Fin.addCases a b)

def balancedDiagonal (r n : ℕ) : Cubical (r + r) n :=
  fun x => if (fun j : Fin r => x (j.castAdd r)) = (fun j : Fin r => x (j.natAdd r))
    then 1 else 0

end Lemmata.TensorRank
