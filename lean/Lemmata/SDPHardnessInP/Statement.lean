module

public import Lemmata.LPHardnessInP.Main
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Trace

@[expose] public section

namespace Lemmata.SDPHardnessInP

/-- A real PSD factorization; the matrix entries are reproduced exactly. -/
structure PSDFactorization {I J : Type*} (S : I → J → ℝ)
    (K : Type*) [Fintype K] where
  row : I → Matrix K K ℝ
  col : J → Matrix K K ℝ
  row_psd : ∀ i, (row i).PosSemidef
  col_psd : ∀ j, (col j).PosSemidef
  trace_eq : ∀ i j, (row i * col j).trace = S i j

/-- Finite PSD-rank lower bound, independent of the factor-coordinate labels.
The external shifted-matching theorem supplies this hypothesis. -/
def PSDLowerBound {I J : Type*} (S : I → J → ℝ) (L : ℕ) : Prop :=
  ∀ (K : Type) [Fintype K], PSDFactorization S K → L ≤ Fintype.card K

/-- An affine SDP with a common feasible realization and exact conic dual
certificates. Equations have been eliminated in the affine parameter space `E`.
Certificate existence is not asserted by this structure. -/
structure CertifiedSDP {I J E : Type*} [AddCommGroup E] [Module ℝ E]
    (value : I → J → ℝ) (bound : I → ℝ) (K : Type*) [Fintype K] where
  pencil : E →ᵃ[ℝ] Matrix K K ℝ
  realization : J → E
  feasible : ∀ j, (pencil (realization j)).PosSemidef
  objective : I → E →ᵃ[ℝ] ℝ
  realizes : ∀ i j, objective i (realization j) = value i j
  dual : I → Matrix K K ℝ
  dual_psd : ∀ i, (dual i).PosSemidef
  offset : I → ℝ
  offset_nonneg : ∀ i, 0 ≤ offset i
  certificate : ∀ i z,
    objective i z - bound i = (dual i * pencil z).trace + offset i

end Lemmata.SDPHardnessInP
