module

public import Lemmata.SpanningTreeSymmetricEF.Models
public import Lemmata.SpanningTreeSymmetricEF.FormulationAffine

@[expose] public section

namespace Lemmata.SpanningTreeSymmetricEF

open scoped BigOperators
open FormulationStructure FormulationAffine ApproximationUpper
noncomputable section

/-- The displayed orientation LP, with its literal row family and a coherent
affine vertex action. The auxiliary variables are all real matrices; diagonal
zero is an equation, not an extra family of inequalities. -/
def orientationLP (n : ℕ) :
    SymmetricLP n (Matrix (Fin n) (Fin n) ℝ) (ScalarConstraint (Fin n)) where
  slice := lpSlice
  slack := lpSlackAffine
  project := projectionAffine
  action := matrixAction
  stable := by
    intro g y hy
    have h : TreeModels.LPFeasible y :=
      (lp_indexed_constraints y).mpr
        ⟨(mem_lpSlice y).mp hy.1, fun q => by simpa using hy.2 q⟩
    obtain ⟨hd, hs⟩ := (lp_indexed_constraints (matrixAction g y)).mp
      ((lpAction_feasible g y).mpr h)
    exact ⟨(mem_lpSlice _).mpr hd, fun q => by simpa using hs q⟩
  covariant := by
    intro g y _
    exact projection_equivariant g y

theorem orientationLP_image (n : ℕ) : (orientationLP n).image = lpRelaxation :=
  lpImage_eq

theorem orientationLP_count (n : ℕ) :
    Fintype.card (ScalarConstraint (Fin n)) = 3 * n.choose 2 + n := by
  simpa using (scalar_constraint_count (V := Fin n))

/-- Exact worst-case approximation factor of this same concrete LP image. -/
theorem orientationLP_factor (n : ℕ) (hn : 3 ≤ n) :
    (orientationLP n).Approximates (3 / 2 : ℝ) ∧
      ∀ β, (orientationLP n).Approximates β → (3 / 2 : ℝ) ≤ β := by
  have h := FormulationTransport.lp_fin_exact_factor n hn
  constructor
  · apply ((orientationLP n).approximates_iff_source _).mpr
    simpa only [orientationLP_image] using h.1
  · intro β hβ
    apply h.2 β
    simpa only [orientationLP_image] using
      ((orientationLP n).approximates_iff_source β).mp hβ

end
end Lemmata.SpanningTreeSymmetricEF
