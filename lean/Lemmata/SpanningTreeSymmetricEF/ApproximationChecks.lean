module

/-
  Concrete and adversarial checks for the approximation modules.
  No geometric interface is assumed in the SDP feasibility examples.
-/
public import Lemmata.SpanningTreeSymmetricEF.Approximation
public import Lemmata.SpanningTreeSymmetricEF.SDPBounds

@[expose] public section


namespace Lemmata.SpanningTreeSymmetricEF.ApproximationChecks

open scoped BigOperators
open SDPBounds
noncomputable section

/-- A concrete clockwise orientation of C4. -/
def cycleY : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0]

def cycleSigns : Fin 4 → ℝ := ![1, -1, 1, -1]

def cycleX : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => cycleSigns i * cycleSigns j

/-- The actual four-cycle SDP witness, including its PSD constraint. -/
theorem four_cycle_feasible : Feasible cycleY cycleX := by
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num [cycleY]
  · intro i
    fin_cases i <;> norm_num [cycleY]
  · intro i
    fin_cases i <;> norm_num [cycleY, Fin.sum_univ_succ]
  · convert Matrix.posSemidef_vecMulVec_self_star cycleSigns using 1
    ext i j
    simp [cycleX, Matrix.vecMulVec_apply]
  · intro i
    fin_cases i <;> norm_num [cycleX, cycleSigns]
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      norm_num [edgeWeights, cycleY, cycleX, cycleSigns] at *

theorem four_cycle_weight : internalWeight (edgeWeights cycleY) Finset.univ = 4 := by
  norm_num [internalWeight, edgeWeights, cycleY, Fin.sum_univ_succ]

theorem four_cycle_scaled_bound :
    (3 / 4 : ℝ) * internalWeight (edgeWeights cycleY) Finset.univ = 3 := by
  rw [four_cycle_weight]
  norm_num

/-- The full triangle has an outdegree-feasible orientation but is excluded
by the PSD cut constraints. -/
def triangleY : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, 1, 0; 0, 0, 1; 1, 0, 0]

theorem full_triangle_not_feasible (X : Matrix (Fin 3) (Fin 3) ℝ) :
    ¬ Feasible triangleY X := by
  intro h
  have ht := h.triangle_bound Finset.univ (by simp)
  norm_num [internalWeight, edgeWeights, triangleY, Fin.sum_univ_succ] at ht

theorem empty_subset_weight (y : Matrix (Fin 4) (Fin 4) ℝ) :
    internalWeight (edgeWeights y) ∅ = 0 := by simp [internalWeight]

theorem singleton_subset_weight (i : Fin 4) :
    internalWeight (edgeWeights cycleY) {i} = 0 := by
  simp [internalWeight, edgeWeights, four_cycle_feasible.diagonal_y]

/-- An inhabited nonnegative-maximization model, not an inconsistent interface. -/
theorem singleton_approximation_model :
    Approximation.MaxApproximation (fun (_ : Unit) (_ : Unit) => (1 : ℝ))
      {fun _ => 1} 1 := by
  constructor
  · norm_num
  · intro t; simp
  · intro c hc x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact ⟨(), by simp [Approximation.objective]⟩

theorem bb_zero_boundary :
    (1 - 6 / (6 : ℝ)) / ((6 - 3) * (6 - 4)) = 0 := by norm_num

theorem bb_negative_below_range :
    (1 - 6 / (5 : ℝ)) / ((5 - 3) * (5 - 4)) = -(1 / 10 : ℝ) := by norm_num

theorem threshold_endpoint :
    (3 / 2 : ℝ) * (1 - 1 / 9) = 4 / 3 := by norm_num

theorem n13_size_and_factor_checks :
    3 * Nat.choose 13 2 + 2 * 13 < Nat.choose 13 3 ∧
      (4 / 3 : ℝ) < (3 / 2 : ℝ) * (1 - 1 / 13) := by
  constructor
  · decide
  · norm_num

end
end Lemmata.SpanningTreeSymmetricEF.ApproximationChecks
