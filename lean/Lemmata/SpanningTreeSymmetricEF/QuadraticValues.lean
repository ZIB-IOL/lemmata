module

public import Lemmata.SpanningTreeSymmetricEF.QuadraticAlgebra

@[expose] public section


/-! Concrete tree vectors satisfying every affine equation. These are proof
witnesses; the fixed coefficient vectors of the lift are defined separately. -/
namespace Lemmata.SpanningTreeSymmetricEF.QuadraticValues
open scoped BigOperators Classical
open Matrix SimpleGraph FormulationStructure QuadraticTrees QuadraticAlgebra
noncomputable section
variable {V J K : Type*} [Fintype V] [DecidableEq V]
variable [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]

theorem pair_one (a b : J → ℝ) : pair (1 : Matrix J J ℝ) a b = a ⬝ᵥ b := by
  simp [pair, Matrix.toBilin'_apply']

/-- Pulling a PSD matrix back along fixed coefficient vectors is linear. -/
theorem pair_congruence (Y : Matrix K K ℝ) (C : Matrix J K ℝ) (a b : J → ℝ) :
    pair (C * Y * Cᵀ) a b = pair Y (Cᵀ *ᵥ a) (Cᵀ *ᵥ b) := by
  simp only [pair, Matrix.toBilin'_apply', ← mulVec_mulVec, dotProduct_mulVec, mulVec_transpose]

def edgeValue (T : SimpleGraph V) (e : Edge V) : Edge V → ℝ :=
  if e.val ∈ T.edgeSet then Pi.single e 1 else 0

def parentValue {T : SimpleGraph V} (hT : T.IsTree) (active : V → Finset V)
    (r v : V) : Edge V → ℝ := if v ∈ active r then parentVector hT r v else 0

def treeCoordinates (T : SimpleGraph V) (e : Edge V) : ℝ :=
  if e.val ∈ T.edgeSet then 1 else 0

theorem sum_nondiagonal (f : Sym2 V → ℝ) (hd : ∀ e, e.IsDiag → f e = 0) :
    (∑ e : Edge V, f e.val) = ∑ e, f e := by
  rw [← Finset.sum_subtype (Finset.univ.filter (fun e : Sym2 V => ¬e.IsDiag)) (by simp)]
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro e _ he
  exact hd e (by simpa using he)

theorem treeCoordinates_mass {T : SimpleGraph V} (hT : T.IsTree) :
    (∑ e, treeCoordinates T e) = (Fintype.card V : ℝ) - 1 := by
  change (∑ e : Edge V, ApproximationUpper.graphIncidence T e.val) = _
  rw [sum_nondiagonal]
  · exact ApproximationSharpness.tree_mass hT
  · intro e he
    simp [ApproximationUpper.graphIncidence, T.not_isDiag_of_mem_edgeSet, he]

/-- All tree-vector equations, including conservation and nonnegativity rows. -/
theorem tree_equations {T : SimpleGraph V} (hT : T.IsTree) (active : V → Finset V)
    (hroot : ∀ r, r ∉ active r) :
    Equations active (edgeValue T) (parentValue hT active) (1 : Matrix (Edge V) (Edge V) ℝ)
      (treeCoordinates T) := by
  constructor
  · intro e
    simp only [pair_one]
    by_cases he : e.val ∈ T.edgeSet <;> simp [edgeValue, treeCoordinates, he]
  · intro e f hef
    simp only [pair_one]
    by_cases he : e.val ∈ T.edgeSet <;> by_cases hf : f.val ∈ T.edgeSet <;>
      simp [edgeValue, he, hf, hef, hef.symm]
  · intro r v w
    simp only [pair_one]
    by_cases hv : v ∈ active r <;> by_cases hw : w ∈ active r
    · have hvr : v ≠ r := fun he => hroot r (he ▸ hv)
      simp [parentValue, hv, hw, parentVector_orthonormal, hvr]
    · have hvw : v ≠ w := fun he => hw (he ▸ hv)
      simp [parentValue, hv, hw, hvw]
    · simp [parentValue, hv, hw]
    · simp [parentValue, hv, hw]
  · intro r v e hv
    simp only [pair_one]
    by_cases he : e.val ∈ T.edgeSet <;> by_cases ha : v ∈ active r <;>
      simp [edgeValue, parentValue, he, ha, parentVector_incidence hT r v e hv]
  · intro r e he
    simp only [pair_one]
    by_cases heT : e.val ∈ T.edgeSet
    · simp only [edgeValue, if_pos heT, treeCoordinates, single_dotProduct, one_mul]
      have hp : (∑ v ∈ active r, parentValue hT active r v e) =
          ∑ v ∈ active r, parentVector hT r v e := by
        apply Finset.sum_congr rfl
        intro v hv
        simp [parentValue, hv]
      rw [hp]
      calc
        _ = ∑ v, parentVector hT r v e := by
          apply Finset.sum_subset (Finset.subset_univ _)
          intro v _ hv
          by_cases hvr : v = r
          · subst v; simp [parentVector_zero]
          · exact parentVector_incidence hT r v e (fun hm => (he v hm).elim hvr hv)
        _ = 1 := by rw [parentVector_sum]; simp [heT]
    · simp [edgeValue, treeCoordinates, heT]
  · exact treeCoordinates_mass hT

end
end Lemmata.SpanningTreeSymmetricEF.QuadraticValues
