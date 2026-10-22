module

public import Lemmata.SpanningTreeSymmetricEF.QuadraticCore

@[expose] public section


/-! Concrete uncompressed exact lifts. All roots share one matrix. -/
namespace Lemmata.SpanningTreeSymmetricEF.QuadraticRaw
open scoped BigOperators Classical
open Matrix FormulationStructure QuadraticTrees QuadraticAlgebra QuadraticValues QuadraticCore
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev ParentIndex (R : RootFamily V) := {p : V × V // p.2 ∈ R.active p.1}
abbrev Label (R : RootFamily V) := Edge V ⊕ ParentIndex R

def edgeCoeff (R : RootFamily V) (e : Edge V) : Label R → ℝ := Pi.single (.inl e) 1

def parentCoeff (R : RootFamily V) (r v : V) : Label R → ℝ :=
  if h : v ∈ R.active r then Pi.single (.inr ⟨(r,v),h⟩) 1 else 0

theorem parentCoeff_zero (R : RootFamily V) (r v : V) (hv : v ∉ R.active r) :
    parentCoeff R r v = 0 := by simp [parentCoeff,hv]

def treeMatrix (R : RootFamily V) (T : SimpleGraph V) (hT : T.IsTree) :
    Matrix (Label R) (Edge V) ℝ
  | .inl e => edgeValue T e
  | .inr p => parentVector hT p.val.1 p.val.2

@[simp] theorem treeMatrix_edge (R : RootFamily V) (T : SimpleGraph V) (hT : T.IsTree) (e : Edge V) :
    (treeMatrix R T hT)ᵀ *ᵥ edgeCoeff R e = edgeValue T e := by
  simp only [edgeCoeff, Matrix.mulVec_single_one]
  rfl

@[simp] theorem treeMatrix_parent (R : RootFamily V) (T : SimpleGraph V) (hT : T.IsTree) (r v : V) :
    (treeMatrix R T hT)ᵀ *ᵥ parentCoeff R r v = parentValue hT R.active r v := by
  by_cases hv : v ∈ R.active r
  · simp only [parentCoeff,dif_pos hv,parentValue,if_pos hv,Matrix.mulVec_single_one]
    rfl
  · simp [parentCoeff,hv,parentValue]

/-- Each actual tree has the displayed finite Gram witness, without rank constraints. -/
theorem tree_witness (R : RootFamily V) (T : SimpleGraph V) (hT : T.IsTree) :
    ApproximationUpper.graphIncidence T ∈ image R (edgeCoeff R) (parentCoeff R) := by
  let H := treeMatrix R T hT
  let Y := H * Hᵀ
  have hY : Y.PosSemidef := by
    simpa only [Y, Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_self_mul_conjTranspose H
  have hpair (u v : Label R → ℝ) :
      pair Y u v = pair (1 : Matrix (Edge V) (Edge V) ℝ) (Hᵀ *ᵥ u) (Hᵀ *ᵥ v) := by
    simpa [Y] using pair_congruence (1 : Matrix (Edge V) (Edge V) ℝ) H u v
  have he := tree_equations hT R.active R.not_root
  have hx : coordinates (edgeCoeff R) Y = treeCoordinates T := by
    ext e
    rw [coordinates,hpair,treeMatrix_edge]
    exact he.diagonal e
  refine ⟨Y,hY,?_,?_⟩
  · rw [hx]
    constructor
    · intro e; rw [hpair,treeMatrix_edge]; exact he.diagonal e
    · intro e f hf; rw [hpair,treeMatrix_edge,treeMatrix_edge]; exact he.edge e f hf
    · intro r v w; rw [hpair,treeMatrix_parent,treeMatrix_parent]; exact he.parent r v w
    · intro r v e hv; rw [hpair,treeMatrix_edge,treeMatrix_parent]; exact he.incidence r v e hv
    · intro r e he'
      simp only [hpair,H,treeMatrix_edge,treeMatrix_parent]
      exact he.conservation r e he'
    · exact he.cardinality
  · rw [hx,extend_tree]

/-- Full affine projection equals the convex hull of actual spanning trees. -/
theorem exact_image [Nonempty V] (R : RootFamily V) :
    image R (edgeCoeff R) (parentCoeff R) =
      convexHull ℝ (Set.range (ApproximationUpper.treeIncidence (V := V))) :=
  image_eq_tree_polytope R _ _ (parentCoeff_zero R)
    (fun T => tree_witness R T.val T.property)

/-- The symmetric root family; no vertex order is used. -/
def allRoots : RootFamily V where
  active r := Finset.univ.erase r
  not_root r := by simp
  cover S hS := by
    obtain ⟨r,hr⟩ := hS
    exact ⟨r,hr,by intro v hv; simpa using (Finset.mem_erase.mp hv).1⟩

/-- The asymmetric family uses only larger vertices as children. -/
def orderedRoots [LinearOrder V] : RootFamily V where
  active r := Finset.univ.filter (fun v => r < v)
  not_root r := by simp
  cover S hS := ⟨S.min' hS,S.min'_mem hS,by
    intro v hv
    simpa using S.min'_lt_of_mem_erase_min' hS hv⟩

theorem symmetric_exact [Nonempty V] :
    image (allRoots (V := V)) (edgeCoeff allRoots) (parentCoeff allRoots) =
      convexHull ℝ (Set.range (ApproximationUpper.treeIncidence (V := V))) := exact_image _

theorem asymmetric_exact [Nonempty V] [LinearOrder V] :
    image (orderedRoots (V := V)) (edgeCoeff orderedRoots) (parentCoeff orderedRoots) =
      convexHull ℝ (Set.range (ApproximationUpper.treeIncidence (V := V))) := exact_image _

theorem symmetric_order : Fintype.card (Label (allRoots (V := V))) =
    3 * (Fintype.card V).choose 2 := by
  have e : ParentIndex (allRoots (V := V)) ≃ Arc V :=
    Equiv.subtypeEquivRight (by intro p; simp [allRoots,ne_comm])
  rw [Fintype.card_sum,Fintype.card_congr e,card_arcs,card_edges]
  omega

end
end Lemmata.SpanningTreeSymmetricEF.QuadraticRaw
