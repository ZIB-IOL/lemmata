module

public import Lemmata.SpanningTreeSymmetricEF.QuadraticRaw

@[expose] public section


/-! Explicit deletion of one parent coordinate for each selected full root.
The reconstructed coefficient is a fixed linear combination. -/
namespace Lemmata.SpanningTreeSymmetricEF.QuadraticCompression
open scoped BigOperators Classical
open Matrix FormulationStructure QuadraticTrees QuadraticAlgebra QuadraticValues QuadraticCore QuadraticRaw
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]

structure Deletion (R : RootFamily V) where
  roots : Finset V
  child : V → V
  child_mem : ∀ r ∈ roots, child r ∈ R.active r
  full : ∀ r ∈ roots, R.active r = Finset.univ.erase r

def removed (R : RootFamily V) (D : Deletion R) : Label R → Prop
  | .inl _ => False
  | .inr p => p.val.1 ∈ D.roots ∧ p.val.2 = D.child p.val.1

abbrev Kept (R : RootFamily V) (D : Deletion R) := {j : Label R // ¬removed R D j}

def edgeCoeff (R : RootFamily V) (D : Deletion R) (e : Edge V) : Kept R D → ℝ :=
  Pi.single ⟨.inl e,by simp [removed]⟩ 1

def keptParent (R : RootFamily V) (D : Deletion R) (r v : V) : Kept R D → ℝ :=
  if h : v ∈ R.active r ∧ ¬(r ∈ D.roots ∧ v = D.child r) then
    Pi.single ⟨.inr ⟨(r,v),h.1⟩,h.2⟩ 1 else 0

def parentCoeff (R : RootFamily V) (D : Deletion R) (r v : V) : Kept R D → ℝ :=
  if v ∈ R.active r then
    if r ∈ D.roots ∧ v = D.child r then
      (∑ e, edgeCoeff R D e) - ∑ w, keptParent R D r w
    else keptParent R D r v
  else 0

def treeMatrix (R : RootFamily V) (D : Deletion R) (T : SimpleGraph V) (hT : T.IsTree) :
    Matrix (Kept R D) (Edge V) ℝ := (QuadraticRaw.treeMatrix R T hT).submatrix Subtype.val id

@[simp] theorem edge_row (R : RootFamily V) (D : Deletion R) (T : SimpleGraph V) (hT : T.IsTree) (e : Edge V) :
    (treeMatrix R D T hT)ᵀ *ᵥ edgeCoeff R D e = edgeValue T e := by
  simp only [edgeCoeff,Matrix.mulVec_single_one]
  rfl

@[simp] theorem keptParent_row (R : RootFamily V) (D : Deletion R) (T : SimpleGraph V) (hT : T.IsTree)
    (r v : V) : (treeMatrix R D T hT)ᵀ *ᵥ keptParent R D r v =
      if v ∈ R.active r ∧ ¬(r ∈ D.roots ∧ v = D.child r) then parentVector hT r v else 0 := by
  by_cases hv : v ∈ R.active r ∧ ¬(r ∈ D.roots ∧ v = D.child r)
  · simp only [keptParent,dif_pos hv,if_pos hv,Matrix.mulVec_single_one]
    rfl
  · simp only [keptParent,dif_neg hv,if_neg hv,Matrix.mulVec_zero]

theorem parentCoeff_zero (R : RootFamily V) (D : Deletion R) (r v : V) (hv : v ∉ R.active r) :
    parentCoeff R D r v = 0 := by simp [parentCoeff,hv]

/-- The full-root relation holds coordinatewise for every actual tree. -/
theorem full_root_relation (T : SimpleGraph V) (hT : T.IsTree) (r : V) :
    (∑ v, parentVector hT r v) = ∑ e, edgeValue T e := by
  ext e
  rw [Finset.sum_apply,parentVector_sum]
  simp only [Finset.sum_apply,edgeValue]
  rw [Finset.sum_eq_single e]
  · by_cases he : e.val ∈ T.edgeSet <;> simp [he,Pi.single_apply]
  · intro f _ hfe
    by_cases hf : f.val ∈ T.edgeSet <;> simp [hf,hfe.symm]
  · intro hn
    exact (hn (Finset.mem_univ e)).elim

/-- Reconstructing deleted coordinates really recovers the original tree vectors. -/
theorem parent_row (R : RootFamily V) (D : Deletion R) (T : SimpleGraph V) (hT : T.IsTree)
    (r v : V) : (treeMatrix R D T hT)ᵀ *ᵥ parentCoeff R D r v = parentValue hT R.active r v := by
  by_cases ha : v ∈ R.active r
  · by_cases hd : r ∈ D.roots ∧ v = D.child r
    · have hv : v ≠ r := fun he => R.not_root r (he ▸ ha)
      have hfull := D.full r hd.1
      simp only [parentCoeff,if_pos ha,if_pos hd,Matrix.mulVec_sub,Matrix.mulVec_sum,
        edge_row,keptParent_row,parentValue,if_pos ha]
      have hkeep (w : V) :
          (if w ∈ R.active r ∧ ¬(r ∈ D.roots ∧ w = D.child r) then parentVector hT r w else 0) =
          if w ≠ v then parentVector hT r w else 0 := by
        by_cases hw : w = r
        · subst w; simp [R.not_root,parentVector_zero,hv.symm]
        · simp [hfull,hd.1,← hd.2,hw]
      simp_rw [hkeep]
      rw [← full_root_relation T hT r]
      have hsub : (∑ w, if w ≠ v then parentVector hT r w else 0) =
          ∑ w : {i : V // i ≠ v}, parentVector hT r w.val := by
        rw [← Finset.sum_filter]
        exact Finset.sum_subtype (Finset.univ.filter (fun w : V => w ≠ v))
          (by simp) (parentVector hT r)
      have hs : (∑ w, parentVector hT r w) = parentVector hT r v +
          ∑ w, if w ≠ v then parentVector hT r w else 0 := by
        rw [hsub]
        exact Fintype.sum_eq_add_sum_subtype_ne _ v
      rw [hs]
      abel
    · simp [parentCoeff,ha,hd,parentValue,keptParent_row]
  · simp [parentCoeff,ha,parentValue]

/-- Actual full exactness survives deletion; there is no assumed compression oracle. -/
theorem exact_image [Nonempty V] (R : RootFamily V) (D : Deletion R) :
    image R (edgeCoeff R D) (parentCoeff R D) =
      convexHull ℝ (Set.range (ApproximationUpper.treeIncidence (V := V))) := by
  apply image_eq_tree_polytope R _ _ (parentCoeff_zero R D)
  intro T
  exact tree_witness_of_rows R _ _ T.val T.property (treeMatrix R D T.val T.property)
    (edge_row R D T.val T.property) (parent_row R D T.val T.property)

/-- Deleted labels are in bijection with the selected roots. -/
def removedEquiv (R : RootFamily V) (D : Deletion R) :
    {j : Label R // removed R D j} ≃ D.roots where
  toFun j := by
    rcases j with ⟨e | p,h⟩
    · exact False.elim h
    · exact ⟨p.val.1,h.1⟩
  invFun r := ⟨.inr ⟨(r.val,D.child r.val),D.child_mem r.val r.property⟩,r.property,rfl⟩
  left_inv j := by
    rcases j with ⟨e | p,h⟩
    · exact False.elim h
    · apply Subtype.ext
      change Sum.inr (⟨(p.val.1,D.child p.val.1),D.child_mem p.val.1 h.1⟩ : ParentIndex R) = Sum.inr p
      apply congrArg Sum.inr
      apply Subtype.ext
      exact Prod.ext rfl h.2.symm
  right_inv r := rfl

theorem compressed_order (R : RootFamily V) (D : Deletion R) :
    Fintype.card (Kept R D) = Fintype.card (Label R) - D.roots.card := by
  rw [Fintype.card_subtype_compl,Fintype.card_congr (removedEquiv R D),Fintype.card_coe]

end
end Lemmata.SpanningTreeSymmetricEF.QuadraticCompression
