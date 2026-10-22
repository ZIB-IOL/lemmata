module

public import Lemmata.Centroid.Proof.Construction.Frames

@[expose] public section

open scoped BigOperators
open Classical

namespace Lemmata.Centroid.Construction

noncomputable section

variable {K α β : Type*} [Field K] [Fintype α] [Fintype β] [DecidableEq α]

def weightedColumn (M : Matrix α α K) (D : α → β → K) (q : α × β) : α × β → K :=
  fun p => M p.1 q.1 * D p.1 q.2 * if p.2 = q.2 then 1 else 0

theorem weighted_columns_span (M : Matrix α α K) (hM : IsUnit M)
    (D : α → β → K) (hD : ∀ a b, D a b ≠ 0) :
    Submodule.span K (Set.range (weightedColumn M D)) = ⊤ := by
  let A : Matrix (α × β) (α × β) K := fun p q => weightedColumn M D q p
  have hrows : LinearIndependent K A.row := by
    convert BigCentroid.Grid.block_rows_independent M
      (Matrix.linearIndependent_rows_of_isUnit hM) D hD using 1
    ext p q
    change M p.1 q.1 * D p.1 q.2 * (if p.2 = q.2 then 1 else 0) =
      if p.2 = q.2 then D p.1 p.2 * M p.1 q.1 else 0
    by_cases h : p.2 = q.2
    · rw [ite_eq_left h, ite_eq_left h, mul_one, h, mul_comm]
    · simp only [ite_eq_right h, mul_zero]
  have hA : IsUnit A := Matrix.linearIndependent_rows_iff_isUnit.mp hrows
  have hrange : LinearMap.range A.mulVecLin = ⊤ :=
    LinearMap.range_eq_top.mpr (Matrix.mulVec_surjective_iff_isUnit.mpr hA)
  have he : A.col = weightedColumn M D := rfl
  rw [Matrix.range_mulVecLin, he] at hrange
  exact hrange

def sliceEquiv (e : (α → K) ≃ₗ[K] (α → K)) :
    ((α × β) → K) ≃ₗ[K] ((α × β) → K) where
  toFun f p := e (fun a => f (a, p.2)) p.1
  invFun f p := e.symm (fun a => f (a, p.2)) p.1
  left_inv f := by
    ext p
    change e.symm (e (fun a => f (a, p.2))) p.1 = f p
    rw [e.symm_apply_apply]
  right_inv f := by
    ext p
    change e (e.symm (fun a => f (a, p.2))) p.1 = f p
    rw [e.apply_symm_apply]
  map_add' f g := by
    ext p
    change e ((fun a => f (a, p.2)) + (fun a => g (a, p.2))) p.1 = _
    rw [map_add]
    rfl
  map_smul' c f := by
    ext p
    change e (c • (fun a => f (a, p.2))) p.1 = _
    rw [map_smul]
    rfl

def normalizedColumn (e : (α → K) ≃ₗ[K] (α → K))
    (M : Matrix α α K) (D : α → β → K) (q : α × β) : α × β → K :=
  fun p => e (fun a => M a q.1 * D a q.2) p.1 * if p.2 = q.2 then 1 else 0

omit [Fintype α] [Fintype β] [DecidableEq α] in
theorem normalizedColumn_eq (e : (α → K) ≃ₗ[K] (α → K))
    (M : Matrix α α K) (D : α → β → K) (q : α × β) :
    normalizedColumn e M D q = sliceEquiv e (weightedColumn M D q) := by
  ext p
  change e (fun a => M a q.1 * D a q.2) p.1 * (if p.2 = q.2 then 1 else 0) =
    e (fun a => M a q.1 * D a q.2 * (if p.2 = q.2 then 1 else 0)) p.1
  by_cases h : p.2 = q.2
  · simp only [ite_eq_left h, mul_one]
  · simp only [ite_eq_right h, mul_zero]
    change 0 = e (0 : α → K) p.1
    rw [map_zero]
    rfl

theorem normalized_columns_span (e : (α → K) ≃ₗ[K] (α → K))
    (M : Matrix α α K) (hM : IsUnit M) (D : α → β → K) (hD : ∀ a b, D a b ≠ 0) :
    Submodule.span K (Set.range (normalizedColumn e M D)) = ⊤ := by
  have hmap := congrArg (Submodule.map (sliceEquiv (β := β) e).toLinearMap)
    (weighted_columns_span M hM D hD)
  rw [LinearMap.map_span, Submodule.map_top, LinearEquiv.range, ← Set.range_comp] at hmap
  have he : (fun q => sliceEquiv e (weightedColumn M D q)) = normalizedColumn e M D := by
    funext q
    exact (normalizedColumn_eq e M D q).symm
  change Submodule.span K (Set.range (fun q => sliceEquiv e (weightedColumn M D q))) = ⊤ at hmap
  rw [he] at hmap
  exact hmap

theorem normalized_expansion (e : (α → K) ≃ₗ[K] (α → K)) (u : α → K) (a : α) :
    e u a = ∑ b, u b * e (Pi.single b 1) a := by
  have hex : u = ∑ b, u b • Pi.single b (1 : K) := by
    ext a
    simp [Pi.single_apply, smul_eq_mul, mul_ite]
  calc
    e u a = e (∑ b, u b • Pi.single b (1 : K)) a := congrArg (fun v => e v a) hex
    _ = _ := by rw [map_sum]; simp [map_smul, smul_eq_mul]

end

end Lemmata.Centroid.Construction
