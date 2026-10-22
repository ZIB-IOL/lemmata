module

public import Lemmata.Centroid.Proof.Construction

@[expose] public section

open scoped BigOperators
open Classical

namespace Lemmata.Centroid.Tensor

noncomputable section

variable {F ι : Type*} [Field F]
variable {V W : ι → Type*} [∀ i, Fintype (V i)] [∀ i, Fintype (W i)]

def relabel (c : ∀ i, V i ≃ W i) (T : Tensor F ι V) : Tensor F ι W :=
  restrict (fun i => (c i).symm) T

omit [∀ i, Fintype (V i)] [∀ i, Fintype (W i)] in
theorem relabel_update (c : ∀ i, V i ≃ W i) (x : ∀ j, W j) (i : ι) (a : V i) :
    (fun j => (c j).symm (Function.update x i (c i a) j)) =
      Function.update (fun j => (c j).symm (x j)) i a := by
  funext j
  by_cases h : j = i
  · subst j; simp
  · simp [Function.update_of_ne h]

omit [Field F] [∀ i, Fintype (V i)] [∀ i, Fintype (W i)] in
theorem relabel_injective (c : ∀ i, V i ≃ W i) :
    Function.Injective (relabel (F := F) c) := by
  intro T S h
  ext x
  have hx := congrFun h (fun i => c i (x i))
  simpa [relabel, restrict] using hx

omit [Field F] [∀ i, Fintype (V i)] [∀ i, Fintype (W i)] in
@[simp] theorem relabel_symm (c : ∀ i, V i ≃ W i) (T : Tensor F ι V) :
    relabel (fun i => (c i).symm) (relabel c T) = T := by
  ext x
  simp [relabel, restrict]

theorem contraction_relabel (c : ∀ i, V i ≃ W i) (T : Tensor F ι V)
    (i : ι) (f : W i → F) :
    contraction (relabel c T) i f =
      relabel c (contraction T i (fun a => f (c i a))) := by
  ext x
  simp only [contraction_apply, relabel, restrict, Lemmata.TensorRank.Tensor.reindex]
  rw [← (c i).sum_comp]
  apply Finset.sum_congr rfl
  intro a ha
  rw [relabel_update]

theorem Concise.relabel {T : Tensor F ι V} (hT : Concise T) (c : ∀ i, V i ≃ W i) :
    Concise (Tensor.relabel c T) := by
  intro i f g h
  rw [contraction_relabel, contraction_relabel] at h
  have hh := hT i (relabel_injective c h)
  ext b
  simpa using congrFun hh ((c i).symm b)

def relabelMatrices (c : ∀ i, V i ≃ W i) (A : ∀ i, Matrix (V i) (V i) F) :
    ∀ i, Matrix (W i) (W i) F :=
  fun i a b => A i ((c i).symm a) ((c i).symm b)

theorem legAction_relabel (c : ∀ i, V i ≃ W i) (T : Tensor F ι V)
    (A : ∀ i, Matrix (V i) (V i) F) (i : ι) :
    legAction (relabel c T) i (relabelMatrices c A i) = relabel c (legAction T i (A i)) := by
  ext x
  simp only [legAction_apply, relabel, restrict, relabelMatrices, Lemmata.TensorRank.Tensor.reindex]
  rw [← (c i).sum_comp]
  apply Finset.sum_congr rfl
  intro a ha
  rw [relabel_update, Equiv.symm_apply_apply]

def centroidRelabel (c : ∀ i, V i ≃ W i) (T : Tensor F ι V) :
    centroid T →ₗ[F] centroid (relabel c T) where
  toFun A := ⟨relabelMatrices c A.val, fun i j => by
    rw [legAction_relabel, legAction_relabel, A.property i j]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem centroidRelabel_injective (c : ∀ i, V i ≃ W i) (T : Tensor F ι V) :
    Function.Injective (centroidRelabel c T) := by
  intro A B h
  apply Subtype.ext
  funext i a b
  have hh := congrArg (fun X : centroid (relabel c T) => X.val i (c i a) (c i b)) h
  change A.val i ((c i).symm (c i a)) ((c i).symm (c i b)) =
    B.val i ((c i).symm (c i a)) ((c i).symm (c i b)) at hh
  simpa using hh

theorem finrank_centroid_le_relabel [Fintype ι]
    (c : ∀ i, V i ≃ W i) (T : Tensor F ι V) :
    Module.finrank F (centroid T) ≤ Module.finrank F (centroid (relabel c T)) :=
  LinearMap.finrank_le_finrank_of_injective (centroidRelabel_injective c T)

theorem finrank_centroid_relabel [Fintype ι]
    (c : ∀ i, V i ≃ W i) (T : Tensor F ι V) :
    Module.finrank F (centroid (relabel c T)) = Module.finrank F (centroid T) := by
  apply le_antisymm
  · have h := finrank_centroid_le_relabel (fun i => (c i).symm) (relabel c T)
    have he : relabel (fun i => (c i).symm) (relabel c T) = T := relabel_symm c T
    exact h.trans_eq (congrArg (fun S : Tensor F ι V => Module.finrank F (centroid S)) he)
  · exact finrank_centroid_le_relabel c T

omit [∀ i, Fintype (V i)] [∀ i, Fintype (W i)] in
theorem RationalBorderRankAtMost.relabel [Fintype ι] {T : Tensor F ι V} {r : ℕ}
    (hT : RationalBorderRankAtMost T r) (c : ∀ i, V i ≃ W i) :
    RationalBorderRankAtMost (Tensor.relabel c T) r := hT.restrict (fun i => (c i).symm)

end

end Lemmata.Centroid.Tensor
