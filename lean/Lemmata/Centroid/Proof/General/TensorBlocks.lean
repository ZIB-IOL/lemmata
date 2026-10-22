module

public import Lemmata.Centroid.Proof.General.Decomposition
public import Lemmata.Centroid.Proof.Tensor.Maps
public import Lemmata.Centroid.Proof.Tensor.Support

@[expose] public section

open scoped BigOperators Matrix
open Classical

noncomputable section

namespace Lemmata.Centroid.Tensor

theorem oneSlice_self {F ι : Type*} [Field F] {V : ι → Type*}
    [∀ i, Fintype (V i)] (T : Tensor F ι V) (i : ι) (x : ∀ i, V i) :
    oneSlice i x T (x i) = T x := by
  simp only [oneSlice_apply, Function.update_eq_self]

theorem legAction_eq_mulVec_slice {F ι : Type*} [Field F] {V : ι → Type*}
    [∀ i, Fintype (V i)] (T : Tensor F ι V) (i : ι)
    (A : Matrix (V i) (V i) F) (x : ∀ i, V i) :
    legAction T i A x = (A *ᵥ oneSlice i x T) (x i) := rfl

end Lemmata.Centroid.Tensor

namespace Lemmata.Centroid.General.TensorBlocks

variable {F A κ : Type*} [Field F] [CommRing A] [Algebra F A] [Fintype κ]
variable {B : κ → Type*} [∀ m, CommRing (B m)] [∀ m, Algebra F (B m)]
variable {V : Fin 3 → Type*} [∀ i, Fintype (V i)]

variable (e : A ≃ₐ[F] ∀ m, B m) (ρ : ∀ i, A →ₐ[F] Module.End F (V i → F))

def blockSize (m : κ) (i : Fin 3) : ℕ := Module.finrank F (blockSpace e (ρ i) m)

abbrev BlockIndex (i : Fin 3) := Σ m, Fin (blockSize e ρ m i)

def encoding (i : Fin 3) : (V i → F) ≃ₗ[F] (BlockIndex e ρ i → F) :=
  (blockCoordinates e (ρ i)).trans
    ((LinearEquiv.piCongrRight fun m => (Module.finBasis F (blockSpace e (ρ i) m)).equivFun).trans
      (LinearEquiv.piCurry F (fun m (_ : Fin (blockSize e ρ m i)) => F)).symm)

@[simp] theorem encoding_apply (i : Fin 3) (v : V i → F) (p : BlockIndex e ρ i) :
    encoding e ρ i v p = (Module.finBasis F (blockSpace e (ρ i) p.1)).equivFun
      (blockCoordinates e (ρ i) v p.1) p.2 := rfl

theorem encoding_projection (i : Fin 3) (v : V i → F) (m : κ) (p : BlockIndex e ρ i) :
    encoding e ρ i (ρ i (Linear.blockIdempotent e m) v) p =
      if p.1 = m then encoding e ρ i v p else 0 := by
  have h := blockCoordinates_projection e (ρ i) v m p.1
  by_cases hm : p.1 = m
  · simp only [hm, ite_true] at h ⊢
    have h' : blockCoordinates e (ρ i) (ρ i (Linear.blockIdempotent e m) v) p.1 =
        blockCoordinates e (ρ i) v p.1 := Subtype.ext h
    simp only [encoding_apply, h']
  · simp only [hm, ite_false] at h ⊢
    have h' : blockCoordinates e (ρ i) (ρ i (Linear.blockIdempotent e m) v) p.1 = 0 :=
      Subtype.ext h
    simp only [encoding_apply, h', map_zero]
    rfl

def algebraMatrices (a : A) : ∀ i, Matrix (V i) (V i) F :=
  fun i => LinearMap.toMatrix' (ρ i a)

def transformed (T : Lemmata.Centroid.Tensor F (Fin 3) V) :
    Lemmata.Centroid.Tensor F (Fin 3) (BlockIndex e ρ) :=
  Tensor.localEquiv (encoding e ρ) T

def transformedMatrices (a : A) : ∀ i, Matrix (BlockIndex e ρ i) (BlockIndex e ρ i) F :=
  Tensor.conjugateFamily (encoding e ρ) (algebraMatrices ρ a)

theorem transformed_projection_mulVec (i : Fin 3) (m : κ) (w : BlockIndex e ρ i → F)
    (p : BlockIndex e ρ i) :
    (transformedMatrices e ρ (Linear.blockIdempotent e m) i *ᵥ w) p =
      if p.1 = m then w p else 0 := by
  obtain ⟨v, rfl⟩ := (encoding e ρ i).surjective w
  have h := congrArg (fun M : Matrix (BlockIndex e ρ i) (V i) F => M *ᵥ v)
    (Tensor.matrixConjugation_intertwines (encoding e ρ i)
      (LinearMap.toMatrix' (ρ i (Linear.blockIdempotent e m))))
  have h' : transformedMatrices e ρ (Linear.blockIdempotent e m) i *ᵥ encoding e ρ i v =
      encoding e ρ i (ρ i (Linear.blockIdempotent e m) v) := by
    change Tensor.matrixConjugation (encoding e ρ i)
        (LinearMap.toMatrix' (ρ i (Linear.blockIdempotent e m))) *ᵥ
        (encoding e ρ i).toLinearMap v =
      (encoding e ρ i).toLinearMap (ρ i (Linear.blockIdempotent e m) v)
    simpa only [← Matrix.mulVec_mulVec, Tensor.matrixOfEquiv,
      LinearMap.toMatrix'_mulVec] using h
  rw [h', encoding_projection]

theorem transformed_projection_action (T : Lemmata.Centroid.Tensor F (Fin 3) V)
    (i : Fin 3) (m : κ) (x : ∀ i, BlockIndex e ρ i) :
    Tensor.legAction (transformed e ρ T) i (transformedMatrices e ρ (Linear.blockIdempotent e m) i) x =
      if (x i).1 = m then transformed e ρ T x else 0 := by
  rw [Tensor.legAction_eq_mulVec_slice, transformed_projection_mulVec, Tensor.oneSlice_self]

theorem transformed_mixed_zero (T : Lemmata.Centroid.Tensor F (Fin 3) V)
    (hbalanced : ∀ a, algebraMatrices ρ a ∈ Tensor.centroid T)
    (x : ∀ i, BlockIndex e ρ i) {i j : Fin 3} (hij : (x i).1 ≠ (x j).1) :
    transformed e ρ T x = 0 := by
  have h := Tensor.conjugateFamily_mem_centroid (encoding e ρ)
    (hbalanced (Linear.blockIdempotent e (x i).1))
  have hx := congrFun (h i j) x
  change Tensor.legAction (transformed e ρ T) i
      (transformedMatrices e ρ (Linear.blockIdempotent e (x i).1) i) x =
    Tensor.legAction (transformed e ρ T) j
      (transformedMatrices e ρ (Linear.blockIdempotent e (x i).1) j) x at hx
  rw [transformed_projection_action, transformed_projection_action] at hx
  simpa only [ite_true, Ne.symm hij, ite_false] using hx

end Lemmata.Centroid.General.TensorBlocks
