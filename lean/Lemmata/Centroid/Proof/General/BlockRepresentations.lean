module

public import Lemmata.Centroid.Proof.General.TensorBlocks
public import Lemmata.Centroid.Proof.Tensor.DirectBlocks

@[expose] public section

open scoped BigOperators Matrix
open Classical

noncomputable section

namespace Lemmata.Centroid.General.TensorBlocks

variable {F A κ : Type*} [Field F] [CommRing A] [Algebra F A] [Fintype κ]
variable {B : κ → Type*} [∀ m, CommRing (B m)] [∀ m, Algebra F (B m)]
variable {V : Fin 3 → Type*} [∀ i, Fintype (V i)]
variable (e : A ≃ₐ[F] ∀ m, B m) (ρ : ∀ i, A →ₐ[F] Module.End F (V i → F))

local instance finDecidableEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

def localMatrices (m : κ) (i : Fin 3) :
    B m →ₐ[F] Matrix (Fin (blockSize e ρ m i)) (Fin (blockSize e ρ m i)) F :=
  (algEquivMatrix (Module.finBasis F (blockSpace e (ρ i) m))).toAlgHom.comp
    (localRepresentation e (ρ i) m)

omit [Fintype κ] in
theorem localMatrices_injective (hρ : ∀ i, Function.Injective (ρ i)) (m : κ) (i : Fin 3) :
    Function.Injective (localMatrices e ρ m i) :=
  (algEquivMatrix (Module.finBasis F (blockSpace e (ρ i) m))).injective.comp
    (localRepresentation_injective e (ρ i) (hρ i) m)

omit [∀ i, Fintype (V i)] in
theorem blockCoordinates_inclusion (m : κ) (i : Fin 3) (b : B m) (v : V i → F) :
    blockCoordinates e (ρ i) (ρ i (blockInclusion e m b) v) m =
      localRepresentation e (ρ i) m b (blockCoordinates e (ρ i) v m) := by
  apply Subtype.ext
  change ρ i (Linear.blockIdempotent e m) (ρ i (blockInclusion e m b) v) =
    ρ i (blockInclusion e m b) (ρ i (Linear.blockIdempotent e m) v)
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_comm]

theorem localMatrices_mulVec (m : κ) (i : Fin 3) (b : B m) (v : V i → F) :
    localMatrices e ρ m i b *ᵥ
        (fun a => encoding e ρ i v ⟨m, a⟩) =
      fun a => encoding e ρ i (ρ i (blockInclusion e m b) v) ⟨m, a⟩ := by
  change LinearMap.toMatrix'
      (((Module.finBasis F (blockSpace e (ρ i) m)).equivFun.conjAlgEquiv F)
        (localRepresentation e (ρ i) m b)) *ᵥ
      (Module.finBasis F (blockSpace e (ρ i) m)).equivFun (blockCoordinates e (ρ i) v m) = _
  rw [LinearMap.toMatrix'_mulVec]
  change (Module.finBasis F (blockSpace e (ρ i) m)).equivFun
      (localRepresentation e (ρ i) m b
        ((Module.finBasis F (blockSpace e (ρ i) m)).equivFun.symm
          ((Module.finBasis F (blockSpace e (ρ i) m)).equivFun (blockCoordinates e (ρ i) v m)))) = _
  rw [LinearEquiv.symm_apply_apply, ← blockCoordinates_inclusion]
  rfl

theorem transformedMatrices_mulVec (a : A) (i : Fin 3) (v : V i → F) :
    transformedMatrices e ρ a i *ᵥ encoding e ρ i v =
      encoding e ρ i (ρ i a v) := by
  have h := congrArg (fun M : Matrix (BlockIndex e ρ i) (V i) F => M *ᵥ v)
    (Tensor.matrixConjugation_intertwines (encoding e ρ i) (LinearMap.toMatrix' (ρ i a)))
  change Tensor.matrixConjugation (encoding e ρ i) (LinearMap.toMatrix' (ρ i a)) *ᵥ
      (encoding e ρ i).toLinearMap v =
    (encoding e ρ i).toLinearMap (ρ i a v)
  simpa only [← Matrix.mulVec_mulVec, Tensor.matrixOfEquiv,
    LinearMap.toMatrix'_mulVec] using h

theorem localMatrices_eq_restrict (m : κ) (i : Fin 3) (b : B m) :
    localMatrices e ρ m i b =
      Tensor.Blocks.restrictMatrix (W := fun m i => Fin (blockSize e ρ m i)) m i
        (transformedMatrices e ρ (blockInclusion e m b) i) := by
  funext a c
  let w : BlockIndex e ρ i → F := Pi.single ⟨m, c⟩ 1
  let v := (encoding e ρ i).symm w
  have h := localMatrices_mulVec e ρ m i b v
  have h' := transformedMatrices_mulVec e ρ (blockInclusion e m b) i v
  have hv : encoding e ρ i v = w := (encoding e ρ i).apply_symm_apply w
  rw [hv] at h h'
  have ha := congrFun h a
  rw [← h'] at ha
  have hw : (fun d => w ⟨m, d⟩) = Pi.single c 1 := by
    funext d
    simp [w, Pi.single_apply]
  rw [hw, Matrix.mulVec_single] at ha
  simpa [w, Matrix.mulVec_single, Tensor.Blocks.restrictMatrix] using ha

def blockTensor (T : Lemmata.Centroid.Tensor F (Fin 3) V) (m : κ) :
    Lemmata.Centroid.Tensor F (Fin 3) (fun i => Fin (blockSize e ρ m i)) :=
  Tensor.Blocks.component (transformed e ρ T) m

theorem transformed_isDiagonal (T : Lemmata.Centroid.Tensor F (Fin 3) V)
    (hbalanced : ∀ a, algebraMatrices ρ a ∈ Tensor.centroid T) :
    Tensor.Blocks.IsDiagonal (transformed e ρ T) :=
  fun x _ _ h => transformed_mixed_zero e ρ T hbalanced x h

theorem blockTensor_concise {T : Lemmata.Centroid.Tensor F (Fin 3) V} (hT : Tensor.Concise T)
    (hbalanced : ∀ a, algebraMatrices ρ a ∈ Tensor.centroid T) (m : κ) :
    Tensor.Concise (blockTensor e ρ T m) :=
  Tensor.Blocks.Concise.component (hT.localEquiv (encoding e ρ))
    (transformed_isDiagonal e ρ T hbalanced) m

theorem localMatrices_mem_centroid (T : Lemmata.Centroid.Tensor F (Fin 3) V)
    (hbalanced : ∀ a, algebraMatrices ρ a ∈ Tensor.centroid T) (m : κ) (b : B m) :
    (fun i => localMatrices e ρ m i b) ∈ Tensor.centroid (blockTensor e ρ T m) := by
  have h := Tensor.conjugateFamily_mem_centroid (encoding e ρ)
    (hbalanced (blockInclusion e m b))
  intro i j
  funext x
  have hx := congrFun (h i j) (Tensor.Blocks.point m x)
  change Tensor.legAction (transformed e ρ T) i
      (transformedMatrices e ρ (blockInclusion e m b) i) (Tensor.Blocks.point m x) =
    Tensor.legAction (transformed e ρ T) j
      (transformedMatrices e ρ (blockInclusion e m b) j) (Tensor.Blocks.point m x) at hx
  rw [Tensor.Blocks.legAction_point (transformed_isDiagonal e ρ T hbalanced),
    Tensor.Blocks.legAction_point (transformed_isDiagonal e ρ T hbalanced)] at hx
  simpa only [← localMatrices_eq_restrict, blockTensor] using hx

def localCentroidHom {T : Lemmata.Centroid.Tensor F (Fin 3) V} (hT : Tensor.Concise T)
    (hbalanced : ∀ a, algebraMatrices ρ a ∈ Tensor.centroid T) (m : κ) :
    B m →ₐ[F] Tensor.centroidAlgebra (blockTensor e ρ T m)
      (blockTensor_concise e ρ hT hbalanced m) :=
  (AlgHom.pi (localMatrices e ρ m)).codRestrict
    (Tensor.centroidAlgebra (blockTensor e ρ T m) (blockTensor_concise e ρ hT hbalanced m))
    (localMatrices_mem_centroid e ρ T hbalanced m)

theorem localCentroidHom_injective {T : Lemmata.Centroid.Tensor F (Fin 3) V} (hT : Tensor.Concise T)
    (hbalanced : ∀ a, algebraMatrices ρ a ∈ Tensor.centroid T)
    (hρ : ∀ i, Function.Injective (ρ i)) (m : κ) :
    Function.Injective (localCentroidHom e ρ hT hbalanced m) := by
  intro b c h
  apply localMatrices_injective e ρ hρ m 0
  exact congrFun (congrArg Subtype.val h) 0

omit [Fintype κ] in
theorem blockSize_pos [∀ m, Nontrivial (B m)]
    (hρ : ∀ i, Function.Injective (ρ i)) (m : κ) (i : Fin 3) :
    0 < blockSize e ρ m i := by
  by_contra h
  have hz : blockSize e ρ m i = 0 := by omega
  have hmat : localMatrices e ρ m i (0 : B m) = localMatrices e ρ m i 1 := by
    funext a b
    have ha := a.isLt
    omega
  exact zero_ne_one (localMatrices_injective e ρ hρ m i hmat)

theorem sum_blockSize (i : Fin 3) :
    ∑ m, blockSize e ρ m i = Fintype.card (V i) := by
  have h := finrank_blockCoordinates e (ρ i)
  simpa only [blockSize, Module.finrank_pi] using h.symm

theorem finrank_centroid_eq_sum (T : Lemmata.Centroid.Tensor F (Fin 3) V) (hT : Tensor.Concise T)
    (hbalanced : ∀ a, algebraMatrices ρ a ∈ Tensor.centroid T) :
    Module.finrank F (Tensor.centroid T) =
      ∑ m, Module.finrank F (Tensor.centroid (blockTensor e ρ T m)) := by
  rw [← Tensor.finrank_centroid_localEquiv (encoding e ρ) T]
  exact Tensor.Blocks.finrank_centroid (hT.localEquiv (encoding e ρ))
    (transformed_isDiagonal e ρ T hbalanced)

end Lemmata.Centroid.General.TensorBlocks
