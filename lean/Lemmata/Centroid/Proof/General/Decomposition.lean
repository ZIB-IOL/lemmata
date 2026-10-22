module

public import Lemmata.Centroid.Proof.Linear.LocalAlgebra
public import Mathlib.LinearAlgebra.Dimension.Constructions

@[expose] public section

open scoped BigOperators
open Classical

noncomputable section

namespace Lemmata.Centroid.General

variable {F A W ι : Type*} [Field F] [CommRing A] [Algebra F A]
variable [AddCommGroup W] [Module F W] [Fintype ι]
variable {B : ι → Type*} [∀ i, CommRing (B i)] [∀ i, Algebra F (B i)]

def blockProjection (e : A ≃ₐ[F] ∀ i, B i) (ρ : A →ₐ[F] Module.End F W) (i : ι) : W →ₗ[F] W :=
  ρ (Linear.blockIdempotent e i)

def blockSpace (e : A ≃ₐ[F] ∀ i, B i) (ρ : A →ₐ[F] Module.End F W) (i : ι) : Submodule F W :=
  (blockProjection e ρ i).range

omit [Fintype ι] in
theorem blockProjection_sq (e : A ≃ₐ[F] ∀ i, B i) (ρ : A →ₐ[F] Module.End F W) (i : ι) :
    (blockProjection e ρ i).comp (blockProjection e ρ i) = blockProjection e ρ i := by
  change ρ (Linear.blockIdempotent e i) * ρ (Linear.blockIdempotent e i) = _
  rw [← map_mul, Linear.blockIdempotent_sq]
  rfl

omit [Fintype ι] in
theorem blockProjection_mul (e : A ≃ₐ[F] ∀ i, B i) (ρ : A →ₐ[F] Module.End F W)
    {i j : ι} (hij : i ≠ j) :
    (blockProjection e ρ i).comp (blockProjection e ρ j) = 0 := by
  change ρ (Linear.blockIdempotent e i) * ρ (Linear.blockIdempotent e j) = 0
  rw [← map_mul, Linear.blockIdempotent_mul e hij, map_zero]

theorem sum_blockProjection (e : A ≃ₐ[F] ∀ i, B i) (ρ : A →ₐ[F] Module.End F W) :
    ∑ i, blockProjection e ρ i = LinearMap.id := by
  change ∑ i, ρ (Linear.blockIdempotent e i) = 1
  rw [← map_sum, Linear.sum_blockIdempotent, map_one]

omit [Fintype ι] in
theorem blockProjection_fixed (e : A ≃ₐ[F] ∀ i, B i) (ρ : A →ₐ[F] Module.End F W)
    (i : ι) (x : blockSpace e ρ i) : blockProjection e ρ i x.val = x.val := by
  obtain ⟨w, hw⟩ := x.property
  change blockProjection e ρ i w = x.val at hw
  rw [← hw]
  exact congrArg (fun f : W →ₗ[F] W => f w) (blockProjection_sq e ρ i)

omit [Fintype ι] in
theorem blockProjection_kills (e : A ≃ₐ[F] ∀ i, B i) (ρ : A →ₐ[F] Module.End F W)
    {i j : ι} (hij : i ≠ j) (x : blockSpace e ρ j) : blockProjection e ρ i x.val = 0 := by
  obtain ⟨w, hw⟩ := x.property
  change blockProjection e ρ j w = x.val at hw
  rw [← hw]
  exact congrArg (fun f : W →ₗ[F] W => f w) (blockProjection_mul e ρ hij)

def blockCoordinates (e : A ≃ₐ[F] ∀ i, B i) (ρ : A →ₐ[F] Module.End F W) :
    W ≃ₗ[F] ∀ i, blockSpace e ρ i where
  toFun x i := ⟨blockProjection e ρ i x, LinearMap.mem_range_self _ x⟩
  invFun x := ∑ i, (x i).val
  left_inv x := by
    have h := congrArg (fun f : W →ₗ[F] W => f x) (sum_blockProjection e ρ)
    simpa only [LinearMap.sum_apply, LinearMap.id_apply] using h
  right_inv x := by
    funext i
    apply Subtype.ext
    change blockProjection e ρ i (∑ j, (x j).val) = (x i).val
    rw [map_sum, Finset.sum_eq_single i]
    · exact blockProjection_fixed e ρ i (x i)
    · intro j _ hji
      exact blockProjection_kills e ρ hji.symm (x j)
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  map_add' x y := by
    funext i
    apply Subtype.ext
    exact (blockProjection e ρ i).map_add x y
  map_smul' c x := by
    funext i
    apply Subtype.ext
    exact (blockProjection e ρ i).map_smul c x

theorem finrank_blockCoordinates [Module.Finite F W]
    (e : A ≃ₐ[F] ∀ i, B i) (ρ : A →ₐ[F] Module.End F W) :
    Module.finrank F W = ∑ i, Module.finrank F (blockSpace e ρ i) := by
  have h := (blockCoordinates e ρ).finrank_eq
  simpa only [Module.finrank_pi_fintype] using h

theorem blockCoordinates_projection (e : A ≃ₐ[F] ∀ i, B i)
    (ρ : A →ₐ[F] Module.End F W) (x : W) (i j : ι) :
    (blockCoordinates e ρ (blockProjection e ρ i x) j).val =
      if j = i then (blockCoordinates e ρ x j).val else 0 := by
  change blockProjection e ρ j (blockProjection e ρ i x) =
    if j = i then blockProjection e ρ j x else 0
  by_cases hji : j = i
  · subst j
    simpa only [ite_true, LinearMap.comp_apply] using
      congrArg (fun f : W →ₗ[F] W => f x) (blockProjection_sq e ρ i)
  · simpa only [hji, ite_false, LinearMap.comp_apply, LinearMap.zero_apply] using
      congrArg (fun f : W →ₗ[F] W => f x) (blockProjection_mul e ρ hji)

def blockInclusion (e : A ≃ₐ[F] ∀ i, B i) (i : ι) : B i →ₗ[F] A :=
  e.symm.toLinearMap.comp (LinearMap.single F B i)

omit [Fintype ι] in
@[simp] theorem blockInclusion_image (e : A ≃ₐ[F] ∀ i, B i) (i : ι) (b : B i) :
    e (blockInclusion e i b) = Pi.single i b := e.apply_symm_apply _

omit [Fintype ι] in
theorem blockInclusion_injective (e : A ≃ₐ[F] ∀ i, B i) (i : ι) :
    Function.Injective (blockInclusion e i) := by
  intro b c h
  have h' := congrFun (congrArg e h) i
  simpa only [blockInclusion_image, Pi.single_eq_same] using h'

omit [Fintype ι] in
theorem blockInclusion_mul (e : A ≃ₐ[F] ∀ i, B i) (i : ι) (b c : B i) :
    blockInclusion e i (b * c) = blockInclusion e i b * blockInclusion e i c := by
  apply e.injective
  simp only [map_mul, blockInclusion_image]
  funext j
  by_cases h : j = i
  · subst j; simp
  · simp [h]

omit [Fintype ι] in
theorem blockInclusion_one (e : A ≃ₐ[F] ∀ i, B i) (i : ι) :
    blockInclusion e i 1 = Linear.blockIdempotent e i := rfl

omit [Fintype ι] in
theorem blockInclusion_mul_idempotent (e : A ≃ₐ[F] ∀ i, B i) (i : ι) (b : B i) :
    blockInclusion e i b * Linear.blockIdempotent e i = blockInclusion e i b := by
  rw [← blockInclusion_one, ← blockInclusion_mul, mul_one]

def localRepresentation (e : A ≃ₐ[F] ∀ i, B i) (ρ : A →ₐ[F] Module.End F W) (i : ι) :
    B i →ₐ[F] Module.End F (blockSpace e ρ i) where
  toFun b :=
    { toFun := fun x => ⟨ρ (blockInclusion e i b) x.val, by
        refine ⟨ρ (blockInclusion e i b) x.val, ?_⟩
        change ρ (Linear.blockIdempotent e i) (ρ (blockInclusion e i b) x.val) = _
        rw [← Module.End.mul_apply, ← map_mul, mul_comm,
          blockInclusion_mul_idempotent]⟩
      map_add' := fun x y => Subtype.ext ((ρ (blockInclusion e i b)).map_add x.val y.val)
      map_smul' := fun c x => Subtype.ext ((ρ (blockInclusion e i b)).map_smul c x.val) }
  map_zero' := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change ρ (blockInclusion e i 0) x.val = 0
    rw [map_zero, map_zero, LinearMap.zero_apply]
  map_one' := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change ρ (blockInclusion e i 1) x.val = x.val
    rw [blockInclusion_one]
    exact blockProjection_fixed e ρ i x
  map_add' b c := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change ρ (blockInclusion e i (b + c)) x.val =
      ρ (blockInclusion e i b) x.val + ρ (blockInclusion e i c) x.val
    rw [map_add, map_add, LinearMap.add_apply]
  map_mul' b c := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change ρ (blockInclusion e i (b * c)) x.val =
      ρ (blockInclusion e i b) (ρ (blockInclusion e i c) x.val)
    rw [blockInclusion_mul, map_mul, Module.End.mul_apply]
  commutes' c := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change ρ (blockInclusion e i (algebraMap F (B i) c)) x.val = c • x.val
    rw [Algebra.algebraMap_eq_smul_one, map_smul, blockInclusion_one, map_smul,
      LinearMap.smul_apply]
    exact congrArg (c • ·) (blockProjection_fixed e ρ i x)

omit [Fintype ι] in
theorem localRepresentation_injective (e : A ≃ₐ[F] ∀ i, B i)
    (ρ : A →ₐ[F] Module.End F W) (hρ : Function.Injective ρ) (i : ι) :
    Function.Injective (localRepresentation e ρ i) := by
  intro b c h
  apply blockInclusion_injective e i
  apply hρ
  apply LinearMap.ext
  intro w
  let x : blockSpace e ρ i := ⟨blockProjection e ρ i w, LinearMap.mem_range_self _ w⟩
  have hx := congrArg (fun f : Module.End F (blockSpace e ρ i) => (f x).val) h
  change ρ (blockInclusion e i b) (blockProjection e ρ i w) =
    ρ (blockInclusion e i c) (blockProjection e ρ i w) at hx
  simpa only [blockProjection, ← Module.End.mul_apply, ← map_mul,
    blockInclusion_mul_idempotent] using hx

end Lemmata.Centroid.General
