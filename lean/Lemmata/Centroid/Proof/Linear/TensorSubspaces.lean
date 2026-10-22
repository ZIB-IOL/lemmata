module

public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Finsupp.Pi
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.RingTheory.Flat.Basic

@[expose] public section

open scoped TensorProduct
open TensorProduct

namespace Lemmata.Centroid.Linear

universe u v w z a

variable {F : Type u} [Field F]
variable {X : Type v} {Y : Type w} {Z : Type z}
variable [AddCommGroup X] [Module F X] [AddCommGroup Y] [Module F Y]
variable [AddCommGroup Z] [Module F Z]
variable {W : Type a} [AddCommGroup W] [Module F W]

/-- The tensor product of two subspaces inside the ambient tensor product. -/
def tensorSubspace (A : Submodule F X) (B : Submodule F Y) :
    Submodule F (X ⊗[F] Y) :=
  Submodule.map₂ (TensorProduct.mk F X Y) A B

theorem tensorSubspace_eq_range (A : Submodule F X) (B : Submodule F Y) :
    tensorSubspace A B = LinearMap.range (TensorProduct.mapIncl A B) :=
  (TensorProduct.range_mapIncl A B).symm

theorem tmul_mem_tensorSubspace {A : Submodule F X} {B : Submodule F Y}
    {x : X} {y : Y} (hx : x ∈ A) (hy : y ∈ B) :
    x ⊗ₜ[F] y ∈ tensorSubspace A B :=
  Submodule.apply_mem_map₂ _ hx hy

theorem tensorSubspace_mono {A A' : Submodule F X} {B B' : Submodule F Y}
    (hA : A ≤ A') (hB : B ≤ B') : tensorSubspace A B ≤ tensorSubspace A' B' :=
  Submodule.map₂_le_map₂ hA hB

@[simp] theorem tensorSubspace_top_top :
    tensorSubspace (⊤ : Submodule F X) (⊤ : Submodule F Y) = ⊤ :=
  TensorProduct.map₂_mk_top_top_eq_top F X Y

@[simp] theorem tensorSubspace_bot_left (B : Submodule F Y) :
    tensorSubspace (⊥ : Submodule F X) B = ⊥ := by
  simp [tensorSubspace]

@[simp] theorem tensorSubspace_bot_right (A : Submodule F X) :
    tensorSubspace A (⊥ : Submodule F Y) = ⊥ := by
  simp [tensorSubspace]

theorem tensorSubspace_map (f : X →ₗ[F] Z) (g : Y →ₗ[F] W)
    (A : Submodule F X) (B : Submodule F Y) :
    (tensorSubspace A B).map (TensorProduct.map f g) =
      tensorSubspace (A.map f) (B.map g) := by
  simp only [tensorSubspace, Submodule.map_map₂, Submodule.map₂_map_map]
  rfl

noncomputable def rightCoefficients {κ : Type*} (b : Module.Basis κ F Y) :
    X ⊗[F] Y ≃ₗ[F] κ →₀ X := by
  classical
  exact TensorProduct.equivFinsuppOfBasisRight b

theorem rightCoefficients_tmul {κ : Type*} (b : Module.Basis κ F Y)
    (x : X) (y : Y) (j : κ) :
    rightCoefficients b (x ⊗ₜ[F] y) j = b.repr y j • x :=
  by
    classical
    exact TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply b x y j

theorem mem_tensorSubspace_top_right {κ : Type*} (b : Module.Basis κ F Y)
    (A : Submodule F X) (t : X ⊗[F] Y) :
    t ∈ tensorSubspace A ⊤ ↔ ∀ j, rightCoefficients b t j ∈ A := by
  classical
  constructor
  · intro ht j
    let c : X ⊗[F] Y →ₗ[F] X :=
      (Finsupp.lapply j).comp (rightCoefficients b).toLinearMap
    have h : tensorSubspace A (⊤ : Submodule F Y) ≤ A.comap c := by
      apply Submodule.map₂_le.mpr
      intro x hx y _
      change rightCoefficients b (x ⊗ₜ[F] y) j ∈ A
      rw [rightCoefficients_tmul]
      exact A.smul_mem _ hx
    exact h ht
  · intro ht
    have h := (rightCoefficients b).symm_apply_apply t
    rw [rightCoefficients, TensorProduct.equivFinsuppOfBasisRight_symm_apply] at h
    rw [← h]
    change (∑ j ∈ (rightCoefficients b t).support,
      (rightCoefficients b t j) ⊗ₜ[F] b j) ∈ tensorSubspace A ⊤
    exact Submodule.sum_mem _ fun j _ => tmul_mem_tensorSubspace (ht j) (Submodule.mem_top)

theorem tensorSubspace_inf_left (A A' : Submodule F X) (B : Submodule F Y) :
    tensorSubspace (A ⊓ A') B = tensorSubspace A B ⊓ tensorSubspace A' B := by
  classical
  apply le_antisymm
  · exact le_inf (tensorSubspace_mono inf_le_left le_rfl)
      (tensorSubspace_mono inf_le_right le_rfl)
  · intro t ht
    let b := Module.Free.chooseBasis F Y
    have hA := (mem_tensorSubspace_top_right b A t).mp
      (tensorSubspace_mono le_rfl le_top ht.1)
    have hA' := (mem_tensorSubspace_top_right b A' t).mp
      (tensorSubspace_mono le_rfl le_top ht.2)
    have hcommon : t ∈ tensorSubspace (A ⊓ A') (⊤ : Submodule F Y) :=
      (mem_tensorSubspace_top_right b (A ⊓ A') t).mpr fun j => ⟨hA j, hA' j⟩
    obtain ⟨C, hC⟩ := B.exists_isCompl
    let p : Y →ₗ[F] Y := B.projection C hC
    have hfix : ∀ u ∈ tensorSubspace (⊤ : Submodule F X) B,
        TensorProduct.map LinearMap.id p u = u := by
      intro u hu
      have hh : tensorSubspace (⊤ : Submodule F X) B ≤
          LinearMap.eqLocus (TensorProduct.map LinearMap.id p) LinearMap.id := by
        apply Submodule.map₂_le.mpr
        intro x _ y hy
        change x ⊗ₜ[F] p y = x ⊗ₜ[F] y
        rw [show p y = y from B.projection_apply_of_mem_left hC hy]
      exact hh hu
    have hmap : TensorProduct.map LinearMap.id p t ∈ tensorSubspace (A ⊓ A') B := by
      have hh := Submodule.mem_map_of_mem (f := TensorProduct.map LinearMap.id p) hcommon
      rw [tensorSubspace_map] at hh
      simpa [p, Submodule.map_id, Submodule.map_top] using hh
    rwa [hfix t (tensorSubspace_mono le_top le_rfl ht.1)] at hmap

theorem tensorSubspace_eq_inf_top (A : Submodule F X) (B : Submodule F Y) :
    tensorSubspace A B = tensorSubspace A ⊤ ⊓ tensorSubspace ⊤ B := by
  classical
  apply le_antisymm
  · exact le_inf (tensorSubspace_mono le_rfl le_top)
      (tensorSubspace_mono le_top le_rfl)
  · intro t ht
    obtain ⟨C, hC⟩ := B.exists_isCompl
    let p : Y →ₗ[F] Y := B.projection C hC
    have hfix : TensorProduct.map LinearMap.id p t = t := by
      have hh : tensorSubspace (⊤ : Submodule F X) B ≤
          LinearMap.eqLocus (TensorProduct.map LinearMap.id p) LinearMap.id := by
        apply Submodule.map₂_le.mpr
        intro x _ y hy
        change x ⊗ₜ[F] p y = x ⊗ₜ[F] y
        rw [show p y = y from B.projection_apply_of_mem_left hC hy]
      exact hh ht.2
    have hmap := Submodule.mem_map_of_mem (f := TensorProduct.map LinearMap.id p) ht.1
    rw [tensorSubspace_map] at hmap
    simpa [p, Submodule.map_id, Submodule.map_top, hfix] using hmap

theorem rightCoefficients_map {κ : Type*} (b : Module.Basis κ F Y)
    (f : X →ₗ[F] Z) (t : X ⊗[F] Y) (j : κ) :
    rightCoefficients b (TensorProduct.map f LinearMap.id t) j =
      f (rightCoefficients b t j) := by
  induction t using TensorProduct.inductionOn with
  | tmul x y => simp [rightCoefficients_tmul]
  | add t u ht hu => simp [ht, hu]

theorem sum_rightCoefficients_tmul {κ : Type*} [Fintype κ]
    (b : Module.Basis κ F Y) (t : X ⊗[F] Y) :
    (∑ j, (rightCoefficients b t j) ⊗ₜ[F] b j) = t := by
  classical
  apply (rightCoefficients b).injective
  ext j
  simp [rightCoefficients_tmul, Module.Basis.repr_self, Finsupp.single_apply]

theorem ker_rTensor (f : X →ₗ[F] Z) :
    LinearMap.ker (TensorProduct.map f (LinearMap.id : Y →ₗ[F] Y)) =
      tensorSubspace (LinearMap.ker f) ⊤ := by
  classical
  let b := Module.Free.chooseBasis F Y
  ext t
  rw [mem_tensorSubspace_top_right b]
  constructor
  · intro ht j
    change f (rightCoefficients b t j) = 0
    rw [← rightCoefficients_map, show TensorProduct.map f LinearMap.id t = 0 from ht]
    simp
  · intro ht
    change TensorProduct.map f LinearMap.id t = 0
    apply (rightCoefficients b).injective
    ext j
    rw [rightCoefficients_map]
    exact ht j

theorem tensorSubspace_comm (A : Submodule F X) (B : Submodule F Y) :
    (tensorSubspace A B).map (TensorProduct.comm F X Y).toLinearMap =
      tensorSubspace B A := by
  simp only [tensorSubspace, Submodule.map_map₂]
  change Submodule.map₂ (TensorProduct.mk F Y X).flip A B = _
  exact Submodule.map₂_flip _ _ _

theorem tensorSubspace_inf_right (A : Submodule F X) (B B' : Submodule F Y) :
    tensorSubspace A (B ⊓ B') = tensorSubspace A B ⊓ tensorSubspace A B' := by
  apply (Submodule.orderIsoMapComap (TensorProduct.comm F X Y)).injective
  simp only [Submodule.orderIsoMapComap_apply, tensorSubspace_comm, map_inf]
  exact tensorSubspace_inf_left B B' A

theorem tensorSubspace_inf (A A' : Submodule F X) (B B' : Submodule F Y) :
    tensorSubspace (A ⊓ A') (B ⊓ B') =
      tensorSubspace A B ⊓ tensorSubspace A' B' := by
  rw [tensorSubspace_inf_left, tensorSubspace_inf_right,
    tensorSubspace_inf_right]
  apply le_antisymm
  · exact le_inf (fun _ h => h.1.1) (fun _ h => h.2.2)
  · intro t ht
    constructor
    · refine ⟨ht.1, ?_⟩
      rw [tensorSubspace_eq_inf_top]
      exact ⟨tensorSubspace_mono le_rfl le_top ht.1,
        tensorSubspace_mono le_top le_rfl ht.2⟩
    · refine ⟨?_, ht.2⟩
      rw [tensorSubspace_eq_inf_top]
      exact ⟨tensorSubspace_mono le_rfl le_top ht.2,
        tensorSubspace_mono le_top le_rfl ht.1⟩

theorem finrank_tensorSubspace [FiniteDimensional F X] [FiniteDimensional F Y]
    (A : Submodule F X) (B : Submodule F Y) :
    Module.finrank F (tensorSubspace A B) =
      Module.finrank F A * Module.finrank F B := by
  rw [tensorSubspace_eq_range]
  rw [LinearMap.finrank_range_of_inj
    (TensorProduct.map_injective_of_flat_flat _ _ A.subtype_injective B.subtype_injective)]
  exact Module.finrank_tensorProduct

theorem mem_tensorSubspace_map_left_iff (f : X →ₗ[F] Z)
    (hf : Function.Injective f) (B : Submodule F Y) (t : X ⊗[F] Y) :
    TensorProduct.map f LinearMap.id t ∈ tensorSubspace (⊤ : Submodule F Z) B ↔
      t ∈ tensorSubspace (⊤ : Submodule F X) B := by
  let g := TensorProduct.map f (LinearMap.id : Y →ₗ[F] Y)
  have hg : Function.Injective g :=
    TensorProduct.map_injective_of_flat_flat _ _ hf Function.injective_id
  have hm : (tensorSubspace (⊤ : Submodule F X) B).map g =
      tensorSubspace (LinearMap.range f) B := by
    rw [tensorSubspace_map]
    simp
  constructor
  · intro ht
    have ht' : g t ∈ tensorSubspace (LinearMap.range f) B := by
      rw [tensorSubspace_eq_inf_top]
      refine ⟨?_, ht⟩
      have h := LinearMap.mem_range_self g t
      simpa [g, TensorProduct.range_map, tensorSubspace] using h
    rw [← hm] at ht'
    obtain ⟨u, hu, heq⟩ := ht'
    exact hg heq ▸ hu
  · intro ht
    have h := Submodule.mem_map_of_mem (f := g) ht
    rw [hm] at h
    exact tensorSubspace_mono le_top le_rfl h

end Lemmata.Centroid.Linear
