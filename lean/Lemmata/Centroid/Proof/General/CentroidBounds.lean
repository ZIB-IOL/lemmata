module

public import Lemmata.Centroid.Proof.General.ProjectedAction
public import Lemmata.Centroid.Proof.Tensor.SupportBound

@[expose] public section

open scoped BigOperators Matrix
open Classical

noncomputable section

namespace Lemmata.Centroid.Tensor

variable {F : Type*} [Field F] {V : Fin 3 → Type*} [∀ i, Fintype (V i)]

def centroidIdealSpace (T : Tensor F (Fin 3) V) (hT : Concise T)
    (I : Ideal (centroidAlgebra T hT)) : Submodule F (∀ i, Matrix (V i) (V i) F) :=
  (I.restrictScalars F).map (centroidAlgebra T hT).val.toLinearMap

theorem centroidIdealSpace_le (T : Tensor F (Fin 3) V) (hT : Concise T)
    (I : Ideal (centroidAlgebra T hT)) : centroidIdealSpace T hT I ≤ centroid T := by
  rintro A ⟨c, _, rfl⟩
  exact c.2

theorem centroidIdealSpace_finrank (T : Tensor F (Fin 3) V) (hT : Concise T)
    (I : Ideal (centroidAlgebra T hT)) :
    Module.finrank F (centroidIdealSpace T hT I) = Module.finrank F I := by
  let f : I →ₗ[F] (∀ i, Matrix (V i) (V i) F) :=
    (centroidAlgebra T hT).val.toLinearMap.comp (I.subtype.restrictScalars F)
  have hf : Function.Injective f := fun x y h => Subtype.ext (Subtype.ext h)
  have hr : f.range = centroidIdealSpace T hT I := by
    ext A
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨c.1, c.2, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨⟨c, hc⟩, rfl⟩
  rw [← hr]
  exact LinearMap.finrank_range_of_inj hf

@[instance_reducible] def centroidModule (T : Tensor F (Fin 3) V) (hT : Concise T)
    (i : Fin 3) : Module (centroidAlgebra T hT) (V i → F) :=
  Module.compHom _ (centroidRepresentation T hT i).toRingHom

theorem centroidModuleScalarTower (T : Tensor F (Fin 3) V) (hT : Concise T) (i : Fin 3) :
    let := centroidModule T hT i
    IsScalarTower F (centroidAlgebra T hT) (V i → F) := by
  let := centroidModule T hT i
  constructor
  intro r c u
  change centroidRepresentation T hT i (r • c) u = r • centroidRepresentation T hT i c u
  rw [map_smul]
  rfl

theorem centroidModuleFaithful (T : Tensor F (Fin 3) V) (hT : Concise T) (i : Fin 3) :
    let := centroidModule T hT i
    FaithfulSMul (centroidAlgebra T hT) (V i → F) := by
  let := centroidModule T hT i
  constructor
  intro c d h
  apply centroidRepresentation_injective hT i
  exact LinearMap.ext h

theorem centroidModule_idealKernel (T : Tensor F (Fin 3) V) (hT : Concise T)
    (I : Ideal (centroidAlgebra T hT)) (i : Fin 3) :
    let := centroidModule T hT i
    let := centroidModuleScalarTower T hT i
    (General.idealKernel (M := V i → F) I).restrictScalars F =
      commonKernel (centroidIdealSpace T hT I) i := by
  let := centroidModule T hT i
  let := centroidModuleScalarTower T hT i
  ext u
  rw [mem_commonKernel]
  constructor
  · intro hu A hA
    obtain ⟨c, hc, rfl⟩ := hA
    exact hu c hc
  · intro hu c hc
    exact hu c.1 ⟨c, hc, rfl⟩

theorem centroid_nilpotent_ideal_kernel_bound (T : Tensor F (Fin 3) V) (hT : Concise T)
    (I : Ideal (centroidAlgebra T hT)) (hI : IsNilpotent I) (i : Fin 3) :
    Module.finrank F I ≤ Module.finrank F (commonKernel (centroidIdealSpace T hT I) i) *
      (Fintype.card (V i) - Module.finrank F (commonKernel (centroidIdealSpace T hT I) i)) := by
  let := centroidModule T hT i
  let := centroidModuleScalarTower T hT i
  let := centroidModuleFaithful T hT i
  have h := General.nilpotent_ideal_dimension_le_kernel_mul_codim
    (F := F) (M := V i → F) I hI
  have hk : Module.finrank F (General.idealKernel (M := V i → F) I) =
      Module.finrank F (commonKernel (centroidIdealSpace T hT I) i) := by
    change Module.finrank F ((General.idealKernel (M := V i → F) I).restrictScalars F) = _
    rw [centroidModule_idealKernel]
  simpa only [hk, Module.finrank_pi] using h

theorem centroid_nilpotent_ideal_residue_bound (T : Tensor F (Fin 3) V) (hT : Concise T)
    (I : Ideal (centroidAlgebra T hT)) [I.IsMaximal] (hI : IsNilpotent I) (i : Fin 3) :
    Module.finrank F I * Module.finrank F (centroidAlgebra T hT ⧸ I) ≤
      Module.finrank F (commonKernel (centroidIdealSpace T hT I) i) *
        (Fintype.card (V i) - Module.finrank F (commonKernel (centroidIdealSpace T hT I) i)) := by
  let := centroidModule T hT i
  let := centroidModuleScalarTower T hT i
  let := centroidModuleFaithful T hT i
  have h := General.ideal_dimension_mul_residue_le_kernel_mul_codim
    (F := F) (M := V i → F) I (General.nilpotentIdeal_le_jacobson I hI)
  have hk : Module.finrank F (General.idealKernel (M := V i → F) I) =
      Module.finrank F (commonKernel (centroidIdealSpace T hT I) i) := by
    change Module.finrank F ((General.idealKernel (M := V i → F) I).restrictScalars F) = _
    rw [centroidModule_idealKernel]
  simpa only [hk, Module.finrank_pi] using h

theorem centroid_ideal_product_bound (T : Tensor F (Fin 3) V) (hT : Concise T)
    (I : Ideal (centroidAlgebra T hT)) :
    Module.finrank F I ^ 2 ≤ ∏ i : Fin 3,
      (Fintype.card (V i) - Module.finrank F (commonKernel (centroidIdealSpace T hT I) i)) := by
  simpa only [centroidIdealSpace_finrank] using
    centroid_subspace_product_bound hT (centroidIdealSpace_le T hT I)

theorem centroidModule_kernel_finrank (T : Tensor F (Fin 3) V) (hT : Concise T)
    (I : Ideal (centroidAlgebra T hT)) (i : Fin 3) :
    let := centroidModule T hT i
    let := centroidModuleScalarTower T hT i
    Module.finrank F (General.idealKernel (M := V i → F) I) =
      Module.finrank F (commonKernel (centroidIdealSpace T hT I) i) := by
  let := centroidModule T hT i
  let := centroidModuleScalarTower T hT i
  change Module.finrank F ((General.idealKernel (M := V i → F) I).restrictScalars F) = _
  rw [centroidModule_idealKernel]

theorem centroid_annihilator_difference_bound (T : Tensor F (Fin 3) V) (hT : Concise T)
    (I : Ideal (centroidAlgebra T hT)) (i : Fin 3) :
    Module.finrank F I - Module.finrank F (General.annihilatorInIdeal I) ≤
      ((Module.finrank F
          (commonKernel (centroidIdealSpace T hT (General.annihilatorInIdeal I)) i) -
          Module.finrank F (commonKernel (centroidIdealSpace T hT I) i)) + 1) ^ 2 / 4 := by
  let := centroidModule T hT i
  let := centroidModuleScalarTower T hT i
  let := centroidModuleFaithful T hT i
  simpa only [centroidModule_kernel_finrank] using
    General.annihilator_dimension_difference_bound (F := F) (M := V i → F) I

theorem centroid_nilpotent_ideal_annihilator_bound (T : Tensor F (Fin 3) V) (hT : Concise T)
    (I : Ideal (centroidAlgebra T hT)) (hI : IsNilpotent I) (i : Fin 3) :
    Module.finrank F I ≤
      Module.finrank F
          (commonKernel (centroidIdealSpace T hT (General.annihilatorInIdeal I)) i) *
        (Fintype.card (V i) - Module.finrank F
          (commonKernel (centroidIdealSpace T hT (General.annihilatorInIdeal I)) i)) := by
  let := centroidModule T hT i
  let := centroidModuleScalarTower T hT i
  let := centroidModuleFaithful T hT i
  simpa only [centroidModule_kernel_finrank, Module.finrank_pi] using
    General.ideal_dimension_le_annihilatorKernel_mul_complement (F := F) (M := V i → F) I hI

theorem centroid_residue_degree_dvd_leg (T : Tensor F (Fin 3) V) (hT : Concise T)
    (I : Ideal (centroidAlgebra T hT)) [I.IsMaximal] (hI : IsNilpotent I) (i : Fin 3) :
    Module.finrank F (centroidAlgebra T hT ⧸ I) ∣ Fintype.card (V i) := by
  let := centroidModule T hT i
  let := centroidModuleScalarTower T hT i
  simpa only [Module.finrank_pi] using
    General.residue_degree_dvd_finrank (F := F) (M := V i → F) I hI

theorem centroid_residue_degree_dvd_ideal (T : Tensor F (Fin 3) V) (hT : Concise T)
    (I : Ideal (centroidAlgebra T hT)) [I.IsMaximal] (hI : IsNilpotent I) :
    Module.finrank F (centroidAlgebra T hT ⧸ I) ∣ Module.finrank F I := by
  let : FiniteDimensional F I := Module.Finite.of_injective
    (I.subtype.restrictScalars F) I.subtype_injective
  exact General.residue_degree_dvd_finrank (F := F) (M := I) I hI

theorem centroid_residue_degree_dvd_kernel (T : Tensor F (Fin 3) V) (hT : Concise T)
    (I : Ideal (centroidAlgebra T hT)) [I.IsMaximal] (hI : IsNilpotent I) (i : Fin 3) :
    Module.finrank F (centroidAlgebra T hT ⧸ I) ∣
      Module.finrank F (commonKernel (centroidIdealSpace T hT I) i) := by
  let := centroidModule T hT i
  let := centroidModuleScalarTower T hT i
  let K := General.idealKernel (M := V i → F) I
  let : FiniteDimensional F K := Module.Finite.of_injective
    (K.subtype.restrictScalars F) K.subtype_injective
  have hd := General.residue_degree_dvd_finrank (F := F) (M := K) I hI
  change Module.finrank F (centroidAlgebra T hT ⧸ I) ∣
    Module.finrank F (General.idealKernel (M := V i → F) I) at hd
  simpa only [centroidModule_kernel_finrank] using hd

theorem centroid_residue_degree_dvd_codim (T : Tensor F (Fin 3) V) (hT : Concise T)
    (I : Ideal (centroidAlgebra T hT)) [I.IsMaximal] (hI : IsNilpotent I) (i : Fin 3) :
    Module.finrank F (centroidAlgebra T hT ⧸ I) ∣
      Fintype.card (V i) - Module.finrank F (commonKernel (centroidIdealSpace T hT I) i) :=
  Nat.dvd_sub (centroid_residue_degree_dvd_leg T hT I hI i)
    (centroid_residue_degree_dvd_kernel T hT I hI i)

end Lemmata.Centroid.Tensor
