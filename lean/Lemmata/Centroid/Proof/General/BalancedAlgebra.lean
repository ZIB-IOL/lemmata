module

public import Lemmata.Centroid.Proof.General.CentroidBounds

@[expose] public section

open scoped BigOperators
open Classical

noncomputable section

namespace Lemmata.Centroid.Tensor.BalancedAlgebra

variable {F A : Type*} [Field F] [CommRing A] [Algebra F A]
variable {V : Fin 3 → Type*} [∀ i, Fintype (V i)]
variable (T : Tensor F (Fin 3) V) (hT : Concise T)
variable (f : A →ₐ[F] centroidAlgebra T hT)

def idealSpace (I : Ideal A) : Submodule F (∀ i, Matrix (V i) (V i) F) :=
  (I.restrictScalars F).map ((centroidAlgebra T hT).val.toLinearMap.comp f.toLinearMap)

theorem idealSpace_le (I : Ideal A) : idealSpace T hT f I ≤ centroid T := by
  rintro _ ⟨c, _, rfl⟩
  exact (f c).2

theorem idealSpace_finrank (hf : Function.Injective f) (I : Ideal A) :
    Module.finrank F (idealSpace T hT f I) = Module.finrank F I := by
  let g : I →ₗ[F] (∀ i, Matrix (V i) (V i) F) :=
    ((centroidAlgebra T hT).val.toLinearMap.comp f.toLinearMap).comp
      (I.subtype.restrictScalars F)
  have hg : Function.Injective g := fun x y h => Subtype.ext (hf (Subtype.ext h))
  have hr : g.range = idealSpace T hT f I := by
    ext B
    constructor
    · rintro ⟨c, rfl⟩; exact ⟨c.1, c.2, rfl⟩
    · rintro ⟨c, hc, rfl⟩; exact ⟨⟨c, hc⟩, rfl⟩
  rw [← hr]
  exact LinearMap.finrank_range_of_inj hg

@[instance_reducible] def legModule (i : Fin 3) : Module A (V i → F) :=
  Module.compHom _ ((centroidRepresentation T hT i).comp f).toRingHom

theorem legScalarTower (i : Fin 3) :
    let := legModule T hT f i
    IsScalarTower F A (V i → F) := by
  let := legModule T hT f i
  constructor
  intro r c u
  change centroidRepresentation T hT i (f (r • c)) u =
    r • centroidRepresentation T hT i (f c) u
  have he := f.toLinearMap.map_smul r c
  change f (r • c) = r • f c at he
  rw [he, map_smul]
  rfl

theorem legFaithful (hf : Function.Injective f) (i : Fin 3) :
    let := legModule T hT f i
    FaithfulSMul A (V i → F) := by
  let := legModule T hT f i
  constructor
  intro c d h
  apply hf
  apply centroidRepresentation_injective hT i
  exact LinearMap.ext h

theorem leg_idealKernel (I : Ideal A) (i : Fin 3) :
    let := legModule T hT f i
    let := legScalarTower T hT f i
    (General.idealKernel (M := V i → F) I).restrictScalars F =
      commonKernel (idealSpace T hT f I) i := by
  let := legModule T hT f i
  let := legScalarTower T hT f i
  ext u
  rw [mem_commonKernel]
  constructor
  · rintro hu _ ⟨c, hc, rfl⟩
    exact hu c hc
  · intro hu c hc
    exact hu (f c).val ⟨c, hc, rfl⟩

theorem leg_kernel_finrank (I : Ideal A) (i : Fin 3) :
    let := legModule T hT f i
    let := legScalarTower T hT f i
    Module.finrank F (General.idealKernel (M := V i → F) I) =
      Module.finrank F (commonKernel (idealSpace T hT f I) i) := by
  let := legModule T hT f i
  let := legScalarTower T hT f i
  change Module.finrank F ((General.idealKernel (M := V i → F) I).restrictScalars F) = _
  rw [leg_idealKernel]

variable [FiniteDimensional F A]

theorem nilpotent_ideal_kernel_bound (hf : Function.Injective f) (I : Ideal A)
    (hI : IsNilpotent I) (i : Fin 3) :
    Module.finrank F I ≤ Module.finrank F (commonKernel (idealSpace T hT f I) i) *
      (Fintype.card (V i) - Module.finrank F (commonKernel (idealSpace T hT f I) i)) := by
  let := legModule T hT f i
  let := legScalarTower T hT f i
  let := legFaithful T hT f hf i
  simpa only [leg_kernel_finrank, Module.finrank_pi] using
    General.nilpotent_ideal_dimension_le_kernel_mul_codim (F := F) (M := V i → F) I hI

theorem nilpotent_ideal_residue_bound (hf : Function.Injective f) (I : Ideal A)
    [I.IsMaximal] (hI : IsNilpotent I) (i : Fin 3) :
    Module.finrank F I * Module.finrank F (A ⧸ I) ≤
      Module.finrank F (commonKernel (idealSpace T hT f I) i) *
        (Fintype.card (V i) - Module.finrank F (commonKernel (idealSpace T hT f I) i)) := by
  let := legModule T hT f i
  let := legScalarTower T hT f i
  let := legFaithful T hT f hf i
  simpa only [leg_kernel_finrank, Module.finrank_pi] using
    General.ideal_dimension_mul_residue_le_kernel_mul_codim (F := F) (M := V i → F)
      I (General.nilpotentIdeal_le_jacobson I hI)

omit [FiniteDimensional F A] in
theorem ideal_product_bound (hf : Function.Injective f) (I : Ideal A) :
    Module.finrank F I ^ 2 ≤ ∏ i : Fin 3,
      (Fintype.card (V i) - Module.finrank F (commonKernel (idealSpace T hT f I) i)) := by
  simpa only [idealSpace_finrank T hT f hf I] using
    centroid_subspace_product_bound hT (idealSpace_le T hT f I)

theorem annihilator_difference_bound (hf : Function.Injective f) (I : Ideal A) (i : Fin 3) :
    Module.finrank F I - Module.finrank F (General.annihilatorInIdeal I) ≤
      ((Module.finrank F (commonKernel (idealSpace T hT f (General.annihilatorInIdeal I)) i) -
          Module.finrank F (commonKernel (idealSpace T hT f I) i)) + 1) ^ 2 / 4 := by
  let := legModule T hT f i
  let := legScalarTower T hT f i
  let := legFaithful T hT f hf i
  simpa only [leg_kernel_finrank] using
    General.annihilator_dimension_difference_bound (F := F) (M := V i → F) I

theorem nilpotent_ideal_annihilator_bound (hf : Function.Injective f) (I : Ideal A)
    (hI : IsNilpotent I) (i : Fin 3) :
    Module.finrank F I ≤
      Module.finrank F (commonKernel (idealSpace T hT f (General.annihilatorInIdeal I)) i) *
        (Fintype.card (V i) -
          Module.finrank F (commonKernel (idealSpace T hT f (General.annihilatorInIdeal I)) i)) := by
  let := legModule T hT f i
  let := legScalarTower T hT f i
  let := legFaithful T hT f hf i
  simpa only [leg_kernel_finrank, Module.finrank_pi] using
    General.ideal_dimension_le_annihilatorKernel_mul_complement (F := F) (M := V i → F) I hI

include T hT f in
theorem residue_degree_dvd_leg (I : Ideal A) [I.IsMaximal] (hI : IsNilpotent I) (i : Fin 3) :
    Module.finrank F (A ⧸ I) ∣ Fintype.card (V i) := by
  let := legModule T hT f i
  let := legScalarTower T hT f i
  simpa only [Module.finrank_pi] using
    General.residue_degree_dvd_finrank (F := F) (M := V i → F) I hI

theorem residue_degree_dvd_kernel (I : Ideal A) [I.IsMaximal]
    (hI : IsNilpotent I) (i : Fin 3) :
    Module.finrank F (A ⧸ I) ∣ Module.finrank F (commonKernel (idealSpace T hT f I) i) := by
  let := legModule T hT f i
  let := legScalarTower T hT f i
  let K := General.idealKernel (M := V i → F) I
  let : FiniteDimensional F K := Module.Finite.of_injective
    (K.subtype.restrictScalars F) K.subtype_injective
  have hd := General.residue_degree_dvd_finrank (F := F) (M := K) I hI
  change Module.finrank F (A ⧸ I) ∣
    Module.finrank F (General.idealKernel (M := V i → F) I) at hd
  simpa only [leg_kernel_finrank] using hd

theorem residue_degree_dvd_codim (I : Ideal A) [I.IsMaximal] (hI : IsNilpotent I) (i : Fin 3) :
    Module.finrank F (A ⧸ I) ∣
      Fintype.card (V i) - Module.finrank F (commonKernel (idealSpace T hT f I) i) :=
  Nat.dvd_sub (residue_degree_dvd_leg T hT f I hI i) (residue_degree_dvd_kernel T hT f I hI i)

end Lemmata.Centroid.Tensor.BalancedAlgebra
