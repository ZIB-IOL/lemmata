module

public import Lemmata.Centroid.Proof.General.ProjectedAction

@[expose] public section

open Classical

noncomputable section

namespace Lemmata.Centroid.General

variable {F A M : Type*} [Field F] [CommRing A] [Algebra F A]
variable [AddCommGroup M] [Module F M] [Module A M] [IsScalarTower F A M]

def secondKernel (I : Ideal A) : Submodule A M where
  carrier := {x | ∀ a ∈ I, a • x ∈ idealKernel (M := M) I}
  zero_mem' := by intro a ha; simp
  add_mem' := by
    intro x y hx hy a ha
    rw [smul_add]
    exact (idealKernel (M := M) I).add_mem (hx a ha) (hy a ha)
  smul_mem' := by
    intro r x hx a ha
    rw [smul_comm a r x]
    exact (idealKernel (M := M) I).smul_mem r (hx a ha)

theorem idealKernel_le_secondKernel (I : Ideal A) :
    idealKernel (M := M) I ≤ secondKernel (M := M) I := by
  intro x hx a ha
  rw [hx a ha]
  exact (idealKernel (M := M) I).zero_mem

theorem projectedKernel_mk_iff [FaithfulSMul A M] (I : Ideal A) (x : M) :
    (idealKernel (M := M) I).mkQ x ∈ projectedKernel (M := M) I ↔
      x ∈ secondKernel (M := M) I := by
  constructor
  · intro hx a ha
    apply (Submodule.Quotient.mk_eq_zero _).mp
    exact hx (Ideal.Quotient.mk (Module.annihilator A I) a) (Ideal.mem_map_of_mem _ ha)
  · intro hx c hc
    obtain ⟨a, ha, rfl⟩ :=
      (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hc
    exact (Submodule.Quotient.mk_eq_zero _).mpr (hx a ha)

def secondKernelProjection [FaithfulSMul A M] (I : Ideal A) :
    secondKernel (M := M) I →ₗ[F] projectedKernel (M := M) I where
  toFun x := ⟨(idealKernel (M := M) I).mkQ x.1, (projectedKernel_mk_iff I x.1).mpr x.2⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' r x := Subtype.ext (map_smul ((idealKernel (M := M) I).mkQ.restrictScalars F) r x.1)

theorem secondKernelProjection_surjective [FaithfulSMul A M] (I : Ideal A) :
    Function.Surjective (secondKernelProjection (F := F) (M := M) I) := by
  intro y
  obtain ⟨x, hx⟩ := (idealKernel (M := M) I).mkQ_surjective y.1
  have hx' : x ∈ secondKernel (M := M) I :=
    (projectedKernel_mk_iff I x).mp (hx.symm ▸ y.2)
  exact ⟨⟨x, hx'⟩, Subtype.ext hx⟩

theorem secondKernelProjection_ker [FaithfulSMul A M] (I : Ideal A) :
    (secondKernelProjection (F := F) (M := M) I).ker =
      ((idealKernel (M := M) I).restrictScalars F).comap
        ((secondKernel (M := M) I).subtype.restrictScalars F) := by
  ext x
  change secondKernelProjection (F := F) I x = 0 ↔ x.1 ∈ idealKernel (M := M) I
  rw [Subtype.ext_iff]
  exact Submodule.Quotient.mk_eq_zero _

theorem secondKernelProjection_ker_finrank [FiniteDimensional F M] [FaithfulSMul A M]
    (I : Ideal A) :
    Module.finrank F (secondKernelProjection (F := F) (M := M) I).ker =
      Module.finrank F (idealKernel (M := M) I) := by
  rw [secondKernelProjection_ker]
  exact (Submodule.comap_equiv_self_of_inj_of_le
    (f := (secondKernel (M := M) I).subtype.restrictScalars F)
    (p := (idealKernel (M := M) I).restrictScalars F) Subtype.val_injective
    (fun x hx => ⟨⟨x, idealKernel_le_secondKernel I hx⟩, rfl⟩)).finrank_eq

theorem projectedKernel_finrank_add_kernel [FiniteDimensional F M] [FaithfulSMul A M]
    (I : Ideal A) :
    Module.finrank F (projectedKernel (M := M) I) +
      Module.finrank F (idealKernel (M := M) I) =
        Module.finrank F (secondKernel (M := M) I) := by
  let L := secondKernel (M := M) I
  let : FiniteDimensional F L := Module.Finite.of_injective
    (L.subtype.restrictScalars F) L.subtype_injective
  have hd := (secondKernelProjection (F := F) (M := M) I).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (secondKernelProjection_surjective I), finrank_top,
    secondKernelProjection_ker_finrank] at hd
  exact hd

theorem projectedKernel_finrank [FiniteDimensional F M] [FaithfulSMul A M]
    (I : Ideal A) :
    Module.finrank F (projectedKernel (M := M) I) =
      Module.finrank F (secondKernel (M := M) I) -
        Module.finrank F (idealKernel (M := M) I) := by
  have h := projectedKernel_finrank_add_kernel (F := F) (M := M) I
  omega

end Lemmata.Centroid.General
