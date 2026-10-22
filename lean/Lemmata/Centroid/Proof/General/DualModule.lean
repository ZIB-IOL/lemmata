module

public import Lemmata.Centroid.Proof.General.AnnihilatorQuotient
public import Mathlib.LinearAlgebra.Dual.Lemmas

@[expose] public section

open scoped Pointwise
open Classical

noncomputable section

namespace Lemmata.Centroid.General

variable {F A M : Type*} [Field F] [CommRing A] [Algebra F A]
variable [AddCommGroup M] [Module F M] [Module A M] [IsScalarTower F A M]

@[instance_reducible] def dualModule : Module A (Module.Dual F M) where
  smul a φ :=
    { toFun := fun x => φ (a • x)
      map_add' := fun x y => by rw [smul_add, map_add]
      map_smul' := fun r x => by simpa only [RingHom.id_apply] using
        (congrArg φ (smul_comm a r x)).trans (map_smul φ r (a • x)) }
  one_smul φ := by ext x; exact congrArg φ (one_smul A x)
  mul_smul a b φ := by ext x; exact congrArg φ (by rw [mul_comm a b, mul_smul])
  smul_zero a := by ext x; rfl
  smul_add a φ ψ := by ext x; rfl
  add_smul a b φ := by ext x; exact (congrArg φ (add_smul a b x)).trans (map_add φ _ _)
  zero_smul φ := by ext x; change φ ((0 : A) • x) = 0; rw [zero_smul, map_zero]

section DualAction

local instance (priority := low) : Module A (Module.Dual F M) := dualModule

instance dualModuleScalarTower : IsScalarTower F A (Module.Dual F M) where
  smul_assoc r a φ := by
    ext x
    change φ ((r • a) • x) = r • φ (a • x)
    rw [smul_assoc, map_smul]

theorem dualModule_smul_apply (a : A) (φ : Module.Dual F M) (x : M) :
    (a • φ) x = φ (a • x) := rfl

instance dualModuleFaithful [FaithfulSMul A M] : FaithfulSMul A (Module.Dual F M) where
  eq_of_smul_eq_smul h := by
    apply eq_of_smul_eq_smul (α := M)
    intro x
    apply sub_eq_zero.mp
    apply (Module.forall_dual_apply_eq_zero_iff F _).mp
    intro φ
    rw [map_sub]
    exact sub_eq_zero.mpr (LinearMap.congr_fun (h φ) x)

theorem dualIdealImage_coannihilator (I : Ideal A) :
    ((idealImage (M := Module.Dual F M) I).restrictScalars F).dualCoannihilator =
      (idealKernel (M := M) I).restrictScalars F := by
  ext x
  rw [Submodule.mem_dualCoannihilator]
  constructor
  · intro hx a ha
    apply (Module.forall_dual_apply_eq_zero_iff F _).mp
    intro φ
    have hmem : a • φ ∈ idealImage (M := Module.Dual F M) I :=
      Submodule.smul_mem_smul ha Submodule.mem_top
    exact hx (a • φ) hmem
  · intro hx φ hφ
    change φ ∈ I • (⊤ : Submodule A (Module.Dual F M)) at hφ
    refine Submodule.smul_induction_on (p := fun ψ : Module.Dual F M => ψ x = 0)
      hφ (fun a ha ψ _ => ?_) (fun ψ χ hψ hχ => ?_)
    · change ψ (a • x) = 0
      rw [hx a ha, map_zero]
    · change ψ x + χ x = 0
      rw [hψ, hχ, zero_add]

theorem dualIdealImage_finrank [FiniteDimensional F M] (I : Ideal A) :
    Module.finrank F (idealImage (M := Module.Dual F M) I) =
      Module.finrank F M - Module.finrank F (idealKernel (M := M) I) := by
  have hd := Subspace.finrank_add_finrank_dualCoannihilator_eq
    ((idealImage (M := Module.Dual F M) I).restrictScalars F)
  rw [dualIdealImage_coannihilator] at hd
  change Module.finrank F (idealImage (M := Module.Dual F M) I) +
    Module.finrank F (idealKernel (M := M) I) = Module.finrank F M at hd
  omega

theorem dualIdealImage_quotient_finrank [FiniteDimensional F M] (I : Ideal A) :
    Module.finrank F (Module.Dual F M ⧸ idealImage (M := Module.Dual F M) I) =
      Module.finrank F (idealKernel (M := M) I) := by
  rw [Submodule.finrank_quotient, Subspace.dual_finrank_eq, dualIdealImage_finrank]
  have hd : Module.finrank F (idealKernel (M := M) I) ≤ Module.finrank F M :=
    LinearMap.finrank_le_finrank_of_injective
      (f := (idealKernel (M := M) I).subtype.restrictScalars F) Subtype.val_injective
  omega

theorem ideal_dimension_le_kernel_mul_codim [FiniteDimensional F M]
    [FiniteDimensional F A] [FaithfulSMul A M] (I : Ideal A)
    (hI : I ≤ Ideal.jacobson (⊥ : Ideal A)) :
    Module.finrank F I ≤ Module.finrank F (idealKernel (M := M) I) *
      (Module.finrank F M - Module.finrank F (idealKernel (M := M) I)) := by
  simpa only [dualIdealImage_quotient_finrank, dualIdealImage_finrank] using
    ideal_dimension_le_quotient_mul_image (F := F) (M := Module.Dual F M) I hI

theorem ideal_dimension_mul_residue_le_kernel_mul_codim [FiniteDimensional F M]
    [FiniteDimensional F A] [FaithfulSMul A M] (I : Ideal A) [I.IsMaximal]
    (hI : I ≤ Ideal.jacobson (⊥ : Ideal A)) :
    Module.finrank F I * Module.finrank F (A ⧸ I) ≤
      Module.finrank F (idealKernel (M := M) I) *
        (Module.finrank F M - Module.finrank F (idealKernel (M := M) I)) := by
  simpa only [dualIdealImage_quotient_finrank, dualIdealImage_finrank] using
    ideal_dimension_mul_residue_le_quotient_mul_image
      (F := F) (M := Module.Dual F M) I hI

end DualAction

theorem nilpotentIdeal_le_jacobson (I : Ideal A) (hI : IsNilpotent I) :
    I ≤ Ideal.jacobson (⊥ : Ideal A) := by
  apply le_trans _ Ideal.radical_le_jacobson
  intro a ha
  obtain ⟨n, hn⟩ := hI
  refine ⟨n, ?_⟩
  have hp := Ideal.pow_mem_pow ha n
  change I ^ n = ⊥ at hn
  rw [hn] at hp
  exact hp

theorem nilpotent_ideal_dimension_le_kernel_mul_codim [FiniteDimensional F M]
    [FiniteDimensional F A] [FaithfulSMul A M] (I : Ideal A) (hI : IsNilpotent I) :
    Module.finrank F I ≤ Module.finrank F (idealKernel (M := M) I) *
      (Module.finrank F M - Module.finrank F (idealKernel (M := M) I)) :=
  ideal_dimension_le_kernel_mul_codim I (nilpotentIdeal_le_jacobson I hI)

end Lemmata.Centroid.General
