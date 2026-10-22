module

public import Lemmata.Centroid.Proof.General.DualModule

@[expose] public section

open scoped Pointwise
open Classical

noncomputable section

namespace Lemmata.Centroid.General

variable {F A M : Type*} [Field F] [CommRing A] [Algebra F A]
variable [AddCommGroup M] [Module F M] [Module A M] [IsScalarTower F A M]

theorem idealKernel_eq_top_iff [FaithfulSMul A M] (I : Ideal A) :
    idealKernel (M := M) I = ⊤ ↔ I = ⊥ := by
  constructor
  · intro h
    apply le_antisymm _ bot_le
    intro a ha
    apply eq_of_smul_eq_smul (α := M)
    intro x
    have hx : x ∈ idealKernel (M := M) I := h.symm ▸ Submodule.mem_top
    rw [hx a ha, zero_smul]
  · rintro rfl
    ext x
    simp [idealKernel]

theorem idealKernel_lt_annihilatorKernel [FaithfulSMul A M] (I : Ideal A)
    (hI : I ^ 2 ≠ ⊥) :
    idealKernel (M := M) I < idealKernel (M := M) (annihilatorInIdeal I) := by
  refine lt_of_le_of_ne (idealKernel_antitone inf_le_left) ?_
  intro heq
  apply hI
  apply le_antisymm _ bot_le
  rw [pow_two]
  apply Ideal.mul_le.mpr
  intro a ha b hb
  apply eq_of_smul_eq_smul (α := M)
  intro x
  have hbx : b • x ∈ idealKernel (M := M) I :=
    heq.symm ▸ idealImage_le_annihilatorKernel I
      (Submodule.smul_mem_smul hb Submodule.mem_top)
  rw [mul_smul, hbx a ha, zero_smul]

theorem annihilatorInIdeal_lt (I : Ideal A) (hI : I ^ 2 ≠ ⊥) :
    annihilatorInIdeal I < I := by
  refine lt_of_le_of_ne inf_le_left ?_
  intro heq
  apply hI
  apply le_antisymm _ bot_le
  rw [pow_two]
  apply Ideal.mul_le.mpr
  intro a ha b hb
  have ha' : a ∈ Module.annihilator A I := (heq.symm ▸ ha).2
  exact congrArg Subtype.val ((Module.mem_annihilator.mp ha') ⟨b, hb⟩)

theorem middleQuotient_finrank_pos [FiniteDimensional F M] [FaithfulSMul A M]
    (I : Ideal A) (hI : I ^ 2 ≠ ⊥) :
    0 < Module.finrank F (MiddleQuotient F A M I) := by
  let H := idealKernel (M := M) (annihilatorInIdeal I)
  let : FiniteDimensional F H := Module.Finite.of_injective
    (H.subtype.restrictScalars F) H.subtype_injective
  have hd := Submodule.finrank_lt_finrank_of_lt
    (show (idealKernel (M := M) I).restrictScalars F < H.restrictScalars F from
      idealKernel_lt_annihilatorKernel I hI)
  rw [middleQuotient_finrank]
  change Module.finrank F (idealKernel (M := M) I) < Module.finrank F H at hd
  change 0 < Module.finrank F H - Module.finrank F (idealKernel (M := M) I)
  omega

theorem annihilatorQuotient_finrank_pos [FiniteDimensional F A]
    (I : Ideal A) (hI : I ^ 2 ≠ ⊥) :
    0 < Module.finrank F (AnnihilatorQuotient F A I) := by
  let : FiniteDimensional F I := Module.Finite.of_injective
    (I.subtype.restrictScalars F) I.subtype_injective
  have hd := Submodule.finrank_lt_finrank_of_lt
    (show (annihilatorInIdeal I).restrictScalars F < I.restrictScalars F from
      annihilatorInIdeal_lt I hI)
  rw [annihilatorQuotient_finrank]
  change Module.finrank F (annihilatorInIdeal I) < Module.finrank F I at hd
  omega

theorem annihilatorKernel_codim_pos [FiniteDimensional F M] [FaithfulSMul A M]
    (I : Ideal A) (hI : IsNilpotent I) (hI0 : I ≠ ⊥) :
    0 < Module.finrank F M -
      Module.finrank F (idealKernel (M := M) (annihilatorInIdeal I)) := by
  have hlt : idealKernel (M := M) (annihilatorInIdeal I) < ⊤ :=
    lt_top_iff_ne_top.mpr fun h => annihilatorInIdeal_ne_bot I hI hI0
      ((idealKernel_eq_top_iff (M := M) _).mp h)
  have hd := Submodule.finrank_lt_finrank_of_lt
    (show (idealKernel (M := M) (annihilatorInIdeal I)).restrictScalars F < ⊤ from hlt)
  rw [finrank_top] at hd
  change Module.finrank F (idealKernel (M := M) (annihilatorInIdeal I)) < Module.finrank F M at hd
  omega

instance projectedScalarTower (I : Ideal A) :
    IsScalarTower F A (M ⧸ idealKernel (M := M) I) where
  smul_assoc r a x := Quotient.inductionOn' x fun m =>
    congrArg (Submodule.Quotient.mk (p := idealKernel (M := M) I)) (smul_assoc r a m)

theorem projected_annihilator [FaithfulSMul A M] (I : Ideal A) :
    Module.annihilator A (M ⧸ idealKernel (M := M) I) = Module.annihilator A I := by
  ext a
  rw [Module.mem_annihilator, Module.mem_annihilator]
  constructor
  · intro ha c
    apply Subtype.ext
    apply eq_of_smul_eq_smul (α := M)
    intro x
    have hax : a • x ∈ idealKernel (M := M) I := by
      apply (Submodule.Quotient.mk_eq_zero _).mp
      exact ha ((idealKernel (M := M) I).mkQ x)
    change (a * c.1) • x = (0 : A) • x
    rw [mul_comm a c.1, mul_smul, hax c.1 c.2, zero_smul]
  · intro ha x
    refine Quotient.inductionOn' x fun x => ?_
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    intro c hc
    have hac : a * c = 0 := congrArg Subtype.val (ha ⟨c, hc⟩)
    change c • (a • x) = 0
    rw [← mul_smul, mul_comm c a, hac, zero_smul]

end Lemmata.Centroid.General
