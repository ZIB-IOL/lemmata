module

public import Lemmata.Centroid.Proof.General.ResidueDimension
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public section

open scoped Pointwise
open Classical

noncomputable section

namespace Lemmata.Centroid.General

variable {F A M : Type*} [Field F] [CommRing A] [Algebra F A]
variable [AddCommGroup M] [Module F M] [Module A M] [IsScalarTower F A M]

def annihilatorInIdeal (I : Ideal A) : Ideal A := I ⊓ Module.annihilator A I

theorem exists_socle_element (I J : Ideal A) (hI : IsNilpotent I) (hJ : J ≠ ⊥) :
    ∃ c : A, c ∈ J ∧ c ≠ 0 ∧ c ∈ Module.annihilator A I := by
  obtain ⟨x, hx, hx0⟩ := J.ne_bot_iff.mp hJ
  let : Nontrivial J := ⟨⟨⟨x, hx⟩, 0, fun h => hx0 (congrArg Subtype.val h)⟩⟩
  obtain ⟨c, hc, hc0⟩ := (idealKernel (M := J) I).ne_bot_iff.mp
    (idealKernel_ne_bot_of_isNilpotent (M := J) I hI)
  refine ⟨c.1, c.2, fun h => hc0 (Subtype.ext h), ?_⟩
  apply Module.mem_annihilator.mpr
  intro a
  apply Subtype.ext
  have hh := congrArg Subtype.val (hc a.1 a.2)
  change a.1 * c.1 = 0 at hh
  change c.1 * a.1 = 0
  simpa only [mul_comm] using hh

theorem annihilatorInIdeal_ne_bot (I : Ideal A) (hI : IsNilpotent I) (hI0 : I ≠ ⊥) :
    annihilatorInIdeal I ≠ ⊥ := by
  obtain ⟨c, hc, hc0, hann⟩ := exists_socle_element I I hI hI0
  exact (annihilatorInIdeal I).ne_bot_iff.mpr ⟨c, ⟨hc, hann⟩, hc0⟩

theorem idealImage_le_annihilatorKernel (I : Ideal A) :
    idealImage (M := M) I ≤ idealKernel (M := M) (annihilatorInIdeal I) := by
  apply Submodule.smul_le.mpr
  intro a ha x _ c hc
  have hca : c * a = 0 :=
    congrArg Subtype.val ((Module.mem_annihilator.mp hc.2) ⟨a, ha⟩)
  calc
    c • (a • x) = (c * a) • x := (mul_smul c a x).symm
    _ = 0 := by rw [hca, zero_smul]

def subspaceAnnihilator (W : Submodule F M) : Ideal A where
  carrier := {c | ∀ w ∈ W, c • w = 0}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb w hw
    rw [add_smul, ha w hw, hb w hw, add_zero]
  smul_mem' := by
    intro a b hb w hw
    change (a * b) • w = 0
    rw [mul_smul, hb w hw, smul_zero]

theorem inf_subspaceAnnihilator_eq_bot [FaithfulSMul A M]
    (I : Ideal A) (hI : IsNilpotent I) (W : Submodule F M)
    (hspan : (idealKernel (M := M) (annihilatorInIdeal I)).restrictScalars F ⊔ W = ⊤) :
    I ⊓ subspaceAnnihilator (A := A) W = ⊥ := by
  by_contra hne
  obtain ⟨c, hc, hc0, hann⟩ := exists_socle_element I
    (I ⊓ subspaceAnnihilator (A := A) W) hI hne
  have hsoc : c ∈ annihilatorInIdeal I := ⟨hc.1, hann⟩
  apply hc0
  apply eq_of_smul_eq_smul (α := M)
  intro x
  have hx : x ∈ (idealKernel (M := M) (annihilatorInIdeal I)).restrictScalars F ⊔ W := by
    rw [hspan]
    exact Submodule.mem_top
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
  rw [smul_add, hy c hsoc, hc.2 z hz, add_zero, zero_smul]

def annihilatorRestriction (I : Ideal A) (W : Submodule F M) :
    I →ₗ[F] (W →ₗ[F] idealKernel (M := M) (annihilatorInIdeal I)) where
  toFun c :=
    { toFun := fun w => ⟨c.1 • w.1,
        idealImage_le_annihilatorKernel I (Submodule.smul_mem_smul c.2 (Submodule.mem_top))⟩
      map_add' := fun x y => Subtype.ext (smul_add _ _ _)
      map_smul' := fun a x => Subtype.ext (smul_comm _ a x.1) }
  map_add' c d := by
    ext w
    exact add_smul c.1 d.1 w.1
  map_smul' a c := by
    ext w
    exact smul_assoc a c.1 w.1

theorem annihilatorRestriction_injective [FaithfulSMul A M]
    (I : Ideal A) (hI : IsNilpotent I) (W : Submodule F M)
    (hspan : (idealKernel (M := M) (annihilatorInIdeal I)).restrictScalars F ⊔ W = ⊤) :
    Function.Injective (annihilatorRestriction (F := F) I W) := by
  intro c d h
  apply sub_eq_zero.mp
  have hm : ((c - d : I) : A) ∈ I ⊓ subspaceAnnihilator (A := A) W := by
    refine ⟨(c - d).2, ?_⟩
    intro w hw
    have he := LinearMap.congr_fun h ⟨w, hw⟩
    have he' : c.1 • w = d.1 • w := congrArg Subtype.val he
    simpa only [Submodule.coe_sub, sub_smul] using sub_eq_zero.mpr he'
  rw [inf_subspaceAnnihilator_eq_bot I hI W hspan] at hm
  exact Subtype.ext hm

theorem ideal_dimension_le_annihilatorKernel_mul_complement
    [FiniteDimensional F M] [FiniteDimensional F A] [FaithfulSMul A M]
    (I : Ideal A) (hI : IsNilpotent I) :
    Module.finrank F I ≤
      Module.finrank F (idealKernel (M := M) (annihilatorInIdeal I)) *
        (Module.finrank F M - Module.finrank F (idealKernel (M := M) (annihilatorInIdeal I))) := by
  let H := idealKernel (M := M) (annihilatorInIdeal I)
  let : FiniteDimensional F H := Module.Finite.of_injective
    (H.subtype.restrictScalars F) H.subtype_injective
  let : Module.Free F H := Module.Free.of_divisionRing F _
  obtain ⟨W, hW⟩ := (H.restrictScalars F).exists_isCompl
  have hd := LinearMap.finrank_le_finrank_of_injective
    (annihilatorRestriction_injective I hI W hW.sup_eq_top)
  rw [Module.finrank_linearMap] at hd
  have hdim : Module.finrank F (H.restrictScalars F) + Module.finrank F W = Module.finrank F M :=
    Submodule.finrank_add_eq_of_isCompl hW
  have hw : Module.finrank F W = Module.finrank F M - Module.finrank F H := by
    change Module.finrank F H + Module.finrank F W = Module.finrank F M at hdim
    omega
  simpa only [hw, Nat.mul_comm] using hd

end Lemmata.Centroid.General
