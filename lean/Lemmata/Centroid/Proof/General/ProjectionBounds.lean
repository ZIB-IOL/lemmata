module

public import Lemmata.Centroid.Proof.General.SecondKernel
public import Mathlib.LinearAlgebra.Projection

@[expose] public section

open Classical

noncomputable section

namespace Lemmata.Centroid.General

variable {F A M : Type*} [Field F] [CommRing A] [Algebra F A]
variable [AddCommGroup M] [Module F M] [Module A M] [IsScalarTower F A M]

def scalarAction (I : Ideal A) : I →ₗ[F] Module.End F M where
  toFun c :=
    { toFun := fun x => c.1 • x
      map_add' := smul_add c.1
      map_smul' := fun r x => smul_comm c.1 r x }
  map_add' c d := by ext x; exact add_smul c.1 d.1 x
  map_smul' r c := by ext x; exact smul_assoc r c.1 x

def leftProjectedAction (I : Ideal A) (P : Module.End F M) : I →ₗ[F] Module.End F M :=
  (LinearMap.llcomp F M M M P).comp (scalarAction I)

def leftProjectedKernel (I : Ideal A) (P : Module.End F M) : Submodule F M :=
  ⨅ c : I, (leftProjectedAction I P c).ker

def rightProjectedKernel (I : Ideal A) (P : Module.End F M) : Submodule F M :=
  ⨅ c : I, ((scalarAction I c).comp P).ker

theorem leftProjectedKernel_eq_secondKernel (I : Ideal A) (P : Module.End F M)
    (hP : P.ker = (idealKernel (M := M) I).restrictScalars F) :
    leftProjectedKernel I P = (secondKernel (M := M) I).restrictScalars F := by
  ext x
  simp only [leftProjectedKernel, Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · intro hx c hc
    have hp : c • x ∈ P.ker := hx ⟨c, hc⟩
    rw [hP] at hp
    exact hp
  · intro hx c
    have hp : c.1 • x ∈ P.ker := hP.symm ▸ hx c.1 c.2
    exact hp

theorem leftProjectedKernel_codim [FiniteDimensional F M] [FaithfulSMul A M]
    (I : Ideal A) (P : Module.End F M)
    (hP : P.ker = (idealKernel (M := M) I).restrictScalars F) :
    Module.finrank F M - Module.finrank F (leftProjectedKernel I P) =
      Module.finrank F (ProjectedModule A M I) - Module.finrank F (projectedKernel (M := M) I) := by
  rw [leftProjectedKernel_eq_secondKernel I P hP, projectedModule_finrank]
  have hd := projectedKernel_finrank_add_kernel (F := F) (M := M) I
  change Module.finrank F (projectedKernel (M := M) I) +
    Module.finrank F (idealKernel (M := M) I) =
      Module.finrank F ((secondKernel (M := M) I).restrictScalars F) at hd
  omega

theorem rightProjectedKernel_codim_le [FiniteDimensional F M] (I : Ideal A)
    (H : Submodule F M) (P : Module.End F M) (hP : P.comp P = P) (hrange : P.range = H)
    (hK : (idealKernel (M := M) I).restrictScalars F ≤ H) :
    Module.finrank F M - Module.finrank F (rightProjectedKernel I P) ≤
      Module.finrank F H - Module.finrank F (idealKernel (M := M) I) := by
  let K := (idealKernel (M := M) I).restrictScalars F
  have hfixed {x : M} (hx : x ∈ H) : P x = x := by
    obtain ⟨y, rfl⟩ := hrange.symm ▸ hx
    exact LinearMap.congr_fun hP y
  have hKL : K ≤ rightProjectedKernel I P := by
    intro x hx
    rw [rightProjectedKernel, Submodule.mem_iInf]
    intro c
    change c.1 • P x = 0
    rw [hfixed (hK hx)]
    exact hx c.1 c.2
  have hPL : P.ker ≤ rightProjectedKernel I P := by
    intro x hx
    rw [rightProjectedKernel, Submodule.mem_iInf]
    intro c
    change c.1 • P x = 0
    rw [hx, smul_zero]
  have hdisj : Disjoint K P.ker := by
    apply disjoint_iff.mpr
    apply bot_unique
    intro x hx
    exact (hfixed (hK hx.1)).symm.trans hx.2
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq K P.ker
  rw [hdisj.eq_bot, finrank_bot, add_zero] at hsum
  have hle := Submodule.finrank_mono (sup_le hKL hPL)
  have hdim := P.finrank_range_add_finrank_ker
  rw [hrange] at hdim
  change Module.finrank F (K ⊔ P.ker : Submodule F M) =
    Module.finrank F (idealKernel (M := M) I) + Module.finrank F P.ker at hsum
  omega

theorem leftProjectedAction_ker [FaithfulSMul A M] (I : Ideal A) (P : Module.End F M)
    (hP : P.ker = (idealKernel (M := M) I).restrictScalars F) :
    (leftProjectedAction I P).ker = annihilatorSubspace (F := F) I := by
  ext c
  change leftProjectedAction I P c = 0 ↔ c.1 ∈ annihilatorInIdeal I
  constructor
  · intro hc
    refine ⟨c.2, Module.mem_annihilator.mpr fun a => ?_⟩
    apply Subtype.ext
    apply eq_of_smul_eq_smul (α := M)
    intro x
    have hp : c.1 • x ∈ P.ker := LinearMap.congr_fun hc x
    rw [hP] at hp
    have hk : c.1 • x ∈ idealKernel (M := M) I := hp
    change (c.1 * a.1) • x = (0 : A) • x
    rw [mul_comm c.1 a.1, mul_smul, hk a.1 a.2, zero_smul]
  · intro hc
    apply LinearMap.ext
    intro x
    have hp : c.1 • x ∈ P.ker := by
      rw [hP]
      intro a ha
      have hca : c.1 * a = 0 :=
        congrArg Subtype.val ((Module.mem_annihilator.mp hc.2) ⟨a, ha⟩)
      rw [← mul_smul, mul_comm a c.1, hca, zero_smul]
    exact hp

theorem leftProjectedAction_range_finrank [FiniteDimensional F A] [FaithfulSMul A M]
    (I : Ideal A) (P : Module.End F M)
    (hP : P.ker = (idealKernel (M := M) I).restrictScalars F) :
    Module.finrank F (leftProjectedAction I P).range =
      Module.finrank F (AnnihilatorQuotient F A I) := by
  have he := (leftProjectedAction I P).quotKerEquivRange
  rw [leftProjectedAction_ker I P hP] at he
  exact he.finrank_eq.symm

end Lemmata.Centroid.General
