module

public import Lemmata.Centroid.Proof.General.LocalBound
public import Mathlib.LinearAlgebra.Dimension.DivisionRing

@[expose] public section

open scoped Pointwise
open Classical

noncomputable section

namespace Lemmata.Centroid.General

variable {F A M : Type*} [Field F] [CommRing A] [Algebra F A]
variable [AddCommGroup M] [Module F M] [Module A M] [IsScalarTower F A M]

theorem idealKernel_finrank_pos [FiniteDimensional F M] [Nontrivial M]
    (I : Ideal A) (hI : IsNilpotent I) : 0 < Module.finrank F (idealKernel (M := M) I) := by
  let : FiniteDimensional F (idealKernel (M := M) I) := Module.Finite.of_injective
    ((idealKernel (M := M) I).subtype.restrictScalars F) (idealKernel (M := M) I).subtype_injective
  apply Module.finrank_pos_iff_exists_ne_zero.mpr
  obtain ⟨x, hx, hx0⟩ := (idealKernel (M := M) I).ne_bot_iff.mp
    (idealKernel_ne_bot_of_isNilpotent I hI)
  exact ⟨⟨x, hx⟩, fun h => hx0 (congrArg Subtype.val h)⟩

theorem residue_degree_dvd_quotient_finrank [FiniteDimensional F M] [FiniteDimensional F A]
    (I : Ideal A) [I.IsMaximal] :
    Module.finrank F (A ⧸ I) ∣ Module.finrank F (M ⧸ idealImage (M := M) I) := by
  let : Field (A ⧸ I) := Ideal.Quotient.field I
  let Q := M ⧸ idealImage (M := M) I
  let : FiniteDimensional F Q := Module.Finite.of_surjective
    ((idealImage (M := M) I).mkQ.restrictScalars F) (idealImage (M := M) I).mkQ_surjective
  let : FiniteDimensional F (A ⧸ I) := Module.Finite.of_surjective
    (Ideal.Quotient.mkₐ F I).toLinearMap Ideal.Quotient.mk_surjective
  let : Module.Free F (A ⧸ I) := Module.Free.of_divisionRing F _
  let : FiniteDimensional (A ⧸ I) Q := Module.Finite.of_restrictScalars_finite F (A ⧸ I) Q
  let : Module.Free (A ⧸ I) Q := Module.Free.of_divisionRing _ _
  exact ⟨Module.finrank (A ⧸ I) Q, (Module.finrank_mul_finrank F (A ⧸ I) Q).symm⟩

theorem residue_degree_dvd_finrank_of_power_image_eq_bot
    [FiniteDimensional F M] [FiniteDimensional F A]
    (I : Ideal A) [I.IsMaximal] (n : ℕ) (hn : I ^ n • (⊤ : Submodule A M) = ⊥) :
    Module.finrank F (A ⧸ I) ∣ Module.finrank F M := by
  induction n generalizing M with
  | zero =>
    simp only [pow_zero, Ideal.one_eq_top, Submodule.top_smul] at hn
    have hx (x : M) : x = 0 := hn.le (Submodule.mem_top)
    let : Subsingleton M := ⟨fun x y => (hx x).trans (hx y).symm⟩
    rw [Module.finrank_zero_of_subsingleton (R := F) (M := M)]
    exact dvd_zero _
  | succ n ih =>
    let J := idealImage (M := M) I
    let : FiniteDimensional F J := Module.Finite.of_injective
      (J.subtype.restrictScalars F) J.subtype_injective
    have hJ : I ^ n • (⊤ : Submodule A J) = ⊥ := by
      apply le_antisymm _ bot_le
      apply Submodule.smul_le.mpr
      intro a ha x _
      apply Subtype.ext
      have hmem : a • x.1 ∈ I ^ n • (I • (⊤ : Submodule A M)) :=
        Submodule.smul_mem_smul ha x.2
      rw [← Submodule.mul_smul, ← pow_succ, hn] at hmem
      exact hmem
    have hdivJ := ih (M := J) hJ
    have hdivQ := residue_degree_dvd_quotient_finrank (F := F) (M := M) I
    have hdim : Module.finrank F (M ⧸ J) + Module.finrank F J = Module.finrank F M :=
      (J.restrictScalars F).finrank_quotient_add_finrank
    exact hdim ▸ dvd_add hdivQ hdivJ

theorem residue_degree_dvd_finrank [FiniteDimensional F M] [FiniteDimensional F A]
    (I : Ideal A) [I.IsMaximal] (hI : IsNilpotent I) :
    Module.finrank F (A ⧸ I) ∣ Module.finrank F M := by
  obtain ⟨n, hn⟩ := hI
  apply residue_degree_dvd_finrank_of_power_image_eq_bot (M := M) I n
  rw [hn]
  exact Submodule.bot_smul (R := A) (A := A) (M := M) (⊤ : Submodule A M)

end Lemmata.Centroid.General
