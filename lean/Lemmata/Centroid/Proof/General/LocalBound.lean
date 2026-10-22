module

public import Mathlib.RingTheory.Nakayama
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.LinearAlgebra.Dimension.Free

@[expose] public section

open scoped BigOperators Pointwise
open Classical

noncomputable section

namespace Lemmata.Centroid.General

variable {F A M : Type*} [Field F] [CommRing A] [Algebra F A]
variable [AddCommGroup M] [Module F M] [Module A M] [IsScalarTower F A M]

def idealImage (I : Ideal A) : Submodule A M := I • (⊤ : Submodule A M)

instance quotientIdealImageModule (I : Ideal A) : Module (A ⧸ I) (M ⧸ idealImage (M := M) I) :=
  (Module.isTorsionBySet_quotient_ideal_smul M I).module

instance quotientIdealImageOriginalScalarTower (I : Ideal A) :
    IsScalarTower F A (M ⧸ idealImage (M := M) I) where
  smul_assoc r a x := Quotient.inductionOn' x fun m =>
    congrArg (Submodule.Quotient.mk (p := idealImage (M := M) I)) (smul_assoc r a m)

instance quotientIdealImageScalarTower (I : Ideal A) :
    IsScalarTower F (A ⧸ I) (M ⧸ idealImage (M := M) I) where
  smul_assoc r a x := Quotient.inductionOn' a fun a => Quotient.inductionOn' x fun m =>
    congrArg (Submodule.Quotient.mk (p := idealImage (M := M) I)) (smul_assoc r a m)

def idealKernel (I : Ideal A) : Submodule A M where
  carrier := {x | ∀ a ∈ I, a • x = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy a ha
    rw [smul_add, hx a ha, hy a ha, add_zero]
  smul_mem' := by
    intro a x hx c hc
    rw [smul_comm c a x, hx c hc, smul_zero]

private theorem idealKernel_ne_bot_of_power_image_eq_bot [Nontrivial M]
    (I : Ideal A) (n : ℕ) (hn : I ^ n • (⊤ : Submodule A M) = ⊥) :
    idealKernel (M := M) I ≠ ⊥ := by
  induction n with
  | zero =>
    simp only [pow_zero, Ideal.one_eq_top, Submodule.top_smul] at hn
    exact (top_ne_bot hn).elim
  | succ n ih =>
    by_cases hzero : I ^ n • (⊤ : Submodule A M) = ⊥
    · exact ih hzero
    · obtain ⟨x, hx, hx0⟩ := (I ^ n • (⊤ : Submodule A M)).ne_bot_iff.mp hzero
      apply (idealKernel (M := M) I).ne_bot_iff.mpr
      refine ⟨x, ?_, hx0⟩
      intro a ha
      have hmem : a • x ∈ I • (I ^ n • (⊤ : Submodule A M)) :=
        Submodule.smul_mem_smul ha hx
      rw [← Submodule.mul_smul, ← pow_succ', hn] at hmem
      exact hmem

theorem idealKernel_ne_bot_of_isNilpotent [Nontrivial M] (I : Ideal A) (hI : IsNilpotent I) :
    idealKernel (M := M) I ≠ ⊥ := by
  obtain ⟨n, hn⟩ := hI
  apply idealKernel_ne_bot_of_power_image_eq_bot (M := M) I n
  rw [hn]
  exact Submodule.bot_smul (R := A) (A := A) (M := M) (⊤ : Submodule A M)

theorem span_top_of_quotient_basis [FiniteDimensional F M]
    (I : Ideal A) (hI : I ≤ Ideal.jacobson (⊥ : Ideal A))
    {κ : Type*} [Fintype κ] (b : Module.Basis κ F (M ⧸ idealImage (M := M) I))
    (v : κ → M) (hv : ∀ j, (idealImage I).mkQ (v j) = b j) :
    Submodule.span A (Set.range v) = ⊤ := by
  let : Module.Finite A M := Module.Finite.of_restrictScalars_finite F A M
  let U := Submodule.span A (Set.range v)
  let q : M →ₗ[F] (M ⧸ idealImage I) := (idealImage I).mkQ.restrictScalars F
  have htop : (⊤ : Submodule A M) ≤ U ⊔ I • (⊤ : Submodule A M) := by
    intro x _
    let w := ∑ j, b.repr (q x) j • v j
    have hw : w ∈ U := by
      apply U.sum_mem
      intro j _
      exact U.smul_of_tower_mem _ (Submodule.subset_span (Set.mem_range_self j))
    have hq : q w = q x := by
      simp only [w, map_sum, map_smul]
      simpa only [q, LinearMap.restrictScalars_apply, hv] using b.sum_repr (q x)
    have hsub : x - w ∈ idealImage I := by
      apply (idealImage I).ker_mkQ.le
      change q (x - w) = 0
      rw [map_sub, hq, sub_self]
    exact Submodule.mem_sup.mpr ⟨w, hw, x - w, hsub, by simp⟩
  apply top_unique
  exact Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top hI htop

def idealEvaluation {κ : Type*} (I : Ideal A) (v : κ → M) :
    I →ₗ[F] (κ → idealImage (M := M) I) where
  toFun c j := ⟨c.1 • v j, Submodule.smul_mem_smul c.2 (Submodule.mem_top)⟩
  map_add' c d := by
    funext j
    apply Subtype.ext
    exact add_smul c.1 d.1 (v j)
  map_smul' a c := by
    funext j
    apply Subtype.ext
    exact smul_assoc a c.1 (v j)

theorem idealEvaluation_injective [FaithfulSMul A M] {κ : Type*}
    (I : Ideal A) (v : κ → M) (hv : Submodule.span A (Set.range v) = ⊤) :
    Function.Injective (idealEvaluation (F := F) I v) := by
  intro c d h
  apply Subtype.ext
  apply eq_of_smul_eq_smul (α := M)
  intro x
  let g : M →ₗ[A] M :=
    { toFun := fun y => (c.1 - d.1) • y
      map_add' := smul_add _
      map_smul' := fun a y => smul_comm _ a y }
  have hker : Submodule.span A (Set.range v) ≤ LinearMap.ker g := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    change (c.1 - d.1) • v j = 0
    rw [sub_smul]
    exact sub_eq_zero.mpr (congrArg Subtype.val (congrFun h j))
  rw [hv] at hker
  have hg : (c.1 - d.1) • x = 0 := hker (Submodule.mem_top)
  exact sub_eq_zero.mp (by simpa only [sub_smul] using hg)

theorem ideal_dimension_le_quotient_mul_image [FiniteDimensional F M]
    [FiniteDimensional F A] [FaithfulSMul A M]
    (I : Ideal A) (hI : I ≤ Ideal.jacobson (⊥ : Ideal A)) :
    Module.finrank F I ≤
      Module.finrank F (M ⧸ idealImage (M := M) I) *
        Module.finrank F (idealImage (M := M) I) := by
  let : FiniteDimensional F (idealImage (M := M) I) :=
    Module.Finite.of_injective ((idealImage (M := M) I).subtype.restrictScalars F)
      (idealImage (M := M) I).subtype_injective
  let : Module.Free F (idealImage (M := M) I) := Module.Free.of_divisionRing F _
  let Q := M ⧸ idealImage (M := M) I
  let : Module.Free F Q := Module.Free.of_divisionRing F Q
  let b := Module.finBasis F Q
  choose v hv using fun j => (idealImage (M := M) I).mkQ_surjective (b j)
  have hspan := span_top_of_quotient_basis I hI b v hv
  have hi := idealEvaluation_injective (F := F) I v hspan
  have hd := LinearMap.finrank_le_finrank_of_injective hi
  simpa [Module.finrank_pi_fintype] using hd

theorem span_top_of_residue_basis [FiniteDimensional F M]
    (I : Ideal A) [I.IsMaximal] (hI : I ≤ Ideal.jacobson (⊥ : Ideal A))
    {κ : Type*} [Fintype κ] (b : Module.Basis κ (A ⧸ I) (M ⧸ idealImage (M := M) I))
    (v : κ → M) (hv : ∀ j, (idealImage I).mkQ (v j) = b j) :
    Submodule.span A (Set.range v) = ⊤ := by
  let : Module.Finite A M := Module.Finite.of_restrictScalars_finite F A M
  let U := Submodule.span A (Set.range v)
  let q := (idealImage (M := M) I).mkQ
  have htop : (⊤ : Submodule A M) ≤ U ⊔ I • (⊤ : Submodule A M) := by
    intro x _
    choose a ha using fun j => Ideal.Quotient.mk_surjective (b.repr (q x) j)
    let w := ∑ j, a j • v j
    have hw : w ∈ U := U.sum_mem fun j _ =>
      U.smul_mem (a j) (Submodule.subset_span (Set.mem_range_self j))
    have hq : q w = q x := by
      simp only [w, map_sum, map_smul, q, hv]
      have hs (j : κ) : a j • b j = b.repr (q x) j • b j := by
        rw [← ha]
        exact Quotient.inductionOn' (b j) fun _ => rfl
      simpa only [hs] using b.sum_repr (q x)
    have hsub : x - w ∈ idealImage I := by
      apply (idealImage I).ker_mkQ.le
      change q (x - w) = 0
      rw [map_sub, hq, sub_self]
    exact Submodule.mem_sup.mpr ⟨w, hw, x - w, hsub, by simp⟩
  apply top_unique
  exact Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top hI htop

theorem ideal_dimension_mul_residue_le_quotient_mul_image [FiniteDimensional F M]
    [FiniteDimensional F A] [FaithfulSMul A M]
    (I : Ideal A) [I.IsMaximal] (hI : I ≤ Ideal.jacobson (⊥ : Ideal A)) :
    Module.finrank F I * Module.finrank F (A ⧸ I) ≤
      Module.finrank F (M ⧸ idealImage (M := M) I) *
        Module.finrank F (idealImage (M := M) I) := by
  let : Field (A ⧸ I) := Ideal.Quotient.field I
  let Q := M ⧸ idealImage (M := M) I
  let : FiniteDimensional F (idealImage (M := M) I) :=
    Module.Finite.of_injective ((idealImage (M := M) I).subtype.restrictScalars F)
      (idealImage (M := M) I).subtype_injective
  let : Module.Free F (idealImage (M := M) I) := Module.Free.of_divisionRing F _
  let : FiniteDimensional F Q := Module.Finite.of_surjective
    ((idealImage (M := M) I).mkQ.restrictScalars F) (idealImage (M := M) I).mkQ_surjective
  let : FiniteDimensional F (A ⧸ I) := Module.Finite.of_surjective
    (Ideal.Quotient.mkₐ F I).toLinearMap Ideal.Quotient.mk_surjective
  let : Module.Free F (A ⧸ I) := Module.Free.of_divisionRing F _
  let : FiniteDimensional (A ⧸ I) Q := Module.Finite.of_restrictScalars_finite F (A ⧸ I) Q
  let : Module.Free (A ⧸ I) Q := Module.Free.of_divisionRing _ _
  let b := Module.finBasis (A ⧸ I) Q
  choose v hv using fun j => (idealImage (M := M) I).mkQ_surjective (b j)
  have hspan := span_top_of_residue_basis (F := F) I hI b v hv
  have hd := LinearMap.finrank_le_finrank_of_injective
    (idealEvaluation_injective (F := F) I v hspan)
  have hd' : Module.finrank F I ≤
      Module.finrank (A ⧸ I) Q * Module.finrank F (idealImage (M := M) I) := by
    simpa [Module.finrank_pi_fintype] using hd
  have hdim := Module.finrank_mul_finrank F (A ⧸ I) Q
  calc
    _ ≤ (Module.finrank (A ⧸ I) Q * Module.finrank F (idealImage (M := M) I)) *
        Module.finrank F (A ⧸ I) := Nat.mul_le_mul_right _ hd'
    _ = (Module.finrank F (A ⧸ I) * Module.finrank (A ⧸ I) Q) *
        Module.finrank F (idealImage (M := M) I) := by ac_rfl
    _ = _ := by rw [hdim]

end Lemmata.Centroid.General
