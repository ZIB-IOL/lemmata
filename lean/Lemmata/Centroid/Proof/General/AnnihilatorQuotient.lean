module

public import Lemmata.Centroid.Proof.General.Annihilator
public import Lemmata.Centroid.Proof.Linear.SpanBudget

@[expose] public section

open Classical

noncomputable section

namespace Lemmata.Centroid.General

variable {F A M : Type*} [Field F] [CommRing A] [Algebra F A]
variable [AddCommGroup M] [Module F M] [Module A M] [IsScalarTower F A M]

def annihilatorSubspace (I : Ideal A) : Submodule F I :=
  ((annihilatorInIdeal I).restrictScalars F).comap (I.subtype.restrictScalars F)

abbrev AnnihilatorQuotient (F : Type*) [Field F] (A : Type*) [CommRing A] [Algebra F A]
    (I : Ideal A) := I ⧸ annihilatorSubspace (F := F) I

def middleKernel (I : Ideal A) : Submodule F (idealKernel (M := M) (annihilatorInIdeal I)) :=
  ((idealKernel (M := M) I).restrictScalars F).comap
    ((idealKernel (M := M) (annihilatorInIdeal I)).subtype.restrictScalars F)

abbrev MiddleQuotient (F : Type*) [Field F] (A M : Type*) [CommRing A] [Algebra F A]
    [AddCommGroup M] [Module F M] [Module A M] [IsScalarTower F A M] (I : Ideal A) :=
  (idealKernel (M := M) (annihilatorInIdeal I)) ⧸ middleKernel (F := F) (M := M) I

def idealAction (I : Ideal A) :
    I →ₗ[F] (M →ₗ[F] idealKernel (M := M) (annihilatorInIdeal I)) where
  toFun c :=
    { toFun := fun x => ⟨c.1 • x,
        idealImage_le_annihilatorKernel I (Submodule.smul_mem_smul c.2 (Submodule.mem_top))⟩
      map_add' := fun x y => Subtype.ext (smul_add _ _ _)
      map_smul' := fun a x => Subtype.ext (smul_comm _ a x) }
  map_add' c d := by ext x; exact add_smul c.1 d.1 x
  map_smul' a c := by ext x; exact smul_assoc a c.1 x

def middleAction (I : Ideal A) (c : I) :
    MiddleQuotient F A M I →ₗ[F] idealKernel (M := M) (annihilatorInIdeal I) :=
  (middleKernel (F := F) (M := M) I).liftQ
    ((idealAction (F := F) (M := M) I c).comp
      ((idealKernel (M := M) (annihilatorInIdeal I)).subtype.restrictScalars F)) (by
        intro x hx
        apply Subtype.ext
        exact hx c.1 c.2)

def middleActionFamily (I : Ideal A) :
    I →ₗ[F] (MiddleQuotient F A M I →ₗ[F] idealKernel (M := M) (annihilatorInIdeal I)) where
  toFun := middleAction (F := F) (M := M) I
  map_add' c d := by
    apply LinearMap.ext
    intro x
    refine Quotient.inductionOn' x fun x => ?_
    apply Subtype.ext
    exact add_smul c.1 d.1 x.1
  map_smul' a c := by
    apply LinearMap.ext
    intro x
    refine Quotient.inductionOn' x fun x => ?_
    apply Subtype.ext
    exact smul_assoc a c.1 x.1

def projectedActionFamily (I : Ideal A) : I →ₗ[F] (M →ₗ[F] MiddleQuotient F A M I) where
  toFun c := (middleKernel (F := F) (M := M) I).mkQ.comp (idealAction I c)
  map_add' c d := by
    apply LinearMap.ext
    intro x
    change (middleKernel I).mkQ (idealAction I (c + d) x) = _
    rw [map_add, LinearMap.add_apply, map_add]
    rfl
  map_smul' a c := by
    apply LinearMap.ext
    intro x
    change (middleKernel I).mkQ (idealAction I (a • c) x) = _
    rw [map_smul, LinearMap.smul_apply, map_smul]
    rfl

def quotientMiddleAction (I : Ideal A) :
    AnnihilatorQuotient F A I →ₗ[F]
      (MiddleQuotient F A M I →ₗ[F] idealKernel (M := M) (annihilatorInIdeal I)) :=
  (annihilatorSubspace (F := F) I).liftQ (middleActionFamily (M := M) I) (by
    intro c hc
    apply LinearMap.ext
    intro x
    refine Quotient.inductionOn' x fun x => ?_
    apply Subtype.ext
    exact x.2 c.1 hc)

def quotientProjectedAction (I : Ideal A) :
    AnnihilatorQuotient F A I →ₗ[F] (M →ₗ[F] MiddleQuotient F A M I) :=
  (annihilatorSubspace (F := F) I).liftQ (projectedActionFamily (M := M) I) (by
    intro c hc
    apply LinearMap.ext
    intro x
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    intro a ha
    have hca : c.1 * a = 0 :=
      congrArg Subtype.val ((Module.mem_annihilator.mp hc.2) ⟨a, ha⟩)
    change a • (c.1 • x) = 0
    rw [← mul_smul, mul_comm a c.1, hca, zero_smul])

theorem quotient_actions_symmetric (I : Ideal A) (c d : AnnihilatorQuotient F A I) :
    (quotientMiddleAction (M := M) I c).comp (quotientProjectedAction I d) =
      (quotientMiddleAction (M := M) I d).comp (quotientProjectedAction I c) := by
  refine Quotient.inductionOn' c fun c => Quotient.inductionOn' d fun d => ?_
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change c.1 • (d.1 • x) = d.1 • (c.1 • x)
  exact smul_comm _ _ _

theorem quotient_actions_nondegenerate [FaithfulSMul A M] (I : Ideal A)
    (c : AnnihilatorQuotient F A I)
    (hc : ∀ d, (quotientMiddleAction (M := M) I c).comp (quotientProjectedAction I d) = 0) :
    c = 0 := by
  revert hc
  refine Quotient.inductionOn' c fun c hc => ?_
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  refine ⟨c.2, ?_⟩
  apply Module.mem_annihilator.mpr
  intro d
  apply Subtype.ext
  change c.1 * d.1 = 0
  apply eq_of_smul_eq_smul (α := M)
  intro x
  have he := LinearMap.congr_fun
    (hc ((annihilatorSubspace (F := F) I).mkQ d)) x
  have he' := congrArg Subtype.val he
  change c.1 • (d.1 • x) = 0 at he'
  rw [mul_smul, he', zero_smul]

theorem annihilator_quotient_dimension_bound [FiniteDimensional F M]
    [FiniteDimensional F A] [FaithfulSMul A M] (I : Ideal A) :
    Module.finrank F (AnnihilatorQuotient F A I) ≤
      (Module.finrank F (MiddleQuotient F A M I) + 1) ^ 2 / 4 := by
  let : FiniteDimensional F I := Module.Finite.of_injective
    (I.subtype.restrictScalars F) I.subtype_injective
  let H := idealKernel (M := M) (annihilatorInIdeal I)
  let : FiniteDimensional F H := Module.Finite.of_injective
    (H.subtype.restrictScalars F) H.subtype_injective
  exact Lemmata.Centroid.Linear.symmetric_composition_bound (quotientMiddleAction I)
    (quotientProjectedAction I) (quotient_actions_symmetric I) (quotient_actions_nondegenerate I)

theorem idealKernel_antitone {I J : Ideal A} (h : I ≤ J) :
    idealKernel (M := M) J ≤ idealKernel (M := M) I :=
  fun _ hx a ha => hx a (h ha)

theorem annihilatorSubspace_finrank [FiniteDimensional F A] (I : Ideal A) :
    Module.finrank F (annihilatorSubspace (F := F) I) =
      Module.finrank F (annihilatorInIdeal I) := by
  exact (Submodule.comap_equiv_self_of_inj_of_le
    (f := I.subtype.restrictScalars F) (p := (annihilatorInIdeal I).restrictScalars F)
    I.subtype_injective
    (fun x hx => ⟨⟨x, hx.1⟩, rfl⟩)).finrank_eq

theorem annihilatorQuotient_finrank [FiniteDimensional F A] (I : Ideal A) :
    Module.finrank F (AnnihilatorQuotient F A I) =
      Module.finrank F I - Module.finrank F (annihilatorInIdeal I) := by
  let : FiniteDimensional F I := Module.Finite.of_injective
    (I.subtype.restrictScalars F) I.subtype_injective
  rw [Submodule.finrank_quotient, annihilatorSubspace_finrank]

theorem middleKernel_finrank [FiniteDimensional F M] (I : Ideal A) :
    Module.finrank F (middleKernel (F := F) (M := M) I) =
      Module.finrank F (idealKernel (M := M) I) := by
  exact (Submodule.comap_equiv_self_of_inj_of_le
    (f := (idealKernel (M := M) (annihilatorInIdeal I)).subtype.restrictScalars F)
    Subtype.val_injective (fun x hx =>
      ⟨⟨x, idealKernel_antitone inf_le_left hx⟩, rfl⟩)).finrank_eq

theorem middleQuotient_finrank [FiniteDimensional F M] (I : Ideal A) :
    Module.finrank F (MiddleQuotient F A M I) =
      Module.finrank F (idealKernel (M := M) (annihilatorInIdeal I)) -
        Module.finrank F (idealKernel (M := M) I) := by
  let H := idealKernel (M := M) (annihilatorInIdeal I)
  let : FiniteDimensional F H := Module.Finite.of_injective
    (H.subtype.restrictScalars F) H.subtype_injective
  rw [Submodule.finrank_quotient, middleKernel_finrank]

theorem annihilator_dimension_difference_bound [FiniteDimensional F M]
    [FiniteDimensional F A] [FaithfulSMul A M] (I : Ideal A) :
    Module.finrank F I - Module.finrank F (annihilatorInIdeal I) ≤
      ((Module.finrank F (idealKernel (M := M) (annihilatorInIdeal I)) -
          Module.finrank F (idealKernel (M := M) I)) + 1) ^ 2 / 4 := by
  simpa only [annihilatorQuotient_finrank, middleQuotient_finrank] using
    annihilator_quotient_dimension_bound (F := F) (M := M) I

end Lemmata.Centroid.General
