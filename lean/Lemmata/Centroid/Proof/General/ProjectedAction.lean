module

public import Lemmata.Centroid.Proof.General.Projected

@[expose] public section

open scoped Pointwise
open Classical

noncomputable section

namespace Lemmata.Centroid.General

variable {F A M : Type*} [Field F] [CommRing A] [Algebra F A]
variable [AddCommGroup M] [Module F M] [Module A M] [IsScalarTower F A M]

abbrev ProjectedModule (A M : Type*) [CommRing A] [AddCommGroup M] [Module A M]
    (I : Ideal A) := M ⧸ idealKernel (M := M) I

abbrev AnnihilatorAlgebra (A : Type*) [CommRing A] (I : Ideal A) :=
  A ⧸ Module.annihilator A I

theorem projectedModule_torsion [FaithfulSMul A M] (I : Ideal A) :
    Module.IsTorsionBySet A (ProjectedModule A M I) (Module.annihilator A I) := by
  rw [← projected_annihilator (M := M) I]
  exact Module.isTorsionBySet_annihilator A _

instance projectedQuotientModule [FaithfulSMul A M] (I : Ideal A) :
    Module (AnnihilatorAlgebra A I) (ProjectedModule A M I) :=
  (projectedModule_torsion (M := M) I).module

instance projectedQuotientScalarTower [FaithfulSMul A M] (I : Ideal A) :
    IsScalarTower F (AnnihilatorAlgebra A I) (ProjectedModule A M I) where
  smul_assoc r a x := Quotient.inductionOn' a fun a =>
    Quotient.inductionOn' x fun m =>
      congrArg (Submodule.Quotient.mk (p := idealKernel (M := M) I)) (smul_assoc r a m)

instance projectedQuotientFaithful [FaithfulSMul A M] (I : Ideal A) :
    FaithfulSMul (AnnihilatorAlgebra A I) (ProjectedModule A M I) where
  eq_of_smul_eq_smul {a b} := by
    refine Quotient.inductionOn₂' a b fun a b h => ?_
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
    rw [← projected_annihilator (M := M) I]
    apply Module.mem_annihilator.mpr
    intro x
    change (a - b) • x = 0
    rw [sub_smul]
    exact sub_eq_zero.mpr (h x)

def projectedIdeal (I : Ideal A) : Ideal (AnnihilatorAlgebra A I) :=
  I.map (Ideal.Quotient.mk (Module.annihilator A I))

theorem projectedIdeal_isNilpotent (I : Ideal A) (hI : IsNilpotent I) :
    IsNilpotent (projectedIdeal I) := by
  obtain ⟨n, hn⟩ := hI
  change I ^ n = ⊥ at hn
  refine ⟨n, ?_⟩
  change I.map (Ideal.Quotient.mk (Module.annihilator A I)) ^ n = ⊥
  rw [← Ideal.map_pow, hn, Ideal.map_bot]

def projectedIdealMap (I : Ideal A) : I →ₗ[F] projectedIdeal I where
  toFun c := ⟨Ideal.Quotient.mk (Module.annihilator A I) c.1,
    Ideal.mem_map_of_mem _ c.2⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' r c := Subtype.ext
    ((Ideal.Quotient.mkₐ F (Module.annihilator A I)).toLinearMap.map_smul r c.1)

theorem projectedIdealMap_surjective (I : Ideal A) :
    Function.Surjective (projectedIdealMap (F := F) I) := by
  intro c
  obtain ⟨a, ha, heq⟩ :=
    (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp c.2
  exact ⟨⟨a, ha⟩, Subtype.ext heq⟩

theorem projectedIdealMap_ker (I : Ideal A) :
    LinearMap.ker (projectedIdealMap (F := F) I) = annihilatorSubspace (F := F) I := by
  ext c
  change projectedIdealMap (F := F) I c = 0 ↔ c.1 ∈ annihilatorInIdeal I
  rw [Subtype.ext_iff]
  change Ideal.Quotient.mk (Module.annihilator A I) c.1 = 0 ↔ c.1 ∈ annihilatorInIdeal I
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact ⟨fun h => ⟨c.2, h⟩, fun h => h.2⟩

theorem projectedIdeal_finrank [FiniteDimensional F A] (I : Ideal A) :
    Module.finrank F (projectedIdeal I) = Module.finrank F (AnnihilatorQuotient F A I) := by
  have he := (projectedIdealMap (F := F) I).quotKerEquivOfSurjective
    (projectedIdealMap_surjective I)
  rw [projectedIdealMap_ker] at he
  exact he.finrank_eq.symm

theorem projectedModule_finrank [FiniteDimensional F M] (I : Ideal A) :
    Module.finrank F (ProjectedModule A M I) =
      Module.finrank F M - Module.finrank F (idealKernel (M := M) I) :=
  Submodule.finrank_quotient _

def projectedKernel [FaithfulSMul A M] (I : Ideal A) :
    Submodule (AnnihilatorAlgebra A I) (ProjectedModule A M I) :=
  idealKernel (M := ProjectedModule A M I) (projectedIdeal I)

theorem projected_module_dimension_bound [FiniteDimensional F M]
    [FiniteDimensional F A] [FaithfulSMul A M] (I : Ideal A) (hI : IsNilpotent I) :
    Module.finrank F (AnnihilatorQuotient F A I) ≤
      Module.finrank F (projectedKernel (M := M) I) *
        (Module.finrank F (ProjectedModule A M I) -
          Module.finrank F (projectedKernel (M := M) I)) := by
  let : FiniteDimensional F (AnnihilatorAlgebra A I) := Module.Finite.of_surjective
    (Ideal.Quotient.mkₐ F (Module.annihilator A I)).toLinearMap Ideal.Quotient.mk_surjective
  let : FiniteDimensional F (ProjectedModule A M I) := Module.Finite.of_surjective
    ((idealKernel (M := M) I).mkQ.restrictScalars F) (idealKernel (M := M) I).mkQ_surjective
  have hd := nilpotent_ideal_dimension_le_kernel_mul_codim
    (F := F) (M := ProjectedModule A M I) (projectedIdeal I) (projectedIdeal_isNilpotent I hI)
  rw [projectedIdeal_finrank] at hd
  convert hd using 1
  rfl

theorem projectedModule_finrank_pos [FiniteDimensional F M] [FaithfulSMul A M]
    (I : Ideal A) (hI : I ≠ ⊥) :
    0 < Module.finrank F (ProjectedModule A M I) := by
  have hlt : idealKernel (M := M) I < ⊤ :=
    lt_top_iff_ne_top.mpr fun h => hI ((idealKernel_eq_top_iff (M := M) I).mp h)
  have hd := Submodule.finrank_lt_finrank_of_lt
    (show (idealKernel (M := M) I).restrictScalars F < ⊤ from hlt)
  rw [finrank_top] at hd
  change Module.finrank F (idealKernel (M := M) I) < Module.finrank F M at hd
  rw [projectedModule_finrank]
  omega

theorem projectedKernel_finrank_pos [FiniteDimensional F M] [FaithfulSMul A M]
    (I : Ideal A) (hI : IsNilpotent I) (hI0 : I ≠ ⊥) :
    0 < Module.finrank F (projectedKernel (M := M) I) := by
  let : FiniteDimensional F (ProjectedModule A M I) := Module.Finite.of_surjective
    ((idealKernel (M := M) I).mkQ.restrictScalars F) (idealKernel (M := M) I).mkQ_surjective
  let : Nontrivial (ProjectedModule A M I) :=
    Module.nontrivial_of_finrank_pos (projectedModule_finrank_pos (F := F) (M := M) I hI0)
  exact idealKernel_finrank_pos (F := F) (M := ProjectedModule A M I)
    (projectedIdeal I) (projectedIdeal_isNilpotent I hI)

theorem projectedKernel_finrank_two_le [FiniteDimensional F M]
    [FiniteDimensional F A] [FaithfulSMul A M] (I : Ideal A) (hI : IsNilpotent I)
    (Q : ℕ) (hQ : Module.finrank F (ProjectedModule A M I) ≤ Q)
    (hx : Q - 1 < Module.finrank F (AnnihilatorQuotient F A I)) :
    2 ≤ Module.finrank F (projectedKernel (M := M) I) := by
  have hd := projected_module_dimension_bound (F := F) (M := M) I hI
  by_contra h
  have hh : Module.finrank F (projectedKernel (M := M) I) = 0 ∨
      Module.finrank F (projectedKernel (M := M) I) = 1 := by omega
  rcases hh with hh | hh <;> simp only [hh, Nat.zero_mul, Nat.one_mul] at hd <;> omega

end Lemmata.Centroid.General
