module

public import Lemmata.CocubicCovering.Proof.Affine
public meta import Lemmata.CocubicCovering.Proof.Affine
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions

@[expose] public section

set_option Elab.async false

namespace Lemmata.CocubicCovering.CoveringWitness

open Module
open scoped BigOperators

variable {ι κ : Type*} [Fintype ι] [Fintype κ] {n : ℕ}

def familyLinear (v : ι → Vector n) : (ι → Field) →ₗ[Field] Vector n :=
  Fintype.linearCombination Field v

def familySpan (v : ι → Vector n) : Submodule Field (Vector n) :=
  Submodule.span Field (Set.range v)

@[simp] theorem familyLinear_apply (v : ι → Vector n) (b : ι → Field) :
    familyLinear v b = ∑ i, b i • v i := rfl

@[simp] theorem range_familyLinear (v : ι → Vector n) :
    LinearMap.range (familyLinear v) = familySpan v :=
  Fintype.range_linearCombination Field v

theorem familyLinear_injective_iff (v : ι → Vector n) :
    Function.Injective (familyLinear v) ↔ LinearIndependent Field v :=
  linearIndependent_iff_injective_fintypeLinearCombination.symm

theorem familySpan_finrank (v : ι → Vector n)
    (hv : Function.Injective (familyLinear v)) :
    finrank Field (familySpan v) = Fintype.card ι :=
  finrank_span_eq_card ((familyLinear_injective_iff v).mp hv)

/-- Checking the dual map on the supplied columns proves a left inverse on every vector. -/
theorem dual_leftInverse [DecidableEq ι] (v : ι → Vector n)
    (dual : Vector n →ₗ[Field] (ι → Field))
    (hdual : ∀ i, dual (v i) = Pi.single i 1) :
    dual.comp (familyLinear v) = LinearMap.id := by
  apply (Pi.basisFun Field ι).ext
  intro i
  simpa only [Pi.basisFun_apply, LinearMap.comp_apply, LinearMap.id_apply,
    familyLinear, Fintype.linearCombination_apply_single, one_smul] using hdual i

theorem injective_of_dual [DecidableEq ι] (v : ι → Vector n)
    (dual : Vector n →ₗ[Field] (ι → Field))
    (hdual : ∀ i, dual (v i) = Pi.single i 1) :
    Function.Injective (familyLinear v) := by
  apply Function.LeftInverse.injective (f := familyLinear v) (g := dual)
  intro b
  exact LinearMap.congr_fun (dual_leftInverse v dual hdual) b

theorem packed_dual_witness {k : ℕ} (v : Fin k → Vector n) (rows : Fin k → ℕ)
    (hdual : ∀ i, CoveringAffine.rowMap rows (v i) = Pi.single i 1) :
    Function.Injective (familyLinear v) ∧ finrank Field (familySpan v) = k := by
  have hv := injective_of_dual v (CoveringAffine.rowMap rows) hdual
  exact ⟨hv, by simpa only [Fintype.card_fin] using familySpan_finrank v hv⟩

theorem familySpan_le_of_coefficients (v : ι → Vector n) (w : κ → Vector n)
    (coefficients : ι → κ → Field)
    (hcoefficients : ∀ i, familyLinear w (coefficients i) = v i) :
    familySpan v ≤ familySpan w := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  rw [← hcoefficients i, ← range_familyLinear]
  exact ⟨coefficients i, rfl⟩

theorem familySpan_eq_of_coefficients (v : ι → Vector n) (w : κ → Vector n)
    (forward : ι → κ → Field) (backward : κ → ι → Field)
    (hforward : ∀ i, familyLinear w (forward i) = v i)
    (hbackward : ∀ j, familyLinear v (backward j) = w j) :
    familySpan v = familySpan w :=
  le_antisymm (familySpan_le_of_coefficients v w forward hforward)
    (familySpan_le_of_coefficients w v backward hbackward)

theorem combined_family {c d : ℕ} (core : Fin c → Vector n) (fresh : Fin d → Vector n)
    (hinjective : Function.Injective (familyLinear (Sum.elim core fresh))) :
    familySpan fresh ⊓ familySpan core = ⊥ ∧
      finrank Field (familySpan fresh) = d := by
  have hindependent := (familyLinear_injective_iff (Sum.elim core fresh)).mp hinjective
  have hparts := linearIndependent_sum.mp hindependent
  have hfresh : LinearIndependent Field fresh := by
    simpa only [Function.comp_def, Sum.elim_inr] using hparts.2.1
  have hdisjoint : Disjoint (familySpan core) (familySpan fresh) := by
    simpa only [familySpan, Function.comp_def, Sum.elim_inl, Sum.elim_inr]
      using hparts.2.2
  refine ⟨hdisjoint.symm.eq_bot, ?_⟩
  calc
    finrank Field (familySpan fresh) = Fintype.card (Fin d) := by
      apply finrank_span_eq_card
      exact hfresh
    _ = d := Fintype.card_fin d

end Lemmata.CocubicCovering.CoveringWitness
