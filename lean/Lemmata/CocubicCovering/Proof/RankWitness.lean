module

public import Lemmata.CocubicCovering.Proof.Witness
public meta import Lemmata.CocubicCovering.Proof.Witness
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Lean.Elab.Tactic.Omega

@[expose] public section

set_option Elab.async false

namespace Lemmata.CocubicCovering.CoveringRankWitness

open Module CoveringWitness

variable {E : Type*} [AddCommGroup E] [Module Field E] [FiniteDimensional Field E]
  {n a r : ℕ}

theorem rank_lower_of_dual (L : Vector n →ₗ[Field] E) (columns : Fin a → Vector n)
    (dual : E →ₗ[Field] Vector a)
    (hdual : ∀ i, dual (L (columns i)) = Pi.single i 1) :
    a ≤ finrank Field (LinearMap.range L) := by
  let f : Vector a →ₗ[Field] E := LinearMap.comp L (familyLinear columns)
  have hleft : dual.comp f = LinearMap.id := by
    apply (Pi.basisFun Field (Fin a)).ext
    intro i
    simpa only [f, Pi.basisFun_apply, LinearMap.comp_apply, LinearMap.id_apply,
      familyLinear, Fintype.linearCombination_apply_single, one_smul] using hdual i
  have hf : Function.Injective f := by
    apply Function.LeftInverse.injective (f := f) (g := dual)
    intro b
    exact LinearMap.congr_fun hleft b
  have hdim := Submodule.finrank_mono
    (LinearMap.range_comp_le_range (familyLinear columns) L)
  change finrank Field (LinearMap.range f) ≤ finrank Field (LinearMap.range L) at hdim
  rw [LinearMap.finrank_range_of_inj hf] at hdim
  simpa only [Vector, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using hdim

theorem rank_add_radical_le (L : Vector n →ₗ[Field] E) (radical : Fin r → Vector n)
    (hindependent : Function.Injective (familyLinear radical))
    (hradical : ∀ i, L (radical i) = 0) :
    finrank Field (LinearMap.range L) + r ≤ n := by
  have hle : familySpan radical ≤ LinearMap.ker L := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hradical i
  have hdim := Submodule.finrank_mono hle
  have hr : finrank Field (familySpan radical) = r := by
    simpa only [Fintype.card_fin] using familySpan_finrank radical hindependent
  have hnull := L.finrank_range_add_finrank_ker
  have hn : finrank Field (Vector n) = n := by simp [Vector]
  omega

theorem rank_eq_of_dual_and_radical (L : Vector n →ₗ[Field] E)
    (columns : Fin a → Vector n) (dual : E →ₗ[Field] Vector a)
    (radical : Fin r → Vector n) (hdim : a + r = n)
    (hdual : ∀ i, dual (L (columns i)) = Pi.single i 1)
    (hindependent : Function.Injective (familyLinear radical))
    (hradical : ∀ i, L (radical i) = 0) :
    finrank Field (LinearMap.range L) = a := by
  have hlower := rank_lower_of_dual L columns dual hdual
  have hupper := rank_add_radical_le L radical hindependent hradical
  omega

theorem kernel_eq_familySpan (L : Vector n →ₗ[Field] E) (radical : Fin r → Vector n)
    (hindependent : Function.Injective (familyLinear radical))
    (hradical : ∀ i, L (radical i) = 0)
    (hdim : finrank Field (LinearMap.range L) + r = n) :
    LinearMap.ker L = familySpan radical := by
  have hle : familySpan radical ≤ LinearMap.ker L := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hradical i
  have hr : finrank Field (familySpan radical) = r := by
    simpa only [Fintype.card_fin] using familySpan_finrank radical hindependent
  have hnull := L.finrank_range_add_finrank_ker
  have hn : finrank Field (Vector n) = n := by simp [Vector]
  symm
  apply Submodule.eq_of_le_of_finrank_eq hle
  omega

/-- An explicitly supplied inverse minor certifies the lower rank bound. -/
theorem matrix_rank_lower_of_minor {m : ℕ} (A : Matrix (Fin m) (Fin n) Field)
    (rows : Fin a → Fin m) (columns : Fin a → Fin n)
    (inverse : Matrix (Fin a) (Fin a) Field)
    (hinverse : inverse * A.submatrix rows columns = 1) : a ≤ A.rank := by
  calc
    a = (1 : Matrix (Fin a) (Fin a) Field).rank := by simp
    _ = (inverse * A.submatrix rows columns).rank := by rw [hinverse]
    _ ≤ (A.submatrix rows columns).rank := Matrix.rank_mul_le_right _ _
    _ ≤ A.rank := Matrix.rank_submatrix_le A rows columns

theorem matrix_rank_eq_of_minor_and_radical {m : ℕ}
    (A : Matrix (Fin m) (Fin n) Field)
    (rows : Fin a → Fin m) (columns : Fin a → Fin n)
    (inverse : Matrix (Fin a) (Fin a) Field)
    (radical : Fin r → Vector n) (radicalDual : Fin r → ℕ)
    (hdim : a + r = n)
    (hinverse : inverse * A.submatrix rows columns = 1)
    (hdual : ∀ i, CoveringAffine.rowMap radicalDual (radical i) = Pi.single i 1)
    (hradical : ∀ i, A.mulVecLin (radical i) = 0) : A.rank = a := by
  have hlower := matrix_rank_lower_of_minor A rows columns inverse hinverse
  have hindependent := (packed_dual_witness radical radicalDual hdual).1
  have hupper := rank_add_radical_le A.mulVecLin radical hindependent hradical
  change A.rank + r ≤ n at hupper
  omega

theorem toBilin_kernel (A : Matrix (Fin n) (Fin n) Field) :
    LinearMap.ker (Matrix.toBilin' A) = LinearMap.ker A.transpose.mulVecLin := by
  ext v
  change Matrix.toBilin' A v = 0 ↔ A.transpose.mulVecLin v = 0
  constructor
  · intro hv
    funext i
    have hi := LinearMap.congr_fun hv (Pi.single i 1)
    simpa [Matrix.toBilin'_apply, Matrix.mulVecLin_apply, Matrix.mulVec, Matrix.vecMul, dotProduct,
      Pi.single_apply, mul_comm] using hi
  · intro hv
    apply (Pi.basisFun Field (Fin n)).ext
    intro i
    have hi := congrFun hv i
    simpa [Pi.basisFun_apply, Matrix.toBilin'_apply, Matrix.mulVecLin_apply, Matrix.mulVec, Matrix.vecMul,
      dotProduct, Pi.single_apply, mul_comm] using hi

theorem toBilin_rank (A : Matrix (Fin n) (Fin n) Field) :
    finrank Field (LinearMap.range (Matrix.toBilin' A)) = A.rank := by
  have hB := (Matrix.toBilin' A).finrank_range_add_finrank_ker
  have hA := A.transpose.mulVecLin.finrank_range_add_finrank_ker
  rw [toBilin_kernel] at hB
  calc
    finrank Field (LinearMap.range (Matrix.toBilin' A)) = A.transpose.rank := by
      change finrank Field (LinearMap.range (Matrix.toBilin' A)) =
        finrank Field (LinearMap.range A.transpose.mulVecLin)
      omega
    _ = A.rank := Matrix.rank_transpose A

end Lemmata.CocubicCovering.CoveringRankWitness
