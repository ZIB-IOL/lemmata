module

public import Lemmata.CocubicCovering.Def.Field
public meta import Lemmata.CocubicCovering.Def.Field
public import Lemmata.CocubicCovering.Proof.Linear
public meta import Lemmata.CocubicCovering.Proof.Linear
public import Lemmata.CocubicCovering.Proof.Matrix
public meta import Lemmata.CocubicCovering.Proof.Matrix
public import Lemmata.CocubicCovering.Proof.Affine
public meta import Lemmata.CocubicCovering.Proof.Affine
public import Lemmata.CocubicCovering.Proof.Bits
public meta import Lemmata.CocubicCovering.Proof.Bits
public import Lemmata.CocubicCovering.Proof.Congruence
public meta import Lemmata.CocubicCovering.Proof.Congruence
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

@[expose] public section

set_option Elab.async false

namespace Lemmata.CocubicCovering.CoveringLocal

open scoped BigOperators
open Covering Module LinearMap
open LinearMap (BilinForm)

theorem localInclusion_injective : Function.Injective CoveringMatrix.localInclusion := by
  unfold Function.Injective
  native_decide

def localEmbedding : Vector 12 →ₗ[Field] Vector 24 :=
  Fintype.linearCombination Field fun i => Pi.single (CoveringMatrix.localInclusion i) 1

def localProjection : Vector 24 →ₗ[Field] Vector 12 where
  toFun v i := v (CoveringMatrix.localInclusion i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem localEmbedding_basis (i : Fin 12) :
    localEmbedding (Pi.single i 1) = Pi.single (CoveringMatrix.localInclusion i) 1 := by
  simp [localEmbedding]

@[simp] theorem localProjection_embedding (v : Vector 12) :
    localProjection (localEmbedding v) = v := by
  ext j
  simp [localEmbedding, localProjection, Fintype.linearCombination_apply,
    Pi.single_apply, localInclusion_injective.eq_iff]

theorem localEmbedding_injective : Function.Injective localEmbedding := by
  intro v w hvw
  have h := congrArg localProjection hvw
  simpa using h

theorem localProjection_comp_embedding :
    localProjection.comp localEmbedding = (LinearMap.id : Vector 12 →ₗ[Field] Vector 12) := by
  apply LinearMap.ext
  intro v
  exact localProjection_embedding v

theorem localProjection_rowMap {n : ℕ} (rows : Fin 24 → ℕ) :
    localProjection.comp (CoveringAffine.rowMap (n := n) rows) =
      CoveringAffine.rowMap (n := n) (fun i => rows (CoveringMatrix.localInclusion i)) := by
  ext v i
  rfl

def localSpace : Submodule Field (Vector 24) := LinearMap.range localEmbedding

theorem localEmbedding_projection {v : Vector 24} (hv : v ∈ localSpace) :
    localEmbedding (localProjection v) = v := by
  obtain ⟨w, rfl⟩ := hv
  rw [localProjection_embedding]

theorem localSpace_finrank : finrank Field localSpace = 12 := by
  change finrank Field (LinearMap.range localEmbedding) = 12
  calc
    _ = finrank Field (Vector 12) :=
      LinearMap.finrank_range_of_inj localEmbedding_injective
    _ = 12 := Module.finrank_fin_fun Field

noncomputable def localRangeEquiv : Vector 12 ≃ₗ[Field] localSpace :=
  LinearEquiv.ofInjective localEmbedding localEmbedding_injective

def localForm (B : BilinForm Field (Vector 24)) : BilinForm Field (Vector 12) :=
  gram B localEmbedding

@[simp] theorem localForm_basis (B : BilinForm Field (Vector 24)) (i j : Fin 12) :
    localForm B (Pi.single i 1) (Pi.single j 1) =
      B (Pi.single (CoveringMatrix.localInclusion i) 1)
        (Pi.single (CoveringMatrix.localInclusion j) 1) := by
  simp [localForm]

theorem localForm_rank (B : BilinForm Field (Vector 24)) :
    finrank Field (LinearMap.range (localForm B)) =
      finrank Field (LinearMap.range (B.restrict localSpace)) := by
  have he : gram (B.restrict localSpace) localRangeEquiv.toLinearMap = localForm B := by
    ext v w
    rfl
  rw [← he]
  exact gram_rank_linearEquiv (B.restrict localSpace) localRangeEquiv

def fullKernel (B : BilinForm Field (Vector 24)) : Submodule Field (Vector 12) :=
  LinearMap.ker (LinearMap.comp B localEmbedding)

def localRadical (B : BilinForm Field (Vector 24)) : Submodule Field (Vector 12) :=
  LinearMap.ker (localForm B)

theorem fullKernel_le_localRadical (B : BilinForm Field (Vector 24)) :
    fullKernel B ≤ localRadical B := by
  intro v hv
  change B (localEmbedding v) = 0 at hv
  change localForm B v = 0
  apply LinearMap.ext
  intro w
  exact LinearMap.congr_fun hv (localEmbedding w)

theorem fullKernel_iff (B : BilinForm Field (Vector 24)) (v : Vector 12) :
    v ∈ fullKernel B ↔
      ∀ j : Fin 24, B (localEmbedding v) (Pi.single j 1) = 0 := by
  constructor
  · intro hv j
    change B (localEmbedding v) = 0 at hv
    exact LinearMap.congr_fun hv (Pi.single j 1)
  · intro h
    change B (localEmbedding v) = 0
    apply (Pi.basisFun Field (Fin 24)).ext
    intro j
    simpa using h j

theorem localRadical_iff (B : BilinForm Field (Vector 24)) (v : Vector 12) :
    v ∈ localRadical B ↔
      ∀ j : Fin 12, B (localEmbedding v) (Pi.single (CoveringMatrix.localInclusion j) 1) = 0 := by
  constructor
  · intro hv j
    change localForm B v = 0 at hv
    have h := LinearMap.congr_fun hv (Pi.single j 1)
    simpa [localForm] using h
  · intro h
    change localForm B v = 0
    apply (Pi.basisFun Field (Fin 12)).ext
    intro j
    simpa [localForm] using h j

theorem fullKernel_map (B : BilinForm Field (Vector 24)) :
    (fullKernel B).map localEmbedding = localSpace ⊓ LinearMap.ker B := by
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨⟨v, rfl⟩, hv⟩
  · rintro ⟨⟨v, rfl⟩, hv⟩
    exact ⟨v, hv, rfl⟩

theorem fullKernel_finrank (B : BilinForm Field (Vector 24)) :
    finrank Field (localSpace ⊓ LinearMap.ker B : Submodule Field (Vector 24)) =
      finrank Field (fullKernel B) := by
  let f := localEmbedding.comp (fullKernel B).subtype
  have hinj : Function.Injective f := by
    intro v w hvw
    apply Subtype.ext
    exact localEmbedding_injective hvw
  have hrange : LinearMap.range f = localSpace ⊓ LinearMap.ker B := by
    change LinearMap.range (localEmbedding.comp (fullKernel B).subtype) = _
    rw [LinearMap.range_comp, Submodule.range_subtype, fullKernel_map]
  have h := LinearMap.finrank_range_of_inj hinj
  rw [hrange] at h
  exact h

theorem local_dimension_inequality (B : BilinForm Field (Vector 24)) (hB : B.IsRefl) :
    24 ≤ finrank Field (LinearMap.range B) + finrank Field (LinearMap.range (localForm B)) +
      2 * finrank Field (fullKernel B) := by
  have h := twice_finrank_le_rank_add_restrict_rank_add_twice_kernel B hB localSpace
  rw [localSpace_finrank, ← localForm_rank B, fullKernel_finrank B] at h
  exact h

theorem localRadical_finrank (B : BilinForm Field (Vector 24)) :
    finrank Field (localRadical B) = 12 - finrank Field (LinearMap.range (localForm B)) := by
  have h := (localForm B).finrank_range_add_finrank_ker
  have hdim : finrank Field (Vector 12) = 12 := Module.finrank_fin_fun Field
  rw [hdim] at h
  change finrank Field (LinearMap.ker (localForm B)) = _
  omega

theorem kernel_thresholds (B : BilinForm Field (Vector 24)) (hB : B.IsRefl)
    (hfull : finrank Field (LinearMap.range B) ≤ 9) :
    (finrank Field (LinearMap.range (localForm B)) = 0 → 8 ≤ finrank Field (fullKernel B)) ∧
    (finrank Field (LinearMap.range (localForm B)) = 6 → 5 ≤ finrank Field (fullKernel B)) ∧
    (finrank Field (LinearMap.range (localForm B)) = 8 → 4 ≤ finrank Field (fullKernel B)) := by
  have h := local_dimension_inequality B hB
  constructor
  · intro hz
    omega
  · constructor <;> intro hr <;> omega

theorem fullKernel_transport (B : BilinForm Field (Vector 24))
    (e : Vector 24 ≃ₗ[Field] Vector 24) (action : Vector 12 →ₗ[Field] Vector 12)
    (hintertwine : localEmbedding.comp action = e.symm.toLinearMap.comp localEmbedding) :
    (fullKernel B).map action ≤ fullKernel (gram B e.toLinearMap) := by
  rintro _ ⟨v, hv, rfl⟩
  change B (localEmbedding v) = 0 at hv
  change gram B e.toLinearMap (localEmbedding (action v)) = 0
  apply LinearMap.ext
  intro w
  change B (e (localEmbedding (action v))) (e w) = 0
  have heq : e (localEmbedding (action v)) = localEmbedding v := by
    have h := LinearMap.congr_fun hintertwine v
    change localEmbedding (action v) = e.symm (localEmbedding v) at h
    rw [h, e.apply_symm_apply]
  rw [heq]
  exact LinearMap.congr_fun hv (e w)

theorem localEmbedding_pairing (B : BilinForm Field (Vector 24))
    (a : Vector 12) (w : Vector 24) :
    B (localEmbedding a) w =
      ∑ i : Fin 12, a i * B (Pi.single (CoveringMatrix.localInclusion i) 1) w := by
  simp only [localEmbedding, Fintype.linearCombination_apply, map_sum, map_smul,
    LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]

theorem evalRow_local_pairing {n : ℕ} (rows : Fin 24 → Fin 24 → ℕ)
    (v : Vector n) (mask : ℕ) (column : Fin 24) :
    CoveringAffine.evalRow (CoveringAffine.composeRow mask
      (fun i : Fin 12 => rows (CoveringMatrix.localInclusion i) column)) v =
        Matrix.toBilin' (CoveringCongruence.coefficientMatrix rows v)
          (localEmbedding (CoveringBits.decodeMask mask)) (Pi.single column 1) := by
  rw [CoveringAffine.evalRow_composeRow, localEmbedding_pairing]
  change (∑ i : Fin 12, if mask.testBit i.val then
    CoveringAffine.evalRow (rows (CoveringMatrix.localInclusion i) column) v else 0) = _
  apply Finset.sum_congr rfl
  intro i hi
  rw [Matrix.toBilin'_single]
  change (if mask.testBit i.val then
    CoveringAffine.evalRow (rows (CoveringMatrix.localInclusion i) column) v else 0) =
      CoveringPolynomial.ofBool (mask.testBit i.val) *
        CoveringAffine.evalRow (rows (CoveringMatrix.localInclusion i) column) v
  cases mask.testBit i.val <;> simp

theorem evalRow_local_kernel_eq_zero {n : ℕ} (rows : Fin 24 → Fin 24 → ℕ)
    (v : Vector n) (mask : ℕ)
    (hmask : CoveringBits.decodeMask mask ∈
      fullKernel (Matrix.toBilin' (CoveringCongruence.coefficientMatrix rows v)))
    (column : Fin 24) :
    CoveringAffine.evalRow (CoveringAffine.composeRow mask
      (fun i : Fin 12 => rows (CoveringMatrix.localInclusion i) column)) v = 0 := by
  rw [evalRow_local_pairing]
  exact (fullKernel_iff _ _).mp hmask column

end Lemmata.CocubicCovering.CoveringLocal
