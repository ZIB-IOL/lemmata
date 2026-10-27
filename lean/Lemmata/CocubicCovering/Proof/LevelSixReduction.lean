module

public import Lemmata.CocubicCovering.Proof.LevelSix
public meta import Lemmata.CocubicCovering.Proof.LevelSix
public import Lemmata.CocubicCovering.Proof.ZeroKernel
public meta import Lemmata.CocubicCovering.Proof.ZeroKernel
public import Lemmata.CocubicCovering.Proof.Symplectic
public meta import Lemmata.CocubicCovering.Proof.Symplectic

@[expose] public section

set_option Elab.async false

namespace Lemmata.CocubicCovering.CoveringLevelSixReduction

open Module Covering CoveringAffine CoveringCongruence
open LinearMap (BilinForm)
open scoped BigOperators

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def common_multipliers_decision (i : Fin 24) : Decidable (CoveringLevelSix.multiplier (Fin.castAdd 3 i) = CoveringMatrix.multiplier i) :=
  inferInstance

@[noinline, never_extract]
def common_multipliers_check (i : Fin 24) : Bool :=
  @decide (CoveringLevelSix.multiplier (Fin.castAdd 3 i) = CoveringMatrix.multiplier i) (common_multipliers_decision i)

theorem common_multipliers_check_sound (i : Fin 24) (computed : common_multipliers_check i = true) :
    CoveringLevelSix.multiplier (Fin.castAdd 3 i) = CoveringMatrix.multiplier i := by
  unfold common_multipliers_check at computed
  exact @of_decide_eq_true (CoveringLevelSix.multiplier (Fin.castAdd 3 i) = CoveringMatrix.multiplier i) (common_multipliers_decision i) computed

theorem common_multipliers : ∀ i : Fin 24,
    CoveringLevelSix.multiplier (Fin.castAdd 3 i) = CoveringMatrix.multiplier i := by
  have computed : ∀ (i : Fin 24), common_multipliers_check i = true := by native_decide
  intro i
  exact common_multipliers_check_sound i (computed i)

def common_parameters_decision (i : Fin 126) : Decidable (CoveringLevelSix.parameterMasks i = CoveringCovarianceData.parameterMasks i) :=
  inferInstance

@[noinline, never_extract]
def common_parameters_check (i : Fin 126) : Bool :=
  @decide (CoveringLevelSix.parameterMasks i = CoveringCovarianceData.parameterMasks i) (common_parameters_decision i)

theorem common_parameters_check_sound (i : Fin 126) (computed : common_parameters_check i = true) :
    CoveringLevelSix.parameterMasks i = CoveringCovarianceData.parameterMasks i := by
  unfold common_parameters_check at computed
  exact @of_decide_eq_true (CoveringLevelSix.parameterMasks i = CoveringCovarianceData.parameterMasks i) (common_parameters_decision i) computed

theorem common_parameters : ∀ i : Fin 126,
    CoveringLevelSix.parameterMasks i = CoveringCovarianceData.parameterMasks i := by
  have computed : ∀ (i : Fin 126), common_parameters_check i = true := by native_decide
  intro i
  exact common_parameters_check_sound i (computed i)

def common_rows_decision (i j : Fin 24) : Decidable (CoveringLevelSix.matrixRows (Fin.castAdd 3 i) (Fin.castAdd 3 j) =
      CoveringCovarianceData.matrixRows i j) :=
  inferInstance

@[noinline, never_extract]
def common_rows_check (i j : Fin 24) : Bool :=
  @decide (CoveringLevelSix.matrixRows (Fin.castAdd 3 i) (Fin.castAdd 3 j) =
      CoveringCovarianceData.matrixRows i j) (common_rows_decision i j)

theorem common_rows_check_sound (i j : Fin 24) (computed : common_rows_check i j = true) :
    CoveringLevelSix.matrixRows (Fin.castAdd 3 i) (Fin.castAdd 3 j) =
      CoveringCovarianceData.matrixRows i j := by
  unfold common_rows_check at computed
  exact @of_decide_eq_true (CoveringLevelSix.matrixRows (Fin.castAdd 3 i) (Fin.castAdd 3 j) =
      CoveringCovarianceData.matrixRows i j) (common_rows_decision i j) computed

theorem common_rows : ∀ i j : Fin 24,
    CoveringLevelSix.matrixRows (Fin.castAdd 3 i) (Fin.castAdd 3 j) =
      CoveringCovarianceData.matrixRows i j := by
  have computed : ∀ (i j : Fin 24), common_rows_check i j = true := by native_decide
  intro i j
  exact common_rows_check_sound i j (computed i j)

def symmetric_rows_decision (i j : Fin 27) : Decidable (CoveringLevelSix.matrixRows i j = CoveringLevelSix.matrixRows j i) :=
  inferInstance

@[noinline, never_extract]
def symmetric_rows_check (i j : Fin 27) : Bool :=
  @decide (CoveringLevelSix.matrixRows i j = CoveringLevelSix.matrixRows j i) (symmetric_rows_decision i j)

theorem symmetric_rows_check_sound (i j : Fin 27) (computed : symmetric_rows_check i j = true) :
    CoveringLevelSix.matrixRows i j = CoveringLevelSix.matrixRows j i := by
  unfold symmetric_rows_check at computed
  exact @of_decide_eq_true (CoveringLevelSix.matrixRows i j = CoveringLevelSix.matrixRows j i) (symmetric_rows_decision i j) computed

private theorem symmetric_rows : ∀ i j : Fin 27,
    CoveringLevelSix.matrixRows i j = CoveringLevelSix.matrixRows j i := by
  have computed : ∀ (i j : Fin 27), symmetric_rows_check i j = true := by native_decide
  intro i j
  exact symmetric_rows_check_sound i j (computed i j)

def diagonal_rows_decision (i : Fin 27) : Decidable (CoveringLevelSix.matrixRows i i = 0) :=
  inferInstance

@[noinline, never_extract]
def diagonal_rows_check (i : Fin 27) : Bool :=
  @decide (CoveringLevelSix.matrixRows i i = 0) (diagonal_rows_decision i)

theorem diagonal_rows_check_sound (i : Fin 27) (computed : diagonal_rows_check i = true) :
    CoveringLevelSix.matrixRows i i = 0 := by
  unfold diagonal_rows_check at computed
  exact @of_decide_eq_true (CoveringLevelSix.matrixRows i i = 0) (diagonal_rows_decision i) computed

private theorem diagonal_rows : ∀ i : Fin 27, CoveringLevelSix.matrixRows i i = 0 := by
  have computed : ∀ (i : Fin 27), diagonal_rows_check i = true := by native_decide
  intro i
  exact diagonal_rows_check_sound i (computed i)

def field_add_self_decision (a : Field) : Decidable (a + a = 0) :=
  inferInstance

@[noinline, never_extract]
def field_add_self_check (a : Field) : Bool :=
  @decide (a + a = 0) (field_add_self_decision a)

theorem field_add_self_check_sound (a : Field) (computed : field_add_self_check a = true) :
    a + a = 0 := by
  unfold field_add_self_check at computed
  exact @of_decide_eq_true (a + a = 0) (field_add_self_decision a) computed

private theorem field_add_self : ∀ a : Field, a + a = 0 := by
  have computed : ∀ (a : Field), field_add_self_check a = true := by native_decide
  intro a
  exact field_add_self_check_sound a (computed a)

theorem matrix_isAlt {n : ℕ} (A : Matrix (Fin n) (Fin n) Field)
    (hsymmetric : ∀ i j, A i j = A j i) (hdiagonal : ∀ i, A i i = 0) :
    (Matrix.toBilin' A).IsAlt := by
  classical
  intro x
  apply (Matrix.toBilin'_apply A x x).trans
  apply (Fintype.sum_prod_type' (fun i j => x i * A i j * x j)).symm.trans
  apply Finset.sum_ninvolution Prod.swap
  · intro p
    change x p.1 * A p.1 p.2 * x p.2 + x p.2 * A p.2 p.1 * x p.1 = 0
    rw [hsymmetric p.2 p.1]
    have he : x p.2 * A p.1 p.2 * x p.1 = x p.1 * A p.1 p.2 * x p.2 := by ring
    rw [he]
    exact field_add_self _
  · intro p hnonzero hfixed
    apply hnonzero
    have he : p.2 = p.1 := congrArg Prod.fst hfixed
    rw [he, hdiagonal p.1, mul_zero, zero_mul]
  · intro p
    exact Finset.mem_univ _
  · intro p
    exact Prod.swap_swap p

def fullForm (v : Vector 127) : BilinForm Field (Vector 27) :=
  Matrix.toBilin' (coefficientMatrix CoveringLevelSix.matrixRows v)

theorem fullForm_isAlt (v : Vector 127) : (fullForm v).IsAlt := by
  apply matrix_isAlt
  · intro i j
    exact congrArg (fun row => evalRow row v) (symmetric_rows i j)
  · intro i
    change evalRow (CoveringLevelSix.matrixRows i i) v = 0
    rw [diagonal_rows]
    simp [evalRow]

theorem actualGram_isAlt (h : BooleanFunction 9) (hh : h ∈ reedMuller 9 5) :
    (supportGram (eval form9 + h) CoveringLevelSix.multiplierLinear).IsAlt := by
  apply supportGram_isAlt (by decide)
    ((reedMuller 9 6).add_mem form9_mem (reedMuller_mono (by decide) hh))
    CoveringLevelSix.multiplierLinear CoveringLevelSix.multiplierLinear_mem

theorem rank_le_ten_of_lt_twelve (v : Vector 127)
    (hrank : finrank Field (LinearMap.range (fullForm v)) < 12) :
    finrank Field (LinearMap.range (fullForm v)) ≤ 10 :=
  CoveringSymplectic.rank_le_ten_of_lt_twelve (fullForm v) (fullForm_isAlt v) hrank

def commonEmbedding : Vector 24 →ₗ[Field] Vector 27 :=
  Fintype.linearCombination Field fun i => Pi.single (Fin.castAdd 3 i) 1

@[simp] theorem commonEmbedding_basis (i : Fin 24) :
    commonEmbedding (Pi.single i 1) = Pi.single (Fin.castAdd 3 i) 1 := by
  simp [commonEmbedding]

def commonProjection : Vector 27 →ₗ[Field] Vector 24 where
  toFun v i := v (Fin.castAdd 3 i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem commonProjection_embedding (v : Vector 24) :
    commonProjection (commonEmbedding v) = v := by
  funext i
  have he : ∀ x : Fin 24, Fin.castAdd 3 i = Fin.castAdd 3 x ↔ i = x := by
    intro x
    constructor
    · intro h
      exact Fin.ext (congrArg (fun a : Fin 27 => a.val) h)
    · rintro rfl
      rfl
  simp [commonProjection, commonEmbedding, Fintype.linearCombination_apply, Pi.single_apply, he]

theorem commonEmbedding_injective : Function.Injective commonEmbedding := by
  intro v w hvw
  have h := congrArg commonProjection hvw
  simpa only [commonProjection_embedding] using h

theorem common_restriction (v : Vector 127) :
    gram (fullForm v) commonEmbedding = CoveringSymmetry.fullForm v := by
  apply (Pi.basisFun Field (Fin 24)).ext
  intro i
  apply (Pi.basisFun Field (Fin 24)).ext
  intro j
  simp only [Pi.basisFun_apply, gram_apply, commonEmbedding_basis,
    fullForm, CoveringSymmetry.fullForm, Matrix.toBilin'_single, coefficientMatrix]
  exact congrArg (fun row => evalRow row v) (common_rows i j)

def localEmbedding : Vector 12 →ₗ[Field] Vector 27 :=
  commonEmbedding.comp CoveringLocal.localEmbedding

@[simp] theorem localEmbedding_basis (i : Fin 12) :
    localEmbedding (Pi.single i 1) =
      Pi.single (Fin.castAdd 3 (CoveringMatrix.localInclusion i)) 1 := by
  rw [localEmbedding, LinearMap.comp_apply, CoveringLocal.localEmbedding_basis,
    commonEmbedding_basis]

theorem localEmbedding_injective : Function.Injective localEmbedding :=
  commonEmbedding_injective.comp CoveringLocal.localEmbedding_injective

def localSpace : Submodule Field (Vector 27) := LinearMap.range localEmbedding

theorem localSpace_finrank : finrank Field localSpace = 12 := by
  change finrank Field (LinearMap.range localEmbedding) = 12
  exact (LinearMap.finrank_range_of_inj localEmbedding_injective).trans
    (Module.finrank_fin_fun Field)

def crossMap (v : Vector 127) := LinearMap.comp (fullForm v) localEmbedding

def fullKernel (v : Vector 127) : Submodule Field (Vector 12) :=
  LinearMap.ker (crossMap v)

private theorem kernel_map {a b : ℕ} (B : BilinForm Field (Vector a))
    (e : Vector b →ₗ[Field] Vector a) :
    (LinearMap.ker (LinearMap.comp B e)).map e = LinearMap.range e ⊓ LinearMap.ker B := by
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨⟨v, rfl⟩, hv⟩
  · rintro ⟨⟨v, rfl⟩, hv⟩
    exact ⟨v, hv, rfl⟩

private theorem kernel_finrank {a b : ℕ} (B : BilinForm Field (Vector a))
    (e : Vector b →ₗ[Field] Vector a) (hinj : Function.Injective e) :
    finrank Field (LinearMap.range e ⊓ LinearMap.ker B : Submodule Field (Vector a)) =
      finrank Field (LinearMap.ker (LinearMap.comp B e)) := by
  let f := e.comp (LinearMap.ker (LinearMap.comp B e)).subtype
  have hf : Function.Injective f := by
    intro v w hvw
    apply Subtype.ext
    exact hinj hvw
  have hrange : LinearMap.range f = LinearMap.range e ⊓ LinearMap.ker B := by
    change LinearMap.range (e.comp (LinearMap.ker (LinearMap.comp B e)).subtype) = _
    rw [LinearMap.range_comp, Submodule.range_subtype, kernel_map]
  have h := LinearMap.finrank_range_of_inj hf
  rw [hrange] at h
  exact h

private theorem gram_rank_restrict {a b : ℕ} (B : BilinForm Field (Vector a))
    (e : Vector b →ₗ[Field] Vector a) (hinj : Function.Injective e) :
    finrank Field (LinearMap.range (gram B e)) =
      finrank Field (LinearMap.range (B.restrict (LinearMap.range e))) := by
  let i := LinearEquiv.ofInjective e hinj
  have he : gram (B.restrict (LinearMap.range e)) i.toLinearMap = gram B e := by
    apply BilinForm.ext
    intro v w
    rfl
  rw [← he]
  exact gram_rank_linearEquiv (B.restrict (LinearMap.range e)) i

private theorem dimension_inequality {a b : ℕ} (B : BilinForm Field (Vector a))
    (hB : B.IsRefl) (e : Vector b →ₗ[Field] Vector a) (hinj : Function.Injective e) :
    2 * b ≤ finrank Field (LinearMap.range B) +
      finrank Field (LinearMap.range (gram B e)) +
      2 * finrank Field (LinearMap.ker (LinearMap.comp B e)) := by
  have h := twice_finrank_le_rank_add_restrict_rank_add_twice_kernel B hB (LinearMap.range e)
  have hd : finrank Field (LinearMap.range e) = b :=
    (LinearMap.finrank_range_of_inj hinj).trans (Module.finrank_fin_fun Field)
  rw [hd, ← gram_rank_restrict B e hinj, kernel_finrank B e hinj] at h
  exact h

theorem fullKernel_map (v : Vector 127) :
    (fullKernel v).map localEmbedding = localSpace ⊓ LinearMap.ker (fullForm v) :=
  kernel_map (fullForm v) localEmbedding

theorem fullKernel_finrank (v : Vector 127) :
    finrank Field (localSpace ⊓ LinearMap.ker (fullForm v) : Submodule Field (Vector 27)) =
      finrank Field (fullKernel v) :=
  kernel_finrank (fullForm v) localEmbedding localEmbedding_injective

theorem local_dimension_inequality (v : Vector 127) :
    24 ≤ finrank Field (LinearMap.range (fullForm v)) +
      finrank Field (LinearMap.range (gram (fullForm v) localEmbedding)) +
      2 * finrank Field (fullKernel v) :=
  dimension_inequality (fullForm v) (fullForm_isAlt v).isRefl localEmbedding localEmbedding_injective

private theorem kernel_comp_le_gram_comp {a b c : ℕ}
    (B : BilinForm Field (Vector a)) (e : Vector b →ₗ[Field] Vector a)
    (l : Vector c →ₗ[Field] Vector b) :
    LinearMap.ker (LinearMap.comp B (e.comp l)) ≤
      LinearMap.ker (LinearMap.comp (gram B e) l) := by
  intro x hx
  change B (e (l x)) = 0 at hx
  change gram B e (l x) = 0
  apply LinearMap.ext
  intro y
  change B (e (l x)) (e y) = 0
  exact LinearMap.congr_fun hx (e y)

theorem fullKernel_le_common (v : Vector 127) :
    fullKernel v ≤ CoveringLocal.fullKernel (CoveringSymmetry.fullForm v) := by
  have h : fullKernel v ≤ LinearMap.ker
      (LinearMap.comp (gram (fullForm v) commonEmbedding) CoveringLocal.localEmbedding) :=
    kernel_comp_le_gram_comp (fullForm v) commonEmbedding CoveringLocal.localEmbedding
  have he := congrArg
    (fun B : BilinForm Field (Vector 24) =>
      LinearMap.ker (LinearMap.comp B CoveringLocal.localEmbedding))
    (common_restriction v)
  exact h.trans (le_of_eq he)

theorem fullKernel_le_seven (v : Vector 127) (hpoint : v (Fin.last 126) = 1)
    (hprojection : CoveringSymmetry.localParameterProjection v = 0) :
    finrank Field (fullKernel v) ≤ 7 :=
  (Submodule.finrank_mono (fullKernel_le_common v)).trans
    (CoveringZeroKernel.finrank_fullKernel_le_seven v hpoint hprojection)

theorem crossRank_ge_five (v : Vector 127) (hpoint : v (Fin.last 126) = 1)
    (hprojection : CoveringSymmetry.localParameterProjection v = 0) :
    5 ≤ finrank Field (LinearMap.range (crossMap v)) := by
  have hkernel := fullKernel_le_seven v hpoint hprojection
  have hnullity := (crossMap v).finrank_range_add_finrank_ker
  have hdimension : finrank Field (Vector 12) = 12 := Module.finrank_fin_fun Field
  change finrank Field (LinearMap.range (crossMap v)) + finrank Field (fullKernel v) =
    finrank Field (Vector 12) at hnullity
  omega

private theorem projection_rows :
    CoveringLocalRanks.localParameterRows = CoveringSymmetry.projectionRows := by
  native_decide

private theorem gram_comp {a b c : ℕ} (B : BilinForm Field (Vector a))
    (e : Vector b →ₗ[Field] Vector a) (l : Vector c →ₗ[Field] Vector b) :
    gram B (e.comp l) = gram (gram B e) l := by
  ext x y
  rfl

theorem local_restriction (v : Vector 127) :
    gram (fullForm v) localEmbedding = CoveringLocal.localForm (CoveringSymmetry.fullForm v) := by
  have hleft := gram_comp (fullForm v) commonEmbedding CoveringLocal.localEmbedding
  have hright := congrArg
    (fun B : BilinForm Field (Vector 24) => gram B CoveringLocal.localEmbedding)
    (common_restriction v)
  exact hleft.trans hright

theorem localGram_eq_zero (v : Vector 127)
    (hprojection : CoveringSymmetry.localParameterProjection v = 0) :
    gram (fullForm v) localEmbedding = 0 := by
  change rowMap CoveringSymmetry.projectionRows v = 0 at hprojection
  have hmatrix : coefficientMatrix CoveringLocalRanks.localRows (0 : Vector 15) = 0 := by
    ext i j
    simp [coefficientMatrix, evalRow]
  have hold : CoveringLocal.localForm (CoveringSymmetry.fullForm v) = 0 := by
    change CoveringLocal.localForm
      (Matrix.toBilin' (coefficientMatrix CoveringCovarianceData.matrixRows v)) = 0
    rw [CoveringLocalRanks.localForm_submatrix, CoveringLocalRanks.local_submatrix,
      projection_rows, hprojection, hmatrix]
    simp
  exact (local_restriction v).trans hold

private theorem twice_rank_comp_le {a b : ℕ} (B : BilinForm Field (Vector a))
    (hB : B.IsRefl) (e : Vector b →ₗ[Field] Vector a) (hgram : gram B e = 0) :
    2 * finrank Field (LinearMap.range (LinearMap.comp B e)) ≤
      finrank Field (LinearMap.range B) := by
  let N := LinearMap.range e
  have hisotropic : N ≤ B.orthogonal N := by
    rintro z ⟨a, rfl⟩ w ⟨b, rfl⟩
    exact BilinForm.congr_fun hgram b a
  have hR : N ⊓ B.orthogonal N = N := inf_eq_left.mpr hisotropic
  have hbound := restrict_rank_add_twice_cross_rank_le B hB N
  rw [hR] at hbound
  have hrange : LinearMap.range (B.domRestrict N) =
      LinearMap.range (LinearMap.comp B e) := by
    ext f
    constructor
    · rintro ⟨⟨z, hz⟩, rfl⟩
      obtain ⟨a, rfl⟩ := hz
      exact ⟨a, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨⟨e a, ⟨a, rfl⟩⟩, rfl⟩
  rw [hrange] at hbound
  omega

theorem twice_crossRank_le (v : Vector 127)
    (hprojection : CoveringSymmetry.localParameterProjection v = 0) :
    2 * finrank Field (LinearMap.range (crossMap v)) ≤
      finrank Field (LinearMap.range (fullForm v)) :=
  twice_rank_comp_le (fullForm v) (fullForm_isAlt v).isRefl localEmbedding
    (localGram_eq_zero v hprojection)

theorem crossRank_eq_five (v : Vector 127) (hpoint : v (Fin.last 126) = 1)
    (hprojection : CoveringSymmetry.localParameterProjection v = 0)
    (hrank : finrank Field (LinearMap.range (fullForm v)) ≤ 10) :
    finrank Field (LinearMap.range (crossMap v)) = 5 := by
  have hlower := crossRank_ge_five v hpoint hprojection
  have hupper := twice_crossRank_le v hprojection
  omega

end Lemmata.CocubicCovering.CoveringLevelSixReduction
