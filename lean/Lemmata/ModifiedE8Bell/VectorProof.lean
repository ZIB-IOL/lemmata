module

public import Lemmata.ModifiedE8Bell.Statement
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Lemmata.ModifiedE8Bell.VectorData
public import Mathlib.Algebra.Order.Star.Real
public meta import Lemmata.ModifiedE8Bell.Statement

@[expose] public section
namespace Lemmata.ModifiedE8Bell
open scoped BigOperators Matrix

lemma realMatrix_symmetric (i j : Setting) : realMatrix i j = realMatrix j i := by
  simp only [realMatrix, fourMatrix, mul_comm, eq_comm]

lemma minus_posSemidef : ((77 : ℝ) • (1 : Matrix Setting Setting ℝ) - realMatrix).PosSemidef := by
  let C : Matrix Setting Setting ℝ := fun i j => (complementMatrix i j : ℝ)
  have he : (77 : ℝ) • (1 : Matrix Setting Setting ℝ) - realMatrix =
      (1/1440 : ℝ) • (Cᴴ * C) := by
    ext i j
    have h : (∑ k, (complementMatrix k i : ℝ) * (complementMatrix k j : ℝ)) =
        360 * (complementMatrix i j : ℝ) := by exact_mod_cast complement_square i j
    change 77 * (if i = j then 1 else 0) - realMatrix i j =
      (1/1440 : ℝ) * (∑ k, (complementMatrix k i : ℝ) * (complementMatrix k j : ℝ))
    rw [h, complement_eq]
    simp only [realMatrix, Int.cast_sub, Int.cast_ite, Int.cast_ofNat]
    by_cases hij : i = j <;> simp [hij] <;> ring
  rw [he]
  exact (Matrix.posSemidef_conjTranspose_mul_self C).smul (by norm_num)

lemma plus_posSemidef : ((77 : ℝ) • (1 : Matrix Setting Setting ℝ) + realMatrix).PosSemidef := by
  let R : Matrix Setting Coordinate ℝ := fun i k => (root i k : ℝ)
  have he : (77 : ℝ) • (1 : Matrix Setting Setting ℝ) + realMatrix =
      (64 : ℝ) • (1 : Matrix Setting Setting ℝ) + (3/4 : ℝ) • (R * Rᴴ) := by
    ext i j
    change 77 * (if i = j then 1 else 0) + realMatrix i j =
      64 * (if i = j then 1 else 0) +
        (3/4:ℝ) * (∑ k, (root i k : ℝ) * (root j k : ℝ))
    simp only [realMatrix, fourMatrix]
    push_cast
    by_cases hij : i = j <;> simp [hij] <;> ring
  rw [he]
  exact (Matrix.PosSemidef.one.smul (by norm_num : (0:ℝ) ≤ 64)).add
    ((Matrix.posSemidef_self_mul_conjTranspose R).smul (by norm_num))

lemma scalar_vector_upper (x y : Setting → ℝ) :
    x ⬝ᵥ (realMatrix *ᵥ y) ≤ (77/2:ℝ) * (x ⬝ᵥ x + y ⬝ᵥ y) := by
  have hm := minus_posSemidef.dotProduct_mulVec_nonneg (x+y)
  have hp := plus_posSemidef.dotProduct_mulVec_nonneg (x-y)
  have hs : realMatrix.IsHermitian := by
    ext i j
    simp [Matrix.conjTranspose_apply, realMatrix_symmetric]
  have hc : y ⬝ᵥ (realMatrix *ᵥ x) = x ⬝ᵥ (realMatrix *ᵥ y) := by
    simpa using hs.star_dotProduct_mulVec_comm y x
  simp only [star_trivial, Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, Matrix.mulVec_add, Matrix.mulVec_sub, dotProduct_sub,
    dotProduct_add, sub_dotProduct, add_dotProduct, dotProduct_smul,
    smul_eq_mul] at hm hp
  rw [hc] at hm hp
  linarith

lemma vectorBell_columns {n : ℕ} (X Y : Setting → Fin n → ℝ) :
    vectorBell X Y = ∑ k, (fun i => X i k) ⬝ᵥ (realMatrix *ᵥ (fun i => Y i k)) := by
  simp only [vectorBell, Matrix.mulVec, dotProduct, Finset.mul_sum]
  calc
    _ = ∑ i, ∑ k, ∑ j, realMatrix i j * (X i k * Y j k) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ k, ∑ i, ∑ j, realMatrix i j * (X i k * Y j k) := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

lemma unitRows_total {n : ℕ} (X : Setting → Fin n → ℝ) (hx : UnitRows X) :
    (∑ k, (fun i => X i k) ⬝ᵥ (fun i => X i k)) = 120 := by
  simp only [dotProduct, ← pow_two]
  rw [Finset.sum_comm]
  change (∑ i, ∑ k, X i k ^ 2) = 120
  have hx' (i : Setting) : (∑ k, X i k ^ 2) = 1 := hx i
  simp_rw [hx']
  norm_num

lemma vectorBell_upper {n : ℕ} (X Y : Setting → Fin n → ℝ)
    (hx : UnitRows X) (hy : UnitRows Y) : vectorBell X Y ≤ 9240 := by
  rw [vectorBell_columns]
  calc
    _ ≤ ∑ k, (77/2:ℝ) * ((fun i => X i k) ⬝ᵥ (fun i => X i k) +
        (fun i => Y i k) ⬝ᵥ (fun i => Y i k)) :=
      Finset.sum_le_sum fun k _ => scalar_vector_upper _ _
    _ = 9240 := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib, unitRows_total X hx, unitRows_total Y hy]
      norm_num

lemma vectorBell_abs_upper {n : ℕ} (X Y : Setting → Fin n → ℝ)
    (hx : UnitRows X) (hy : UnitRows Y) : |vectorBell X Y| ≤ 9240 := by
  have hu := vectorBell_upper X Y hx hy
  have hn : UnitRows (fun i k => -X i k) := by simpa [UnitRows] using hx
  have hl := vectorBell_upper (fun i k => -X i k) Y hn hy
  have he : vectorBell (fun i k => -X i k) Y = -vectorBell X Y := by
    simp [vectorBell, Finset.sum_neg_distrib, mul_neg, neg_mul]
  rw [he] at hl
  exact abs_le.mpr ⟨by linarith, hu⟩

lemma rootMeasurements_unit : UnitRows rootMeasurements := by
  intro i
  have hn : (∑ k, (root i k : ℝ)^2) = 8 := by exact_mod_cast root_norm i
  simp only [rootMeasurements, div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 8),
    ← Finset.sum_div, hn]
  norm_num

lemma rootMeasurements_value : vectorBell rootMeasurements rootMeasurements = 9240 := by
  have hn : (∑ i, ∑ j, (fourMatrix i j : ℝ) *
      (∑ k, (root i k : ℝ) * (root j k : ℝ))) = 295680 := by
    exact_mod_cast vector_witness_integer
  have he : vectorBell rootMeasurements rootMeasurements =
      (∑ i, ∑ j, (fourMatrix i j : ℝ) *
        (∑ k, (root i k : ℝ) * (root j k : ℝ))) / 32 := by
    simp only [vectorBell, rootMeasurements, realMatrix, div_mul_div_comm,
      Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 8), ← Finset.sum_div]
    norm_num
  rw [he, hn]
  norm_num

/-- The vector value is 9240 in every dimension and is attained in dimension eight. -/
theorem exact_vector_value : ExactVectorValue :=
  ⟨fun _ X Y hx hy => vectorBell_abs_upper X Y hx hy,
   rootMeasurements_unit, rootMeasurements_value⟩

end Lemmata.ModifiedE8Bell
