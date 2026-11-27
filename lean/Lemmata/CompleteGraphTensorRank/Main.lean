module

public import Lemmata.CompleteGraphTensorRank.Restriction
public import Mathlib.Data.Nat.Choose.Cast

@[expose] public section

namespace Lemmata.CompleteGraphTensorRank

open Lemmata.TensorRank

variable {F : Type*} [Field F]

/-- The rectangular correction supplies exactly the missing quarter. -/
theorem odd_rectangular_exponent (r : ℕ) (hr : 1 ≤ r) :
    rectangularExponent ((r : ℝ) ^ 2) r r = (2 * (r : ℝ) + 1) ^ 2 / 4 := by
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (by omega : r ≠ 0)
  have h : ((r : ℝ) ^ 2 + r) * r - (r : ℝ) ^ 2 * r = (r : ℝ) ^ 2 := by ring
  unfold rectangularExponent
  rw [h, max_eq_left (sq_nonneg _)]
  field_simp
  ring

-- DOCS_BEGIN_MAIN
/-- The external rectangular lower bound and the explicit three-block
restriction meet Kirill Khoruzhii's upper bound for every odd order. -/
theorem odd_completeGraph_rank (source : RectangularLowerBound F)
    (r d : ℕ) (hr : 1 ≤ r) (hd : 2 ≤ d) :
    Tensor.asymptoticRank (completeGraph (𝕜 := F) (2 * r + 1) d) =
      (d : ℝ) ^ ((2 * (r : ℝ) + 1) ^ 2 / 4) := by
  have hl := (source r d hr hd).trans (rectangle_le_completeGraph r d (by omega))
  rw [odd_rectangular_exponent r hr] at hl
  have hu := (completeGraphBounds (𝕜 := F) (2 * r + 1) d (by omega) (by omega)).2.1
  push_cast at hu
  exact le_antisymm hu hl

/-- Exact complete-graph asymptotic rank for all orders at least two;
only the stated rectangular lower-bound input is external. -/
theorem completeGraph_rank (source : RectangularLowerBound F) : CompleteGraphEquality F := by
  intro k d hk hd
  by_cases hd1 : d = 1
  · subst d
    obtain ⟨hl, hu, _⟩ := completeGraphBounds (𝕜 := F) k 1 hk (by decide)
    simp only [Nat.cast_one, one_pow, Real.one_rpow] at hl hu ⊢
    exact le_antisymm hu hl
  by_cases he : Even k
  · exact (completeGraphBounds (𝕜 := F) k d hk hd).2.2 he
  obtain ⟨r, rfl⟩ := Nat.not_even_iff_odd.mp he
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using
    odd_completeGraph_rank source r d (by omega) (by omega)

/-- The exponent per edge is exact for odd as well as even complete graphs. -/
theorem edgeExponent_eq (source : RectangularLowerBound F) (k : ℕ) (hk : 2 ≤ k) :
    edgeExponent (𝕜 := F) k = (k : ℝ) / (2 * ((k : ℝ) - 1)) := by
  have hg : graphExponent (𝕜 := F) k = (k : ℝ) ^ 2 / 4 := by
    rw [graphExponent_eq_log_asymptoticRank (b := 2) (by decide),
      completeGraph_rank source k 2 hk (by decide), Real.log_rpow (by norm_num)]
    have hlog : Real.log (2 : ℝ) ≠ 0 := (Real.log_pos (by norm_num)).ne'
    field_simp
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hk1 : (k : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  rw [edgeExponent, hg, Nat.cast_choose_two]
  field_simp
  ring
-- DOCS_END_MAIN

end Lemmata.CompleteGraphTensorRank
