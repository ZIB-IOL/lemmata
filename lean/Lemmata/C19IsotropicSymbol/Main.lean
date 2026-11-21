module

public import Lemmata.C19IsotropicSymbol.Statement

public section

namespace Lemmata.C19IsotropicSymbol

theorem c19IsotropicMoment (k : WaveVector) :
    2 * (positiveBonds.map fun b =>
      (b.weight : ℝ) * (dotSite k b.offset) ^ 2).sum =
      speedSq * waveNormSq k := by
  norm_num [positiveBonds, speedSq, waveNormSq, dotSite]
  ring

theorem c19SpeedSquared : speedSq = 12 := by
  norm_num [speedSq, positiveBonds]

theorem dotSiteScale (h : ℝ) (k : WaveVector) (s : Site) :
    dotSite (scaleWave h k) s = h * dotSite k s := by
  unfold dotSite scaleWave
  ring

theorem centeredCosineError (x : ℝ) :
    |2 * (1 - Real.cos x) - x ^ 2| ≤ x ^ 4 / 12 := by
  have hc : Real.cos x = 1 - 2 * Real.sin (x / 2) ^ 2 := by
    conv_lhs => rw [show x = 2 * (x / 2) by ring]
    exact Real.cos_two_mul_eq_one_sub _
  have hsum : |Real.sin (x / 2) + x / 2| ≤ 2 * |x / 2| := by
    calc
      _ ≤ |Real.sin (x / 2)| + |x / 2| := abs_add_le _ _
      _ ≤ _ := by linarith [Real.abs_sin_le_abs (x := x / 2)]
  have hsub : |Real.sin (x / 2) - x / 2| ≤ |x / 2| ^ 3 / 6 := by
    rw [abs_sub_comm]
    exact Real.abs_sub_sin_le _
  have hm := mul_le_mul hsub hsum (abs_nonneg _)
    (by positivity : 0 ≤ |x / 2| ^ 3 / 6)
  rw [hc, show 2 * (1 - (1 - 2 * Real.sin (x / 2) ^ 2)) - x ^ 2 =
      4 * ((Real.sin (x / 2) - x / 2) * (Real.sin (x / 2) + x / 2)) by ring,
    abs_mul, abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (4 : ℝ))]
  calc
    _ ≤ 4 * ((|x / 2| ^ 3 / 6) * (2 * |x / 2|)) := by
      simpa [mul_assoc] using
        mul_le_mul_of_nonneg_left hm (by norm_num : 0 ≤ (4 : ℝ))
    _ = x ^ 4 / 12 := by
      rw [abs_div, abs_of_pos (by norm_num : 0 < (2 : ℝ))]
      rw [show (|x| / 2) ^ 3 / 6 * (2 * (|x| / 2)) = |x| ^ 4 / 48 by ring,
        pow_abs, abs_of_nonneg (by positivity : 0 ≤ x ^ 4)]
      ring

private theorem spatialListError (bs : List Bond) (h : ℝ) (k : WaveVector) :
    |4 * (bs.map fun b =>
      (b.weight : ℝ) * (1 - Real.cos (dotSite (scaleWave h k) b.offset))).sum -
      h ^ 2 * (2 * (bs.map fun b =>
        (b.weight : ℝ) * (dotSite k b.offset) ^ 2).sum)| ≤
      h ^ 4 * ((bs.map fun b =>
        (b.weight : ℝ) * (dotSite k b.offset) ^ 4).sum / 6) := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
    simp only [List.map_cons, List.sum_cons]
    let q := dotSite k b.offset
    let w : ℝ := b.weight
    let s := (bs.map fun d =>
      (d.weight : ℝ) * (1 - Real.cos (dotSite (scaleWave h k) d.offset))).sum
    let m := (bs.map fun d =>
      (d.weight : ℝ) * (dotSite k d.offset) ^ 2).sum
    let e := (bs.map fun d =>
      (d.weight : ℝ) * (dotSite k d.offset) ^ 4).sum
    rw [dotSiteScale]
    change |4 * (w * (1 - Real.cos (h * q)) + s) -
      h ^ 2 * (2 * (w * q ^ 2 + m))| ≤ h ^ 4 * ((w * q ^ 4 + e) / 6)
    rw [show 4 * (w * (1 - Real.cos (h * q)) + s) -
      h ^ 2 * (2 * (w * q ^ 2 + m)) =
      (2 * w) * (2 * (1 - Real.cos (h * q)) - (h * q) ^ 2) +
        (4 * s - h ^ 2 * (2 * m)) by ring]
    have hw : 0 ≤ 2 * w := by positivity
    calc
      _ ≤ |(2 * w) * (2 * (1 - Real.cos (h * q)) - (h * q) ^ 2)| +
          |4 * s - h ^ 2 * (2 * m)| := abs_add_le _ _
      _ ≤ (2 * w) * ((h * q) ^ 4 / 12) + h ^ 4 * (e / 6) := by
        rw [abs_mul, abs_of_nonneg hw]
        exact add_le_add
          (mul_le_mul_of_nonneg_left (centeredCosineError _) hw) ih
      _ = _ := by ring

theorem c19SpatialQuarticError (h : ℝ) (k : WaveVector) :
    |spaceSymbol (scaleWave h k) - h ^ 2 * (speedSq * waveNormSq k)| ≤
      h ^ 4 * spatialErrorWeight k := by
  rw [← c19IsotropicMoment k]
  exact spatialListError positiveBonds h k

-- DOCS_BEGIN_MAIN
/-- The exact C19 isotropy and finite-spacing quartic error certificate. -/
theorem c19IsotropicSymbol : C19SymbolStatement := by
  exact ⟨c19IsotropicMoment, c19SpeedSquared, c19SpatialQuarticError⟩
-- DOCS_END_MAIN

end Lemmata.C19IsotropicSymbol
