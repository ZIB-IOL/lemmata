module

public import Lemmata.GrothendieckLowerBounds.Statement
public import Lemmata.GrothendieckLowerBounds.Rotation
public import Lemmata.GrothendieckLowerBounds.Sphere
public import Lemmata.GrothendieckLowerBounds.Witness3
public import Lemmata.GrothendieckLowerBounds.Witness3Split
public import Lemmata.GrothendieckLowerBounds.Witness3Orbit
public import Lemmata.GrothendieckLowerBounds.Witness5
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

public section

namespace Lemmata.GrothendieckLowerBounds

open scoped BigOperators

theorem score_le_entry {n m : ℕ} (D : BellMatrix n m)
    (a : Fin n → ℝ) (ha : IsSign a) : score D a ≤ entryNorm D := by
  unfold score entryNorm
  apply Finset.sum_le_sum
  intro j _
  calc
    |∑ i, a i * D i j| ≤ ∑ i, |a i * D i j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |D i j| := by
      apply Finset.sum_congr rfl
      intro i _
      rw [abs_mul, ha i, one_mul]

theorem score_add_le {n m : ℕ} (M D : BellMatrix n m)
    (a : Fin n → ℝ) :
    score (fun i j => M i j + D i j) a ≤ score M a + score D a := by
  unfold score
  simp_rw [mul_add, Finset.sum_add_distrib]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun j _ => abs_add_le _ _)

theorem score_scale {n m : ℕ} (M : BellMatrix n m)
    (a : Fin n → ℝ) (t : ℝ) (ht : 0 ≤ t) :
    score (fun i j => t * M i j) a = t * score M a := by
  unfold score
  simp_rw [mul_left_comm (a _) t, ← Finset.mul_sum, abs_mul, abs_of_nonneg ht]
  rw [Finset.mul_sum]

/-- Perturbation control for each actual deterministic Alice strategy. -/
theorem perturbation_bound {n m : ℕ} (M Y : BellMatrix n m)
    (a : Fin n → ℝ) (ha : IsSign a) (t : ℝ) (ht : 0 ≤ t) :
    score Y a ≤ t * score M a + entryNorm (fun i j => Y i j - t * M i j) := by
  have hid : Y = fun i j => t * M i j + (Y i j - t * M i j) := by
    funext i j
    ring
  calc
    score Y a ≤ score (fun i j => t * M i j) a +
        score (fun i j => Y i j - t * M i j) a := by
      conv_lhs => rw [hid]
      exact score_add_le _ _ _
    _ ≤ t * score M a + entryNorm (fun i j => Y i j - t * M i j) := by
      rw [score_scale M a t ht]
      exact add_le_add (le_refl _) (score_le_entry _ a ha)

/-- An exhaustive near set and a residual bound certify a new matrix. -/
theorem reuse_classical_certificate {n m : ℕ} (M Y : BellMatrix n m)
    (S : Finset (Fin n → ℝ)) (T t R : ℝ) (ht : 0 ≤ t)
    (coverage : NearCoverage M Y T S)
    (near_bound : ∀ s ∈ S, score Y s ≤ R) :
    ClassicalUpper Y (max R
      (t * T + entryNorm (fun i j => Y i j - t * M i j))) := by
  intro a ha
  by_cases h : T < score M a
  · obtain ⟨s, hs, _, heq⟩ := coverage a ha h
    rw [heq]
    exact (near_bound s hs).trans (le_max_left _ _)
  · have hsmall : score M a ≤ T := le_of_not_gt h
    exact (perturbation_bound M Y a ha t ht).trans
      ((add_le_add (mul_le_mul_of_nonneg_left hsmall ht) (le_refl _)).trans
        (le_max_right _ _))

/-- The value of integer vectors over a common denominator `D`. -/
theorem vectorObj_scaled {n m d : ℕ} (M : Fin n → Fin m → ℤ) (A : Fin n → Fin d → ℤ)
    (B : Fin m → Fin d → ℤ) (D : ℝ) (hD : D ≠ 0) :
    vectorObj (fun i j => (M i j : ℝ)) (fun i k => (A i k : ℝ) / D) (fun j k => (B j k : ℝ) / D) =
      ((∑ i, ∑ j, M i j * ∑ k, A i k * B j k : ℤ) : ℝ) / D ^ 2 := by
  unfold vectorObj
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_div_assoc, Finset.sum_div]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  field_simp

/-- A common positive integer denominator normalizes a family of integer vectors. -/
theorem ball_scaled_den {n d : ℕ} (A : Fin n → Fin d → ℤ) (D : ℤ) (hD : 0 < D)
    (hA : ∀ i, ∑ k, A i k ^ 2 ≤ D ^ 2) :
    ∀ i, ∑ k, ((A i k : ℝ) / (D : ℝ)) ^ 2 ≤ 1 := by
  intro i
  have h' : (∑ k, (A i k : ℝ) ^ 2) ≤ (D : ℝ) ^ 2 := by exact_mod_cast hA i
  have hpos : (0 : ℝ) < D := by exact_mod_cast hD
  simpa only [div_pow, ← Finset.sum_div, div_le_one (sq_pos_of_pos hpos)] using h'

/-- Integer vectors with squared numerators at most `10³⁰` lie in the unit ball. -/
theorem ball_scaled {n d : ℕ} (A : Fin n → Fin d → ℤ) (hA : ∀ i, ∑ k, A i k ^ 2 ≤ 10 ^ 30) :
    ∀ i, ∑ k, ((A i k : ℝ) / 10 ^ 15) ^ 2 ≤ 1 := by
  intro i
  have h' : (∑ k, (A i k : ℝ) ^ 2) ≤ 10 ^ 30 := by exact_mod_cast hA i
  simp only [div_pow, ← Finset.sum_div]
  rw [div_le_one (by positivity)]
  norm_num at h' ⊢
  exact h'

/-- Signs attaining a classical value. -/
theorem score_attained {n m : ℕ} (M : Fin n → Fin m → ℤ) (s : Fin n → ℤ)
    (hs : ∀ i, s i = 1 ∨ s i = -1) (c : ℤ) (h : ∑ j, |∑ i, s i * M i j| = c) :
    ∃ a, IsSign a ∧ score (fun i j => (M i j : ℝ)) a = c := by
  refine ⟨fun i => (s i : ℝ), fun i => ?_, ?_⟩
  · rcases hs i with h | h <;> simp [h]
  · unfold score
    rw [← h]
    push_cast
    rfl

-- DOCS_BEGIN_MAIN
/-- A row transport with absolute column sums bounded by `s` increases the one-norm
by at most a factor of `s`. Apply this with `u = K b` to transfer the sign cutoff. -/
theorem transport_one_norm {n k : ℕ} (V : BellMatrix n k) (u : Fin k → ℝ) (s : ℝ)
    (hs : ∀ j, ∑ i, |V i j| ≤ s) :
    ∑ i, |∑ j, V i j * u j| ≤ s * ∑ j, |u j| := by
  calc
    _ ≤ ∑ i, ∑ j, |V i j| * |u j| := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [abs_mul] using Finset.abs_sum_le_sum_abs (fun j => V i j * u j) Finset.univ
    _ = ∑ j, (∑ i, |V i j|) * |u j| := by rw [Finset.sum_comm]; simp only [Finset.sum_mul]
    _ ≤ ∑ j, s * |u j| := Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hs j) (abs_nonneg _)
    _ = _ := by rw [Finset.mul_sum]

/-- An upper bound obtained by enumerating Bob's signs bounds the same classical
value in the row-sign convention of `GrothendieckLowerBound`. -/
theorem classicalUpper_of_transpose {n m : ℕ} (M : BellMatrix n m) (C : ℝ)
    (hC : ClassicalUpper (fun j i => M i j) C) : ClassicalUpper M C := by
  intro a ha
  let y (j : Fin m) := ∑ i, a i * M i j
  let b (j : Fin m) : ℝ := if 0 ≤ y j then 1 else -1
  have hb : IsSign b := by
    intro j
    dsimp only [b]
    split <;> norm_num
  have choose_sign (j : Fin m) : |y j| = b j * y j := by
    by_cases h : 0 ≤ y j
    · simp [b, h, abs_of_nonneg h]
    · simp [b, h, abs_of_neg (lt_of_not_ge h)]
  calc
    score M a = ∑ j, b j * y j := Finset.sum_congr rfl fun j _ => choose_sign j
    _ = ∑ i, a i * ∑ j, b j * M i j := by
      dsimp only [y]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    _ ≤ score (fun j i => M i j) b := by
      apply Finset.sum_le_sum
      intro i _
      calc
        _ ≤ |a i * ∑ j, b j * M i j| := le_abs_self _
        _ = _ := by rw [abs_mul, ha i, one_mul]
    _ ≤ C := hC b hb

/-- The archived Bob assignment attains the stated classical score on the 301-row matrix. -/
theorem orbit_attained :
    ∃ b, IsSign b ∧ score (fun j i => mOrbit i j) b = 641951269303647081416258863417 :=
  score_attained (fun j i => mOrbitZ i j) sOrbitZ sOrbit_signs _ attainedOrbit

/-- **Order three, 301 rows.** The classical upper bound is the exhaustive column-sign
computation in the supplement. The exact rank-three vector score is checked in Lean. -/
theorem order_three_orbit
    (hC : ClassicalUpper (fun j i => mOrbit i j) 641951269303647081416258863417) :
    GrothendieckLowerBound 3 (14397098471655953 / 10 ^ 16) := by
  have ha := ball_scaled_den aOrbitZ (10 ^ 40) (by norm_num) (by
    intro i
    convert aOrbit_ball i using 1
    norm_num)
  have hb := ball_scaled_den bOrbitZ (10 ^ 40) (by norm_num) (by
    intro j
    convert bOrbit_ball j using 1
    norm_num)
  simp only [Int.cast_pow, Int.cast_ofNat] at ha hb
  obtain ⟨u, v, hu, hv, hge⟩ := exists_unit_ge (by norm_num) mOrbit _ _ ha hb
  refine ⟨301, 321, mOrbit, 641951269303647081416258863417, by norm_num,
    classicalUpper_of_transpose mOrbit _ hC, u, v, hu, hv, lt_of_lt_of_le ?_ hge⟩
  have hobj := vectorObj_scaled mOrbitZ aOrbitZ bOrbitZ (10 ^ 40) (by norm_num)
  rw [show mOrbit = fun i j => (mOrbitZ i j : ℝ) from rfl, hobj, objectiveOrbit]
  norm_num

/-- **Order three.** If the explicit 81 × 321 matrix `m3` has classical value at most
`320975296`, then `K_G(3) > 1.43888070193021`. The vectors are checked in `Witness3.lean`;
the classical bound is the exhaustive search of `certificate-k3`. -/
theorem order_three (hC : ClassicalUpper m3 320975296) :
    GrothendieckLowerBound 3 (143888070193021 / 10 ^ 14) := by
  obtain ⟨u, v, hu, hv, hge⟩ := exists_unit_ge (by norm_num) m3
    (fun i k => (a3Z i k : ℝ) / 10 ^ 15) (fun j k => (b3Z j k : ℝ) / 10 ^ 15)
    (ball_scaled a3Z a3_ball) (ball_scaled b3Z b3_ball)
  refine ⟨81, 321, m3, 320975296, by norm_num, hC, u, v, hu, hv, lt_of_lt_of_le ?_ hge⟩
  have hobj := vectorObj_scaled m3Z a3Z b3Z (10 ^ 15) (by norm_num)
  rw [show m3 = fun i j => (m3Z i j : ℝ) from rfl, hobj, objective3]
  norm_num

/-- **Order three, 141 rows.** The split matrix gives a strict lower bound from its
classical upper bound, certified by the exhaustive search in `certificate-k3-split`. -/
theorem order_three_split (hC : ClassicalUpper mSplit 641951276514383746) :
    GrothendieckLowerBound 3 (14396139030752404 / 10 ^ 16) := by
  have ha := ball_scaled_den aSplitZ (10 ^ 36) (by norm_num) (by
    intro i
    convert aSplit_ball i using 1
    norm_num)
  have hb := ball_scaled_den bSplitZ (10 ^ 36) (by norm_num) (by
    intro j
    convert bSplit_ball j using 1
    norm_num)
  simp only [Int.cast_pow, Int.cast_ofNat] at ha hb
  obtain ⟨u, v, hu, hv, hge⟩ := exists_unit_ge (by norm_num) mSplit _ _ ha hb
  refine ⟨141, 321, mSplit, 641951276514383746, by norm_num, hC, u, v, hu, hv,
    lt_of_lt_of_le ?_ hge⟩
  have hobj := vectorObj_scaled mSplitZ aSplitZ bSplitZ (10 ^ 36) (by norm_num)
  rw [show mSplit = fun i j => (mSplitZ i j : ℝ) from rfl, hobj, objectiveSplit]
  norm_num

/-- **Orders five and six.** If the 80 × 269 matrix `m5` of Márton et al. has classical value
at most `919782264` (their Table 4), then `K_G(5), K_G(6) > 1.49936483533988`. The new vectors
are checked in `Witness5.lean`. -/
theorem order_five_six (hC : ClassicalUpper m5 919782264) :
    GrothendieckLowerBound 5 (149936483533988 / 10 ^ 14) ∧
      GrothendieckLowerBound 6 (149936483533988 / 10 ^ 14) := by
  have h5 : GrothendieckLowerBound 5 (149936483533988 / 10 ^ 14) := by
    obtain ⟨u, v, hu, hv, hge⟩ := exists_unit_ge (by norm_num) m5
      (fun i k => (a5Z i k : ℝ) / 10 ^ 15) (fun j k => (b5Z j k : ℝ) / 10 ^ 15)
      (ball_scaled a5Z a5_ball) (ball_scaled b5Z b5_ball)
    refine ⟨80, 269, m5, 919782264, by norm_num, hC, u, v, hu, hv, lt_of_lt_of_le ?_ hge⟩
    have hobj := vectorObj_scaled m5Z a5Z b5Z (10 ^ 15) (by norm_num)
    rw [show m5 = fun i j => (m5Z i j : ℝ) from rfl, hobj, objective5]
    norm_num
  exact ⟨h5, h5.mono (by norm_num)⟩

/-- The attaining signs: with the classical bounds the classical values are exactly
`320975296` and `919782264`. -/
theorem classical_attained :
    (∃ a, IsSign a ∧ score m3 a = 320975296) ∧ (∃ a, IsSign a ∧ score m5 a = 919782264) :=
  ⟨score_attained m3Z s3Z s3_signs _ attained3, score_attained m5Z s5Z s5_signs _ attained5⟩
-- DOCS_END_MAIN

end Lemmata.GrothendieckLowerBounds
