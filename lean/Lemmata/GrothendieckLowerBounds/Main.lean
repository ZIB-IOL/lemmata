module

public import Lemmata.GrothendieckLowerBounds.Statement
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

-- DOCS_BEGIN_MAIN
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

/-- The exact numerical implication; the witness and classical bound remain inputs. -/
theorem order_three_bound_from_certificate (K q c : ℝ)
    (hK : 0 ≤ K) (hc : c ≤ 320975296)
    (hq : (461845159210737970564046146266219485493 : ℝ) / 10^30 ≤ q)
    (hgroth : q ≤ K * c) :
    (143888070193021 : ℝ) / 10^14 < K := by
  have h := hq.trans (hgroth.trans (mul_le_mul_of_nonneg_left hc hK))
  norm_num at h ⊢
  linarith

/-- The order-five implication and its transfer to any larger constant. -/
theorem orders_five_six_bound_from_certificate (K5 K6 q c : ℝ)
    (hK : 0 ≤ K5) (hmono : K5 ≤ K6) (hc : c ≤ 919782264)
    (hq : (1379089182810903048332452323838491520594 : ℝ) / 10^30 ≤ q)
    (hgroth : q ≤ K5 * c) :
    (149936483533988 : ℝ) / 10^14 < K5 ∧
    (149936483533988 : ℝ) / 10^14 < K6 := by
  have h := hq.trans (hgroth.trans (mul_le_mul_of_nonneg_left hc hK))
  have h5 : (149936483533988 : ℝ) / 10^14 < K5 := by
    norm_num at h ⊢
    linarith
  exact ⟨h5, h5.trans_le hmono⟩

/-- A ceiling for one fixed matrix, conditional on its objective upper bound.
This does not give an upper bound on a Grothendieck constant. -/
theorem fixed_matrix_ratio_ceiling (Q c : ℝ)
    (hc : (919782264 : ℝ) ≤ c)
    (hQ : Q ≤ (689544591405532440504120517535361 : ℝ) /
      500000000000000000000000) :
    Q / c < (149936483534006 : ℝ) / 10^14 := by
  have hpos : 0 < c := by linarith
  apply (div_lt_iff₀ hpos).2
  linarith
-- DOCS_END_MAIN

end Lemmata.GrothendieckLowerBounds
