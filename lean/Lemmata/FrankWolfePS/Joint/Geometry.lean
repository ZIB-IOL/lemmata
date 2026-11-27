module
public import Lemmata.FrankWolfePS.Upper.Main
@[expose] public section
namespace Lemmata.FrankWolfePS.Joint
open Upper
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The ball of radius R tangent at any supporting point contains the entire body. -/
def OuterBall (C : Set E) (R : ℝ) : Prop :=
  ∀ s ∈ C, ∀ n : E, ‖n‖ = 1 → Supports C s n → ∀ a ∈ C, ‖a - (s - R • n)‖ ≤ R

/-- Every ball of radius r about a core point is contained in the same
outer tangent ball. Extending its radial segment removes r from the radius. -/
theorem core_outer {K : Set E} {r R : ℝ} (hr : 0 ≤ r) (hR : r ≤ R)
    (outer : OuterBall (Rounded K r) R) : OuterBall K (R - r) := by
  intro s hs n hn sup a ha
  let c := s - (R - r) • n
  have ctr : s + r • n - R • n = c := by dsimp [c]; rw [sub_smul]; abel
  have supp : Supports (Rounded K r) (s + r • n) n := by
    rintro z ⟨v, hv, hd⟩
    have b := real_inner_le_norm n (z - v)
    rw [hn, one_mul, inner_sub_right] at b
    rw [inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hn]
    linarith [sup v hv]
  change ‖a - c‖ ≤ R - r
  by_cases e : a - c = 0
  · rw [e, norm_zero]; linarith
  · let m := unit (a - c)
    have hm : ‖m‖ = 1 := norm_unit e
    have H := outer _ (ball_point hs hn hr) n hn supp _ (ball_point ha hm hr)
    rw [ctr, show a + r • m - c =
        (‖a - c‖ + r) • m by rw [add_smul, show ‖a - c‖ • m = a - c from unscale_unit _]; abel,
      norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), hm, mul_one] at H
    linarith

theorem minimizer_support {K : Set E} {q s : E}
    (least : ∀ v ∈ K, ⟪q, s⟫ ≤ ⟪q, v⟫) : Supports K s (-unit q) := by
  intro v hv
  simp only [unit, inner_neg_left, real_inner_smul_left, neg_le_neg_iff]
  exact mul_le_mul_of_nonneg_left (least v hv) (by positivity)

/-- Squaring the tangent ball gives the precise quadratic support inequality. -/
theorem outer_gap {K : Set E} {h : ℝ} (hh : 0 ≤ h) (outer : OuterBall K h)
    {a s q : E} (ha : a ∈ K) (hs : s ∈ K) (hq : q ≠ 0)
    (least : ∀ v ∈ K, ⟪q, s⟫ ≤ ⟪q, v⟫) :
    ‖q‖ * ‖s - a‖ ^ 2 ≤ 2 * h * ⟪q, a - s⟫ := by
  let m := unit q
  have hm : ‖m‖ = 1 := norm_unit hq
  have H := outer s hs (-m) (by simpa using hm) (minimizer_support least) a ha
  rw [show a - (s - h • (-m)) = (a - s) - h • m by rw [smul_neg]; abel] at H
  have S := pow_le_pow_left₀ (norm_nonneg _) H 2
  rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg hh, hm,
    real_inner_comm m (a - s)] at S
  have G : ⟪q, a - s⟫ = ‖q‖ * ⟪m, a - s⟫ := by
    rw [← real_inner_smul_left, show ‖q‖ • m = q from unscale_unit _]
  rw [G, norm_sub_rev s a]
  nlinarith only [mul_le_mul_of_nonneg_left S (norm_nonneg q)]

theorem core_singleton {K : Set E} (outer : OuterBall K 0) {q s : E} (hs : s ∈ K) (hq : q ≠ 0)
    (least : ∀ v ∈ K, ⟪q, s⟫ ≤ ⟪q, v⟫) : ∀ a ∈ K, a = s := by
  intro a ha
  have H := outer s hs (-unit q) (by simp [norm_unit hq]) (minimizer_support least) a ha
  exact sub_eq_zero.mp (by simpa using H)

end Lemmata.FrankWolfePS.Joint
