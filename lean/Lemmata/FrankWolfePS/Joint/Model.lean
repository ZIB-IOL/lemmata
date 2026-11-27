module
public import Lemmata.FrankWolfePS.Joint.Geometry
public import Lemmata.FrankWolfePS.Upper.LineSearch
@[expose] public section
namespace Lemmata.FrankWolfePS.Joint
open Upper
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def rateShare (r h : ℝ) := min 1 (r / (2 * h)) / 2

theorem share_spec {r h : ℝ} (hr : 0 < r) (hh : 0 < h) :
    0 < rateShare r h ∧ rateShare r h ≤ 1 / 2 ∧ 4 * h * rateShare r h ≤ r := by
  let t := min 1 (r / (2 * h))
  have ht : 0 < t := lt_min (by norm_num) (by positivity)
  have h1 : t ≤ 1 := min_le_left _ _
  have h2 := (le_div_iff₀ (show 0 < 2 * h by positivity)).mp
    (show t ≤ r / (2 * h) from min_le_right _ _)
  change 0 < t / 2 ∧ t / 2 ≤ 1 / 2 ∧ 4 * h * (t / 2) ≤ r
  exact ⟨by positivity, by linarith, by linarith⟩

/-- Exact scalar line search for half squared distance after the one core reply. -/
noncomputable def coreMove (u a s : E) := blend (lineFraction ⟪a - u, a - s⟫ (‖s - a‖ ^ 2)) a s

theorem core_move_model {K : Set E} (conv : Convex ℝ K) {r h c : ℝ}
    (hr : 0 ≤ r) (hh : 0 < h) (outer : OuterBall K h)
    (hc : 0 ≤ c) (hc1 : c ≤ 1 / 2) (size : 4 * h * c ≤ r)
    {a u s : E} (ha : a ∈ K) (hs : s ∈ K) (far : r < ‖a - u‖)
    (least : ∀ v ∈ K, ⟪a - u, s⟫ ≤ ⟪a - u, v⟫) :
    coreMove u a s ∈ K ∧ ∀ v ∈ K, ‖coreMove u a s - u‖ ^ 2 ≤ (1 - c) * ‖a - u‖ ^ 2 +
        c * ‖v - u‖ ^ 2 := by
  let q := a - u
  let G := ⟪q, a - s⟫
  let H := ‖s - a‖ ^ 2
  have g0 : 0 ≤ G := by dsimp [G, q]; rw [inner_sub_right]; exact sub_nonneg.mpr (least a ha)
  have h0 : 0 ≤ H := _root_.sq_nonneg _
  have q0 : q ≠ 0 := norm_pos_iff.mp (hr.trans_lt far)
  have gap := outer_gap hh.le outer ha hs q0 least
  change ‖q‖ * H ≤ 2 * h * G at gap
  have curv : 2 * c * H ≤ G := by
    apply le_of_mul_le_mul_left (a := 2 * h) _ (by positivity)
    nlinarith only [gap, mul_le_mul_of_nonneg_right (size.trans far.le) h0]
  let t := lineFraction G H
  obtain ⟨t0, t1, best⟩ := lineFraction_spec g0 h0
  have pred := best (2 * c) (by positivity) (by linarith)
  have dec : -t * G + H / 2 * t ^ 2 ≤ -c * G := by
    nlinarith only [pred, mul_le_mul_of_nonneg_left curv hc]
  have step := iso_taylor 1 u a (blend t a s)
  rw [blend_sub, real_inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg t0] at step
  have neg : ⟪a - u, s - a⟫ = -G := by dsimp [G, q]; simp only [inner_sub_right]; ring
  simp only [isoGrad, one_smul, neg, iso] at step
  refine ⟨blend_mem conv t0 t1 ha hs, ?_⟩
  intro v hv
  have quad := iso_taylor 1 u a v
  simp only [isoGrad, one_smul, iso, inner_sub_right] at quad
  have dual : ‖a - u‖ ^ 2 - ‖v - u‖ ^ 2 ≤ 2 * G := by
    dsimp [G, q]; rw [inner_sub_right]
    nlinarith only [quad, least v hv, _root_.sq_nonneg ‖v - a‖]
  change ‖blend t a s - u‖ ^ 2 ≤ _
  change - t * G + ‖s - a‖ ^ 2 / 2 * t ^ 2 ≤ -c * G at dec
  nlinarith only [step, dec, mul_le_mul_of_nonneg_left dual hc]

theorem lift_distance {r : ℝ} (hr : 0 ≤ r) (u a : E) :
    ‖liftCore r u a - u‖ = max 0 (‖a - u‖ - r) := by
  unfold liftCore clip
  rw [norm_sub_rev u a]
  split
  · next h =>
      rw [show a + (u - a) - u = 0 by abel, norm_zero, max_eq_left (sub_nonpos.mpr h)]
  · next h =>
      have ne : u - a ≠ 0 := by intro e; apply h; rw [← norm_sub_rev, e, norm_zero]; exact hr
      have hm := norm_unit ne
      have eq : a + r • unit (u - a) - u = -((‖a - u‖ - r) • unit (u - a)) := by
        rw [sub_smul, ← norm_sub_rev u a, unscale_unit]; abel
      rw [eq, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr (lt_of_not_ge h)),
        hm, mul_one, max_eq_right (sub_nonneg.mpr (lt_of_not_ge h).le)]

/-- A supporting affine function in squared distance. This proves the
ball-envelope transfer without any differentiation at the clipping threshold. -/
theorem radius_tangent {r t A B : ℝ} (hr : 0 ≤ r) (ht : r < t) (ha : 0 ≤ A)
    (near : A ≤ B + r) :
    (t - r) * A ^ 2 - t * r * (t - r) ≤ t * B ^ 2 := by
  have e := pow_le_pow_left₀ ha near 2
  nlinarith only [mul_le_mul_of_nonneg_left e (sub_nonneg.mpr ht.le),
    mul_nonneg hr (_root_.sq_nonneg (B - (t - r)))]

theorem lift_contraction {r c : ℝ} (hr : 0 ≤ r) (hc : 0 ≤ c) (hc1 : c ≤ 1)
    {a v a' u x z : E} (hx : ‖x - a‖ ≤ r) (hz : ‖z - v‖ ≤ r)
    (step : ‖a' - u‖ ^ 2 ≤ (1 - c) * ‖a - u‖ ^ 2 + c * ‖v - u‖ ^ 2) :
    ‖liftCore r u a' - u‖ ^ 2 ≤ (1 - c) * ‖x - u‖ ^ 2 + c * ‖z - u‖ ^ 2 := by
  rw [lift_distance hr]
  let t := ‖a' - u‖
  by_cases h : t ≤ r
  · rw [max_eq_left (sub_nonpos.mpr h), zero_pow (by decide : 2 ≠ 0)]
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr hc1) (_root_.sq_nonneg _))
      (mul_nonneg hc (_root_.sq_nonneg _))
  · have ht := lt_of_not_ge h
    rw [max_eq_right (sub_nonneg.mpr ht.le)]
    have triangle (a x : E) (hax : ‖x - a‖ ≤ r) : ‖a - u‖ ≤ ‖x - u‖ + r := by
      have H : ‖a - u‖ ≤ ‖a - x‖ + ‖x - u‖ := by simpa [dist_eq_norm] using dist_triangle a x u
      rw [norm_sub_rev a x] at H
      linarith
    have A := radius_tangent hr ht (norm_nonneg _) (triangle a x hx)
    have B := radius_tangent hr ht (norm_nonneg _) (triangle v z hz)
    apply le_of_mul_le_mul_left (a := t) _ (hr.trans_lt ht)
    change t * (t - r) ^ 2 ≤ _
    change t ^ 2 ≤ _ at step
    nlinarith only [mul_le_mul_of_nonneg_left step (sub_nonneg.mpr ht.le),
      mul_le_mul_of_nonneg_left A (sub_nonneg.mpr hc1), mul_le_mul_of_nonneg_left B hc]

end Lemmata.FrankWolfePS.Joint
