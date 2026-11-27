module

public import Lemmata.FrankWolfePS.Upper.Geometry
public import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
public import Mathlib.Topology.MetricSpace.HausdorffDistance

@[expose] public section

namespace Lemmata.FrankWolfePS.Upper
open scoped RealInnerProductSpace Pointwise Classical
open Metric
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]

def NormalBound (C : Set E) (r : ℝ) : Prop :=
  ∀ z ∈ C, ∀ y ∈ C, ∀ n m : E, ‖n‖ = 1 → ‖m‖ = 1 → Supports C z n → Supports C y m →
    r * ‖m - n‖ ≤ ‖y - z‖

omit [ProperSpace E] in
private theorem nearest_normal {C : Set E} (hc : IsCompact C) (hv : Convex ℝ C)
    (hne : C.Nonempty) {p : E} (hp : p ∉ C) :
    ∃ y ∈ C, ∃ m : E, ‖m‖ = 1 ∧ Supports C y m ∧
      p - y = (infDist p C) • m ∧ 0 < infDist p C := by
  obtain ⟨y, hy, hd⟩ := hc.exists_infDist_eq_dist hne p
  rw [dist_eq_norm] at hd
  have h0 : p - y ≠ 0 := sub_ne_zero.mpr (fun e => hp (e ▸ hy))
  have hmin : ‖p - y‖ = ⨅ w : C, ‖p - w‖ := by rw [← hd, infDist_eq_iInf]; simp only [dist_eq_norm]
  have hvi := (norm_eq_iInf_iff_real_inner_le_zero hv hy).mp hmin
  refine ⟨y, hy, unit (p - y), norm_unit h0, ?_,
      by rw [hd, unscale_unit], by rw [hd]; exact norm_pos_iff.mpr h0⟩
  intro v hv'
  have h := hvi v hv'
  simp only [unit, real_inner_smul_left, inner_sub_right] at h ⊢
  exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

omit [ProperSpace E] in
private theorem support_le_infDist {C : Set E} (hne : C.Nonempty) {y m : E} (hm : ‖m‖ = 1)
    (hs : Supports C y m) (x : E) : ⟪m, x - y⟫ ≤ infDist x C := by
  apply (le_infDist hne).mpr
  intro v hv
  have h := real_inner_le_norm m (x - v)
  rw [hm, one_mul, inner_sub_right] at h
  rw [dist_eq_norm, inner_sub_right]
  linarith [hs v hv]

/-- Converse rolling-ball theorem. Maximize distance to C on the alleged
protruding ball. Its farthest point and its projection have the same radial
normal, contradicting the pairwise normal estimate. -/
theorem rolling_of_normals {C : Set E} (hc : IsCompact C) (hv : Convex ℝ C)
    {r : ℝ} (hr : 0 < r) (regular : NormalBound C r) {z n : E}
    (hz : z ∈ C) (hn : ‖n‖ = 1) (hnz : Supports C z n) :
    closedBall (z - r • n) r ⊆ C := by
  let w := z - r • n
  have ne : C.Nonempty := ⟨z, hz⟩
  intro x hx
  by_contra hxc
  obtain ⟨p, hp, hmax⟩ := (isCompact_closedBall w r).exists_isMaxOn
    ⟨w, mem_closedBall_self hr.le⟩ (continuous_infDist_pt C).continuousOn
  have hxp : 0 < infDist x C :=
      (infDist_pos_iff_notMem_closure ne).mp (by simpa [hc.isClosed.closure_eq] using hxc)
  have hpc : p ∉ C := by intro h; have := hmax hx; simp [infDist_zero_of_mem h] at this; linarith
  obtain ⟨y, hy, m, hm, hs, he, hd⟩ := nearest_normal hc hv ne hpc
  have hup : ⟪m, p - y⟫ = infDist p C := by
    rw [he, real_inner_smul_right, real_inner_self_eq_norm_sq, hm]; ring
  have hball : Supports (Rounded {w} r) p m := by
    rintro v ⟨c, hc', hv'⟩
    obtain rfl : c = w := hc'
    have H := (support_le_infDist ne hm hs v).trans (hmax (show v ∈
        closedBall w r by simpa [mem_closedBall, dist_eq_norm] using hv'))
    change ⟪m, v - y⟫ ≤ infDist p C at H
    rw [← hup, inner_sub_right, inner_sub_right] at H
    linarith
  have hp' : p ∈ Rounded {w} r := ⟨w, rfl, by simpa [mem_closedBall, dist_eq_norm] using hp⟩
  obtain ⟨c, hc', hpball, _⟩ := tangent_center hr hp' hm hball
  have ec : c = w := hc'
  rw [ec] at hpball
  have e : r • (m - n) = (y - z) + (infDist p C) • m := by
    rw [smul_sub, ← he, hpball]; dsimp [w]; abel
  have H := regular z hz y hy n m hn hm hnz hs
  have H' : ‖r • (m - n)‖ ≤ ‖y - z‖ := by simpa [norm_smul, abs_of_pos hr] using H
  have sqH := pow_le_pow_left₀ (norm_nonneg _) H' 2
  rw [e, norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_pos hd, hm,
      mul_one] at sqH
  have hp0 : 0 ≤ ⟪y - z, m⟫ := by rw [real_inner_comm, inner_sub_right]; linarith [hs z hz]
  nlinarith [mul_nonneg hd.le hp0, sq_pos_of_pos hd]

/-- The inner parallel body of `C` at distance `r`: the points `a` with `a + B_r ⊆ C`. -/
def innerParallelBody (C : Set E) (r : ℝ) : Set E := {a | ∀ b : E, ‖b‖ ≤ r → a + b ∈ C}

omit [ProperSpace E] in
theorem erosion_compact_convex {C : Set E} (hc : IsCompact C) (hv : Convex ℝ C)
    {r : ℝ} (hr : 0 ≤ r) :
    IsCompact (innerParallelBody C r) ∧ Convex ℝ (innerParallelBody C r) := by
  have eq : innerParallelBody C r = ⋂ b : E, ⋂ (_ : ‖b‖ ≤ r), (fun a => a + b) ⁻¹' C := by
    ext a; simp [innerParallelBody]
  constructor
  · apply hc.of_isClosed_subset
    · rw [eq]; exact isClosed_iInter fun b => isClosed_iInter fun _ =>
        hc.isClosed.preimage (continuous_id.add continuous_const)
    · intro x hx; simpa using hx 0 (by simpa using hr)
  · intro x hx y hy a b ha hb hab v hvr
    have H := hv (hx v hvr) (hy v hvr) ha hb hab
    have eq' : a • (x + v) + b • (y + v) = a • x + b • y + v := by
      rw [smul_add, smul_add, show a • x + a • v + (b • y + b • v) = a • x + b • y +
          (a • v + b • v) by abel, ← add_smul, hab, one_smul]
    rwa [eq'] at H

private theorem support_in_rounded {C : Set E} (hc : IsCompact C) (hv : Convex ℝ C)
    {r : ℝ} (hr : 0 < r) (regular : NormalBound C r) {z n : E} (hz : z ∈ C)
    (hn : ‖n‖ = 1) (hs : Supports C z n) : z ∈ Rounded (innerParallelBody C r) r := by
  have ball := rolling_of_normals hc hv hr regular hz hn hs
  refine ⟨z - r • n, fun b hb => ball (by simpa [mem_closedBall, dist_eq_norm] using hb), ?_⟩
  simp [norm_smul, abs_of_pos hr, hn]

/-- The core is the concrete innerParallelBody. The argument never supplies it to the algorithm. -/
theorem parallel_of_normals {C : Set E} (hc : IsCompact C) (hv : Convex ℝ C) (hne : C.Nonempty)
    {r : ℝ} (hr : 0 < r) (regular : NormalBound C r) {e : E} (he : e ≠ 0) :
    C = Rounded (innerParallelBody C r) r := by
  let K := innerParallelBody C r
  have hk := erosion_compact_convex hc hv hr.le
  have addEq := rounded_eq_add K r
  have hrc : IsCompact (Rounded K r) := addEq ▸ hk.1.add (isCompact_closedBall _ _)
  have hrv : Convex ℝ (Rounded K r) := addEq ▸ hk.2.add (convex_closedBall _ _)
  have reaches (m : E) (hm : ‖m‖ = 1) : ∃ z ∈ Rounded K r, ∀ v ∈ C, ⟪m, v⟫ ≤ ⟪m, z⟫ := by
    obtain ⟨z, hz, hs⟩ := hc.exists_isMaxOn hne (show Continuous (fun v : E =>
        ⟪m, v⟫) from continuous_const.inner continuous_id).continuousOn
    exact ⟨z, support_in_rounded hc hv hr regular hz hm (fun _ h => hs h), fun _ h => hs h⟩
  have nr : (Rounded K r).Nonempty := by
    obtain ⟨z, hz, _⟩ := reaches (unit e) (norm_unit he); exact ⟨_, hz⟩
  ext x; constructor
  · intro hx
    by_contra h
    obtain ⟨y, hy, m, hm, hs, heq, hd⟩ := nearest_normal hrc hrv nr h
    obtain ⟨z, hz, hmax⟩ := reaches m hm
    have hh : ⟪m, x - y⟫ ≤ 0 := by rw [inner_sub_right]; linarith [hmax x hx, hs z hz]
    rw [heq, real_inner_smul_right, real_inner_self_eq_norm_sq, hm] at hh
    nlinarith
  · rintro ⟨a, ha, hd⟩
    simpa using ha (x - a) hd

/-- The diameter identity also covers a singleton core. -/
theorem parallel_diameter {K : Set E} (hk : IsCompact K) (ne : K.Nonempty)
    {r : ℝ} (hr : 0 < r) (e : E) (he : e ≠ 0) :
    Metric.diam (Rounded K r) = 2 * r + Metric.diam K := by
  have hc : IsCompact (Rounded K r) := by
    rw [rounded_eq_add]; exact hk.add (isCompact_closedBall _ _)
  obtain ⟨a, ha⟩ := ne
  let n := unit e
  have hn : ‖n‖ = 1 := norm_unit he
  have two : 2 * r ≤ Metric.diam (Rounded K r) := by
    have hn' : ‖-n‖ = 1 := by simpa using hn
    have H := dist_le_diam_of_mem hc.isBounded (ball_point ha hn hr.le) (ball_point ha hn' hr.le)
    have eq : (a + r • n) - (a + r • (-n)) = (2 * r) • n := by
      rw [show 2 * r = r + r by ring, add_smul, smul_neg]; abel
    rw [dist_eq_norm, eq, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), hn, mul_one] at H
    exact H
  apply le_antisymm
  · apply diam_le_of_forall_dist_le (by positivity)
    rintro x ⟨u, hu, hu'⟩ y ⟨v, hv, hv'⟩
    have uv := dist_le_diam_of_mem hk.isBounded hu hv
    have D := dist_triangle x u v
    have D' := dist_triangle x v y
    rw [← dist_eq_norm] at hu' hv'
    rw [dist_comm y v] at hv'
    linarith
  · have H : Metric.diam K ≤ Metric.diam (Rounded K r) - 2 * r := by
      apply diam_le_of_forall_dist_le (sub_nonneg.mpr two)
      intro u hu v hv
      rw [dist_eq_norm]
      exact core_width hr two (fun x hx y hy =>
          by rw [← dist_eq_norm]; exact dist_le_diam_of_mem hc.isBounded hx hy) hu hv
    linarith

end Lemmata.FrankWolfePS.Upper
