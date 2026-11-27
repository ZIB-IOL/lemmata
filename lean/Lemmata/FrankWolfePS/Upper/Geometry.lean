module

public import Lemmata.FrankWolfePS.Lower.Results
@[expose] public section

namespace Lemmata.FrankWolfePS.Upper
open scoped RealInnerProductSpace Classical
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- An arbitrary fixed exact linear minimization oracle. -/
structure LMO (C : Set E) where
  query : E → E
  mem : ∀ q, query q ∈ C
  least : ∀ q, ∀ z ∈ C, ⟪q, query q⟫ ≤ ⟪q, z⟫

noncomputable def clip (r : ℝ) (v : E) : E :=
  if ‖v‖ ≤ r then v else r • unit v

theorem norm_clip {r : ℝ} (hr : 0 ≤ r) (v : E) : ‖clip r v‖ ≤ r := by
  unfold clip
  split
  · assumption
  · next h =>
      have hv : v ≠ 0 := by intro e; simp [e, hr] at h
      simp [norm_smul, norm_unit hv, abs_of_nonneg hr]

theorem unscale_unit (v : E) : ‖v‖ • unit v = v := by
  by_cases h : v = 0
  · simp [h]
  · simp [unit, smul_smul, norm_ne_zero_iff.mpr h]

/-- Euclidean projection onto the radius-r ball, with the variational inequality. -/
theorem clip_vi {r : ℝ} (hr : 0 ≤ r) (v z : E) (hz : ‖z‖ ≤ r) :
    ⟪v - clip r v, z - clip r v⟫ ≤ 0 := by
  unfold clip
  split
  · simp
  · next h =>
      have hv : v ≠ 0 := by intro e; simp [e, hr] at h
      have e : v - r • unit v = (‖v‖ - r) • unit v := by rw [sub_smul, unscale_unit]
      rw [e, real_inner_smul_left, inner_sub_right, real_inner_smul_right,
        real_inner_self_eq_norm_sq, norm_unit hv]
      have H := real_inner_le_norm (unit v) z
      rw [norm_unit hv, one_mul] at H
      exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)

noncomputable def unwrap {C : Set E} (O : LMO C) (r : ℝ) (q : E) : E :=
  O.query q + r • unit q

theorem unwrap_spec {K : Set E} {r : ℝ} (hr : 0 < r) (O : LMO (Rounded K r))
    {q : E} (hq : q ≠ 0) : unwrap O r q ∈ K ∧ ∀ u ∈ K, ⟪q, unwrap O r q⟫ ≤ ⟪q, u⟫ := by
  have hnorm := norm_unit hq
  have hp : 0 < ‖q‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hq)
  have reverse (x y : E) : ⟪-unit q, x⟫ ≤ ⟪-unit q, y⟫ ↔ ⟪q, y⟫ ≤ ⟪q, x⟫ := by
    simp only [unit, inner_neg_left, real_inner_smul_left, neg_le_neg_iff]
    exact mul_le_mul_iff_right₀ hp
  have hs : Supports (Rounded K r) (O.query q) (-unit q) := by
    intro w hw; exact (reverse _ _).mpr (O.least q w hw)
  obtain ⟨u, hu, he, hmax⟩ := tangent_center hr (O.mem q) (by simpa using hnorm) hs
  have eq : unwrap O r q = u := by simp [unwrap, he, smul_neg]
  exact ⟨eq ▸ hu, by rw [eq]; exact fun v hv => (reverse _ _).mp (hmax v hv)⟩

/-- A zero direction uses the already recovered core anchor. -/
noncomputable def coreLMO {K : Set E} {r : ℝ} (hr : 0 < r)
    (O : LMO (Rounded K r)) (p : E) (hp : p ∈ K) : LMO K where
  query q := if q = 0 then p else unwrap O r q
  mem q := by split <;> first | exact hp | exact (unwrap_spec hr O (by assumption)).1
  least q v hv := by
    split <;> first | (subst q; simp) | exact (unwrap_spec hr O (by assumption)).2 v hv

theorem core_width {K : Set E} {r D : ℝ} (hr : 0 < r) (hD : 2 * r ≤ D)
    (width : ∀ x ∈ Rounded K r, ∀ y ∈ Rounded K r, ‖x - y‖ ≤ D)
    {u v : E} (hu : u ∈ K) (hv : v ∈ K) : ‖u - v‖ ≤ D - 2 * r := by
  by_cases e : u = v
  · simp [e]; linarith
  · let n := unit (u - v)
    have hn : ‖n‖ = 1 := norm_unit (sub_ne_zero.mpr e)
    have hn' : ‖-n‖ = 1 := by simpa using hn
    have h := width _ (ball_point hu hn hr.le) _ (ball_point hv hn' hr.le)
    have eq : (u + r • n) - (v + r • (-n)) = (‖u - v‖ + 2 * r) • n := by
      rw [add_smul, show ‖u - v‖ • n = u - v from unscale_unit _, smul_neg, show 2 * r = r +
          r by ring, add_smul]; abel
    rw [eq, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), hn, mul_one] at h
    linarith

def blend (t : ℝ) (x y : E) : E := (1 - t) • x + t • y

theorem blend_mem {K : Set E} (hK : Convex ℝ K) {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1)
    {x y : E} (hx : x ∈ K) (hy : y ∈ K) : blend t x y ∈ K :=
  hK hx hy (by linarith : 0 ≤ 1 - t) ht (by ring)

theorem blend_sub (t : ℝ) (x y : E) : blend t x y - x = t • (y - x) := by
  rw [blend, sub_smul, one_smul, smul_sub]; abel

theorem blend_diff (t : ℝ) (x y v : E) : blend t x y - blend t x v = t • (y - v) := by
  rw [blend, blend, smul_sub]; abel

end Lemmata.FrankWolfePS.Upper
