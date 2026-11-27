module
public import Lemmata.FrankWolfePS.Unique.Geometry
@[expose] public section
namespace Lemmata.FrankWolfePS.Unique
open Finset
open scoped BigOperators RealInnerProductSpace
variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def MinAt (C : Set E) (p x : E) := x ∈ C ∧ ∀ y ∈ C, ⟪p, x⟫ ≤ ⟪p, y⟫
noncomputable def loss (v : ι → E) (s : ℝ) (p : E) (u : ι → ℝ) := ⟪p, center v u⟫ + s * sq u
noncomputable def edge (v : ι → E) (s : ℝ) (p : E) (u : ι → ℝ) := center v u - radius s u • p
noncomputable def point (v : ι → E) (s : ℝ) (p : E) (u : ι → ℝ) := edge v s p u - p

omit [DecidableEq ι] in
theorem edge_mem (v : ι → E) {s : ℝ} (hs : 0 ≤ s) {I : Finset ι} {u : ι → ℝ}
    (hu : Base I u) {p : E} (hp : ‖p‖ = 1) : edge v s p u ∈ Core v s I := by
  refine ⟨u, hu, ?_⟩
  simp [edge, sub_sub_cancel_left, norm_smul, hp, abs_of_nonneg (radius_nonneg hu hs)]

omit [DecidableEq ι] in
theorem edge_value (v : ι → E) (s : ℝ) {p : E} (hp : ‖p‖ = 1) (u : ι → ℝ) :
    ⟪p, edge v s p u⟫ = loss v s p u - s := by
  simp [edge, loss, radius, inner_sub_right, real_inner_smul_right, 
      hp]; ring

theorem ball_eq {z c p : E} {r : ℝ} (hr : 0 ≤ r) (hp : ‖p‖ = 1) (h : ‖z - c‖ ≤ r)
    (hmin : ⟪p, z⟫ ≤ ⟪p, c - r • p⟫) : z = c - r • p := by
  rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hp] at hmin
  have val : ⟪z - c, p⟫ ≤ -r := by rw [real_inner_comm, inner_sub_right]; linarith
  have hn := pow_le_pow_left₀ (norm_nonneg _) h 2
  have he : ‖(z - c) + r • p‖ ^ 2 ≤ 0 := by
    rw [norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr, hp]
    nlinarith [mul_le_mul_of_nonneg_left val hr]
  have hz : (z - c) + r • p = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg ((z - c) + r • p)])
  abel_nf at hz ⊢
  exact sub_eq_zero.mp (by convert hz using 1; abel)

omit [DecidableEq ι] in
theorem min_rep {v : ι → E} {s : ℝ} (hs : 0 ≤ s) {I : Finset ι} {p x : E}
    (hp : ‖p‖ = 1) (h : MinAt (Body v s I) p x) :
    ∃ u, Base I u ∧ x = point v s p u ∧ ∀ w, Base I w → loss v s p u ≤ loss v s p w := by
  have hn : ‖-p‖ = 1 := by simpa using hp
  have supp : Supports (Body v s I) x (-p) := by intro y hy; simp [inner_neg_left, h.2 y hy]
  obtain ⟨z, hz, ex, mn⟩ := tangent_center (by norm_num : (0 : ℝ) < 1) h.1 hn supp
  obtain ⟨u, hu, hd⟩ := hz
  have mi (w) (hw : Base I w) : ⟪p, z⟫ ≤ ⟪p, edge v s p w⟫ := by
    simpa using mn _ (edge_mem v hs hw hp)
  have ez := ball_eq (radius_nonneg hu hs) hp hd (mi u hu)
  refine ⟨u, hu, ?_, fun w hw => ?_⟩
  · simpa [point, edge, ez, sub_eq_add_neg] using ex
  · change z = edge v s p u at ez
    have H := mi w hw
    rw [ez, edge_value v s hp, edge_value v s hp] at H; linarith

omit [DecidableEq ι] in
theorem sq_diff_pos {u w : ι → ℝ} (h : u ≠ w) : 0 < sq (fun i => u i - w i) := by
  classical
  obtain ⟨i, hi⟩ := Function.ne_iff.mp h
  have H : (u i - w i) ^ 2 ≤ sq (fun j => u j - w j) :=
    single_le_sum (f := fun j => (u j - w j) ^ 2) (fun _ _ => _root_.sq_nonneg _) (mem_univ i)
  exact (sq_pos_of_ne_zero (sub_ne_zero.mpr hi)).trans_le H

omit [DecidableEq ι] in
theorem weights_unique {v : ι → E} {s : ℝ} (hs : 0 < s) {I : Finset ι} {p : E}
    {u w : ι → ℝ} (hu : Base I u) (hw : Base I w)
    (fu : ∀ t, Base I t → loss v s p u ≤ loss v s p t)
    (fw : ∀ t, Base I t → loss v s p w ≤ loss v s p t) : u = w := by
  by_contra ne
  have half : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hb := mix_base hu hw half half (by norm_num)
  have H := fu _ hb
  have H' := fw _ hu
  simp only [loss, center_mix, inner_add_right, real_inner_smul_right,
      sq_mix u w (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)] at H
  unfold loss at H'
  nlinarith [mul_pos hs (sq_diff_pos ne)]

omit [DecidableEq ι] in
theorem min_unique {v : ι → E} {s : ℝ} (hs : 0 < s) {I : Finset ι} {p x y : E}
    (hp : ‖p‖ = 1) (hx : MinAt (Body v s I) p x) (hy : MinAt (Body v s I) p y) : x = y := by
  obtain ⟨u, hu, ex, mu⟩ := min_rep hs.le hp hx
  obtain ⟨w, hw, ey, mw⟩ := min_rep hs.le hp hy
  rw [ex, ey, weights_unique hs hu hw mu mw]

theorem normalize_min {C : Set E} {p x : E} (hp : p ≠ 0) :
    MinAt C (unit p) x ↔ MinAt C p x := by
  have h := inv_pos.mpr (norm_pos_iff.mpr hp)
  simp only [MinAt, unit, real_inner_smul_left, mul_le_mul_iff_right₀ h]

noncomputable def reply (C : Set E) (start p : E) : E := by
  classical exact if p = 0 then start else
    if h : ∃ x, MinAt C p x then h.choose else start

theorem reply_min {C : Set E} (hc : IsCompact C) {start : E} (hstart : start ∈ C) (p : E) :
    MinAt C p (reply C start p) := by
  classical
  by_cases hp : p = 0
  · subst p; simp [reply, MinAt, hstart]
  · obtain ⟨x, hx, hm⟩ := hc.exists_isMinOn ⟨_, hstart⟩ (show Continuous (fun z : E =>
      ⟪p, z⟫) from continuous_const.inner continuous_id).continuousOn
    have ne : ∃ x, MinAt C p x := ⟨x, hx, fun _ hy => hm hy⟩
    simpa [reply, hp, ne] using ne.choose_spec

end Lemmata.FrankWolfePS.Unique
