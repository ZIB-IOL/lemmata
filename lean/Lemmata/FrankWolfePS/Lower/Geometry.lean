module

public import Lemmata.FrankWolfePS.Lower.Objective
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

namespace Lemmata.FrankWolfePS
open scoped RealInnerProductSpace BigOperators
open Finset
section Hilbert
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def Rounded (K : Set E) (R : ℝ) : Set E := {z | ∃ u ∈ K, ‖z - u‖ ≤ R}

def Supports (K : Set E) (z n : E) : Prop := ∀ w ∈ K, ⟪n, w⟫ ≤ ⟪n, z⟫

theorem ball_point {K : Set E} {u n : E} {R : ℝ} (hu : u ∈ K)
    (hn : ‖n‖ = 1) (hR : 0 ≤ R) : u + R • n ∈ Rounded K R := by
  exact ⟨u, hu, by simp [norm_smul, hn, abs_of_nonneg hR]⟩

theorem tangent_center {K : Set E} {R : ℝ} {z n : E} (hR : 0 < R)
    (hz : z ∈ Rounded K R) (hn : ‖n‖ = 1) (hs : Supports (Rounded K R) z n) :
    ∃ u ∈ K, z = u + R • n ∧ Supports K u n := by
  obtain ⟨u, hu, hzu⟩ := hz
  have h1 := hs _ (ball_point hu hn hR.le)
  rw [inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hn] at h1
  have hin : R ≤ ⟪n, z - u⟫ := by rw [inner_sub_right]; linarith
  have hz2 := pow_le_pow_left₀ (norm_nonneg _) hzu 2
  have h2 : ‖z - u - R • n‖ ^ 2 ≤ 0 := by
    rw [norm_sub_sq_real, real_inner_smul_right, real_inner_comm n (z - u), norm_smul,
      Real.norm_eq_abs, abs_of_pos hR, hn]
    nlinarith [mul_le_mul_of_nonneg_left hin hR.le]
  have hz0 : ‖z - u - R • n‖ = 0 := by nlinarith [_root_.sq_nonneg ‖z - u - R • n‖]
  have he := sub_eq_zero.mp (norm_eq_zero.mp hz0)
  have he' : z = u + R • n := by rw [sub_eq_iff_eq_add.mp he, add_comm]
  refine ⟨u, hu, he', ?_⟩
  intro v hv
  have H := hs _ (ball_point hv hn hR.le)
  rw [he', inner_add_right, inner_add_right] at H
  linarith

/-- A radius R parallel body has 1/R-Lipschitz unit outward normals.
The quantifiers include all support points, and even allow an arbitrary core. -/
theorem rounded_lipschitz_normals {K : Set E} {R : ℝ} (hR : 0 < R)
    {z w n m : E} (hz : z ∈ Rounded K R) (hw : w ∈ Rounded K R)
    (hn : ‖n‖ = 1) (hm : ‖m‖ = 1)
    (hs : Supports (Rounded K R) z n) (ht : Supports (Rounded K R) w m) :
    ‖n - m‖ ≤ (1 / R) * ‖z - w‖ := by
  obtain ⟨u, hu, e1, ns⟩ := tangent_center hR hz hn hs
  obtain ⟨v, hv, e2, ms⟩ := tangent_center hR hw hm ht
  have mono : 0 ≤ ⟪n - m, u - v⟫ := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right]; linarith [ns _ hv, ms _ hu]
  have eq : z - w = (u - v) + R • (n - m) := by rw [e1, e2, smul_sub]; abel
  have co : R * ‖n - m‖ ^ 2 ≤ ⟪n - m, z - w⟫ := by
    rw [eq, inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq]; linarith
  have ch := co.trans (real_inner_le_norm (n - m) (z - w))
  by_cases hn0 : ‖n - m‖ = 0
  · rw [hn0]; positivity
  · have pos := lt_of_le_of_ne (norm_nonneg (n - m)) (Ne.symm hn0)
    have h' : ‖n - m‖ * R ≤ ‖z - w‖ := by
      apply le_of_mul_le_mul_left (a := ‖n - m‖) _ pos
      nlinarith
    rw [one_div_mul_eq_div]
    exact (le_div_iff₀ hR).mpr h'

noncomputable def unit (q : E) := ‖q‖⁻¹ • q

theorem norm_unit {q : E} (hq : q ≠ 0) : ‖unit q‖ = 1 := by
  simp [unit, norm_smul, norm_ne_zero_iff.mpr hq]

theorem rounded_minimizer {K : Set E} {R : ℝ} {q u : E} (hq : q ≠ 0)
    (hR : 0 < R) (hu : u ∈ K) (hm : ∀ v ∈ K, ⟪q, u⟫ ≤ ⟪q, v⟫) :
    u - R • unit q ∈ Rounded K R ∧
    ∀ z ∈ Rounded K R, ⟪q, u - R • unit q⟫ ≤ ⟪q, z⟫ := by
  refine ⟨⟨u, hu, ?_⟩, ?_⟩
  · simp [sub_sub_cancel_left, norm_smul, norm_unit hq, abs_of_pos hR]
  · rintro z ⟨v, hv, hz⟩
    have a := real_inner_le_norm q (v - z)
    rw [inner_sub_right, norm_sub_rev] at a
    have b := mul_le_mul_of_nonneg_left hz (norm_nonneg q)
    have hq' : ‖q‖ ≠ 0 := norm_ne_zero_iff.mpr hq
    have qu : ⟪q, unit q⟫ = ‖q‖ := by
      rw [unit, real_inner_smul_right, real_inner_self_eq_norm_sq]
      field_simp
    rw [inner_sub_right, real_inner_smul_right, qu]
    linarith [hm v hv]

end Hilbert

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
abbrev Ambient (ι : Type*) := EuclideanSpace ℝ (Option ι)

noncomputable def embed (z : Pt ι) : Ambient ι := WithLp.toLp 2 (fun
  | none => z.2
  | some i => z.1 i)

/-- The coordinates of an ambient point: horizontal part and height. -/
def coords (v : Ambient ι) : Pt ι := (fun i => v (some i), v none)

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem coords_embed (z : Pt ι) : coords (embed z) = z := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem embed_coords (v : Ambient ι) : embed (coords v) = v := by
  ext i
  cases i <;> rfl

def core (R : ℝ) (I : Finset ι) : Set (Ambient ι) :=
  {v | ∃ u, Base I u ∧ v = embed (u, R)}

omit [DecidableEq ι] in
theorem embed_dist_sq (z w : Pt ι) :
    ‖embed z - embed w‖ ^ 2 = sq (fun i => z.1 i - w.1 i) + (z.2 - w.2) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_option]
  simp [embed, sq, Real.norm_eq_abs, sq_abs, add_comm]

omit [DecidableEq ι] in
theorem feasible_iff_rounded {R : ℝ} (hR : 0 < R) (I : Finset ι) (z : Pt ι) :
    Feasible R I z ↔ embed z ∈ Rounded (core R I) R := by
  constructor
  · rintro ⟨u, hu, hd⟩
    refine ⟨embed (u, R), ⟨u, hu, rfl⟩, ?_⟩
    rw [← embed_dist_sq z (u, R)] at hd
    nlinarith [norm_nonneg (embed z - embed (u, R))]
  · rintro ⟨v, ⟨u, hu, rfl⟩, hd⟩
    refine ⟨u, hu, ?_⟩
    rw [← embed_dist_sq z (u, R)]
    exact pow_le_pow_left₀ (norm_nonneg _) hd 2

end Lemmata.FrankWolfePS
