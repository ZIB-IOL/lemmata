module

public import Lemmata.FrankWolfePS.Unique.Local
public import Lemmata.FrankWolfePS.Unique.Grid

@[expose] public section

/-!
# The base family at simplex scale `A`, and stability of the jittered family

The base body `Old A I` is the hard body with simplex scale `A` and rounding radius one: the
simplex `{(A u, 1) : u ∈ Δ_I}` plus the closed unit ball. The jittered body `Body v s I` moves
each vertex by at most `η` and adds a bulge of radius at most `s`; the two bodies are within
`η + s` of each other in both directions (`near_old`, `near_new`). The public repair pulls a
point that is close to the base body into it (`repair_mem`).
-/

namespace Lemmata.FrankWolfePS.Unique
open Finset
open scoped BigOperators RealInnerProductSpace
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The unperturbed vertex `(A e_i, 1)`. -/
noncomputable def baseV (A : ℝ) (i : ι) : Ambient ι := embed (A • atom i, 1)

/-- The public start point `(A e_a, 0)`, the lowest point of the anchor's unit ball. -/
noncomputable def start (A : ℝ) (a : ι) : Ambient ι := embed (A • atom a, 0)

/-- The base body: the hard body with simplex scale `A` and rounding radius one. -/
abbrev Old (A : ℝ) (I : Finset ι) : Set (Ambient ι) := physicalBody A 1 I

/-- The tilt of the objective. -/
noncomputable def tilt : Ambient ι := embed (fun _ => 0, 32)

/-- The objective `‖x‖² / 2 + 32 x_vert` (the hard objective for `L = 1`, `r = 1`). -/
noncomputable def cost (x : Ambient ι) := quadratic 1 tilt x

/-- The optimal value of `cost` on a set. -/
noncomputable def valC (C : Set (Ambient ι)) := sInf (cost '' C)

omit [Fintype ι] [DecidableEq ι] in
theorem smul_atom_pt (A : ℝ) (u : ι → ℝ) (hA : A ≠ 0) :
    scalePt A ((u, 1 / A) : Pt ι) = (A • u, 1) := by
  ext i <;> simp [scalePt, hA]

omit [DecidableEq ι] in
/-- Membership in the base body. -/
theorem mem_old {A : ℝ} (hA : 0 < A) (I : Finset ι) (x : Ambient ι) :
    x ∈ Old A I ↔ ∃ u, Base I u ∧ ‖x - embed (A • u, 1)‖ ≤ 1 := by
  rw [Old, physical_parallel hA]
  constructor
  · rintro ⟨_, ⟨w, ⟨u, hu, rfl⟩, rfl⟩, hx⟩
    refine ⟨u, hu, ?_⟩
    rwa [← smul_atom_pt A u hA.ne', scale_embed]
  · rintro ⟨u, hu, hx⟩
    refine ⟨embed (A • u, 1), ⟨embed (u, 1 / A), ⟨u, hu, rfl⟩, ?_⟩, hx⟩
    show A • embed (u, 1 / A) = embed (A • u, 1)
    rw [← scale_embed, smul_atom_pt A u hA.ne']

omit [DecidableEq ι] in
theorem base_mem {A : ℝ} (hA : 0 < A) {I : Finset ι} {u : ι → ℝ} (hu : Base I u) :
    embed (A • u, 1) ∈ Old A I :=
  (mem_old hA I _).mpr ⟨u, hu, by simp⟩

theorem base_center {A : ℝ} {I : Finset ι} {u : ι → ℝ} (hu : Base I u) :
    center (baseV A) u = embed (A • u, 1) := by
  classical
  ext c; cases c with
  | none => simpa [center, baseV, embed, WithLp.ofLp_sum, Finset.sum_apply] using base_total hu
  | some j =>
    simp [center, baseV, embed, atom, WithLp.ofLp_sum, Finset.sum_apply, mul_ite, mul_comm]

theorem center_perturb {A : ℝ} {I : Finset ι} {u : ι → ℝ} (hu : Base I u) {v : ι → Ambient ι}
    {η : ℝ} (near : ∀ j, ‖v j - baseV A j‖ ≤ η) : ‖center v u - embed (A • u, 1)‖ ≤ η := by
  rw [← base_center hu]
  have eq : center v u - center (baseV A) u = ∑ i, u i • (v i - baseV A i) := by
    simp [center, smul_sub, sum_sub_distrib]
  rw [eq]
  calc
    _ ≤ ∑ i, ‖u i • (v i - baseV A i)‖ := norm_sum_le _ _
    _ ≤ ∑ i, u i * η := sum_le_sum fun i _ => by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hu.1 i)]
      exact mul_le_mul_of_nonneg_left (near i) (hu.1 i)
    _ = _ := by rw [← sum_mul, base_total hu, one_mul]

/-- Every point of the jittered body is within `η + s` of the base body. -/
theorem near_old {A : ℝ} (hA : 0 < A) {I : Finset ι} {v : ι → Ambient ι} {η s : ℝ} (hs : 0 ≤ s)
    (near : ∀ j, ‖v j - baseV A j‖ ≤ η) {x} (hx : x ∈ Body v s I) :
    ∃ w ∈ Old A I, ‖x - w‖ ≤ η + s := by
  rcases hx with ⟨z, ⟨u, hu, hz⟩, hx⟩
  refine ⟨embed (A • u, 1) + (x - z), (mem_old hA I _).mpr ⟨u, hu, by simpa using hx⟩, ?_⟩
  have h := norm_add_le (z - center v u) (center v u - embed (A • u, 1))
  have r : radius s u ≤ s := by unfold radius; nlinarith [mul_nonneg hs (sq_nonneg u)]
  rw [show x - (embed (A • u, 1) + (x - z)) = (z - center v u) + (center v u - embed (A • u, 1))
    by abel]
  linarith [center_perturb hu near]

/-- Every point of the base body is within `η` of the jittered body. -/
theorem near_new {A : ℝ} (hA : 0 < A) {I : Finset ι} {v : ι → Ambient ι} {η s : ℝ} (hs : 0 ≤ s)
    (near : ∀ j, ‖v j - baseV A j‖ ≤ η) {x} (hx : x ∈ Old A I) :
    ∃ w ∈ Body v s I, ‖w - x‖ ≤ η := by
  obtain ⟨u, hu, hx⟩ := (mem_old hA I x).mp hx
  let c := center v u
  have hm : c ∈ Core v s I := ⟨u, hu, by simpa [c] using radius_nonneg hu hs⟩
  refine ⟨c + (x - embed (A • u, 1)), ⟨c, hm, by simpa using hx⟩, ?_⟩
  rw [show c + (x - embed (A • u, 1)) - x = c - embed (A • u, 1) by abel]
  exact center_perturb hu near

omit [DecidableEq ι] in
theorem base_norm {A : ℝ} (hA : 0 ≤ A) {I : Finset ι} {u : ι → ℝ} (hu : Base I u) :
    ‖embed (A • u, 1)‖ ≤ A + 1 := by
  have H := embed_dist_sq ((A • u, 1) : Pt ι) ((0 : ι → ℝ), 0)
  have h0 : embed (((0 : ι → ℝ), (0 : ℝ)) : Pt ι) = 0 := by ext c; cases c <;> rfl
  have hs : sq (fun i => (A • u, (1 : ℝ)).1 i - ((0 : ι → ℝ), (0 : ℝ)).1 i) = A ^ 2 * sq u := by
    simp [sq, mul_pow, ← mul_sum]
  rw [h0, sub_zero, hs] at H
  norm_num at H
  have h1 := sq_base_le_one hu
  have key : ‖embed (A • u, 1)‖ ^ 2 ≤ (A + 1) ^ 2 := by
    rw [H]; nlinarith
  nlinarith [norm_nonneg (embed (A • u, 1))]

omit [DecidableEq ι] in
theorem old_norm {A : ℝ} (hA : 0 < A) {I : Finset ι} {x} (hx : x ∈ Old A I) : ‖x‖ ≤ A + 2 := by
  obtain ⟨u, hu, hx⟩ := (mem_old hA I x).mp hx
  have h := norm_add_le (x - embed (A • u, 1)) (embed (A • u, 1))
  simp only [sub_add_cancel] at h
  linarith [base_norm hA.le hu]

theorem anchor_mem {A : ℝ} {I : Finset ι} {a : ι} (ha : a ∈ I) {v : ι → Ambient ι}
    (fix : v a = baseV A a) {s : ℝ} (hs : 0 ≤ s) : start A a ∈ Body v s I := by
  refine ⟨v a, vertex_mem v ha hs, ?_⟩
  rw [fix]
  have H := embed_dist_sq ((A • atom a, 0) : Pt ι) (A • atom a, 1)
  simp [sq] at H
  change ‖embed (A • atom a, 0) - embed (A • atom a, 1)‖ ≤ 1
  rcases H with h | h <;> linarith

omit [DecidableEq ι] in
theorem cost_obj (x : Ambient ι) : cost x = obj 1 (coords x) := by
  simpa [cost, tilt] using (objective_as_quadratic 1 1 (coords x)).symm

omit [DecidableEq ι] in
theorem tilt_norm : ‖(tilt : Ambient ι)‖ = 32 := by
  have H := EuclideanSpace.norm_sq_eq (tilt : Ambient ι)
  rw [Fintype.sum_option] at H
  simp [tilt, embed] at H
  exact H

omit [DecidableEq ι] in
/-- The objective is `(ρ + 32)`-Lipschitz from a point of norm at most `ρ`, downwards. -/
theorem cost_diff {x y : Ambient ι} {ρ : ℝ} (hx : ‖x‖ ≤ ρ) :
    cost x - cost y ≤ (ρ + 32) * ‖x - y‖ := by
  have H := quadratic_taylor 1 tilt x y
  have hg : ‖grad 1 tilt x‖ ≤ ρ + 32 := by
    simp only [grad, one_smul]; linarith [norm_add_le x tilt, tilt_norm (ι := ι)]
  have hb := mul_le_mul_of_nonneg_right hg (norm_nonneg (x - y))
  have hi := real_inner_le_norm (grad 1 tilt x) (x - y)
  have eq : ⟪grad 1 tilt x, y - x⟫ = -⟪grad 1 tilt x, x - y⟫ := by
    simp only [inner_sub_right]; ring
  rw [eq] at H; unfold cost; linarith [_root_.sq_nonneg ‖y - x‖]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The public repair: the convex combination `(x + h c) / (1 + h)`. -/
noncomputable def repair (c : E) (h : ℝ) (x : E) := (1 + h)⁻¹ • x + (h / (1 + h)) • c

/-- If `C` is convex and contains the unit ball about `c`, the repair moves any point within
`h` of `C` into `C`. -/
theorem repair_mem {C : Set E} (cv : Convex ℝ C) {c x w : E} (ball : ∀ z, ‖z - c‖ ≤ 1 → z ∈ C)
    {h : ℝ} (hp : 0 < h) (hw : w ∈ C) (hw' : ‖x - w‖ ≤ h) : repair c h x ∈ C := by
  let z := c + h⁻¹ • (x - w)
  have hz : z ∈ C := ball z (by
    simpa [z, norm_smul, abs_of_pos (inv_pos.mpr hp), inv_mul_eq_div, abs_of_pos hp,
      div_le_one hp] using hw')
  have p : 0 < 1 + h := by linarith
  have ab : (1 + h)⁻¹ + h / (1 + h) = 1 := by field_simp
  have cc := cv hw hz (inv_nonneg.mpr p.le) (div_nonneg hp.le p.le) ab
  have eq : (1 + h)⁻¹ • w + (h / (1 + h)) • z = repair c h x := by
    simp only [z, repair, smul_add, smul_smul, show h / (1 + h) * h⁻¹ = (1 + h)⁻¹ by field_simp,
      smul_sub]; abel
  rwa [eq] at cc

/-- The repair moves a point by at most `h (‖c‖ + ‖x‖)`. -/
theorem repair_dist (c x : E) {h : ℝ} (hp : 0 < h) :
    ‖repair c h x - x‖ ≤ h * (‖c‖ + ‖x‖) := by
  have p : 0 < 1 + h := by linarith
  have ed : repair c h x - x = (h / (1 + h)) • (c - x) := by
    unfold repair
    rw [show (1 + h)⁻¹ • x + (h / (1 + h)) • c - x = ((1 + h)⁻¹ - 1) • x + (h / (1 + h)) • c by
      rw [sub_smul, one_smul]; abel]
    rw [show (1 + h)⁻¹ - 1 = -(h / (1 + h)) by field_simp; ring, neg_smul, smul_sub]; abel
  have hb : h / (1 + h) ≤ h := (div_le_iff₀ p).mpr (by nlinarith [_root_.sq_nonneg h])
  rw [ed, norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hp.le p.le)]
  calc
    _ ≤ h * ‖c - x‖ := mul_le_mul_of_nonneg_right hb (norm_nonneg _)
    _ ≤ h * (‖c‖ + ‖x‖) := mul_le_mul_of_nonneg_left (norm_sub_le c x) hp.le

end Lemmata.FrankWolfePS.Unique
