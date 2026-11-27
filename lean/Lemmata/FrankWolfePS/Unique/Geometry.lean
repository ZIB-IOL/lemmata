module
public import Lemmata.FrankWolfePS.Upper.Main
@[expose] public section

namespace Lemmata.FrankWolfePS.Unique
open Finset
open scoped BigOperators RealInnerProductSpace Pointwise
variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def center (v : ι → E) (u : ι → ℝ) := ∑ i, u i • v i
noncomputable def radius (s : ℝ) (u : ι → ℝ) := s * (1 - sq u)
def Core (v : ι → E) (s : ℝ) (I : Finset ι) : Set E :=
  {x | ∃ u, Base I u ∧ ‖x - center v u‖ ≤ radius s u}
def Body (v : ι → E) (s : ℝ) (I : Finset ι) := Rounded (Core v s I) 1
def mix (a b : ℝ) (u w : ι → ℝ) := fun i => a * u i + b * w i

omit [Fintype ι] [DecidableEq ι] in
theorem mix_base {I : Finset ι} {u w : ι → ℝ} (hu : Base I u) (hw : Base I w)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) : Base I (mix a b u w) := by
  refine ⟨fun i => add_nonneg (mul_nonneg ha (hu.1 i)) (mul_nonneg hb (hw.1 i)), ?_, ?_⟩
  · intro i hi; simp [mix, hu.2.1 i hi, hw.2.1 i hi]
  · simp only [mix, sum_add_distrib, ← mul_sum, hu.2.2, hw.2.2, mul_one]; exact hab

omit [DecidableEq ι] in
theorem center_mix (v : ι → E) (a b : ℝ) (u w : ι → ℝ) :
    center v (mix a b u w) = a • center v u + b • center v w := by
  simp [center, mix, add_smul, mul_smul, sum_add_distrib, smul_sum]

omit [DecidableEq ι] in
theorem sq_mix (u w : ι → ℝ) {a b : ℝ} (hab : a + b = 1) :
    sq (mix a b u w) = a * sq u + b * sq w - a * b * sq (fun i => u i - w i) := by
  unfold sq mix
  simp only [mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
  apply sum_congr rfl; intro i _
  rw [show b = 1 - a by linarith]; ring

omit [DecidableEq ι] in
theorem radius_nonneg {I : Finset ι} {u : ι → ℝ} (hu : Base I u) {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ radius s u := mul_nonneg hs (sub_nonneg.mpr (sq_base_le_one hu))

omit [DecidableEq ι] in
theorem core_convex (v : ι → E) {s : ℝ} (hs : 0 ≤ s) (I : Finset ι) : Convex ℝ (Core v s I) := by
  rintro x ⟨u, hu, hd⟩ y ⟨w, hw, he⟩ a b ha hb hab
  refine ⟨mix a b u w, mix_base hu hw ha hb hab, ?_⟩
  rw [center_mix, show a • x + b • y - (a • center v u + b • center v w) = a • (x - center v u) +
      b • (y - center v w) by
    simp only [smul_sub]; abel]
  have h := norm_add_le (a • (x - center v u)) (b • (y - center v w))
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb] at h
  have H := add_le_add (mul_le_mul_of_nonneg_left hd ha) (mul_le_mul_of_nonneg_left he hb)
  apply (h.trans H).trans
  unfold radius
  rw [sq_mix u w hab]
  nlinarith only [mul_nonneg hs (mul_nonneg (mul_nonneg ha hb) (sq_nonneg (fun i => u i - w i))),
      congrArg (fun t => s * t) hab]

omit [DecidableEq ι] in
theorem core_compact [ProperSpace E] (v : ι → E) {s : ℝ} (hs : 0 ≤ s) (I : Finset ι) :
    IsCompact (Core v s I) := by
  let F : (ι → ℝ) × E → E := fun z => center v z.1 + radius s z.1 • z.2
  have cont : Continuous F := by unfold F center radius sq; fun_prop
  have eq : Core v s I = F '' ({u | Base I u} ×ˢ Metric.closedBall 0 1) := by
    ext x; constructor
    · rintro ⟨u, hu, hd⟩
      have h := radius_nonneg hu hs
      by_cases hz : radius s u = 0
      · rw [hz, norm_le_zero_iff, sub_eq_zero] at hd
        exact ⟨(u, 0), ⟨hu, by simp⟩, by simp [F, hd]⟩
      · have hp := lt_of_le_of_ne h (Ne.symm hz)
        refine ⟨(u, (radius s u)⁻¹ • (x - center v u)), ⟨hu, ?_⟩, ?_⟩
        · simp only [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
            abs_of_pos (inv_pos.mpr hp)]
          rw [inv_mul_eq_div, div_le_one hp]; exact hd
        · simp [F, smul_smul, hz]
    · rintro ⟨⟨u, b⟩, ⟨hu, hb⟩, rfl⟩
      refine ⟨u, hu, ?_⟩
      change ‖center v u + radius s u • b - center v u‖ ≤ radius s u
      simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (radius_nonneg hu hs)]
      exact mul_le_of_le_one_right (radius_nonneg hu hs) (by simpa using hb)
  rw [eq]; exact ((base_compact I).prod (isCompact_closedBall (0 : E) 1)).image cont

omit [DecidableEq ι] in
theorem geometry [ProperSpace E] (v : ι → E) {s : ℝ} (hs : 0 ≤ s) (I : Finset ι) :
    IsCompact (Body v s I) ∧ Convex ℝ (Body v s I) ∧ Upper.LipschitzNormals (Body v s I) 1 := by
  constructor
  · rw [Body, rounded_eq_add]; exact (core_compact v hs I).add (isCompact_closedBall _ _)
  constructor
  · rw [Body, rounded_eq_add]; exact (core_convex v hs I).add (convex_closedBall _ _)
  · intro x hx y hy n m hn hm hn' hm'
    simpa using rounded_lipschitz_normals (by norm_num : (0 : ℝ) < 1) hx hy hn hm hn' hm'

theorem center_atom (v : ι → E) (i : ι) : center v (atom i) = v i := by
  classical
  simp [center, atom, ite_smul]

theorem vertex_mem (v : ι → E) {i : ι} {I : Finset ι} (hi : i ∈ I) {s : ℝ} (hs : 0 ≤ s) :
    v i ∈ Core v s I :=
        ⟨atom i, atom_base hi, by simpa [center_atom] using radius_nonneg (atom_base hi) hs⟩

end Lemmata.FrankWolfePS.Unique
