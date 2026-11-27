module
public import Lemmata.FrankWolfePS.Unique.Support
@[expose] public section
namespace Lemmata.FrankWolfePS.Unique
open Finset
open scoped BigOperators RealInnerProductSpace
variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [DecidableEq ι] in
theorem base_restrict {I J : Finset ι} {u : ι → ℝ} (hu : Base I u)
    (hz : ∀ i ∉ J, u i = 0) : Base J u :=
  ⟨hu.1, hz, (sum_subset (subset_univ J) (fun j _ hj => hz j hj)).trans (base_total hu)⟩

omit [DecidableEq ι] in
theorem body_mono (v : ι → E) (s : ℝ) {I J : Finset ι} (h : I ⊆ J) : Body v s I ⊆ Body v s J := by
  rintro x ⟨z, ⟨u, hu, hz⟩, hx⟩
  exact ⟨z, ⟨u, base_restrict hu (fun j hj => hu.2.1 j (fun h' => hj (h h'))), hz⟩, hx⟩

theorem body_congr {v v' : ι → E} (s : ℝ) {I : Finset ι} (h : ∀ i ∈ I, v i = v' i) :
    Body v s I = Body v' s I := by
  have hh (u : ι → ℝ) (hu : Base I u) : center v u = center v' u := by
    apply sum_congr rfl; intro i _
    by_cases hi : i ∈ I
    · rw [h i hi]
    · simp [hu.2.1 i hi]
  ext x; constructor
  · rintro ⟨y, ⟨u, hu, hy⟩, hx⟩; exact ⟨y, ⟨u, hu, hh u hu ▸ hy⟩, hx⟩
  · rintro ⟨y, ⟨u, hu, hy⟩, hx⟩; exact ⟨y, ⟨u, hu, (hh u hu).symm ▸ hy⟩, hx⟩

def move (u : ι → ℝ) (j b : ι) (i : ι) := u i + u j * atom b i - u j * atom j i

omit [Fintype ι] in
theorem move_base {I : Finset ι} {u : ι → ℝ} (hu : Base I u) {j b : ι}
    (hj : j ∈ I) (hb : b ∈ I) (ne : j ≠ b) : Base I (move u j b) := by
  refine ⟨fun i => ?_, fun i hi => ?_, ?_⟩
  · by_cases e : i = j <;> by_cases d : i = b <;> simp_all [move, atom, hu.1, add_nonneg]
  · have h1 : i ≠ j := by rintro rfl; contradiction
    have h2 : i ≠ b := by rintro rfl; contradiction
    simp [move, atom, h1, h2, hu.2.1 i hi]
  · simp [move, atom, mul_ite, sum_add_distrib, sum_sub_distrib, hj, hb, hu.2.2]

theorem move_sq (u : ι → ℝ) {j b : ι} (ne : j ≠ b) :
    sq (move u j b) = sq u + 2 * u b * u j := by
  have h (i : ι) : move u j b i ^ 2 = u i ^ 2 + (2 * u b * u j +
      u j ^ 2) * atom b i - u j ^ 2 * atom j i := by
    by_cases e : i = j <;> by_cases d : i = b <;> simp_all [move, atom]; ring
  simp [sq, h, atom, mul_ite, sum_add_distrib, sum_sub_distrib]; ring

theorem move_center (v : ι → E) (u : ι → ℝ) (j b : ι) :
    center v (move u j b) = center v u + u j • v b - u j • v j := by
  simp [center, move, atom, sub_smul, add_smul, mul_ite, ite_smul, sum_add_distrib, sum_sub_distrib]

theorem excluded_weight {v : ι → E} {s : ℝ} (hs : 0 ≤ s) {I : Finset ι} {p : E} {u : ι → ℝ}
    (hu : Base I u) (hm : ∀ w, Base I w → loss v s p u ≤ loss v s p w) {j b : ι}
    (hj : j ∈ I) (hb : b ∈ I) (gap : ⟪p, v b⟫ + 2 * s < ⟪p, v j⟫) : u j = 0 := by
  have ne : j ≠ b := by rintro rfl; linarith
  by_contra h
  have hp : 0 < u j := lt_of_le_of_ne (hu.1 j) (Ne.symm h)
  have hb1 : u b ≤ 1 := by rw [← hu.2.2]; exact single_le_sum (fun i _ => hu.1 i) hb
  have H := hm _ (move_base hu hj hb ne)
  simp only [loss, move_sq u ne, move_center, inner_add_right, inner_sub_right,
      real_inner_smul_right] at H
  nlinarith only [H, mul_lt_mul_of_pos_right gap hp,
    mul_nonneg (mul_nonneg hs hp.le) (sub_nonneg.mpr hb1)]

/-- Every hidden competitor separated from one known winner has zero weight.
The two numerical responses coincide exactly. -/
theorem reply_local [ProperSpace E] {v : ι → E} {s : ℝ} (hs : 0 < s) {I R : Finset ι}
    (sub : R ⊆ I) {start q : E} (hstart : start ∈ Body v s R) (hq : q ≠ 0)
    {b : ι} (hb : b ∈ R) (sep : ∀ j ∈ I, j ∉ R → ⟪unit q, v b⟫ + 2 * s < ⟪unit q, v j⟫) :
    reply (Body v s I) start q = reply (Body v s R) start q := by
  have m := body_mono v s sub
  have hI := (normalize_min hq).mpr (reply_min (geometry v hs.le I).1 (m hstart) q)
  have hR := (normalize_min hq).mpr (reply_min (geometry v hs.le R).1 hstart q)
  obtain ⟨u, hu, e, hm⟩ := min_rep hs.le (norm_unit hq) hI
  have hu' := base_restrict hu (J := R) (fun j hj => by
    by_cases hjI : j ∈ I
    · exact excluded_weight hs.le hu hm hjI (sub hb) (sep j hjI hj)
    · exact hu.2.1 j hjI)
  have mem : reply (Body v s I) start q ∈ Body v s R := by
    rw [e]; exact ⟨edge v s (unit q) u, edge_mem v hs.le hu' (norm_unit hq),
        by simp [point, norm_unit hq]⟩
  exact min_unique hs (norm_unit hq) ⟨mem, fun y hy => hI.2 y (m hy)⟩ hR
end Lemmata.FrankWolfePS.Unique
