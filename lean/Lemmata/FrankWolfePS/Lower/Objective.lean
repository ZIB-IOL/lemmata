module

public import Lemmata.FrankWolfePS.Lower.Prelude
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

@[expose] public section

namespace Lemmata.FrankWolfePS
open Finset
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev Pt (ι : Type*) := (ι → ℝ) × ℝ

def sq (x : ι → ℝ) : ℝ := ∑ i, x i ^ 2

def Base (I : Finset ι) (u : ι → ℝ) : Prop :=
  (∀ i, 0 ≤ u i) ∧ (∀ i ∉ I, u i = 0) ∧ ∑ i ∈ I, u i = 1

def Feasible (R : ℝ) (I : Finset ι) (z : Pt ι) : Prop :=
  ∃ u, Base I u ∧ sq (fun i => z.1 i - u i) + (z.2 - R) ^ 2 ≤ R ^ 2

noncomputable def obj (R : ℝ) (z : Pt ι) : ℝ := (sq z.1 + z.2 ^ 2) / 2 + 32 * R * z.2

noncomputable def optimum (R : ℝ) (I : Finset ι) : ℝ :=
  sInf (obj R '' {z | Feasible R I z})

def failure (R : ℝ) (k : ℕ) (I : Finset ι) (z : Pt ι) : Prop :=
  ¬ Feasible R I z ∨ 1 / (16 * (k : ℝ)) ≤ obj R z - optimum R I

omit [DecidableEq ι] in
theorem sq_nonneg (x : ι → ℝ) : 0 ≤ sq x := sum_nonneg fun _ _ => _root_.sq_nonneg _

omit [DecidableEq ι] in
theorem horizontal_cost {R : ℝ} {I : Finset ι} {z : Pt ι}
    (hR : 0 < R) (hz : Feasible R I z) :
    0 ≤ z.2 ∧ sq z.1 / 2 ≤ obj R z := by
  obtain ⟨u, _, hu⟩ := hz
  have hdist := sq_nonneg (fun i => z.1 i - u i)
  have hprod : 0 ≤ 2 * R * z.2 := by nlinarith [_root_.sq_nonneg z.2]
  have hy : 0 ≤ z.2 := nonneg_of_mul_nonneg_right hprod (by positivity)
  refine ⟨hy, ?_⟩
  unfold obj
  nlinarith [mul_nonneg hR.le hy, _root_.sq_nonneg z.2]

omit [DecidableEq ι] in
theorem objective_bddBelow {R : ℝ} (hR : 0 < R) (I : Finset ι) :
    BddBelow (obj R '' {z | Feasible R I z}) := by
  refine ⟨0, ?_⟩
  rintro v ⟨z, hz, rfl⟩
  exact le_trans (by have := sq_nonneg z.1; linarith) (horizontal_cost hR hz).2

noncomputable def simplexBarycenter (I : Finset ι) (i : ι) : ℝ :=
  if i ∈ I then 1 / (I.card : ℝ) else 0

omit [Fintype ι] in
theorem barycenter_base {I : Finset ι} (hne : I.Nonempty) : Base I (simplexBarycenter I) := by
  have hc : 0 < (I.card : ℝ) := by exact_mod_cast card_pos.mpr hne
  refine ⟨fun i => ?_, fun i hi => by simp [simplexBarycenter, hi], ?_⟩
  · unfold simplexBarycenter; split <;> positivity
  · calc
      ∑ i ∈ I, simplexBarycenter I i = ∑ _i ∈ I, 1 / (I.card : ℝ) :=
        sum_congr rfl (fun i hi => ite_eq_left hi)
      _ = 1 := by simp [hc.ne']

theorem barycenter_upper {R : ℝ} (hR : 0 < R) {I : Finset ι} {k : ℕ}
    (hk : 0 < k) (hI : I.card = 8 * k) : optimum R I ≤ 1 / (16 * (k : ℝ)) := by
  classical
  let u := simplexBarycenter I
  have hu : Base I u := barycenter_base (card_pos.mp (by omega))
  have hf : Feasible R I (u, 0) := ⟨u, hu, by simp [sq]⟩
  have hs : sq u = I.card * (1 / (I.card : ℝ)) ^ 2 := by
    unfold sq
    change (∑ i, (if i ∈ I then 1 / (I.card : ℝ) else 0) ^ 2) = _
    simp_rw [ite_pow, zero_pow (by decide : 2 ≠ 0)]
    simp
  calc
    optimum R I ≤ obj R (u, 0) :=
      csInf_le (objective_bddBelow hR I) ⟨(u, 0), hf, rfl⟩
    _ = 1 / (16 * (k : ℝ)) := by
      simp only [obj, hs, hI, Nat.cast_mul, Nat.cast_ofNat, zero_pow (by decide : 2 ≠ 0),
        mul_zero, add_zero]
      have hk' : 0 < (k : ℝ) := by exact_mod_cast hk
      field_simp
      ring

/-- Above the horizontal norm threshold the estimator is zero, so its mass event
also implies failure on that whole branch. -/
noncomputable def guess (k : ℕ) (z : Pt ι) (i : ι) : ℝ :=
  if 4 * (k : ℝ) * sq z.1 ≤ 1 then |z.1 i| else 0

omit [DecidableEq ι] in
theorem guess_nonneg (k : ℕ) (z : Pt ι) (i : ι) : 0 ≤ guess k z i := by
  unfold guess; split <;> positivity

omit [DecidableEq ι] in
theorem guess_energy (k : ℕ) (z : Pt ι) :
    (k : ℝ) * sq (guess k z) ≤ 1 / 4 := by
  by_cases h : 4 * (k : ℝ) * sq z.1 ≤ 1
  · have he : sq (guess k z) = sq z.1 := by unfold sq; simp only [guess, ite_eq_left h, sq_abs]
    rw [he]; linarith
  · unfold sq; simp only [guess, ite_eq_right h]; norm_num

omit [DecidableEq ι] in
/-- **The height argument.** A feasible point whose horizontal coordinates sum to at most
`m ≤ 1` over `I` lies at height at least `(1 - m)² / (16 k R)`, so its cost is at least
`2 (1 - m)² / k`. -/
theorem height_cost {R m : ℝ} {k : ℕ} {I : Finset ι} {z : Pt ι} (hk : 0 < k)
    (hI : I.card = 8 * k) (hz : Feasible R I z) (hm : ∑ i ∈ I, z.1 i ≤ m) (hm1 : m ≤ 1) :
    2 * (1 - m) ^ 2 / k ≤ obj R z := by
  have hk' : 0 < (k : ℝ) := by exact_mod_cast hk
  obtain ⟨u, hu, hd⟩ := hz
  have hsum : 1 - m ≤ ∑ i ∈ I, (u i - z.1 i) := by
    rw [sum_sub_distrib, hu.2.2]; linarith
  have hcs : (∑ i ∈ I, (u i - z.1 i)) ^ 2 ≤ I.card * ∑ i ∈ I, (u i - z.1 i) ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have hsub : (∑ i ∈ I, (u i - z.1 i) ^ 2) ≤ sq (fun i => z.1 i - u i) := by
    simp only [sq, ← sub_sq_comm (u _) (z.1 _)]
    exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun i _ _ => _root_.sq_nonneg _
  have hd' : sq (fun i => z.1 i - u i) ≤ 2 * R * z.2 := by nlinarith [_root_.sq_nonneg z.2]
  have hcard : (I.card : ℝ) = 8 * k := by exact_mod_cast hI
  rw [hcard] at hcs
  have hsquare : (1 - m) ^ 2 ≤ (∑ i ∈ I, (u i - z.1 i)) ^ 2 :=
    pow_le_pow_left₀ (by linarith) hsum 2
  have hbig := mul_le_mul_of_nonneg_left (hsub.trans hd') (by positivity : 0 ≤ (8 : ℝ) * k)
  have hobj : 32 * R * z.2 ≤ obj R z := by
    unfold obj; nlinarith [sq_nonneg z.1, _root_.sq_nonneg z.2]
  have hobj' := mul_le_mul_of_nonneg_right hobj hk'.le
  rw [div_le_iff₀ hk']
  nlinarith

omit [DecidableEq ι] in
/-- A feasible point with guessed mass at most `3/4` on `I` costs at least `1 / (8k)`: on the
small-norm branch by the height argument, on the other branch by its horizontal norm. -/
theorem small_mass_objective {R : ℝ} {k : ℕ} {I : Finset ι} {z : Pt ι}
    (hR : 0 < R) (hk : 0 < k) (hI : I.card = 8 * k) (hf : Feasible R I z)
    (hm : ∑ i ∈ I, guess k z i ≤ 3 / 4) : 1 / (8 * (k : ℝ)) ≤ obj R z := by
  have hk' : 0 < (k : ℝ) := by exact_mod_cast hk
  by_cases h : 4 * (k : ℝ) * sq z.1 ≤ 1
  · have hm' : ∑ i ∈ I, z.1 i ≤ 3 / 4 :=
      le_trans (sum_le_sum fun i _ => le_abs_self (z.1 i)) (by simpa [guess, h] using hm)
    have H := height_cost hk hI hf hm' (by norm_num)
    have e : 2 * (1 - 3 / 4 : ℝ) ^ 2 / k = 1 / (8 * k) := by field_simp; norm_num
    linarith
  · have hx := (horizontal_cost hR hf).2
    push Not at h
    rw [div_le_iff₀ (by positivity)]
    nlinarith

theorem small_mass_failure {R : ℝ} {k : ℕ} {I : Finset ι} {z : Pt ι}
    (hR : 0 < R) (hk : 0 < k) (hI : I.card = 8 * k)
    (hm : ∑ i ∈ I, guess k z i ≤ 3 / 4) : failure R k I z := by
  by_cases hf : Feasible R I z
  · right
    have hb := barycenter_upper hR hk hI
    have hc := small_mass_objective hR hk hI hf hm
    have heq : 1 / (8 * (k : ℝ)) = 2 * (1 / (16 * (k : ℝ))) := by field_simp; ring
    linarith
  · exact Or.inl hf

end Lemmata.FrankWolfePS
