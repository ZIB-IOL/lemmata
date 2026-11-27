module

public import Lemmata.FrankWolfePS.Lower.Numerical
public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Analysis.Normed.Module.Ball.Pointwise

@[expose] public section

namespace Lemmata.FrankWolfePS
open Finset
open scoped BigOperators RealInnerProductSpace Pointwise
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem base_total {I : Finset ι} {u : ι → ℝ} (hu : Base I u) : ∑ i, u i = 1 := by
  rw [← hu.2.2]
  exact (sum_subset (subset_univ _) fun j _ hj => hu.2.1 j hj).symm

omit [DecidableEq ι] in
theorem base_compact (I : Finset ι) : IsCompact {u | Base I u} := by
  have h1 : IsClosed {u : ι → ℝ | ∀ i, 0 ≤ u i} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
  have h2 : IsClosed {u : ι → ℝ | ∀ i ∉ I, u i = 0} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun _ =>
      isClosed_eq (continuous_apply i) continuous_const
  have h3 : IsClosed {u : ι → ℝ | ∑ i ∈ I, u i = 1} :=
    isClosed_eq (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const
  refine (isCompact_univ_pi fun _ => isCompact_Icc (a := (0 : ℝ)) (b := 1)).of_isClosed_subset
    (h1.inter (h2.inter h3)) fun u hu i _ => ⟨hu.1 i, ?_⟩
  have := single_le_sum (s := univ) (f := u) (fun j _ => hu.1 j) (mem_univ i)
  rwa [base_total hu] at this

omit [DecidableEq ι] in
theorem core_compact (I : Finset ι) (R : ℝ) : IsCompact (core R I) := by
  let F : (ι → ℝ) → Ambient ι := fun u => embed (u, R)
  have hF : Continuous F := by
    apply (PiLp.continuous_toLp 2 _).comp
    apply continuous_pi
    intro i
    cases i with
    | none => exact continuous_const
    | some i => exact continuous_apply i
  have he : core R I = F '' {u | Base I u} := by ext v; simp [core, F, eq_comm]
  rw [he]; exact (base_compact I).image hF

omit [Fintype ι] [DecidableEq ι] in
theorem core_convex (I : Finset ι) (R : ℝ) : Convex ℝ (core R I) := by
  rintro x ⟨u, hu, rfl⟩ y ⟨v, hv, rfl⟩ a b ha hb hab
  let w := fun i => a * u i + b * v i
  refine ⟨w, ⟨fun i => add_nonneg (mul_nonneg ha (hu.1 i)) (mul_nonneg hb (hv.1 i)), ?_, ?_⟩, ?_⟩
  · intro i hi; simp [w, hu.2.1 i hi, hv.2.1 i hi]
  · simp only [w, sum_add_distrib, ← mul_sum, hu.2.2, hv.2.2, mul_one]; exact hab
  · ext i
    cases i with
    | none => change a * R + b * R = R; rw [← add_mul, hab, one_mul]
    | some i => rfl

theorem rounded_eq_add {E : Type*} [NormedAddCommGroup E] (K : Set E) (R : ℝ) :
    Rounded K R = K + Metric.closedBall 0 R := by
  ext z
  constructor
  · rintro ⟨u, hu, hz⟩
    exact ⟨u, hu, z - u, by simpa [Metric.mem_closedBall, dist_zero_right] using hz, by abel_nf⟩
  · rintro ⟨u, hu, b, hb, rfl⟩
    exact ⟨u, hu, by simpa [Metric.mem_closedBall, dist_zero_right] using hb⟩

omit [DecidableEq ι] in
theorem body_compact_convex (I : Finset ι) (R : ℝ) :
    IsCompact (Rounded (core R I) R) ∧ Convex ℝ (Rounded (core R I) R) := by
  rw [rounded_eq_add]
  exact ⟨(core_compact I R).add (isCompact_closedBall _ _),
    (core_convex I R).add (convex_closedBall _ _)⟩

omit [DecidableEq ι] in
theorem sq_base_le_one {I : Finset ι} {u : ι → ℝ} (hu : Base I u) : sq u ≤ 1 := by
  have H := sum_sq_le_sq_sum_of_nonneg (s := univ) (f := u) (fun i _ => hu.1 i)
  simpa [base_total hu, sq] using H

omit [DecidableEq ι] in
private theorem base_pair_bound {I : Finset ι} {u v : ι → ℝ} (hu : Base I u) (hv : Base I v) :
    sq (fun i => u i - v i) ≤ 2 := by
  have H := sum_le_sum (s := univ) (f := fun i => (u i - v i) ^ 2) (g := fun i => u i ^ 2 + v i ^ 2)
    (fun i _ => by nlinarith [mul_nonneg (hu.1 i) (hv.1 i)])
  rw [sum_add_distrib] at H
  change _ ≤ sq u + sq v at H
  exact H.trans (by linarith [sq_base_le_one hu, sq_base_le_one hv])

private theorem atom_pair_sq {i j : ι} (hij : i ≠ j) :
    sq (fun n => atom i n - atom j n) = 2 := by
  have h (n : ι) : (atom i n - atom j n) ^ 2 = atom i n + atom j n := by
    by_cases e : n = i <;> by_cases f : n = j <;> simp_all [atom]
  simp only [sq, h, sum_add_distrib]
  norm_num [atom]

theorem body_diameter (I : Finset ι) (hI : 1 < I.card) (R : ℝ) (hR : 0 < R) :
    Metric.diam (Rounded (core R I) R) = 2 * R + Real.sqrt 2 := by
  have root := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hs := Real.sqrt_nonneg (2 : ℝ)
  have coreBound {x y : Ambient ι} (hx : x ∈ core R I) (hy : y ∈ core R I) : dist x y ≤
      Real.sqrt 2 := by
    obtain ⟨u, hu, rfl⟩ := hx
    obtain ⟨v, hv, rfl⟩ := hy
    have H := embed_dist_sq ((u, R) : Pt ι) (v, R)
    simp only [sub_self, zero_pow (by decide : 2 ≠ 0), add_zero] at H
    rw [dist_eq_norm]
    nlinarith [base_pair_bound hu hv]
  apply le_antisymm
  · apply Metric.diam_le_of_forall_dist_le (by positivity)
    rintro x ⟨u, hu, hx⟩ y ⟨v, hv, hy⟩
    have a := dist_triangle x u v
    have b := dist_triangle x v y
    rw [← dist_eq_norm] at hx hy
    rw [dist_comm y v] at hy
    linarith [coreBound hu hv]
  · obtain ⟨i, hi, j, hj, hij⟩ := one_lt_card.mp hI
    let u := embed (atom i, R)
    let v := embed (atom j, R)
    have hu : u ∈ core R I := ⟨_, atom_base hi, rfl⟩
    have hv : v ∈ core R I := ⟨_, atom_base hj, rfl⟩
    have he : ‖u - v‖ ^ 2 = 2 := by
      simpa [u, v, atom_pair_sq hij] using embed_dist_sq ((atom i, R) : Pt ι) (atom j, R)
    have hp : 0 < ‖u - v‖ := by nlinarith [norm_nonneg (u - v)]
    have hd : ‖u - v‖ = Real.sqrt 2 := by nlinarith
    let n := unit (u - v)
    have hn : ‖n‖ = 1 := norm_unit (norm_pos_iff.mp hp)
    have ee : ‖u - v‖ • n = u - v := by simp [n, unit, smul_smul, hp.ne']
    have e : (u + R • n) - (v + R • (-n)) = (‖u - v‖ + 2 * R) • n := by
      rw [add_smul, ee, smul_neg, show (2 : ℝ) * R = R + R by ring, add_smul]; abel
    have a := Metric.dist_le_diam_of_mem (body_compact_convex I R).1.isBounded
      (ball_point hu hn hR.le) (ball_point hv (by simpa using hn : ‖-n‖ = 1) hR.le)
    rw [dist_eq_norm, e, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), hn, mul_one,
        hd] at a
    linarith

end Lemmata.FrankWolfePS
