module

public import Lemmata.FWCaratheodory.Cardinality

@[expose] public section

/-!
# Uniformly convex sets (Corollaries 5.4, 5.5 and 7.2)

The objective `‖z - x⋆‖_p²/2` has `‖f'(z)‖ = ‖z - x⋆‖` (Lemma 3.1). For `x⋆ ∈ C` it is therefore
`√(1/2)`-gradient dominated, and the rate of Theorem 2.24 of the basics entry over uniformly convex
sets applies; for `x⋆ ∉ C` its gradient norm is at least `dist(x⋆, C)`, and Theorem 2.20 applies.
The thresholds turn these rates into iteration counts, and the sparsity of the iterates gives the
cardinality.
-/

namespace Lemmata.FWCaratheodory

open Lemmata.FrankWolfe Lemmata.CGBasics

universe u

/-- From `(a/ε²)^{1/s} ≤ A` with `a ≥ 0` and `s > 0`: `b / A^s ≤ ε²/2` whenever `b ≤ a/2`. -/
theorem rate_threshold {a b A s ε : ℝ} (ha : 0 < a) (hab : 2 * b ≤ a) (hs : 0 < s) (hε : 0 < ε)
    (hA : (a / ε ^ 2) ^ (1 / s) ≤ A) : 2 * (b / A ^ s) ≤ ε ^ 2 := by
  have hpos : 0 < (a / ε ^ 2) ^ (1 / s) := by positivity
  have hA0 : 0 < A := lt_of_lt_of_le hpos hA
  have h1 : a / ε ^ 2 ≤ A ^ s := by
    have := Real.rpow_le_rpow hpos.le hA hs.le
    rwa [← Real.rpow_mul (by positivity), one_div_mul_cancel hs.ne', Real.rpow_one] at this
  have hAs : 0 < A ^ s := by positivity
  rw [div_le_iff₀ (by positivity)] at h1
  rw [mul_div_assoc', div_le_iff₀ hAs]
  nlinarith

namespace Proof

theorem uniformly_convex_cardinality : UniformlyConvexCardinality := by
  intro n p _ hp2 hpt C V α q xStar x v γ hCc hC hUC hq hα hVC hxs hx0 hv hrun L K t₀ ε hε t ht hthr
  have hr2 : 2 ≤ p.toReal := by simpa using ENNReal.toReal_mono hpt hp2
  obtain ⟨hdiff, hconv, -, hlip, hnorm, -⟩ := lpObjective_props hp2 hpt xStar
  have hL0 : 0 < L := by show 0 < p.toReal - 1; linarith
  have hLnn : ((Real.toNNReal (p.toReal - 1) : NNReal) : ℝ) = L :=
    Real.coe_toNNReal _ hL0.le
  have hxsmin := (minimizers_lpObjective (C := C) hxs).1
  set c := Real.sqrt (1 / 2) with hc
  have hc0 : 0 < c := Real.sqrt_pos.mpr (by norm_num)
  have hc2 : c ^ 2 = 1 / 2 := Real.sq_sqrt (by norm_num)
  have hgd : IsGradientDominated C (lpObjective xStar) c := by
    intro y _ z _
    rw [hc2, hnorm y]
    have h1 := lpObjective_nonneg xStar z
    have h2 : lpObjective xStar y = ‖y - xStar‖ ^ 2 / 2 := rfl
    rw [div_le_iff₀ (by norm_num)]
    linarith
  have hrate := gradient_dominated_rate C (lpObjective xStar) (Real.toNNReal (p.toReal - 1)) α c q
    x v γ hCc hC hUC hq hα hc0 (by rw [hLnn]; exact hL0) hconv ⟨hdiff, hlip⟩ hgd hrun xStar hxsmin
  dsimp only at hrate
  have hKeq : (L : ℝ) * c ^ 2 / α ^ 2 = L / (2 * α ^ 2) := by rw [hc2]; field_simp
  rw [hLnn, hKeq] at hrate
  obtain ⟨-, hlate⟩ := hrate
  have hb := hlate t ht
  rw [lpObjective_self, sub_zero] at hb
  refine ⟨norm_le_of_obj hε ?_, run_sparsity_bound (shortStep_isFWRun hrun) hx0 hv t⟩
  have hq1 : 0 < q - 1 := by linarith
  have hK0 : 0 < K := by positivity
  have hs : 0 < q / (q - 1) := by positivity
  have hthr' : (2 * L * K / ε ^ 2) ^ (1 / (q / (q - 1))) ≤
      1 + 1 / 2 * (1 - 1 / q) * ((t : ℝ) - t₀) := by
    rw [one_div_div]; exact hthr
  have hb' : lpObjective xStar (x t) ≤
      L * K / (1 + 1 / 2 * (1 - 1 / q) * ((t : ℝ) - t₀)) ^ (q / (q - 1)) := hb
  have := rate_threshold (a := 2 * L * K) (b := L * K) (by positivity) (le_of_eq (by ring)) hs hε
    hthr'
  linarith

theorem uniformly_convex_projection_cardinality : UniformlyConvexProjectionCardinality := by
  intro n p _ hp2 hpt C V α q xStar x v γ hCc hC hUC hq hα hVC hxs hx0 hv hrun L c K t₀ ε hε t ht
    hthr
  have hr2 : 2 ≤ p.toReal := by simpa using ENNReal.toReal_mono hpt hp2
  obtain ⟨hdiff, hconv, -, hlip, hnorm, -⟩ := lpObjective_props hp2 hpt xStar
  have hL0 : 0 < L := by show 0 < p.toReal - 1; linarith
  have hLnn : ((Real.toNNReal (p.toReal - 1) : NNReal) : ℝ) = L :=
    Real.coe_toNNReal _ hL0.le
  have hCne : C.Nonempty := ⟨x 0, hVC hx0⟩
  have hc0 : 0 < c := (hCc.isClosed.notMem_iff_infDist_pos hCne).mp hxs
  have hgrad : ∀ y ∈ C, c ≤ ‖fderiv ℝ (lpObjective xStar) y‖ := by
    intro y hy
    rw [hnorm y, ← dist_eq_norm, dist_comm]
    exact Metric.infDist_le_dist_of_mem hy
  obtain ⟨xb, hxb, hxbd⟩ := hCc.exists_infDist_eq_dist hCne xStar
  have hfxb : lpObjective xStar xb = c ^ 2 / 2 := by
    show ‖xb - xStar‖ ^ 2 / 2 = c ^ 2 / 2
    rw [show c = Metric.infDist xStar C from rfl, hxbd, dist_comm, dist_eq_norm]
  have hxbmin : xb ∈ minimizers C (lpObjective xStar) := by
    refine ⟨hxb, fun y hy => ?_⟩
    rw [hfxb]
    have h1 : c ≤ ‖y - xStar‖ := by
      rw [← dist_eq_norm, dist_comm]; exact Metric.infDist_le_dist_of_mem hy
    show c ^ 2 / 2 ≤ ‖y - xStar‖ ^ 2 / 2
    have := pow_le_pow_left₀ hc0.le h1 2
    linarith
  have hrate := uniformly_convex_power C (lpObjective xStar) (Real.toNNReal (p.toReal - 1)) α c q
    x v γ hCc hC hUC hq hα hc0 (by rw [hLnn]; exact hL0) hconv ⟨hdiff, hlip⟩ hgrad hrun xb hxbmin
  dsimp only at hrate
  rw [hLnn] at hrate
  obtain ⟨-, hlate⟩ := hrate
  have hb := hlate t ht
  rw [hfxb] at hb
  refine ⟨?_, run_sparsity_bound (shortStep_isFWRun hrun) hx0 hv t⟩
  have hq2 : 0 < q - 2 := by linarith
  have hK0 : 0 < K := by positivity
  have hs : 0 < q / (q - 2) := by positivity
  have hthr' : (2 * L * K / ε ^ 2) ^ (1 / (q / (q - 2))) ≤
      1 + (1 / 2 - 1 / q) * ((t : ℝ) - t₀) := by
    rw [one_div_div]; exact hthr
  have hb' : lpObjective xStar (x t) - c ^ 2 / 2 ≤
      L * K / (1 + (1 / 2 - 1 / q) * ((t : ℝ) - t₀)) ^ (q / (q - 2)) := hb
  have h1 := rate_threshold (a := 2 * L * K) (b := L * K) (by positivity) (le_of_eq (by ring)) hs
    hε hthr'
  have h2 : lpObjective xStar (x t) = ‖x t - xStar‖ ^ 2 / 2 := rfl
  rw [h2] at hb'
  linarith

end Proof

end Lemmata.FWCaratheodory
