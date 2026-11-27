module

public import Lemmata.AwayStepFW.SimplexLike

@[expose] public section

/-!
# Decomposition-invariant pairwise Frank–Wolfe (Theorem 3.8)

Sparsity scaling and strong convexity at `x_t` give `‖x⋆‖₀ f'(x_t)(a_t - v_t)² ≥ 2 μ h_t`. With
`h_t ≤ (L D²/2)(1 - c)^{t-1}` and `γ_t ≥ η_t/2`, the step gains at least `4 c h_t`, while the
quadratic term costs at most `c (L D²/2)(1 - c)^{t-1}`; here `c ≤ 1/16` because `μ ≤ L`, `D ≥ 1`
and `‖x⋆‖₀ ≥ 1`.
-/

namespace Lemmata.AwayStepFW

open Lemmata.FrankWolfe

namespace Proof

set_option maxHeartbeats 1000000 in
theorem dipfw_rate : DIPFWRate := by
  intro n V f L μ γ x hV hsm hμ hstrong xStar hxs c hγ hrun t ht
  classical
  set P := convexHull ℝ (↑V : Set (EuclideanSpace ℝ (Fin n))) with hPdef
  set D := Metric.diam (↑V : Set (EuclideanSpace ℝ (Fin n))) with hD
  set k := (Finset.univ.filter fun i => xStar i ≠ 0).card with hk
  have hcdef : c = μ / (16 * L * D ^ 2 * k) := rfl
  obtain ⟨⟨m1, hm1⟩, -, -, hγ1le⟩ := hγ 1 le_rfl
  have hγ1pos : 0 < γ 1 := by rw [hm1]; positivity
  have hc0 : 0 < c := by
    have h1 : 0 < √c := by
      have h := hγ1le
      simp only [Nat.cast_one, sub_self, zero_div, Real.rpow_zero, mul_one] at h
      exact lt_of_lt_of_le hγ1pos h
    exact Real.sqrt_pos.mp h1
  have hden : 0 < 16 * (L : ℝ) * D ^ 2 * k := by
    by_contra hneg
    push Not at hneg
    have : c ≤ 0 := by rw [hcdef]; exact div_nonpos_of_nonneg_of_nonpos hμ.le hneg
    linarith
  have hL0 : (0 : ℝ) ≤ L := L.coe_nonneg
  have hLpos : (0 : ℝ) < L := by
    rcases eq_or_lt_of_le hL0 with h | h
    · rw [← h] at hden; simp at hden
    · exact h
  have hkpos : (0 : ℝ) < k := by
    rcases eq_or_lt_of_le (Nat.cast_nonneg k : (0 : ℝ) ≤ k) with h | h
    · rw [← h] at hden; simp at hden
    · exact h
  have hDpos : 0 < D := by
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ D from Metric.diam_nonneg) with h | h
    · rw [← h] at hden; simp at hden
    · exact h
  have hPc : IsCompact P := V.finite_toSet.isCompact_convexHull (𝕜 := ℝ)
  have hdist : ∀ y ∈ P, ∀ z ∈ P, ‖y - z‖ ≤ D := fun y hy z hz => by
    rw [← dist_eq_norm, hD, ← convexHull_diam]
    exact Metric.dist_le_diam_of_mem hPc.isBounded hy hz
  obtain ⟨h01, W, hP⟩ := hV
  have hVnn : ∀ u ∈ V, ∀ i, 0 ≤ u i := fun u hu i => by
    rcases h01 u hu i with h | h <;> simp [h]
  -- two distinct vertices give `D ≥ 1` and `μ ≤ L`
  have hnt : (↑V : Set (EuclideanSpace ℝ (Fin n))).Nontrivial := by
    by_contra hsub
    rw [Set.not_nontrivial_iff] at hsub
    have := Metric.diam_subsingleton hsub
    rw [← hD] at this
    linarith
  obtain ⟨v₁, hv₁, v₂, hv₂, hne⟩ := hnt
  have hv₁P : v₁ ∈ P := subset_convexHull ℝ _ hv₁
  have hv₂P : v₂ ∈ P := subset_convexHull ℝ _ hv₂
  have hD1 : 1 ≤ D := by
    obtain ⟨i, hi⟩ : ∃ i, v₁ i ≠ v₂ i := by
      by_contra hall
      push Not at hall
      exact hne (by ext i; exact hall i)
    have h1 : |v₁ i - v₂ i| = 1 := by
      rcases h01 v₁ hv₁ i with h | h <;> rcases h01 v₂ hv₂ i with h' | h' <;>
        simp_all
    have h2 : ‖(v₁ - v₂) i‖ ≤ ‖v₁ - v₂‖ := PiLp.norm_apply_le _ i
    rw [PiLp.sub_apply, Real.norm_eq_abs, h1] at h2
    exact h2.trans (hdist v₁ hv₁P v₂ hv₂P)
  have hμL : μ ≤ L := by
    have h1 := hstrong v₁ hv₁P v₂ hv₂P
    have h2 := hsm.le_quadratic v₁ v₂
    have hpos : 0 < ‖v₂ - v₁‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hne))
    have h3 : (μ - L) * ‖v₂ - v₁‖ ^ 2 ≤ 0 := by nlinarith
    by_contra hlt
    push Not at hlt
    have : 0 < (μ - L) * ‖v₂ - v₁‖ ^ 2 := mul_pos (by linarith) (by positivity)
    linarith
  have hk1 : (1 : ℝ) ≤ k := by
    have h1 : 0 < k := by exact_mod_cast hkpos
    have h2 : 1 ≤ k := h1
    exact_mod_cast h2
  have hc16 : c ≤ 1 / 16 := by
    rw [hcdef, div_le_iff₀ hden]
    have : (1 : ℝ) ≤ D ^ 2 * k := by nlinarith
    nlinarith
  have hfeas : ∀ t, x t ∈ P := dipfw_feasible n V f γ x ⟨h01, W, hP⟩
    (fun t ht => (hγ t ht).1) (fun t ht => (hγ t ht).2.1) hrun
  set M₂ : ℝ := L * D ^ 2 / 2 with hM₂
  have hcM : c * M₂ = μ / (32 * k) := by
    rw [hcdef, hM₂]
    field_simp
    ring
  set h : ℕ → ℝ := fun t => f (x t) - f xStar with hh
  have hh0 : ∀ t, 0 ≤ h t := fun t => by simp only [hh]; linarith [hxs.2 _ (hfeas t)]
  -- the first step
  have hbase : h 1 ≤ M₂ := by
    have h1 := hsm.le_quadratic (x 0) (x 1)
    have h2 := ge_on_hull (fderiv ℝ f (x 0)) hrun.2.2.1 hxs.1
    have h3 := hstrong (x 0) (hfeas 0) xStar hxs.1
    have h4 := hdist (x 1) (hfeas 1) (x 0) (hfeas 0)
    have h5 : L / 2 * ‖x 1 - x 0‖ ^ 2 ≤ M₂ := by
      rw [hM₂]
      have := pow_le_pow_left₀ (norm_nonneg _) h4 2
      nlinarith
    have h6 : 0 ≤ μ / 2 * ‖xStar - x 0‖ ^ 2 := by positivity
    simp only [hh]
    rw [map_sub] at h1 h3
    linarith
  -- the induction
  have hind : ∀ t, 1 ≤ t → h t ≤ M₂ * (1 - c) ^ (t - 1) := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => simpa using hbase
    | succ t ht ih =>
      obtain ⟨-, -, hγlo, hγhi⟩ := hγ t ht
      obtain ⟨v, hvV, hv, a, haV, hasupp, ha, hx'⟩ := hrun.2.2.2 t ht
      set g := fderiv ℝ f (x t) with hg
      set G := g (a - v) with hG
      set e := (1 - c) ^ (((t : ℝ) - 1) / 2) with he
      set η := √c * e with hη
      have hc1 : 0 < 1 - c := by linarith
      have he0 : 0 ≤ e := Real.rpow_nonneg hc1.le _
      have he2 : e ^ 2 = (1 - c) ^ (t - 1) := by
        rw [he, ← Real.rpow_natCast, ← Real.rpow_mul hc1.le,
          show ((t : ℝ) - 1) / 2 * ((2 : ℕ) : ℝ) = ((t - 1 : ℕ) : ℝ) by
            rw [Nat.cast_sub ht]; push_cast; ring,
          Real.rpow_natCast]
      have hη2 : η ^ 2 = c * e ^ 2 := by rw [hη, mul_pow, Real.sq_sqrt hc0.le]
      have hη0 : 0 ≤ η := mul_nonneg (Real.sqrt_nonneg _) he0
      have hγ0 : 0 ≤ γ t := by linarith
      -- smoothness along the step
      have hstep : h (t + 1) ≤ h t - γ t * G + γ t ^ 2 * M₂ := by
        have h1 := hsm.le_quadratic (x t) (x (t + 1))
        have hd : x (t + 1) - x t = γ t • (v - a) := by rw [hx']; abel
        have h2 : ‖v - a‖ ≤ D := hdist v (subset_convexHull ℝ _ (Finset.mem_coe.mpr hvV)) a
          (subset_convexHull ℝ _ (Finset.mem_coe.mpr haV))
        rw [hd, map_smul, smul_eq_mul, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at h1
        have h3 : g (v - a) = -G := by rw [hG, map_sub, map_sub]; ring
        rw [← hg, h3] at h1
        have h4 : L / 2 * (γ t ^ 2 * ‖v - a‖ ^ 2) ≤ γ t ^ 2 * M₂ := by
          rw [hM₂]
          have := pow_le_pow_left₀ (norm_nonneg _) h2 2
          have := mul_le_mul_of_nonneg_left this (sq_nonneg (γ t))
          nlinarith
        show f (x (t + 1)) - f xStar ≤ f (x t) - f xStar - γ t * G + γ t ^ 2 * M₂
        linarith
      -- sparsity scaling and strong convexity at `x t`
      have hsc := sparsity_scaling n V ⟨h01, W, hP⟩ (x t) (hfeas t) xStar hxs.1 g a v haV hasupp
        ha hvV hv
      have hsx := hstrong (x t) (hfeas t) xStar hxs.1
      have hG0 : 0 ≤ G := by
        have h1 := le_of_support hVnn g ha (hfeas t) (fun i hi => hi)
        have h2 := ge_on_hull g hv (hfeas t)
        rw [hG, map_sub]
        linarith
      set r := ‖x t - xStar‖ with hr
      have hr' : ‖xStar - x t‖ = r := by rw [hr, norm_sub_rev]
      have hgxt : g (x t - xStar) = -g (xStar - x t) := by rw [map_sub, map_sub]; ring
      have hkey : h t + μ / 2 * r ^ 2 ≤ √k * r * G := by
        rw [hr'] at hsx
        simp only [hh]
        rw [← hg] at hsx
        linarith
      have hsk : (√(k : ℝ)) ^ 2 = k := Real.sq_sqrt (Nat.cast_nonneg _)
      have hdisc : 2 * μ * h t ≤ k * G ^ 2 := by
        have h1 := sq_nonneg (μ * r - √k * G)
        have hr0 : 0 ≤ r := norm_nonneg _
        nlinarith
      -- the gain dominates `4 c h`
      have hB : h t ≤ M₂ * e ^ 2 := by rw [he2]; exact ih
      have hgain : 4 * c * h t ≤ η * G / 2 := by
        have h1 : (4 * c * h t) ^ 2 ≤ (η * G / 2) ^ 2 := by
          have hl : (η * G / 2) ^ 2 = c * e ^ 2 * G ^ 2 / 4 := by
            rw [div_pow, mul_pow, hη2]
            ring
          rw [hl]
          have h2 : c * e ^ 2 * (2 * μ * h t) ≤ c * e ^ 2 * (k * G ^ 2) :=
            mul_le_mul_of_nonneg_left hdisc (by positivity)
          have h3 : 16 * c ^ 2 * h t * h t ≤ 16 * c ^ 2 * h t * (M₂ * e ^ 2) :=
            mul_le_mul_of_nonneg_left hB (by have := hh0 t; positivity)
          have h4 : 16 * c ^ 2 * h t * (M₂ * e ^ 2) * (2 * k) = c * e ^ 2 * (μ * h t) := by
            have : 16 * c * M₂ * (2 * k) = μ := by
              rw [show 16 * c * M₂ * (2 * k) = 32 * k * (c * M₂) by ring, hcM]
              field_simp
            calc 16 * c ^ 2 * h t * (M₂ * e ^ 2) * (2 * k) =
                  c * e ^ 2 * h t * (16 * c * M₂ * (2 * k)) := by ring
              _ = c * e ^ 2 * (μ * h t) := by rw [this]; ring
          have h5 : (4 * c * h t) ^ 2 * (2 * k) ≤ c * e ^ 2 * G ^ 2 / 4 * (2 * k) := by
            nlinarith
          exact le_of_mul_le_mul_right h5 (by positivity)
        exact (pow_le_pow_iff_left₀ (by have := hh0 t; positivity) (by positivity)
          two_ne_zero).mp h1
      have hγG : η / 2 * G ≤ γ t * G := mul_le_mul_of_nonneg_right hγlo hG0
      have hγ2 : γ t ^ 2 ≤ η ^ 2 := pow_le_pow_left₀ hγ0 hγhi 2
      have hfin : h (t + 1) ≤ M₂ * e ^ 2 * (1 - c) := by
        have h1 : γ t ^ 2 * M₂ ≤ c * e ^ 2 * M₂ := by
          rw [← hη2]
          exact mul_le_mul_of_nonneg_right hγ2 (by positivity)
        have h2 : (1 - 4 * c) * h t ≤ (1 - 4 * c) * (M₂ * e ^ 2) :=
          mul_le_mul_of_nonneg_left hB (by linarith)
        have h3 : 0 ≤ c * (M₂ * e ^ 2) := by positivity
        nlinarith
      rw [he2] at hfin
      calc h (t + 1) ≤ M₂ * (1 - c) ^ (t - 1) * (1 - c) := hfin
        _ = M₂ * (1 - c) ^ (t + 1 - 1) := by
          rw [mul_assoc, ← pow_succ, show t - 1 + 1 = t + 1 - 1 by omega]
  exact hind t ht

end Proof

end Lemmata.AwayStepFW
