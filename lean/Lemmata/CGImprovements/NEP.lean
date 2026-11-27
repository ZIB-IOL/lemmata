module

public import Lemmata.CGImprovements.SharpAFW
public import Lemmata.FrankWolfe.Proof.Rate

@[expose] public section

/-!
# Frank–Wolfe with the nearest extreme point oracle (Theorem 3.36, Lemma 3.37)

The vertex chosen by the oracle is at least as good as any convex combination of vertices in the
smoothness bound. Comparing with a representation of the nearest minimizer over `S⋆` and using
`∑ λ_u ‖u - x‖² = ‖y - x‖² + ∑ λ_u ‖u - y‖²` gives the recursion
`h_{t+1} ≤ (1 - γ_t) h_t + γ_t² L (dist(x_t, Ω*)² + D₀²)/2`.
-/

namespace Lemmata.CGImprovements

open Lemmata.FrankWolfe

namespace Proof

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The NEP vertex beats every convex combination of vertices in the smoothness bound. -/
theorem nep_avg {V : Finset E} {f : E → ℝ} {L : NNReal} (hsm : IsSmooth f L) {x v : E} {γ : ℝ}
    (hγ : 0 ≤ γ) (hv : ∀ u ∈ V, fderiv ℝ f x v + L * γ * ‖x - v‖ ^ 2 / 2 ≤
      fderiv ℝ f x u + L * γ * ‖x - u‖ ^ 2 / 2)
    (T : Finset E) (hT : T ⊆ V) (w : E → ℝ) (hw0 : ∀ u ∈ T, 0 ≤ w u) (hw1 : ∑ u ∈ T, w u = 1) :
    f (x + γ • (v - x)) ≤ f x + γ * (fderiv ℝ f x (∑ u ∈ T, w u • u - x) +
      L * γ / 2 * ∑ u ∈ T, w u * ‖u - x‖ ^ 2) := by
  have hq := hsm.le_quadratic x (x + γ • (v - x))
  rw [add_sub_cancel_left, map_smul, smul_eq_mul, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    at hq
  -- average the oracle inequality
  have havg : fderiv ℝ f x v + L * γ * ‖x - v‖ ^ 2 / 2 ≤
      ∑ u ∈ T, w u * (fderiv ℝ f x u + L * γ * ‖x - u‖ ^ 2 / 2) := by
    calc fderiv ℝ f x v + L * γ * ‖x - v‖ ^ 2 / 2 =
          ∑ u ∈ T, w u * (fderiv ℝ f x v + L * γ * ‖x - v‖ ^ 2 / 2) := by
          rw [← Finset.sum_mul, hw1, one_mul]
      _ ≤ _ := Finset.sum_le_sum (fun u hu => mul_le_mul_of_nonneg_left (hv u (hT hu)) (hw0 u hu))
  have hlin : fderiv ℝ f x (∑ u ∈ T, w u • u - x) = ∑ u ∈ T, w u * fderiv ℝ f x u -
      fderiv ℝ f x x := by
    rw [map_sub, map_sum]; simp [map_smul]
  have hsplit : ∑ u ∈ T, w u * (fderiv ℝ f x u + L * γ * ‖x - u‖ ^ 2 / 2) =
      ∑ u ∈ T, w u * fderiv ℝ f x u + L * γ / 2 * ∑ u ∈ T, w u * ‖u - x‖ ^ 2 := by
    rw [Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [norm_sub_rev x u]; ring
  have hvx : fderiv ℝ f x (v - x) = fderiv ℝ f x v - fderiv ℝ f x x := map_sub _ _ _
  rw [hvx, norm_sub_rev] at hq
  rw [hlin]
  have := mul_le_mul_of_nonneg_left (havg.trans (le_of_eq hsplit)) hγ
  nlinarith

/-- `∑ w_u ‖u - x‖² = ‖y - x‖² + ∑ w_u ‖u - y‖²` for `y = ∑ w_u u` with `∑ w_u = 1`. -/
theorem variance_id (T : Finset E) (w : E → ℝ) (hw1 : ∑ u ∈ T, w u = 1) (x : E) :
    ∑ u ∈ T, w u * ‖u - x‖ ^ 2 = ‖∑ u ∈ T, w u • u - x‖ ^ 2 +
      ∑ u ∈ T, w u * ‖u - ∑ v ∈ T, w v • v‖ ^ 2 := by
  set y := ∑ v ∈ T, w v • v with hy
  have h1 : ∀ u, ‖u - x‖ ^ 2 = ‖u - y‖ ^ 2 + 2 * inner ℝ (u - y) (y - x) + ‖y - x‖ ^ 2 := by
    intro u
    have : u - x = (u - y) + (y - x) := by abel
    rw [this, norm_add_sq_real]
  have h2 : ∑ u ∈ T, w u * inner ℝ (u - y) (y - x) = 0 := by
    have : ∑ u ∈ T, w u • (u - y) = 0 := by
      simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hw1, one_smul, hy, sub_self]
    calc ∑ u ∈ T, w u * inner ℝ (u - y) (y - x) = inner ℝ (∑ u ∈ T, w u • (u - y)) (y - x) := by
          rw [sum_inner]; simp [real_inner_smul_left]
      _ = 0 := by rw [this, inner_zero_left]
  calc ∑ u ∈ T, w u * ‖u - x‖ ^ 2 = ∑ u ∈ T, (w u * ‖u - y‖ ^ 2 +
        2 * (w u * inner ℝ (u - y) (y - x)) + w u * ‖y - x‖ ^ 2) :=
        Finset.sum_congr rfl (fun u _ => by rw [h1 u]; ring)
    _ = ∑ u ∈ T, w u * ‖u - y‖ ^ 2 + 2 * ∑ u ∈ T, w u * inner ℝ (u - y) (y - x) +
        (∑ u ∈ T, w u) * ‖y - x‖ ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
    _ = ‖y - x‖ ^ 2 + ∑ u ∈ T, w u * ‖u - y‖ ^ 2 := by rw [h2, hw1]; ring

/-- `∑_{s<t} (s+2)^{-2θ} ≤ (t+2)^{1-2θ}/(1-2θ)` for `0 ≤ θ < 1/2`. -/
theorem sum_rpow_le {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ < 1 / 2) (t : ℕ) :
    ∑ s ∈ Finset.range t, ((s : ℝ) + 2) ^ (-(2 * θ)) ≤
      ((t : ℝ) + 2) ^ (1 - 2 * θ) / (1 - 2 * θ) := by
  set p := 1 - 2 * θ with hp
  have hp0 : 0 < p := by linarith
  have hp1 : p ≤ 1 := by linarith
  have hterm : ∀ s : ℕ, ((s : ℝ) + 2) ^ (-(2 * θ)) ≤
      (((s : ℝ) + 2) ^ p - ((s : ℝ) + 1) ^ p) / p := by
    intro s
    have hs2 : (0 : ℝ) < (s : ℝ) + 2 := by positivity
    have hs0 : (0 : ℝ) ≤ (s : ℝ) := s.cast_nonneg
    have hb := rpow_one_add_le_one_add_mul_self (s := -1 / ((s : ℝ) + 2))
      (by rw [neg_div, neg_le_neg_iff, div_le_one hs2]; linarith) hp0.le hp1
    have e1 : 1 + -1 / ((s : ℝ) + 2) = ((s : ℝ) + 1) / ((s : ℝ) + 2) := by field_simp; ring
    rw [e1, Real.div_rpow (by positivity) hs2.le] at hb
    set A := ((s : ℝ) + 2) ^ p with hA
    have hA0 : 0 < A := Real.rpow_pos_of_pos hs2 p
    rw [div_le_iff₀ hA0] at hb
    have e3 : (1 + p * (-1 / ((s : ℝ) + 2))) * A * ((s : ℝ) + 2) = A * ((s : ℝ) + 2) - p * A := by
      field_simp; ring
    have h3 := mul_le_mul_of_nonneg_right hb hs2.le
    rw [e3] at h3
    have e2 : ((s : ℝ) + 2) ^ (-(2 * θ)) = A / ((s : ℝ) + 2) := by
      rw [hA, show -(2 * θ) = p - 1 by rw [hp]; ring, Real.rpow_sub hs2, Real.rpow_one]
    rw [e2, le_div_iff₀ hp0, div_mul_eq_mul_div, div_le_iff₀ hs2]
    linarith
  have htel : ∀ n : ℕ, ∑ s ∈ Finset.range n, (((s : ℝ) + 2) ^ p - ((s : ℝ) + 1) ^ p) =
      ((n : ℝ) + 1) ^ p - 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring_nf
  calc ∑ s ∈ Finset.range t, ((s : ℝ) + 2) ^ (-(2 * θ)) ≤
        ∑ s ∈ Finset.range t, (((s : ℝ) + 2) ^ p - ((s : ℝ) + 1) ^ p) / p :=
        Finset.sum_le_sum (fun s _ => hterm s)
    _ = (((t : ℝ) + 1) ^ p - 1) / p := by rw [← Finset.sum_div, htel]
    _ ≤ ((t : ℝ) + 2) ^ p / p := by
        apply div_le_div_of_nonneg_right _ hp0.le
        have : ((t : ℝ) + 1) ^ p ≤ ((t : ℝ) + 2) ^ p :=
          Real.rpow_le_rpow (by positivity) (by linarith) hp0.le
        linarith

/-- `∑_{s<t} (s+2)^{-1} ≤ ln (t+2)`. -/
theorem sum_inv_le_log (t : ℕ) :
    ∑ s ∈ Finset.range t, ((s : ℝ) + 2) ^ (-(2 * (1 / 2 : ℝ))) ≤ Real.log ((t : ℝ) + 2) := by
  have hterm : ∀ s : ℕ, ((s : ℝ) + 2) ^ (-(2 * (1 / 2 : ℝ))) ≤
      Real.log ((s : ℝ) + 2) - Real.log ((s : ℝ) + 1) := by
    intro s
    rw [show -(2 * (1 / 2 : ℝ)) = -1 by norm_num, Real.rpow_neg_one]
    have h := Real.one_sub_inv_le_log_of_pos (x := ((s : ℝ) + 2) / ((s : ℝ) + 1)) (by positivity)
    rw [Real.log_div (by positivity) (by positivity), inv_div] at h
    have e : 1 - ((s : ℝ) + 1) / ((s : ℝ) + 2) = ((s : ℝ) + 2)⁻¹ := by field_simp; ring
    linarith
  have htel : ∀ n : ℕ, ∑ s ∈ Finset.range n, (Real.log ((s : ℝ) + 2) - Real.log ((s : ℝ) + 1)) =
      Real.log ((n : ℝ) + 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring_nf
  calc ∑ s ∈ Finset.range t, ((s : ℝ) + 2) ^ (-(2 * (1 / 2 : ℝ))) ≤
        ∑ s ∈ Finset.range t, (Real.log ((s : ℝ) + 2) - Real.log ((s : ℝ) + 1)) :=
        Finset.sum_le_sum (fun s _ => hterm s)
    _ = Real.log ((t : ℝ) + 1) := htel t
    _ ≤ Real.log ((t : ℝ) + 2) := Real.log_le_log (by positivity) (by linarith)

universe u

theorem nep_rate : NEPRate.{u} := by
  intro E _ _ V Sstar f L c θ x v hconv hsm hc hθ0 hθ hsharp hSV hΩ hrun xStar hxs t ht
  classical
  set P := convexHull ℝ (↑V : Set E) with hP
  set D := Metric.diam (↑V : Set E) with hD
  set D₀ := Metric.diam (↑Sstar : Set E) with hD₀
  set h : ℕ → ℝ := fun t => f (x t) - f xStar with hh
  have hPc : IsCompact P := V.finite_toSet.isCompact_convexHull (𝕜 := ℝ)
  have hγ0 : ∀ t : ℕ, (0 : ℝ) ≤ 2 / ((t : ℝ) + 2) := fun t => by positivity
  have hγ1 : ∀ t : ℕ, 2 / ((t : ℝ) + 2) ≤ 1 := fun t => by
    rw [div_le_one (by positivity)]; linarith [(t.cast_nonneg : (0 : ℝ) ≤ t)]
  have hxP : ∀ t, x t ∈ P := by
    intro t
    induction t with
    | zero => exact subset_convexHull ℝ _ (by exact_mod_cast hrun.1)
    | succ t ih =>
      rw [(hrun.2 t).2.2]
      exact (convex_convexHull ℝ _).add_smul_sub_mem ih
        (subset_convexHull ℝ _ (by exact_mod_cast (hrun.2 t).1)) ⟨hγ0 t, hγ1 t⟩
  have hh0 : ∀ t, 0 ≤ h t := fun t => by simp only [hh]; linarith [hxs.2 _ (hxP t)]
  have hdist : ∀ y ∈ P, ∀ z ∈ P, ‖y - z‖ ≤ D := fun y hy z hz => by
    rw [← dist_eq_norm, hD, ← convexHull_diam]
    exact Metric.dist_le_diam_of_mem hPc.isBounded hy hz
  have hdist0 : ∀ y ∈ convexHull ℝ (↑Sstar : Set E), ∀ z ∈ convexHull ℝ (↑Sstar : Set E),
      ‖y - z‖ ≤ D₀ := fun y hy z hz => by
    rw [← dist_eq_norm, hD₀, ← convexHull_diam]
    exact Metric.dist_le_diam_of_mem
      (Sstar.finite_toSet.isCompact_convexHull (𝕜 := ℝ)).isBounded hy hz
  have hcvx : ∀ t, ∀ y ∈ minimizers P f, fderiv ℝ f (x t) (y - x t) ≤ -h t := fun t y hy => by
    have h1 := add_fderiv_le_of_convexOn hconv hsm.1 (x t) y
    have hfy : f y = f xStar := le_antisymm (hy.2 xStar hxs.1) (hxs.2 y hy.1)
    simp only [hh]; linarith
  have hcm : ∀ (T : Finset E) (w : E → ℝ), ∑ u ∈ T, w u = 1 →
      T.centerMass w id = ∑ u ∈ T, w u • u := fun T w hw1 => by
    rw [Finset.centerMass, hw1, inv_one, one_smul]; rfl
  -- one step against a representation of a minimizer
  have hstep : ∀ t, ∀ T ⊆ V, ∀ w : E → ℝ, (∀ u ∈ T, 0 ≤ w u) → ∑ u ∈ T, w u = 1 →
      ∑ u ∈ T, w u • u ∈ minimizers P f →
      h (t + 1) ≤ (1 - 2 / ((t : ℝ) + 2)) * h t +
        (2 / ((t : ℝ) + 2)) ^ 2 * L / 2 * ∑ u ∈ T, w u * ‖u - x t‖ ^ 2 := by
    intro t T hT w hw0 hw1 hmin
    have hn := nep_avg hsm (hγ0 t) (hrun.2 t).2.1 T hT w hw0 hw1
    rw [← (hrun.2 t).2.2] at hn
    have h1 := mul_le_mul_of_nonneg_left (hcvx t _ hmin) (hγ0 t)
    simp only [hh]
    nlinarith
  -- Lemma 3.37 (a)
  have ha : ∀ t, h (t + 1) ≤ (1 - 2 / ((t : ℝ) + 2)) * h t +
      (2 / ((t : ℝ) + 2)) ^ 2 * (L * D ^ 2) / 2 := by
    intro t
    obtain ⟨w, hw0, hw1, hwx⟩ := Finset.mem_convexHull.mp hxs.1
    have hsum : ∑ u ∈ V, w u • u = xStar := by rw [← hcm V w hw1]; exact hwx
    have h1 := hstep t V subset_rfl w hw0 hw1 (hsum ▸ hxs)
    have hsq : ∑ u ∈ V, w u * ‖u - x t‖ ^ 2 ≤ D ^ 2 := by
      calc ∑ u ∈ V, w u * ‖u - x t‖ ^ 2 ≤ ∑ u ∈ V, w u * D ^ 2 :=
            Finset.sum_le_sum (fun u hu => mul_le_mul_of_nonneg_left (pow_le_pow_left₀
              (norm_nonneg _) (hdist u (subset_convexHull ℝ _ (by exact_mod_cast hu)) (x t)
              (hxP t)) 2) (hw0 u hu))
        _ = D ^ 2 := by rw [← Finset.sum_mul, hw1, one_mul]
    have := mul_le_mul_of_nonneg_left hsq
      (by positivity : (0 : ℝ) ≤ (2 / ((t : ℝ) + 2)) ^ 2 * L / 2)
    nlinarith
  -- Lemma 3.37 (b)
  have hΩc : IsCompact (minimizers P f) := by
    have e : minimizers P f = P ∩ f ⁻¹' Set.Iic (f xStar) := by
      ext y
      constructor
      · rintro ⟨hy, hmin⟩; exact ⟨hy, by simpa using hmin xStar hxs.1⟩
      · rintro ⟨hy, hle⟩
        exact ⟨hy, fun z hz => le_trans (by simpa using hle) (hxs.2 z hz)⟩
    rw [e]
    exact hPc.inter_right (isClosed_Iic.preimage hsm.1.continuous)
  have hb : ∀ t, h (t + 1) ≤ (1 - 2 / ((t : ℝ) + 2)) * h t +
      (2 / ((t : ℝ) + 2)) ^ 2 * L * (c ^ 2 * h t ^ (2 * θ) + D₀ ^ 2) / 2 := by
    intro t
    obtain ⟨y, hy, hydist⟩ := hΩc.exists_infDist_eq_dist ⟨xStar, hxs⟩ (x t)
    obtain ⟨w, hw0, hw1, hwy⟩ := Finset.mem_convexHull.mp (hΩ hy)
    have hsum : ∑ u ∈ Sstar, w u • u = y := by rw [← hcm Sstar w hw1]; exact hwy
    have h1 := hstep t Sstar hSV w hw0 hw1 (hsum ▸ hy)
    rw [variance_id Sstar w hw1 (x t), hsum] at h1
    have hd1 : ‖y - x t‖ ≤ c * h t ^ θ := by
      rw [norm_sub_rev, ← dist_eq_norm, ← hydist]; exact hsharp (x t) (hxP t) xStar hxs
    have hd1sq : ‖y - x t‖ ^ 2 ≤ c ^ 2 * h t ^ (2 * θ) := by
      have := pow_le_pow_left₀ (norm_nonneg _) hd1 2
      rw [mul_pow, ← Real.rpow_natCast (h t ^ θ), ← Real.rpow_mul (hh0 t)] at this
      convert this using 3; push_cast; ring
    have hd2 : ∑ u ∈ Sstar, w u * ‖u - y‖ ^ 2 ≤ D₀ ^ 2 := by
      calc ∑ u ∈ Sstar, w u * ‖u - y‖ ^ 2 ≤ ∑ u ∈ Sstar, w u * D₀ ^ 2 :=
            Finset.sum_le_sum (fun u hu => mul_le_mul_of_nonneg_left (pow_le_pow_left₀
              (norm_nonneg _) (hdist0 u (subset_convexHull ℝ _ (by exact_mod_cast hu)) y
              (hΩ hy)) 2) (hw0 u hu))
        _ = D₀ ^ 2 := by rw [← Finset.sum_mul, hw1, one_mul]
    have := mul_le_mul_of_nonneg_left (add_le_add hd1sq hd2)
      (by positivity : (0 : ℝ) ≤ (2 / ((t : ℝ) + 2)) ^ 2 * L / 2)
    nlinarith
  have hK0 : (0 : ℝ) ≤ L * D ^ 2 := by positivity
  have hrate : ∀ s : ℕ, 1 ≤ s → h s ≤ 2 * (L * D ^ 2) / ((s : ℝ) + 2) :=
    Lemmata.FrankWolfe.rate_of_recursion hK0 ha
  have hacc : ∀ n : ℕ, ((n : ℝ) + 1) * ((n : ℝ) + 2) * h (n + 1) ≤
      L * D ^ 2 + 2 * L * D₀ ^ 2 * n +
        2 * L * c ^ 2 * ∑ s ∈ Finset.range n, h (s + 1) ^ (2 * θ) := by
    intro n
    induction n with
    | zero =>
      have := ha 0
      norm_num at this ⊢
      linarith
    | succ n ih =>
      have h1 := hb (n + 1)
      rw [Finset.sum_range_succ]
      push_cast at h1 ⊢
      set A := h (n + 1) with hA
      have hA0 : 0 ≤ A := hh0 (n + 1)
      set B := c ^ 2 * A ^ (2 * θ) + D₀ ^ 2 with hB
      have hB0 : 0 ≤ B := by have := Real.rpow_nonneg hA0 (2 * θ); positivity
      have hn : (0 : ℝ) ≤ n := n.cast_nonneg
      have e : ((n : ℝ) + 1 + 1) * ((n : ℝ) + 1 + 2) * ((1 - 2 / ((n : ℝ) + 1 + 2)) * A +
          (2 / ((n : ℝ) + 1 + 2)) ^ 2 * L * B / 2) =
          ((n : ℝ) + 1) * ((n : ℝ) + 2) * A + 2 * L * B * (((n : ℝ) + 2) / ((n : ℝ) + 3)) := by
        field_simp; ring
      have hfrac : ((n : ℝ) + 2) / ((n : ℝ) + 3) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
      have h2 := mul_le_mul_of_nonneg_left h1
        (by positivity : (0 : ℝ) ≤ ((n : ℝ) + 1 + 1) * ((n : ℝ) + 1 + 2))
      rw [e] at h2
      have h3 := mul_le_mul_of_nonneg_left hfrac (by positivity : (0 : ℝ) ≤ 2 * L * B)
      rw [hB] at h3 h2
      nlinarith
  obtain ⟨n, rfl⟩ : ∃ n, t = n + 1 := ⟨t - 1, by omega⟩
  set K := L * D ^ 2 with hK
  set R := (if θ < 1 / 2 then (((n + 1 : ℕ) : ℝ) + 2) ^ (1 - 2 * θ) / (1 - 2 * θ)
    else Real.log (((n + 1 : ℕ) : ℝ) + 2)) with hRdef
  have hR : ∑ s ∈ Finset.range (n + 1), ((s : ℝ) + 2) ^ (-(2 * θ)) ≤ R := by
    rw [hRdef]
    split_ifs with hθ'
    · exact sum_rpow_le hθ0.le hθ' (n + 1)
    · have : θ = 1 / 2 := le_antisymm hθ (not_lt.mp hθ')
      subst this
      exact sum_inv_le_log (n + 1)
  have hpow : ∀ s ∈ Finset.range n,
      h (s + 1) ^ (2 * θ) ≤ (2 * K) ^ (2 * θ) * (((s + 1 : ℕ) : ℝ) + 2) ^ (-(2 * θ)) := by
    intro s _
    have h1 := hrate (s + 1) (by omega)
    calc h (s + 1) ^ (2 * θ) ≤ (2 * K / (((s + 1 : ℕ) : ℝ) + 2)) ^ (2 * θ) :=
          Real.rpow_le_rpow (hh0 _) h1 (by linarith)
      _ = (2 * K) ^ (2 * θ) * (((s + 1 : ℕ) : ℝ) + 2) ^ (-(2 * θ)) := by
          rw [Real.div_rpow (by positivity) (by positivity), Real.rpow_neg (by positivity),
            div_eq_mul_inv]
  have hsum : ∑ s ∈ Finset.range n, h (s + 1) ^ (2 * θ) ≤ (2 * K) ^ (2 * θ) * R := by
    calc ∑ s ∈ Finset.range n, h (s + 1) ^ (2 * θ) ≤
          ∑ s ∈ Finset.range n, (2 * K) ^ (2 * θ) * (((s + 1 : ℕ) : ℝ) + 2) ^ (-(2 * θ)) :=
          Finset.sum_le_sum hpow
      _ = (2 * K) ^ (2 * θ) * ∑ s ∈ Finset.range n, (((s + 1 : ℕ) : ℝ) + 2) ^ (-(2 * θ)) := by
          rw [Finset.mul_sum]
      _ ≤ (2 * K) ^ (2 * θ) * ∑ s ∈ Finset.range (n + 1), ((s : ℝ) + 2) ^ (-(2 * θ)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [Finset.sum_range_succ']
          have : (0 : ℝ) ≤ (((0 : ℕ) : ℝ) + 2) ^ (-(2 * θ)) := by positivity
          linarith
      _ ≤ (2 * K) ^ (2 * θ) * R := mul_le_mul_of_nonneg_left hR (by positivity)
  have hconst : 2 * (L : ℝ) * c ^ 2 * (2 * K) ^ (2 * θ) =
      2 ^ (2 * θ + 1) * (L : ℝ) ^ (2 * θ + 1) * c ^ 2 * D ^ (4 * θ) := by
    have hD0 : 0 ≤ D := Metric.diam_nonneg
    have e1 : (2 * K) ^ (2 * θ) = 2 ^ (2 * θ) * (L : ℝ) ^ (2 * θ) * D ^ (4 * θ) := by
      rw [hK, ← mul_assoc, Real.mul_rpow (by positivity) (by positivity),
        Real.mul_rpow (by norm_num) (NNReal.coe_nonneg L), ← Real.rpow_natCast D 2,
        ← Real.rpow_mul hD0]
      congr 2; push_cast; ring
    rw [e1, Real.rpow_add_one two_ne_zero]
    rcases eq_or_lt_of_le (NNReal.coe_nonneg L) with hL0 | hLpos
    · rw [← hL0, Real.zero_rpow (by linarith), Real.zero_rpow (by linarith)]; ring
    · rw [Real.rpow_add_one hLpos.ne']; ring
  have hQ : (0 : ℝ) < ((n : ℝ) + 1) * ((n : ℝ) + 2) := by positivity
  have hA := hacc n
  have hn : (0 : ℝ) ≤ n := n.cast_nonneg
  have hD0n : 2 * L * D₀ ^ 2 * n ≤
      2 * L * D₀ ^ 2 * (((n : ℝ) + 1) * ((n : ℝ) + 2) / ((n : ℝ) + 3)) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [le_div_iff₀ (by positivity)]; nlinarith
  have hS := mul_le_mul_of_nonneg_left hsum (by positivity : (0 : ℝ) ≤ 2 * L * c ^ 2)
  rw [← mul_assoc, hconst] at hS
  have hfin : h (n + 1) * (((n : ℝ) + 1) * ((n : ℝ) + 2)) ≤ L * D ^ 2 +
      2 * L * D₀ ^ 2 * (((n : ℝ) + 1) * ((n : ℝ) + 2) / ((n : ℝ) + 3)) +
      2 ^ (2 * θ + 1) * (L : ℝ) ^ (2 * θ + 1) * c ^ 2 * D ^ (4 * θ) * R := by
    nlinarith
  calc f (x (n + 1)) - f xStar = h (n + 1) := rfl
    _ ≤ (L * D ^ 2 + 2 * L * D₀ ^ 2 * (((n : ℝ) + 1) * ((n : ℝ) + 2) / ((n : ℝ) + 3)) +
          2 ^ (2 * θ + 1) * (L : ℝ) ^ (2 * θ + 1) * c ^ 2 * D ^ (4 * θ) * R) /
          (((n : ℝ) + 1) * ((n : ℝ) + 2)) := by rw [le_div_iff₀ hQ]; exact hfin
    _ = _ := by rw [hRdef]; push_cast; field_simp; ring

end Proof

end Lemmata.CGImprovements
