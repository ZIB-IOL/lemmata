module

public import Lemmata.FWRestart.Holder
public import Lemmata.FWOpenLoop.Main

@[expose] public section

/-!
# Fractional Frank–Wolfe with an interior optimum

Near an interior minimizer the Frank–Wolfe gap dominates the norm of the gradient (Lemma 7.1).
For the restarts, the interior gap bound of the open-loop entries
(`Lemmata.FWOpenLoop.interior_gap`) gives the primal bound
`f(x) - f⋆ ≤ ((c/z) g(x))^{1/(1-θ)}` at every point of `C`. Every step of fractional Frank–Wolfe
before it stops decreases `f` by at least `ε²/(2 L D²)` with `ε = e^{-γ} G₀`, so a run takes at most
`K G₀^{r-2}` iterations, and telescoping over the restarts gives Proposition 7.2.
-/

namespace Lemmata.FWRestart

open Lemmata.FrankWolfe

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Lemma 7.1.** -/
theorem interior_scaling_bound {C : Set E} {f : E → ℝ} {z : ℝ} {x xStar v : E} (hz : 0 < z)
    (hball : Metric.closedBall xStar z ⊆ C) (hx : ‖x - xStar‖ ≤ z / 2)
    (hvmin : ∀ w ∈ C, fderiv ℝ f x v ≤ fderiv ℝ f x w) :
    z / 2 * ‖fderiv ℝ f x‖ ≤ fderiv ℝ f x (x - v) := by
  set g := fderiv ℝ f x with hg
  have hu : ∀ u : E, ‖u‖ ≤ 1 → z / 2 * g u ≤ g (x - v) := by
    intro u hu
    have hmem : x - (z / 2) • u ∈ C := by
      apply hball
      rw [Metric.mem_closedBall, dist_eq_norm]
      calc ‖x - (z / 2) • u - xStar‖ = ‖(x - xStar) - (z / 2) • u‖ := by congr 1; abel
        _ ≤ ‖x - xStar‖ + ‖(z / 2) • u‖ := norm_sub_le _ _
        _ ≤ z / 2 + z / 2 * 1 := by
            rw [norm_smul, Real.norm_of_nonneg (by positivity)]
            gcongr
        _ = z := by ring
    have h1 := hvmin _ hmem
    rw [map_sub, map_smul, smul_eq_mul] at h1
    rw [map_sub]
    linarith
  have hbound : ‖g‖ ≤ 2 / z * g (x - v) := by
    have hg0 : 0 ≤ g (x - v) := by
      have := hu 0 (by simp)
      simpa using this
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro u
    rcases eq_or_ne u 0 with rfl | hne
    · simp
    · have hn : 0 < ‖u‖ := norm_pos_iff.mpr hne
      have hw : ‖(‖u‖⁻¹ : ℝ) • u‖ ≤ 1 := (norm_smul_inv_norm hne).le
      have h1 := hu _ hw
      have h2 := hu (-((‖u‖⁻¹ : ℝ) • u)) (by rw [norm_neg]; exact hw)
      rw [map_neg, map_smul, smul_eq_mul] at h2
      rw [map_smul, smul_eq_mul] at h1
      have k1 : g u ≤ 2 / z * g (x - v) * ‖u‖ := by
        have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 / z * ‖u‖)
        have e : 2 / z * ‖u‖ * (z / 2 * (‖u‖⁻¹ * g u)) = g u := by field_simp
        rw [e] at this
        linarith
      have k2 : -g u ≤ 2 / z * g (x - v) * ‖u‖ := by
        have := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 2 / z * ‖u‖)
        have e : 2 / z * ‖u‖ * (z / 2 * -(‖u‖⁻¹ * g u)) = -g u := by field_simp
        rw [e] at this
        linarith
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith, k1⟩
  have := mul_le_mul_of_nonneg_left hbound (by positivity : (0 : ℝ) ≤ z / 2)
  have e : z / 2 * (2 / z * g (x - v)) = g (x - v) := by field_simp
  linarith

/-- One step of fractional Frank–Wolfe: the iterate stays in `C` and `f` decreases by
`η ε - η² L D²/2` for every `η ∈ [0, 1]`. -/
theorem ffw_step {C : Set E} {f : E → ℝ} {L : NNReal} {D ε : ℝ} (hC : Convex ℝ C)
    (hsm : IsSmooth f L) (hD : ∀ y ∈ C, ∀ w ∈ C, ‖y - w‖ ≤ D) {x : ℕ → E} {t : ℕ}
    (hx : x t ∈ C) (hit : IsFFWIter C f ε x t) :
    x (t + 1) ∈ C ∧ ∀ η ∈ Set.Icc (0 : ℝ) 1,
      f (x (t + 1)) ≤ f (x t) - η * ε + η ^ 2 * (L * D ^ 2) / 2 := by
  obtain ⟨v, hv, -, hgap, η, hη, hmin, hx'⟩ := hit
  have hmem : ∀ s ∈ Set.Icc (0 : ℝ) 1, x t - s • (x t - v) ∈ C := by
    intro s hs
    have := hC.add_smul_sub_mem hx hv hs
    rwa [show x t + s • (v - x t) = x t - s • (x t - v) by
      rw [← neg_sub (x t) v, smul_neg, ← sub_eq_add_neg]] at this
  refine ⟨hx' ▸ hmem η hη, fun s hs => ?_⟩
  have h1 := Lemmata.FrankWolfe.descent_lemma f L hsm (x t) (x t - s • (x t - v))
  rw [show x t - s • (x t - v) - x t = -(s • (x t - v)) by abel, map_neg, map_smul, smul_eq_mul,
    norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1] at h1
  have h2 : s * ε ≤ s * fderiv ℝ f (x t) (x t - v) := mul_le_mul_of_nonneg_left hgap.le hs.1
  have h3 : (s * ‖x t - v‖) ^ 2 ≤ s ^ 2 * D ^ 2 := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hD _ hx _ hv) 2)
      (sq_nonneg s)
  have h4 : (L : ℝ) / 2 * (s * ‖x t - v‖) ^ 2 ≤ (L : ℝ) / 2 * (s ^ 2 * D ^ 2) :=
    mul_le_mul_of_nonneg_left h3 (by positivity)
  rw [hx']
  have := hmin s hs
  nlinarith

/-- A run of fractional Frank–Wolfe with level `0 < ε ≤ L D²` makes progress `ε²/(2 L D²)` per
iteration. -/
theorem ffw_segment {C : Set E} {f : E → ℝ} {L : NNReal} {D ε : ℝ} (hC : Convex ℝ C)
    (hsm : IsSmooth f L) (hD : ∀ y ∈ C, ∀ w ∈ C, ‖y - w‖ ≤ D) (hε : 0 < ε)
    (hburn : ε ≤ L * D ^ 2) {x : ℕ → E} {t₀ : ℕ} (h0 : x t₀ ∈ C) :
    ∀ n : ℕ, (∀ i < n, IsFFWIter C f ε x (t₀ + i)) →
      x (t₀ + n) ∈ C ∧ (n : ℝ) * (ε ^ 2 / (2 * (L * D ^ 2))) ≤ f (x t₀) - f (x (t₀ + n)) := by
  have hCpos : 0 < (L : ℝ) * D ^ 2 := lt_of_lt_of_le hε hburn
  intro n
  induction n with
  | zero => intro _; simpa using h0
  | succ n ih =>
    intro hit
    obtain ⟨hmem, hprog⟩ := ih (fun i hi => hit i (by omega))
    obtain ⟨hmem', hstep⟩ := ffw_step hC hsm hD hmem (hit n (by omega))
    have hη : ε / (L * D ^ 2) ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨by positivity, (div_le_one hCpos).mpr hburn⟩
    have h1 := hstep _ hη
    have e : ε / (L * D ^ 2) * ε - (ε / (L * D ^ 2)) ^ 2 * (L * D ^ 2) / 2 =
        ε ^ 2 / (2 * (L * D ^ 2)) := by field_simp; ring
    rw [show t₀ + (n + 1) = t₀ + n + 1 by omega]
    refine ⟨hmem', ?_⟩
    push_cast
    linarith

theorem ffw_gap_unique {C : Set E} {f : E → ℝ} {y v v' : E}
    (hv : v ∈ C) (hv' : v' ∈ C) (hvmin : ∀ w ∈ C, fderiv ℝ f y v ≤ fderiv ℝ f y w)
    (hv'min : ∀ w ∈ C, fderiv ℝ f y v' ≤ fderiv ℝ f y w) :
    fderiv ℝ f y (y - v) = fderiv ℝ f y (y - v') := by
  have := hvmin v' hv'
  have := hv'min v hv
  rw [map_sub, map_sub]
  linarith

namespace Proof

theorem interior_fw_scaling' : InteriorFWScaling.{u} := by
  intro E _ _ C f z x xStar v hz hball hx _ hvmin
  exact interior_scaling_bound hz hball hx hvmin

theorem fractional_fw_rate : FractionalFWRate.{u} := by
  intro E _ _ C f L D c θ z γ x τ G xStar hCc hC hconv hsm hD heb hc hθ hz hball hxs hγ hrun
    hburn R r K
  obtain ⟨hx0, hτ0, hk⟩ := hrun
  have hdiff : ∀ y ∈ C, DifferentiableAt ℝ f y := fun y _ => hsm.1 y
  have hconvC : ConvexOn ℝ C f := hconv.subset (Set.subset_univ _) hC
  have hθ1 : 0 < 1 - θ := by linarith [hθ.2]
  -- the restart points lie in `C`
  have hmemk : ∀ k, x (τ k) ∈ C := by
    intro k
    induction k with
    | zero => rw [hτ0]; exact hx0
    | succ k ih =>
      have hle := (hk k).1
      have hGk := (hk k).2.1
      obtain ⟨v, hv, hvmin, hGv⟩ := hGk
      -- if the level is positive the segment stays in `C`; it always does, step by step
      have hseg : ∀ n : ℕ, n ≤ τ (k + 1) - τ k → x (τ k + n) ∈ C := by
        intro n
        induction n with
        | zero => intro _; simpa using ih
        | succ n ihn =>
          intro hn
          have hmem := ihn (by omega)
          have hit := (hk k).2.2.2 (τ k + n) (by omega) (by omega)
          exact (ffw_step hC hsm hD hmem hit).1
      have := hseg (τ (k + 1) - τ k) le_rfl
      rwa [Nat.add_sub_cancel' hle] at this
  have hGnn : ∀ k, 0 ≤ G k := by
    intro k
    obtain ⟨v, -, hvmin, hGv⟩ := (hk k).2.1
    rw [hGv, map_sub]
    linarith [hvmin _ (hmemk k)]
  have hGstep : ∀ k, G (k + 1) ≤ Real.exp (-γ) * G k := fun k => (hk k).2.2.1
  have hexp1 : Real.exp (-γ) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hGle : ∀ k, G k ≤ G 0 := by
    intro k
    induction k with
    | zero => exact le_rfl
    | succ k ih =>
      have := hGstep k
      have := hGnn k
      nlinarith
  -- the Frank–Wolfe gap bounds the primal gap
  have hprim : ∀ k, f (x (τ k)) - f xStar ≤ G k := by
    intro k
    obtain ⟨v, -, hvmin, hGv⟩ := (hk k).2.1
    have hc' := Lemmata.FrankWolfe.convexOn_add_fderiv_le hconv (Set.mem_univ (x (τ k)))
      (hsm.1 (x (τ k))) (Set.mem_univ xStar)
    have h1 := hvmin xStar hxs.1
    rw [hGv, map_sub]
    rw [map_sub] at hc'
    linarith
  -- the primal bound from the interior bound of the open-loop entry
  have hμpos : 0 < (c / z) ^ r := Real.rpow_pos_of_pos (div_pos hc hz) r
  have hswp : ∀ k, f (x (τ k)) - f xStar ≤ (c / z) ^ r * G k ^ r := by
    intro k
    obtain ⟨v, -, hvmin, hGv⟩ := (hk k).2.1
    have hint := Lemmata.FWOpenLoop.interior_gap hCc hconvC hdiff heb hc (by linarith [hθ.2]) hz
      hball hxs (hmemk k) hvmin
    rw [← hGv] at hint
    have hh0 : 0 ≤ f (x (τ k)) - f xStar := sub_nonneg.mpr (hxs.2 _ (hmemk k))
    have h1 : (f (x (τ k)) - f xStar) ^ (1 - θ) ≤ c / z * G k := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hz]
      have := mul_le_mul_of_nonneg_left hint hc.le
      have e : c * (z / c * (f (x (τ k)) - f xStar) ^ (1 - θ)) =
          (f (x (τ k)) - f xStar) ^ (1 - θ) * z := by field_simp
      linarith
    have h2 := Real.rpow_le_rpow (Real.rpow_nonneg hh0 _) h1 (by positivity : 0 ≤ 1 / (1 - θ))
    rwa [← Real.rpow_mul hh0, mul_one_div_cancel hθ1.ne', Real.rpow_one,
      Real.mul_rpow (by positivity) (hGnn k)] at h2
  have hK0 : 0 ≤ K := by
    show 0 ≤ 2 * Real.exp (2 * γ) * ((L : ℝ) * D ^ 2) * (c / z) ^ r
    positivity
  -- the per-run bound
  have hrunb : ∀ k, ((τ (k + 1) : ℝ) - τ k) ≤ K * G k ^ (-(2 - r)) := by
    intro k
    have hle := (hk k).1
    rcases eq_or_lt_of_le (hGnn k) with h0 | hpos
    · -- no iteration starts with gap `0`
      have hτ : τ (k + 1) = τ k := by
        by_contra hne
        have hlt : τ k < τ (k + 1) := lt_of_le_of_ne hle (Ne.symm hne)
        obtain ⟨v', hv', hv'min, hgap', -⟩ := (hk k).2.2.2 (τ k) le_rfl hlt
        obtain ⟨v, hv, hvmin, hGv⟩ := (hk k).2.1
        rw [← ffw_gap_unique hv hv' hvmin hv'min, ← hGv, ← h0, mul_zero] at hgap'
        exact lt_irrefl _ hgap'
      rw [hτ, sub_self]
      exact mul_nonneg hK0 (Real.rpow_nonneg (hGnn k) _)
    · set ε := Real.exp (-γ) * G k with hε
      have hεpos : 0 < ε := mul_pos (Real.exp_pos _) hpos
      have hburnk : ε ≤ L * D ^ 2 := by
        have := mul_le_mul_of_nonneg_left (hGle k) (Real.exp_pos (-γ)).le
        linarith
      have hCpos : 0 < (L : ℝ) * D ^ 2 := lt_of_lt_of_le hεpos hburnk
      obtain ⟨hmem', hprog⟩ := ffw_segment hC hsm hD hεpos hburnk (hmemk k)
        (τ (k + 1) - τ k) (fun i hi => (hk k).2.2.2 (τ k + i) (by omega) (by omega))
      rw [Nat.add_sub_cancel' hle, Nat.cast_sub hle] at hprog
      rw [Nat.add_sub_cancel' hle] at hmem'
      have hfin : f xStar ≤ f (x (τ (k + 1))) := hxs.2 _ hmem'
      have hP : 0 < ε ^ 2 / (2 * (L * D ^ 2)) := by positivity
      have h1 : ((τ (k + 1) : ℝ) - τ k) * (ε ^ 2 / (2 * (L * D ^ 2))) ≤ (c / z) ^ r * G k ^ r := by
        have := hswp k
        linarith
      have h2 : (τ (k + 1) : ℝ) - τ k ≤ (c / z) ^ r * G k ^ r / (ε ^ 2 / (2 * (L * D ^ 2))) :=
        (le_div_iff₀ hP).mpr h1
      have e : (c / z) ^ r * G k ^ r / (ε ^ 2 / (2 * (L * D ^ 2))) = K * G k ^ (-(2 - r)) := by
        rw [show -(2 - r) = r - 2 by ring, Real.rpow_sub hpos, Real.rpow_two, hε]
        show _ = 2 * Real.exp (2 * γ) * ((L : ℝ) * D ^ 2) * (c / z) ^ r * (G k ^ r / G k ^ 2)
        have he : Real.exp (2 * γ) * Real.exp (-γ) ^ 2 = 1 := by
          rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
        have hE : Real.exp (2 * γ) = 1 / Real.exp (-γ) ^ 2 := by
          rw [eq_div_iff (by positivity)]; exact he
        rw [hE]
        field_simp
      rw [← e]
      exact h2
  have htel : ∀ R' : ℕ, (τ R' : ℝ) ≤ K * ∑ k ∈ Finset.range R', G k ^ (-(2 - r)) := by
    intro R'
    induction R' with
    | zero => rw [hτ0]; simp
    | succ R' ih =>
      rw [Finset.sum_range_succ, mul_add]
      have := hrunb R'
      linarith
  have hKpos : 0 < G 0 → 0 < K := by
    intro hG0
    have hCpos : 0 < (L : ℝ) * D ^ 2 := lt_of_lt_of_le (mul_pos (Real.exp_pos _) hG0) hburn
    show 0 < 2 * Real.exp (2 * γ) * ((L : ℝ) * D ^ 2) * (c / z) ^ r
    have := Real.exp_pos (2 * γ)
    positivity
  have hτR0 : (0 : ℝ) ≤ τ R := Nat.cast_nonneg _
  refine ⟨fun hθlt => ?_, fun hθeq => ?_⟩
  · have hr2 : r < 2 := by
      show 1 / (1 - θ) < 2
      rw [div_lt_iff₀ hθ1]; linarith
    have hrate := rate_of_telescope R hγ (by linarith : 0 < 2 - r) hGnn hGstep hK0 hKpos (htel R)
    rw [max_eq_right hτR0, show G 0 ^ (-(2 - r)) = G 0 ^ (r - 2) by ring_nf] at hrate
    exact (hprim R).trans hrate
  · have hr : r = 2 := by
      show 1 / (1 - θ) = 2
      rw [hθeq]; norm_num
    have hsum : ∑ k ∈ Finset.range R, G k ^ (-(2 - r)) = R := by
      rw [hr, sub_self, neg_zero]
      simp
    have hTle : (τ R : ℝ) ≤ K * R := by
      have := htel R
      rwa [hsum] at this
    have hGR : G R ≤ Real.exp (-(γ * R)) * G 0 := by
      have hchain : ∀ j : ℕ, G j ≤ Real.exp (-(γ * j)) * G 0 := by
        intro j
        induction j with
        | zero => simp
        | succ j ih =>
          calc G (j + 1) ≤ Real.exp (-γ) * G j := hGstep j
            _ ≤ Real.exp (-γ) * (Real.exp (-(γ * j)) * G 0) :=
                mul_le_mul_of_nonneg_left ih (Real.exp_pos _).le
            _ = Real.exp (-(γ * ↑(j + 1))) * G 0 := by
                rw [← mul_assoc, ← Real.exp_add]; push_cast; ring_nf
      exact hchain R
    calc f (x (τ R)) - f xStar ≤ G R := hprim R
      _ ≤ Real.exp (-(γ * R)) * G 0 := hGR
      _ ≤ G 0 * Real.exp (-(γ * τ R / K)) := by
        rcases eq_or_lt_of_le (hGnn 0) with h0 | hpos
        · rw [← h0]; simp
        · have hKp := hKpos hpos
          rw [mul_comm]
          apply mul_le_mul_of_nonneg_left _ hpos.le
          apply Real.exp_le_exp.mpr
          have h1 : (τ R : ℝ) / K ≤ R := by rw [div_le_iff₀ hKp]; linarith
          have h2 : γ * τ R / K ≤ γ * R := by
            rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left h1 hγ.le
          linarith

end Proof

end Lemmata.FWRestart
