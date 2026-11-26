module

public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow

@[expose] public section

/-!
# Uniform smoothness of the squared `ℓ_p` norm, regularised

For `p ≥ 2`, vectors `a b : Fin n → ℝ` and `δ > 0`, put `g_i(t) = (a_i + t b_i)² + δ`,
`S(t) = ∑ g_i(t)^{p/2}` and `ψ(t) = S(t)^{2/p}`. All of these are smooth since `g_i > 0`. This file
computes `ψ'` and `ψ''` exactly and shows `ψ'' ≤ 2 (p - 1) ‖b‖_p²`, using Hölder's inequality with
exponents `p/(p-2)` and `p/2`.
-/

namespace Lemmata.FrankWolfeIntro.Proof

variable {n : ℕ}

/-- The regularised `p`-th power sum along the line `a + t b`. -/
noncomputable def lpS (p δ : ℝ) (a b : Fin n → ℝ) (t : ℝ) : ℝ :=
  ∑ i, ((a i + t * b i) ^ 2 + δ) ^ (p / 2)

/-- The derivative of `lpS`. -/
noncomputable def lpS' (p δ : ℝ) (a b : Fin n → ℝ) (t : ℝ) : ℝ :=
  ∑ i, p * ((a i + t * b i) ^ 2 + δ) ^ (p / 2 - 1) * ((a i + t * b i) * b i)

/-- The second derivative of `lpS`. -/
noncomputable def lpS'' (p δ : ℝ) (a b : Fin n → ℝ) (t : ℝ) : ℝ :=
  ∑ i, p * b i ^ 2 * ((p - 2) * ((a i + t * b i) ^ 2 + δ) ^ (p / 2 - 2) * (a i + t * b i) ^ 2 +
    ((a i + t * b i) ^ 2 + δ) ^ (p / 2 - 1))

/-- The squared regularised `p`-norm along the line. -/
noncomputable def lpψ (p δ : ℝ) (a b : Fin n → ℝ) (t : ℝ) : ℝ := lpS p δ a b t ^ (2 / p)

/-- The derivative of `lpψ`. -/
noncomputable def lpψ' (p δ : ℝ) (a b : Fin n → ℝ) (t : ℝ) : ℝ :=
  lpS' p δ a b t * (2 / p) * lpS p δ a b t ^ (2 / p - 1)

/-- The second derivative of `lpψ`. -/
noncomputable def lpψ'' (p δ : ℝ) (a b : Fin n → ℝ) (t : ℝ) : ℝ :=
  lpS'' p δ a b t * (2 / p) * lpS p δ a b t ^ (2 / p - 1) +
    lpS' p δ a b t * (2 / p) * (lpS' p δ a b t * (2 / p - 1) * lpS p δ a b t ^ (2 / p - 1 - 1))

theorem hasDerivAt_lin (c d t : ℝ) : HasDerivAt (fun t => c + t * d) d t := by
  simpa using ((hasDerivAt_id t).mul_const d).const_add c

theorem hasDerivAt_sqδ (c d δ t : ℝ) :
    HasDerivAt (fun t => (c + t * d) ^ 2 + δ) (2 * (c + t * d) * d) t := by
  have := ((hasDerivAt_lin c d t).pow 2).add_const δ
  convert this using 1
  simp

theorem hasDerivAt_term (p c d δ t : ℝ) (hδ : 0 < δ) :
    HasDerivAt (fun t => ((c + t * d) ^ 2 + δ) ^ (p / 2))
      (p * ((c + t * d) ^ 2 + δ) ^ (p / 2 - 1) * ((c + t * d) * d)) t := by
  have hpos : 0 < (c + t * d) ^ 2 + δ := by positivity
  have := (hasDerivAt_sqδ c d δ t).rpow_const (p := p / 2) (Or.inl hpos.ne')
  convert this using 1
  ring

theorem hasDerivAt_term' (p c d δ t : ℝ) (hδ : 0 < δ) :
    HasDerivAt (fun t => p * ((c + t * d) ^ 2 + δ) ^ (p / 2 - 1) * ((c + t * d) * d))
      (p * d ^ 2 * ((p - 2) * ((c + t * d) ^ 2 + δ) ^ (p / 2 - 2) * (c + t * d) ^ 2 +
        ((c + t * d) ^ 2 + δ) ^ (p / 2 - 1))) t := by
  have hpos : 0 < (c + t * d) ^ 2 + δ := by positivity
  have h1 := ((hasDerivAt_sqδ c d δ t).rpow_const (p := p / 2 - 1) (Or.inl hpos.ne')).const_mul p
  have h2 := (hasDerivAt_lin c d t).mul_const d
  have := h1.mul h2
  rw [show p / 2 - 1 - 1 = p / 2 - 2 by ring] at this
  convert this using 1
  ring

theorem lpS_pos (hn : 0 < n) {p δ : ℝ} (hδ : 0 < δ) (a b : Fin n → ℝ) (t : ℝ) :
    0 < lpS p δ a b t := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact Finset.sum_pos (fun i _ => Real.rpow_pos_of_pos (by positivity) _) Finset.univ_nonempty

theorem hasDerivAt_lpS {p δ : ℝ} (hδ : 0 < δ) (a b : Fin n → ℝ) (t : ℝ) :
    HasDerivAt (lpS p δ a b) (lpS' p δ a b t) t := by
  unfold lpS lpS'
  exact HasDerivAt.fun_sum (fun i _ => hasDerivAt_term p (a i) (b i) δ t hδ)

theorem hasDerivAt_lpS' {p δ : ℝ} (hδ : 0 < δ) (a b : Fin n → ℝ) (t : ℝ) :
    HasDerivAt (lpS' p δ a b) (lpS'' p δ a b t) t := by
  unfold lpS' lpS''
  exact HasDerivAt.fun_sum (fun i _ => hasDerivAt_term' p (a i) (b i) δ t hδ)

theorem hasDerivAt_lpψ (hn : 0 < n) {p δ : ℝ} (hδ : 0 < δ) (a b : Fin n → ℝ) (t : ℝ) :
    HasDerivAt (lpψ p δ a b) (lpψ' p δ a b t) t :=
  (hasDerivAt_lpS hδ a b t).rpow_const (Or.inl (lpS_pos hn hδ a b t).ne')

theorem hasDerivAt_lpψ' (hn : 0 < n) {p δ : ℝ} (hδ : 0 < δ) (a b : Fin n → ℝ) (t : ℝ) :
    HasDerivAt (lpψ' p δ a b) (lpψ'' p δ a b t) t := by
  have h1 := ((hasDerivAt_lpS' (p := p) hδ a b t).mul_const (2 / p))
  have h2 := (hasDerivAt_lpS (p := p) hδ a b t).rpow_const (p := 2 / p - 1)
    (Or.inl (lpS_pos hn hδ a b t).ne')
  exact h1.mul h2

variable {p δ : ℝ}

theorem lpS''_le (hp : 2 ≤ p) (hδ : 0 < δ) (a b : Fin n → ℝ) (t : ℝ) :
    lpS'' p δ a b t ≤ p * (p - 1) * ∑ i, ((a i + t * b i) ^ 2 + δ) ^ (p / 2 - 1) * b i ^ 2 := by
  unfold lpS''
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  set w := a i + t * b i
  set g := w ^ 2 + δ with hg
  have hgpos : 0 < g := by positivity
  have h1 : g ^ (p / 2 - 2) * w ^ 2 ≤ g ^ (p / 2 - 1) := by
    have e : g ^ (p / 2 - 1) = g ^ (p / 2 - 2) * g := by
      rw [← Real.rpow_add_one hgpos.ne']; congr 1; ring
    rw [e]
    exact mul_le_mul_of_nonneg_left (by rw [hg]; linarith) (Real.rpow_nonneg hgpos.le _)
  have h2 : (p - 2) * g ^ (p / 2 - 2) * w ^ 2 ≤ (p - 2) * g ^ (p / 2 - 1) := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h1 (by linarith)
  have hb : 0 ≤ p * b i ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  calc p * b i ^ 2 * ((p - 2) * g ^ (p / 2 - 2) * w ^ 2 + g ^ (p / 2 - 1))
      ≤ p * b i ^ 2 * ((p - 2) * g ^ (p / 2 - 1) + g ^ (p / 2 - 1)) :=
        mul_le_mul_of_nonneg_left (by linarith) hb
    _ = p * (p - 1) * (g ^ (p / 2 - 1) * b i ^ 2) := by ring

theorem holder_step (hp : 2 ≤ p) (hδ : 0 < δ) (a b : Fin n → ℝ) (t : ℝ) :
    ∑ i, ((a i + t * b i) ^ 2 + δ) ^ (p / 2 - 1) * b i ^ 2 ≤
      lpS p δ a b t ^ (1 - 2 / p) * (∑ i, (b i ^ 2) ^ (p / 2)) ^ (2 / p) := by
  rcases eq_or_lt_of_le hp with h2 | h2
  · subst h2
    norm_num [lpS]
  · have hp0 : p ≠ 0 := by positivity
    have hp2 : p - 2 ≠ 0 := by linarith
    have hP : (p / (p - 2)).HolderConjugate (p / 2) :=
      ⟨by field_simp; ring, div_pos (by linarith) (by linarith), by linarith⟩
    have H := Real.inner_le_Lp_mul_Lq_of_nonneg (s := Finset.univ) hP
      (f := fun i => ((a i + t * b i) ^ 2 + δ) ^ (p / 2 - 1)) (g := fun i => b i ^ 2)
      (fun i _ => Real.rpow_nonneg (by positivity) _) (fun i _ => sq_nonneg _)
    beta_reduce at H
    have e1 : ∑ i, (((a i + t * b i) ^ 2 + δ) ^ (p / 2 - 1)) ^ (p / (p - 2)) = lpS p δ a b t := by
      unfold lpS
      apply Finset.sum_congr rfl
      intro i _
      rw [← Real.rpow_mul (by positivity)]
      congr 1
      field_simp
    have e2 : 1 / (p / (p - 2)) = 1 - 2 / p := by field_simp
    have e3 : 1 / (p / 2) = 2 / p := by field_simp
    rw [e1, e2, e3] at H
    exact H

theorem lpψ''_le (hn : 0 < n) (hp : 2 ≤ p) (hδ : 0 < δ) (a b : Fin n → ℝ) (t : ℝ) :
    lpψ'' p δ a b t ≤ 2 * (p - 1) * (∑ i, (b i ^ 2) ^ (p / 2)) ^ (2 / p) := by
  have hS := lpS_pos (p := p) hn hδ a b t
  have hp0 : 0 < p := by linarith
  have hS'' := lpS''_le hp hδ a b t
  have hH := holder_step hp hδ a b t
  unfold lpψ''
  set S := lpS p δ a b t
  set B := (∑ i, (b i ^ 2) ^ (p / 2)) ^ (2 / p)
  set X := ∑ i, ((a i + t * b i) ^ 2 + δ) ^ (p / 2 - 1) * b i ^ 2
  set D1 := lpS' p δ a b t
  have h2nd : D1 * (2 / p) * (D1 * (2 / p - 1) * S ^ (2 / p - 1 - 1)) ≤ 0 := by
    have hneg : 2 / p - 1 ≤ 0 := by
      rw [div_sub_one hp0.ne']; exact div_nonpos_of_nonpos_of_nonneg (by linarith) hp0.le
    have hpow := Real.rpow_nonneg hS.le (2 / p - 1 - 1)
    have e : D1 * (2 / p) * (D1 * (2 / p - 1) * S ^ (2 / p - 1 - 1)) =
        (2 / p - 1) * ((2 / p) * D1 ^ 2 * S ^ (2 / p - 1 - 1)) := by ring
    rw [e]
    exact mul_nonpos_of_nonpos_of_nonneg hneg (by positivity)
  have hc : 0 ≤ (2 / p) * S ^ (2 / p - 1) := by positivity
  have hpp : 0 ≤ p * (p - 1) := by nlinarith
  have step1 : lpS'' p δ a b t * (2 / p) * S ^ (2 / p - 1) ≤
      p * (p - 1) * (S ^ (1 - 2 / p) * B) * ((2 / p) * S ^ (2 / p - 1)) := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_right (le_trans hS'' (mul_le_mul_of_nonneg_left hH hpp)) hc
  have hcancel : S ^ (2 / p - 1) * S ^ (1 - 2 / p) = 1 := by
    rw [← Real.rpow_add hS]; norm_num
  have hp' : p * (2 / p) = 2 := by field_simp
  have step2 : p * (p - 1) * (S ^ (1 - 2 / p) * B) * ((2 / p) * S ^ (2 / p - 1)) =
      2 * (p - 1) * B := by
    calc p * (p - 1) * (S ^ (1 - 2 / p) * B) * ((2 / p) * S ^ (2 / p - 1))
        = (p * (2 / p)) * (p - 1) * B * (S ^ (2 / p - 1) * S ^ (1 - 2 / p)) := by ring
      _ = 2 * (p - 1) * B := by rw [hp', hcancel, mul_one]
  linarith

theorem lpψ_taylor (hn : 0 < n) (hp : 2 ≤ p) (hδ : 0 < δ) (a b : Fin n → ℝ) :
    lpψ p δ a b 1 ≤ lpψ p δ a b 0 + lpψ' p δ a b 0 +
      (p - 1) * (∑ i, (b i ^ 2) ^ (p / 2)) ^ (2 / p) := by
  set B := (∑ i, (b i ^ 2) ^ (p / 2)) ^ (2 / p)
  -- `χ t = ψ' t - 2 (p - 1) B t` does not exceed `χ 0` for `t > 0`
  have hχd : ∀ x : ℝ, HasDerivAt (fun t => lpψ' p δ a b t - 2 * (p - 1) * B * t)
      (lpψ'' p δ a b x - 2 * (p - 1) * B) x := by
    intro x
    have := (hasDerivAt_lpψ' (p := p) hn hδ a b x).sub
      ((hasDerivAt_id x).const_mul (2 * (p - 1) * B))
    exact this.congr_deriv (by simp)
  have hχ : ∀ c : ℝ, 0 < c → lpψ' p δ a b c - 2 * (p - 1) * B * c ≤ lpψ' p δ a b 0 := by
    intro c hc
    obtain ⟨ξ, -, heq⟩ := exists_hasDerivAt_eq_slope
      (fun t => lpψ' p δ a b t - 2 * (p - 1) * B * t) (fun t => lpψ'' p δ a b t - 2 * (p - 1) * B)
      hc (fun x _ => (hχd x).continuousAt.continuousWithinAt) (fun x _ => hχd x)
    have hle := lpψ''_le hn hp hδ a b ξ
    rw [sub_zero, eq_div_iff hc.ne'] at heq
    simp only [mul_zero, sub_zero] at heq
    nlinarith
  have hφd : ∀ x : ℝ, HasDerivAt
      (fun t => lpψ p δ a b t - t * lpψ' p δ a b 0 - (p - 1) * B * t ^ 2)
      (lpψ' p δ a b x - lpψ' p δ a b 0 - 2 * (p - 1) * B * x) x := by
    intro x
    have := ((hasDerivAt_lpψ (p := p) hn hδ a b x).sub
      ((hasDerivAt_id x).mul_const (lpψ' p δ a b 0))).sub
      (((hasDerivAt_id x).pow 2).const_mul ((p - 1) * B))
    exact this.congr_deriv (by simp; ring)
  obtain ⟨ξ, hξ, heq⟩ := exists_hasDerivAt_eq_slope
    (fun t => lpψ p δ a b t - t * lpψ' p δ a b 0 - (p - 1) * B * t ^ 2)
    (fun t => lpψ' p δ a b t - lpψ' p δ a b 0 - 2 * (p - 1) * B * t)
    zero_lt_one (fun x _ => (hφd x).continuousAt.continuousWithinAt) (fun x _ => hφd x)
  have h1 := hχ ξ hξ.1
  simp only [sub_zero, div_one, one_mul, zero_mul, one_pow, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, mul_zero] at heq
  linarith

open Filter Topology

/-- The derivative of the squared `p`-norm at `a` in direction `b`, written with `(a_i²)^{p/2}`. -/
noncomputable def lpJ (p : ℝ) (a b : Fin n → ℝ) : ℝ :=
  2 * (∑ i, (a i ^ 2) ^ (p / 2)) ^ (2 / p - 1) * ∑ i, (a i ^ 2) ^ (p / 2 - 1) * a i * b i

theorem tendsto_rpow_add (x q : ℝ) (hq : 0 < q) :
    Tendsto (fun δ : ℝ => (x + δ) ^ q) (𝓝[>] 0) (𝓝 (x ^ q)) := by
  have h1 : Tendsto (fun δ : ℝ => x + δ) (𝓝 0) (𝓝 x) := by
    simpa using (tendsto_const_nhds (x := x)).add (tendsto_id (x := 𝓝 (0 : ℝ)))
  exact ((Real.continuousAt_rpow_const x q (Or.inr hq.le)).tendsto.comp h1).mono_left
    nhdsWithin_le_nhds

theorem tendsto_lpψ (hp : 2 ≤ p) (a b : Fin n → ℝ) (t : ℝ) :
    Tendsto (fun δ => lpψ p δ a b t) (𝓝[>] 0)
      (𝓝 ((∑ i, ((a i + t * b i) ^ 2) ^ (p / 2)) ^ (2 / p))) := by
  have hp0 : 0 < p := by linarith
  unfold lpψ lpS
  exact (Real.continuousAt_rpow_const _ (2 / p) (Or.inr (by positivity))).tendsto.comp
    (tendsto_finsetSum _ (fun i _ => tendsto_rpow_add _ _ (by positivity)))

theorem tendsto_lpψ' (hp : 2 ≤ p) (a b : Fin n → ℝ) :
    Tendsto (fun δ => lpψ' p δ a b 0) (𝓝[>] 0) (𝓝 (lpJ p a b)) := by
  have hp0 : 0 < p := by linarith
  by_cases ha : a = 0
  · have h0 : ∀ δ, lpψ' p δ a b 0 = 0 := by intro δ; simp [lpψ', lpS', ha]
    have hJ : lpJ p a b = 0 := by simp [lpJ, ha]
    simp only [h0, hJ]
    exact tendsto_const_nhds
  · have hSpos : 0 < ∑ i, (a i ^ 2) ^ (p / 2) := by
      obtain ⟨j, hj⟩ : ∃ j, a j ≠ 0 := by
        by_contra h; push Not at h; exact ha (funext h)
      exact lt_of_lt_of_le (Real.rpow_pos_of_pos (by positivity) _)
        (Finset.single_le_sum (f := fun i => (a i ^ 2) ^ (p / 2))
          (fun i _ => Real.rpow_nonneg (sq_nonneg _) _) (Finset.mem_univ j))
    have hterm : ∀ i, Tendsto (fun δ => p * ((a i + 0 * b i) ^ 2 + δ) ^ (p / 2 - 1) *
        ((a i + 0 * b i) * b i)) (𝓝[>] 0) (𝓝 (p * (a i ^ 2) ^ (p / 2 - 1) * (a i * b i))) := by
      intro i
      simp only [zero_mul, add_zero]
      by_cases hai : a i = 0
      · simp only [hai, zero_mul, mul_zero]; exact tendsto_const_nhds
      · have hc : Tendsto (fun δ : ℝ => (a i ^ 2 + δ) ^ (p / 2 - 1)) (𝓝[>] 0)
            (𝓝 ((a i ^ 2) ^ (p / 2 - 1))) := by
          have h1 : Tendsto (fun δ : ℝ => a i ^ 2 + δ) (𝓝 0) (𝓝 (a i ^ 2)) := by
            simpa using (tendsto_const_nhds (x := a i ^ 2)).add (tendsto_id (x := 𝓝 (0 : ℝ)))
          exact ((Real.continuousAt_rpow_const _ _ (Or.inl (by positivity))).tendsto.comp
            h1).mono_left nhdsWithin_le_nhds
        exact (hc.const_mul p).mul_const _
    have hS' := tendsto_finsetSum Finset.univ (fun i _ => hterm i)
    have hS : Tendsto (fun δ => lpS p δ a b 0 ^ (2 / p - 1)) (𝓝[>] 0)
        (𝓝 ((∑ i, (a i ^ 2) ^ (p / 2)) ^ (2 / p - 1))) := by
      unfold lpS
      simp only [zero_mul, add_zero]
      exact (Real.continuousAt_rpow_const _ _ (Or.inl hSpos.ne')).tendsto.comp
        (tendsto_finsetSum _ (fun i _ => tendsto_rpow_add _ _ (by positivity)))
    have := (hS'.mul_const (2 / p)).mul hS
    unfold lpψ' lpS'
    convert this using 2
    unfold lpJ
    rw [Finset.sum_mul, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    field_simp

theorem lp_sq_smooth_fun (hn : 0 < n) (hp : 2 ≤ p) (a b : Fin n → ℝ) :
    (∑ i, ((a i + b i) ^ 2) ^ (p / 2)) ^ (2 / p) ≤
      (∑ i, (a i ^ 2) ^ (p / 2)) ^ (2 / p) + lpJ p a b +
        (p - 1) * (∑ i, (b i ^ 2) ^ (p / 2)) ^ (2 / p) := by
  have T1 := tendsto_lpψ hp a b 1
  have T0 := tendsto_lpψ hp a b 0
  have T' := tendsto_lpψ' hp a b
  simp only [one_mul, zero_mul, add_zero] at T1 T0
  refine le_of_tendsto_of_tendsto T1 ((T0.add T').add tendsto_const_nhds) ?_
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact lpψ_taylor hn hp hδ a b

end Lemmata.FrankWolfeIntro.Proof
