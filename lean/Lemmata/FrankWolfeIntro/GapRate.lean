module

public import Lemmata.FrankWolfeIntro.Proof

@[expose] public section

/-!
# Theorem 4.5: the Frank–Wolfe gap

Summing `γ_k g_k ≤ h_k - h_{k+1} + γ_k² L D²/2` over the second half `k₀ ≤ k ≤ t` of the run, with
`k₀ = ⌊(t+2)/2⌋`, `h_{k₀} ≤ 2 L D²/(k₀+2)` and `Σ 1/(k+2)² ≤ 1/(k₀+1) - 1/(t+2)`, bounds the
smallest
gap `g_k` in that window by `6.75 L D²/(t+2)`.
-/

namespace Lemmata.FrankWolfeIntro

open Lemmata.FrankWolfe

universe u

namespace Proof

/-- The final inequality: `4N²(1/a + 1/(a-1) - 1/N) ≤ 27 m` for `N = t + 2 ≥ 3`, `a = ⌊N/2⌋ + 2`,
`m = N - a + 1`, written with `k₀ = ⌊N/2⌋`. -/
theorem key_ineq (t : ℕ) (ht : 1 ≤ t) :
    4 * ((t : ℝ) + 2) ^ 2 * (1 / (((t + 2) / 2 : ℕ) + 2 : ℝ) + 1 / (((t + 2) / 2 : ℕ) + 1 : ℝ) -
      1 / ((t : ℝ) + 2)) ≤ 27 * ((t : ℝ) + 1 - ((t + 2) / 2 : ℕ)) := by
  rcases Nat.even_or_odd t with ⟨n, hn⟩ | ⟨n, hn⟩
  · -- t = 2n, N = 2n + 2, k₀ = n + 1
    subst hn
    have hk : ((n + n + 2) / 2 : ℕ) = n + 1 := by omega
    rw [hk]; push_cast
    have hn1 : (1 : ℝ) ≤ n := by
      have : 1 ≤ n := by omega
      exact_mod_cast this
    rw [div_add_div _ _ (by positivity) (by positivity),
      div_sub_div _ _ (by positivity) (by positivity)]
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith [hn1, sq_nonneg (n : ℝ),
      mul_pos (by linarith : (0 : ℝ) < n) (by linarith : (0 : ℝ) < n)]
  · -- t = 2n + 1, N = 2n + 3, k₀ = n + 1
    subst hn
    have hk : ((2 * n + 1 + 2) / 2 : ℕ) = n + 1 := by omega
    rw [hk]; push_cast
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    rw [div_add_div _ _ (by positivity) (by positivity),
      div_sub_div _ _ (by positivity) (by positivity)]
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith [hn0, sq_nonneg (n : ℝ), mul_nonneg hn0 hn0, mul_nonneg (mul_nonneg hn0 hn0) hn0]

/-- The gap bound for real sequences: if `γ_k g_k ≤ h_k - h_{k+1} + γ_k² K/2` with `γ_k = 2/(k+2)`,
`0 ≤ h_k`, and `h_k ≤ 2K/(k+2)` for `k ≥ 1`, then for `t ≥ 1` some `g_τ` with `τ ≤ t` is at most
`27/4 · K/(t+2)`. -/
theorem gap_rate_abstract {g h : ℕ → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hA : ∀ k : ℕ, 2 / ((k : ℝ) + 2) * g k ≤ h k - h (k + 1) + (2 / ((k : ℝ) + 2)) ^ 2 * K / 2)
    (hB : ∀ k : ℕ, 1 ≤ k → h k ≤ 2 * K / ((k : ℝ) + 2)) (hC : ∀ k, 0 ≤ h k)
    (t : ℕ) (ht : 1 ≤ t) : ∃ τ ≤ t, g τ ≤ 27 / 4 * K / ((t : ℝ) + 2) := by
  set k0 := (t + 2) / 2 with hk0
  have hk01 : 1 ≤ k0 := by omega
  have hk0t : k0 ≤ t := by omega
  obtain ⟨τ, hτ, hmin⟩ := Finset.exists_min_image (Finset.Icc k0 t) g
    ⟨k0, Finset.mem_Icc.mpr ⟨le_rfl, hk0t⟩⟩
  refine ⟨τ, (Finset.mem_Icc.mp hτ).2, ?_⟩
  have hN : (0 : ℝ) < (t : ℝ) + 2 := by positivity
  rcases le_or_gt (g τ) 0 with hneg | hpos
  · exact hneg.trans (by positivity)
  -- telescoping the per-step inequality
  have hsum : ∀ n, k0 ≤ n → ∑ k ∈ Finset.Ico k0 n, 2 / ((k : ℝ) + 2) * g k ≤
      h k0 - h n + K / 2 * ∑ k ∈ Finset.Ico k0 n, (2 / ((k : ℝ) + 2)) ^ 2 := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => simp
    | succ n hn ih =>
      rw [Finset.sum_Ico_succ_top hn, Finset.sum_Ico_succ_top hn]
      have := hA n
      linarith
  -- `Σ 1/(k+2)² ≤ 1/(k₀+1) - 1/(n+1)`
  have hsq : ∀ n, k0 ≤ n → ∑ k ∈ Finset.Ico k0 n, (2 / ((k : ℝ) + 2)) ^ 2 ≤
      4 * (1 / ((k0 : ℝ) + 1) - 1 / ((n : ℝ) + 1)) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => simp
    | succ n hn ih =>
      rw [Finset.sum_Ico_succ_top hn]
      have e1 : (2 / ((n : ℝ) + 2)) ^ 2 = 4 / (((n : ℝ) + 2) ^ 2) := by rw [div_pow]; norm_num
      have e2 : 4 * (1 / ((n : ℝ) + 1) - 1 / ((n : ℝ) + 1 + 1)) =
          4 / (((n : ℝ) + 1) * ((n : ℝ) + 2)) := by field_simp; ring
      have hstep : (2 / ((n : ℝ) + 2)) ^ 2 ≤ 4 * (1 / ((n : ℝ) + 1) - 1 / ((n : ℝ) + 1 + 1)) := by
        rw [e1, e2, div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
      push_cast
      linarith
  have hS := hsum (t + 1) (by omega)
  have hQ := hsq (t + 1) (by omega)
  -- the lower bound by the minimum
  have hlow : g τ * (((t + 1 - k0 : ℕ) : ℝ) * (2 / ((t : ℝ) + 2))) ≤
      ∑ k ∈ Finset.Ico k0 (t + 1), 2 / ((k : ℝ) + 2) * g k := by
    have hcard := Finset.card_nsmul_le_sum (Finset.Ico k0 (t + 1))
      (fun k => 2 / ((k : ℝ) + 2) * g k) (2 / ((t : ℝ) + 2) * g τ) (fun k hk => by
        have hk' := Finset.mem_Ico.mp hk
        have hkt : (k : ℝ) ≤ t := by exact_mod_cast Nat.lt_succ_iff.mp hk'.2
        have hγk : 2 / ((t : ℝ) + 2) ≤ 2 / ((k : ℝ) + 2) :=
          div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
        have hgk : g τ ≤ g k := hmin k (Finset.mem_Icc.mpr ⟨hk'.1, Nat.lt_succ_iff.mp hk'.2⟩)
        nlinarith [mul_le_mul hγk hgk hpos.le (by positivity)])
    rw [Nat.card_Ico, nsmul_eq_mul] at hcard
    nlinarith [hcard]
  have hB0 := hB k0 hk01
  have hCt := hC (t + 1)
  have hkey := key_ineq t ht
  rw [← hk0] at hkey
  have hm : ((t + 1 - k0 : ℕ) : ℝ) = (t : ℝ) + 1 - k0 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [hm] at hlow
  have hmpos : (0 : ℝ) < (t : ℝ) + 1 - k0 := by
    have : (k0 : ℝ) ≤ t := by exact_mod_cast hk0t
    linarith
  -- `g τ · m · 2/N ≤ 2K(1/a + 1/(a-1) - 1/N)` and `4N²(…) ≤ 27 m`
  push_cast at hQ
  have hupper : g τ * (((t : ℝ) + 1 - k0) * (2 / ((t : ℝ) + 2))) ≤
      2 * K * (1 / ((k0 : ℝ) + 2) + 1 / ((k0 : ℝ) + 1) - 1 / ((t : ℝ) + 2)) := by
    have : (t : ℝ) + 1 + 1 = (t : ℝ) + 2 := by ring
    rw [this] at hQ
    have hKQ := mul_le_mul_of_nonneg_left hQ (by positivity : (0 : ℝ) ≤ K / 2)
    have e : 2 * K * (1 / ((k0 : ℝ) + 2) + 1 / ((k0 : ℝ) + 1) - 1 / ((t : ℝ) + 2)) =
        2 * K / ((k0 : ℝ) + 2) + K / 2 * (4 * (1 / ((k0 : ℝ) + 1) - 1 / ((t : ℝ) + 2))) := by ring
    rw [e]
    linarith [hS, hKQ, hB0, hCt, hlow]
  set Q := 1 / ((k0 : ℝ) + 2) + 1 / ((k0 : ℝ) + 1) - 1 / ((t : ℝ) + 2) with hQdef
  set m := (t : ℝ) + 1 - k0 with hmdef
  set N := (t : ℝ) + 2 with hNdef
  have h1 : g τ * m * 2 ≤ 2 * K * Q * N := by
    have := mul_le_mul_of_nonneg_right hupper hN.le
    rw [show g τ * (m * (2 / N)) * N = g τ * m * 2 by field_simp] at this
    linarith
  have h2 : g τ * m * (4 * N) ≤ 27 * K * m := by
    have := mul_le_mul_of_nonneg_left hkey hK
    nlinarith [h1, hN, hK]
  rw [show 27 / 4 * K / N = 27 * K * m / (4 * N * m) by field_simp]
  rw [le_div_iff₀ (by positivity)]
  nlinarith [h2]

theorem gap_rate : GapRate.{u} := by
  intro E _ _ C lmo f L h xStar hxs x₀ hx₀ t ht
  have hγI : ∀ k : ℕ, ∀ y ∈ C, (openLoopStep 2 : ℕ → E → ℝ) k y ∈ Set.Icc (0 : ℝ) 1 :=
    fun k _ _ => by
      show (2 : ℝ) / ((k : ℝ) + 2) ∈ Set.Icc (0 : ℝ) 1
      exact ⟨by positivity, by
        rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]⟩
  set x := fwIterates lmo (fderiv ℝ f) (openLoopStep 2) x₀ with hx
  have hmem : ∀ k, x k ∈ C := fwIterates_mem h.convex h.lmo_mem (fderiv ℝ f) hγI hx₀
  have hK : (0 : ℝ) ≤ L * Metric.diam C ^ 2 := by positivity
  have hA : ∀ k : ℕ, 2 / ((k : ℝ) + 2) * fderiv ℝ f (x k) (x k - lmo (fderiv ℝ f (x k))) ≤
      (f (x k) - f xStar) - (f (x (k + 1)) - f xStar) +
        (2 / ((k : ℝ) + 2)) ^ 2 * (L * Metric.diam C ^ 2) / 2 := by
    intro k
    have hprog := h.isSmooth.progress (x k) (lmo (fderiv ℝ f (x k))) (2 / ((k : ℝ) + 2))
    have hd : ‖lmo (fderiv ℝ f (x k)) - x k‖ ≤ Metric.diam C := by
      rw [← dist_eq_norm]
      exact Metric.dist_le_diam_of_mem h.isCompact.isBounded (h.lmo_mem _) (hmem k)
    have hd2 := pow_le_pow_left₀ (norm_nonneg _) hd 2
    have hc : (0 : ℝ) ≤ (2 / ((k : ℝ) + 2)) ^ 2 * L / 2 := by positivity
    have hsucc : x (k + 1) = x k + (2 / ((k : ℝ) + 2)) • (lmo (fderiv ℝ f (x k)) - x k) := rfl
    rw [hsucc]
    nlinarith [mul_le_mul_of_nonneg_left hd2 hc]
  have hB : ∀ k : ℕ, 1 ≤ k → f (x k) - f xStar ≤ 2 * (L * Metric.diam C ^ 2) / ((k : ℝ) + 2) := by
    intro k hk
    have := rate_of_dominated h (step := openLoopStep 2) hγI (fun _ _ _ => Or.inl le_rfl) hxs hx₀
      k hk
    have e : 2 * (L : ℝ) * Metric.diam C ^ 2 = 2 * (L * Metric.diam C ^ 2) := by ring
    rw [e] at this
    exact this
  have hC : ∀ k, 0 ≤ f (x k) - f xStar := fun k => by linarith [hxs.2 _ (hmem k)]
  obtain ⟨τ, hτ, hb⟩ := gap_rate_abstract
    (g := fun k => fderiv ℝ f (x k) (x k - lmo (fderiv ℝ f (x k))))
    (h := fun k => f (x k) - f xStar) hK hA hB hC t ht
  refine ⟨τ, hτ, ?_⟩
  rw [fwGap_eq_lmo h.isLMO]
  have e : 27 / 4 * (L : ℝ) * Metric.diam C ^ 2 / ((t : ℝ) + 2) =
      27 / 4 * (L * Metric.diam C ^ 2) / ((t : ℝ) + 2) := by ring
  rw [e]
  exact hb

end Proof

end Lemmata.FrankWolfeIntro
