module

public import Lemmata.CGImprovements.Proof

@[expose] public section

/-!
# Lazy conditional gradients (Theorem 3.15)

A negative oracle answer certifies `h_t ≤ φ_t`, so `φ_t ≥ h_t/2` throughout. A positive answer
gains at least `φ_t²/(2 K² L D²) ≥ h_t²/(8 K² L D²)`, so after `k` positive answers
`h_t ≤ 8 K² L D²/(k + 8)`; and after `⌈log₂ (φ₀/ε)⌉₊ + 1` negative answers `h_t ≤ ε`.
-/

namespace Lemmata.CGImprovements

open Lemmata.FrankWolfe

universe u

namespace Proof

theorem lazy_rate : LazyRate.{u} := by
  intro E _ _ C f L K x φ hC hCc hconv hsm hK hrun xStar hxs hφ0 hφ0' ε hε t ht
  set D := Metric.diam C with hD
  set Q : ℝ := 8 * K ^ 2 * L * D ^ 2 with hQ
  set h : ℕ → ℝ := fun t => f (x t) - f xStar with hh
  have hbdd := hC.isBounded
  have hxC : ∀ t, x t ∈ C := by
    intro t
    induction t with
    | zero => exact hrun.1
    | succ t ih =>
      rcases hrun.2 t with ⟨v, hv, -, γ, hγ, hx', -, -⟩ | ⟨-, hx', -⟩
      · rw [hx']; exact hCc.add_smul_sub_mem ih hv hγ
      · rw [hx']; exact ih
  have hh0 : ∀ t, 0 ≤ h t := fun t => by simp only [hh]; linarith [hxs.2 _ (hxC t)]
  have hgap : ∀ t, h t ≤ fderiv ℝ f (x t) (x t - xStar) := fun t => by
    have := add_fderiv_le_of_convexOn hconv hsm.1 (x t) xStar
    simp only [hh]; rw [map_sub] at this ⊢; linarith
  have hmono : ∀ t, h (t + 1) ≤ h t := fun t => by
    rcases hrun.2 t with ⟨v, hv, -, γ, hγ, hx', hq, -⟩ | ⟨-, hx', -⟩
    · have := hq 0 ⟨le_rfl, zero_le_one⟩
      simp only [hh]; simp at this; linarith
    · simp only [hh, hx', le_refl]
  have hφb : ∀ t, 0 ≤ φ t ∧ φ t ≤ φ 0 := by
    intro t
    induction t with
    | zero => exact ⟨by linarith [hh0 0], le_rfl⟩
    | succ t ih =>
      rcases hrun.2 t with ⟨-, -, -, -, -, -, -, hφ'⟩ | ⟨-, -, hφ'⟩
      · rw [hφ']; exact ih
      · rw [hφ']; constructor <;> linarith [ih.1, ih.2]
  have hinv : ∀ t, h t ≤ 2 * φ t := by
    intro t
    induction t with
    | zero => simp only [hh]; linarith
    | succ t ih =>
      rcases hrun.2 t with ⟨-, -, -, -, -, -, -, hφ'⟩ | ⟨hcert, hx', hφ'⟩
      · rw [hφ']; linarith [hmono t]
      · rw [hφ']
        have h1 := hcert xStar hxs.1
        have h2 := hgap t
        have e : h (t + 1) = h t := by simp only [hh, hx']
        linarith
  -- the degenerate case `L D² = 0`
  rcases eq_or_lt_of_le (by positivity : (0 : ℝ) ≤ L * D ^ 2) with hK0 | hKpos
  · have := hinv t
    have := (hφb t).2
    have : h t ≤ 0 := by linarith
    simp only [hh] at this
    linarith
  have hQpos : 0 < Q := by
    rw [hQ]; have : (0 : ℝ) < K ^ 2 := by positivity
    nlinarith
  -- progress of a positive answer
  have hprog : ∀ t, (∃ v ∈ C, φ t / K < fderiv ℝ f (x t) (x t - v) ∧ ∃ γ ∈ Set.Icc (0 : ℝ) 1,
      x (t + 1) = x t + γ • (v - x t) ∧
      (∀ s ∈ Set.Icc (0 : ℝ) 1, f (x (t + 1)) ≤
        f (x t) - s * fderiv ℝ f (x t) (x t - v) + s ^ 2 * L / 2 * ‖v - x t‖ ^ 2) ∧
      φ (t + 1) = φ t) → h (t + 1) ≤ h t - h t ^ 2 / Q := by
    rintro t ⟨v, hv, hgv, γ, hγ, hx', hq, -⟩
    have hK1 : (0 : ℝ) < K := by linarith
    set s := φ t / (K * (L * D ^ 2)) with hs
    have hs0 : 0 ≤ s := div_nonneg (hφb t).1 (by positivity)
    have hs1 : s ≤ 1 := by
      rw [hs, div_le_one (by positivity)]
      have := (hφb t).2
      nlinarith
    have h1 := hq s ⟨hs0, hs1⟩
    have hd : ‖v - x t‖ ≤ D := by
      rw [← dist_eq_norm]; exact Metric.dist_le_diam_of_mem hbdd hv (hxC t)
    have hd2 : s ^ 2 * L / 2 * ‖v - x t‖ ^ 2 ≤ s ^ 2 * (L * D ^ 2) / 2 := by
      have := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hd 2)
        (by positivity : (0 : ℝ) ≤ s ^ 2 * L)
      nlinarith
    have hg : s * (φ t / K) ≤ s * fderiv ℝ f (x t) (x t - v) :=
      mul_le_mul_of_nonneg_left hgv.le hs0
    -- `s φ/K - s² L D²/2 = φ²/(2 K² L D²)`
    have he : s * (φ t / K) - s ^ 2 * (L * D ^ 2) / 2 = φ t ^ 2 / (2 * K ^ 2 * (L * D ^ 2)) := by
      rw [hs]; field_simp; ring
    have hφh : h t ^ 2 / Q ≤ φ t ^ 2 / (2 * K ^ 2 * (L * D ^ 2)) := by
      rw [hQ, div_le_div_iff₀ (by positivity) (by positivity)]
      have := hinv t
      have := pow_le_pow_left₀ (hh0 t) this 2
      nlinarith [this]
    simp only [hh]
    linarith
  -- counting positive and negative answers
  set n₀ := ⌈Real.logb 2 (φ 0 / ε)⌉₊ with hn₀
  have hφε : φ 0 / 2 ^ n₀ ≤ ε := by
    rcases le_or_gt (φ 0) 0 with hφ | hφ
    · have : φ 0 / 2 ^ n₀ ≤ 0 := div_nonpos_of_nonpos_of_nonneg hφ (by positivity)
      linarith
    · rw [div_le_iff₀ (by positivity)]
      have h1 : Real.logb 2 (φ 0 / ε) ≤ n₀ := Nat.le_ceil _
      have h2 : φ 0 / ε ≤ (2 : ℝ) ^ (n₀ : ℝ) := by
        rw [← Real.logb_le_logb (b := 2) (by norm_num) (div_pos hφ hε) (by positivity),
          Real.logb_rpow (by norm_num) (by norm_num)]
        exact h1
      rw [Real.rpow_natCast, div_le_iff₀ hε] at h2
      linarith
  have hstate : ∀ t, ∃ P N : ℕ, P + N = t ∧ h t * (P + 8) ≤ Q ∧ φ t = φ 0 / 2 ^ N ∧
      (n₀ + 1 ≤ N → h t ≤ ε) := by
    intro t
    induction t with
    | zero =>
      refine ⟨0, 0, rfl, ?_, by simp, fun h => absurd h (by omega)⟩
      have h1 := hinv 0
      have h2 : (1 : ℝ) ≤ K ^ 2 := by nlinarith
      have h3 : L * D ^ 2 ≤ K ^ 2 * (L * D ^ 2) := by nlinarith
      push_cast
      rw [hQ]
      nlinarith
    | succ t ih =>
      obtain ⟨P, N, hPN, hbd, hφN, hε'⟩ := ih
      rcases hrun.2 t with hpos | ⟨hcert, hx', hφ'⟩
      · have hp := hprog t hpos
        obtain ⟨-, -, -, -, -, -, -, hφ'⟩ := hpos
        refine ⟨P + 1, N, by omega, ?_, by rw [hφ', hφN], fun hN => (hmono t).trans (hε' hN)⟩
        -- `φ(h) = h - h²/Q` is increasing on `[0, Q/2]`
        set b := Q / ((P : ℝ) + 8) with hb
        have hP8 : (0 : ℝ) < (P : ℝ) + 8 := by positivity
        have hhb : h t ≤ b := by rw [hb, le_div_iff₀ hP8]; exact hbd
        have hbQ : b ≤ Q / 2 := by
          rw [hb, div_le_div_iff₀ hP8 (by norm_num)]
          have : (0 : ℝ) ≤ P := Nat.cast_nonneg P
          nlinarith
        have hmon : h t - h t ^ 2 / Q ≤ b - b ^ 2 / Q := by
          have e : (b - b ^ 2 / Q) - (h t - h t ^ 2 / Q) = (b - h t) * (Q - (b + h t)) / Q := by
            field_simp; ring
          have : 0 ≤ (b - h t) * (Q - (b + h t)) / Q :=
            div_nonneg (mul_nonneg (by linarith) (by linarith [hh0 t])) hQpos.le
          linarith
        have hfin : (b - b ^ 2 / Q) * ((P : ℝ) + 9) ≤ Q := by
          have e : b - b ^ 2 / Q = Q * ((P : ℝ) + 7) / ((P : ℝ) + 8) ^ 2 := by
            rw [hb]; field_simp; ring
          rw [e, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
          nlinarith
        have h1 : h (t + 1) ≤ b - b ^ 2 / Q := hp.trans hmon
        have h2 : 0 ≤ (P : ℝ) + 9 := by positivity
        push_cast
        nlinarith [mul_le_mul_of_nonneg_right h1 h2]
      · have e : h (t + 1) = h t := by simp only [hh, hx']
        refine ⟨P, N + 1, by omega, by rw [e]; exact hbd, ?_, fun hN => ?_⟩
        · rw [hφ', hφN, pow_succ]; field_simp
        · rw [e]
          rcases Nat.lt_or_ge N (n₀ + 1) with hlt | hge
          · have hN0 : N = n₀ := by omega
            have h1 := hcert xStar hxs.1
            have h2 := hgap t
            rw [hφN, hN0] at h1
            linarith
          · exact hε' hge
  obtain ⟨P, N, hPN, hbd, -, hεN⟩ := hstate t
  set P₀ := ⌈Q / ε⌉₊ with hP₀
  rcases Nat.lt_or_ge P P₀ with hlt | hge
  · exact hεN (by omega)
  · have h1 : Q ≤ ε * P₀ := by
      have := Nat.le_ceil (Q / ε)
      rw [div_le_iff₀ hε] at this
      linarith
    have h2 : (P₀ : ℝ) ≤ P := by exact_mod_cast hge
    have h3 : h t * ((P : ℝ) + 8) ≤ ε * ((P : ℝ) + 8) := by nlinarith
    have hP8 : (0 : ℝ) < (P : ℝ) + 8 := by positivity
    have := le_of_mul_le_mul_right h3 hP8
    simpa [hh] using this

end Proof

end Lemmata.CGImprovements
