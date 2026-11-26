module

public import Lemmata.FrankWolfeIntro.Cocoercive

@[expose] public section

/-!
# Lemma 4.10: progress from the adaptive test

Lemma 4.9 at `(x⁺, x)`, with `x - x⁺ = γ (x - v)`, gives
`f x - f x⁺ ≥ γ a + (g - a)²/(2 L d²)`, from
which both cases follow.
-/

namespace Lemmata.FrankWolfeIntro

open Lemmata.FrankWolfe

universe u

namespace Proof

theorem adaptive_progress : AdaptiveProgress.{u} := by
  intro E _ _ f L M hconv hsm hL hM x v γ hd hg hγ ha
  set g := fderiv ℝ f x (x - v) with hgdef
  set d := ‖v - x‖ with hddef
  set y := x + γ • (v - x) with hy
  set a := fderiv ℝ f y (x - v) with hadef
  have hL' : (0 : ℝ) < L := hL
  have hM' : (0 : ℝ) < M := hM
  have hγ0 : 0 ≤ γ := by rw [hγ]; exact le_min (by positivity) zero_le_one
  -- the basic inequality `f x - f y ≥ γ a + (g - a)² / (2 L d²)`
  have hbase : γ * a + (g - a) ^ 2 / (2 * L * d ^ 2) ≤ f x - f y := by
    rcases eq_or_lt_of_le hγ0 with h0 | hpos
    · -- `γ = 0`: then `g = 0`, `y = x` and `a = g`
      have hγz : γ = 0 := h0.symm
      have hyx : y = x := by rw [hy, hγz, zero_smul, add_zero]
      have hag : a = g := by rw [hadef, hyx]
      have hg0 : g = 0 := by
        have : min (g / (M * d ^ 2)) 1 = 0 := by rw [← hγ, hγz]
        rcases min_choice (g / (M * d ^ 2)) 1 with h | h
        · rw [h] at this
          have := (div_eq_zero_iff.mp this)
          rcases this with h' | h'
          · exact h'
          · exfalso; have : (0 : ℝ) < M * d ^ 2 := by positivity
            linarith
        · rw [h] at this; norm_num at this
      rw [hyx, hag, hg0, hγz]; simp
    · have h49 := smoothness_revisited f L hconv hsm hL y x
      have hxy : x - y = γ • (x - v) := by rw [hy]; module
      rw [hxy] at h49
      simp only [map_smul, smul_eq_mul, norm_smul, Real.norm_of_nonneg hγ0] at h49
      have happ : (fderiv ℝ f x - fderiv ℝ f y) (x - v) = g - a := rfl
      rw [happ, ← hadef, norm_sub_rev x v, ← hddef] at h49
      have hfrac : (γ * (g - a)) ^ 2 / (2 * L * (γ * d) ^ 2) = (g - a) ^ 2 / (2 * L * d ^ 2) := by
        field_simp
      rw [hfrac] at h49
      linarith
  refine ⟨fun hle => ?_, fun h1 hLM => ?_⟩
  · -- `γ = g/(M d²)`
    have hγv : γ = g / (M * d ^ 2) := by rw [hγ]; exact min_eq_left hle
    set K := max (L : ℝ) M with hK
    have hKL : (L : ℝ) ≤ K := le_max_left _ _
    have hKM : (M : ℝ) ≤ K := le_max_right _ _
    have hKpos : 0 < K := lt_of_lt_of_le hL' hKL
    have h1 : g * a / (K * d ^ 2) ≤ γ * a := by
      rw [hγv, div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_mul_of_nonneg_right hKM (by positivity))
    have h2 : (g - a) ^ 2 / (2 * K * d ^ 2) ≤ (g - a) ^ 2 / (2 * L * d ^ 2) :=
      div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by nlinarith [sq_nonneg d])
    have e : (g ^ 2 + a ^ 2) / (2 * K * d ^ 2) =
        g * a / (K * d ^ 2) + (g - a) ^ 2 / (2 * K * d ^ 2) := by field_simp; ring
    show (g ^ 2 + a ^ 2) / (2 * max (L : ℝ) M * d ^ 2) ≤ f x - f y
    rw [← hK, e]; linarith
  · -- `γ = 1`, `M ≥ L`: then `g ≥ M d² ≥ L d² > 0`
    have hge : 1 ≤ g / (M * d ^ 2) := by
      by_contra hlt; push Not at hlt
      have : γ = g / (M * d ^ 2) := by rw [hγ]; exact min_eq_left hlt.le
      rw [h1] at this; linarith
    have hMd : (M : ℝ) * d ^ 2 ≤ g := by rwa [le_div_iff₀ (by positivity), one_mul] at hge
    have hLM' : (L : ℝ) ≤ M := hLM
    have hgpos : 0 < g := lt_of_lt_of_le (by positivity) hMd
    have hLd : (L : ℝ) * d ^ 2 ≤ g := le_trans (by nlinarith [sq_nonneg d]) hMd
    have h2 : (g - a) ^ 2 / (2 * g) ≤ (g - a) ^ 2 / (2 * L * d ^ 2) :=
      div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by nlinarith)
    have e : g / 2 + a ^ 2 / (2 * g) = a + (g - a) ^ 2 / (2 * g) := by field_simp; ring
    rw [h1, one_mul] at hbase
    show g / 2 + a ^ 2 / (2 * g) ≤ f x - f y
    rw [e]; linarith

end Proof

end Lemmata.FrankWolfeIntro
