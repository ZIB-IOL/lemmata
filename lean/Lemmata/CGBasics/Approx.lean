module

public import Lemmata.CGBasics.Statement
public import Lemmata.FrankWolfe.Proof.Calculus

@[expose] public section

/-!
# Approximate linear minimization (Theorem 2.6)

For every `s ∈ [0, 1]`, the step condition, approximate optimality of `v_t` and convexity give
`h_{t+1} ≤ (1 - s) h_t + s ε_t + s² L D²/2`. With `s = 2/(t + 3)` and `ε_t = L D² δ/(t + 3)`, the
error term is `s² L D² δ/2`, and the open-loop induction gives `h_t ≤ 2 L D² (1 + δ)/(t + 3)`.
-/

namespace Lemmata.CGBasics

open Lemmata.FrankWolfe

universe u

namespace Proof

theorem approx_step (K : ℝ) (hK : 0 ≤ K) (t : ℝ) (ht : 0 ≤ t) :
    (1 - 2 / (t + 3)) * (2 * K / (t + 3)) + (2 / (t + 3)) ^ 2 * K / 2 ≤ 2 * K / (t + 4) := by
  have h3 : 0 < t + 3 := by linarith
  have h4 : 0 < t + 4 := by linarith
  have e : 2 * K / (t + 4) - ((1 - 2 / (t + 3)) * (2 * K / (t + 3)) + (2 / (t + 3)) ^ 2 * K / 2) =
      2 * K / ((t + 4) * (t + 3) ^ 2) := by
    field_simp
    ring
  have : 0 ≤ 2 * K / ((t + 4) * (t + 3) ^ 2) := by positivity
  linarith

theorem approximate_oracle_rate : ApproximateOracleRate.{u} := by
  intro E _ _ C f L δ x v γ hC hCc hconv hsm hδ hx0 hrun xStar hxs
  set D := Metric.diam C with hD
  have hbdd := hC.isBounded
  have hxC : ∀ t, x t ∈ C := by
    intro t
    induction t with
    | zero => exact hx0
    | succ t ih =>
      obtain ⟨hv, -, hγ, hx, -⟩ := hrun t
      rw [hx]
      exact hCc.add_smul_sub_mem ih hv hγ
  have hL0 : (0 : ℝ) ≤ L := NNReal.coe_nonneg L
  have hone : ∀ t : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) 1, f (x (t + 1)) - f xStar ≤
      (1 - s) * (f (x t) - f xStar) + s * (L * D ^ 2 * δ / ((t : ℝ) + 3)) +
        s ^ 2 * L / 2 * D ^ 2 := by
    intro t s hs
    obtain ⟨hv, happ, -, -, hstep⟩ := hrun t
    have h1 := hstep s hs
    have h2 := happ xStar hxs.1
    have h3 := add_fderiv_le_of_convexOn hconv hsm.1 (x t) xStar
    have hd : ‖v t - x t‖ ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ (norm_nonneg _)
      (by rw [← dist_eq_norm]; exact Metric.dist_le_diam_of_mem hbdd hv (hxC t)) 2
    have h4 : s ^ 2 * L / 2 * ‖v t - x t‖ ^ 2 ≤ s ^ 2 * L / 2 * D ^ 2 :=
      mul_le_mul_of_nonneg_left hd (by positivity)
    rw [map_sub] at h1 h3
    have h5 := mul_le_mul_of_nonneg_left h2 hs.1
    have h6 : s * (fderiv ℝ f (x t) xStar - fderiv ℝ f (x t) (x t)) ≤ s * (f xStar - f (x t)) :=
      mul_le_mul_of_nonneg_left (by linarith) hs.1
    nlinarith
  intro t ht
  set K : ℝ := L * D ^ 2 * (1 + δ) with hK
  have hK0 : 0 ≤ K := by positivity
  have goal_eq : ∀ n : ℕ, 2 * L * D ^ 2 * (1 + δ) / ((n : ℝ) + 3) = 2 * K / ((n : ℝ) + 3) := by
    intro n; rw [hK]; ring
  rw [goal_eq]
  induction t, ht using Nat.le_induction with
  | base =>
    have := hone 0 1 ⟨zero_le_one, le_rfl⟩
    have hLD : 0 ≤ (L : ℝ) * D ^ 2 * δ := by positivity
    norm_num at this ⊢
    rw [hK]
    nlinarith
  | succ t ht ih =>
    have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
    set s : ℝ := 2 / ((t : ℝ) + 3) with hs
    have hsI : s ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨by positivity, by rw [hs, div_le_one (by positivity)]; linarith⟩
    have h1 := hone t s hsI
    have herr : s * (L * D ^ 2 * δ / ((t : ℝ) + 3)) + s ^ 2 * L / 2 * D ^ 2 = s ^ 2 * K / 2 := by
      rw [hs, hK]; field_simp; ring
    have h2 : (1 - s) * (f (x t) - f xStar) ≤ (1 - s) * (2 * K / ((t : ℝ) + 3)) :=
      mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr hsI.2)
    have h3 := approx_step K hK0 t ht0
    have ecast : ((t + 1 : ℕ) : ℝ) + 3 = (t : ℝ) + 4 := by push_cast; ring
    rw [ecast]
    rw [← hs] at h3
    linarith

end Proof

end Lemmata.CGBasics
