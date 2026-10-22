module

public import Lemmata.DistributionalLowerBounds.Core.Distributional.FerrersArithmetic
public import Mathlib.Tactic

@[expose] public section

/-!
# Finite probability identities

The hidden family has `d!` elements, so the distributional proof can be modeled
without measure-theoretic machinery.  This module provides the exact finite
expectation and Jensen identities needed by the manuscript.
-/

namespace Lemmata.DistributionalLowerBounds.Core.Distributional

/-- A real-valued probability mass function on a finite type. -/
structure FinitePMF (Ω : Type*) [Fintype Ω] where
  weight : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ weight ω
  sum_weight : ∑ ω, weight ω = 1

namespace FinitePMF

variable {Ω : Type*} [Fintype Ω]

/-- Expectation under a finite PMF. -/
noncomputable def expect (P : FinitePMF Ω) (X : Ω → ℝ) : ℝ :=
  ∑ ω, P.weight ω * X ω

@[simp] lemma expect_const (P : FinitePMF Ω) (c : ℝ) :
    P.expect (fun _ => c) = c := by
  simp only [expect]
  rw [← Finset.sum_mul, P.sum_weight, one_mul]

lemma expect_nonneg (P : FinitePMF Ω) {X : Ω → ℝ}
    (hX : ∀ ω, 0 ≤ X ω) : 0 ≤ P.expect X := by
  apply Finset.sum_nonneg
  intro ω _
  exact mul_nonneg (P.nonneg ω) (hX ω)

lemma expect_mono (P : FinitePMF Ω) {X Y : Ω → ℝ}
    (hXY : ∀ ω, X ω ≤ Y ω) : P.expect X ≤ P.expect Y := by
  apply Finset.sum_le_sum
  intro ω _
  exact mul_le_mul_of_nonneg_left (hXY ω) (P.nonneg ω)

lemma expect_const_mul (P : FinitePMF Ω) (a : ℝ) (X : Ω → ℝ) :
    P.expect (fun ω => a * X ω) = a * P.expect X := by
  simp only [expect]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  ring

/-- Variance identity in unnormalized finite-sum form. -/
lemma expect_centered_sq (P : FinitePMF Ω) (X : Ω → ℝ) :
    P.expect (fun ω => (X ω - P.expect X) ^ 2) =
      P.expect (fun ω => X ω ^ 2) - (P.expect X) ^ 2 := by
  let mu := P.expect X
  change (∑ ω, P.weight ω * (X ω - mu) ^ 2) =
    (∑ ω, P.weight ω * X ω ^ 2) - mu ^ 2
  have hexpand : ∀ ω,
      P.weight ω * (X ω - mu) ^ 2 =
        P.weight ω * X ω ^ 2 - (2 * mu) * (P.weight ω * X ω) +
          mu ^ 2 * P.weight ω := by
    intro ω
    ring
  simp_rw [hexpand]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, P.sum_weight]
  dsimp [mu, expect]
  ring

/-- Jensen's inequality for the square, proved directly from nonnegative
variance. -/
theorem sq_expect_le_expect_sq (P : FinitePMF Ω) (X : Ω → ℝ) :
    (P.expect X) ^ 2 ≤ P.expect (fun ω => X ω ^ 2) := by
  have hvar : 0 ≤ P.expect (fun ω => (X ω - P.expect X) ^ 2) :=
    P.expect_nonneg (fun ω => sq_nonneg _)
  rw [P.expect_centered_sq] at hvar
  linarith

/-- Pointwise loss lower bounds average without any minimax theorem. -/
lemma expect_ge_of_pointwise (P : FinitePMF Ω) {X : Ω → ℝ} {a : ℝ}
    (h : ∀ ω, a ≤ X ω) : a ≤ P.expect X := by
  rw [← P.expect_const a]
  exact P.expect_mono h

/-- Finite-probability wrapper for the arithmetic endgame theorem. -/
theorem expected_loss_from_pointwise_deficit
    (P : FinitePMF Ω) (Delta loss : Ω → ℝ)
    {d rho C : ℝ}
    (hd : 0 < d)
    (hmean : d ^ 2 / 8 ≤ P.expect Delta)
    (hloss : ∀ ω,
      rho ^ 2 * C ^ 2 * Delta ω ^ 2 / (48 * d ^ 2) ≤ loss ω) :
    rho ^ 2 * C ^ 2 * d ^ 2 / 3072 ≤ P.expect loss := by
  apply expected_loss_from_deficit hd hmean
    (P.sq_expect_le_expect_sq Delta)
  have hmono := P.expect_mono hloss
  have heq :
      P.expect (fun ω => rho ^ 2 * C ^ 2 * Delta ω ^ 2 / (48 * d ^ 2)) =
        rho ^ 2 * C ^ 2 * P.expect (fun ω => Delta ω ^ 2) / (48 * d ^ 2) := by
    rw [show (fun ω => rho ^ 2 * C ^ 2 * Delta ω ^ 2 / (48 * d ^ 2)) =
        (fun ω => (rho ^ 2 * C ^ 2 / (48 * d ^ 2)) * Delta ω ^ 2) by
      funext ω
      ring]
    rw [P.expect_const_mul]
    ring
  rw [heq] at hmono
  exact hmono

end FinitePMF
end Lemmata.DistributionalLowerBounds.Core.Distributional
