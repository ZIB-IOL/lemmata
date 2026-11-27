module

public import Lemmata.LazyCG.Statement
public import Lemmata.FrankWolfe.Proof.Calculus

@[expose] public section

/-!
# Weak separation and lazy conditional gradients (Algorithm 2, Theorem 3.1)
-/

namespace Lemmata.LazyCG

open Lemmata.FrankWolfe

universe u

namespace Proof

theorem lp_sep_via_lp_correct : LPSepViaLPCorrect.{u} := by
  intro E _ _ V cache c x Φ K y₀ ans hcache hy₀ hmin hK hΦ hans
  rcases hans with ⟨y, hy, hgt, rfl⟩ | ⟨-, ⟨hgt, rfl⟩ | ⟨hle, rfl⟩⟩
  · exact ⟨hcache hy, hgt⟩
  · exact ⟨hy₀, hgt⟩
  · intro z hz
    have hcz : c y₀ ≤ c z := by
      have hsub : convexHull ℝ V ⊆ {w | c y₀ ≤ c w} :=
        convexHull_min (fun v hv => hmin v hv)
          (convex_halfSpace_ge (c : E →ₗ[ℝ] ℝ).isLinear (c y₀))
      exact hsub hz
    have hΦK : Φ / K ≤ Φ := div_le_self hΦ hK
    rw [map_sub] at hle ⊢
    linarith

/-- The step of the bound on `Φ_t` in Theorem 3.1. -/
theorem lcg_phi_step (M K t : ℝ) (hM : 0 ≤ M) (hK : 0 < K) (ht : 0 ≤ t) :
    2 * M * (K ^ 2 + 1) / (t + K ^ 2 + 2) +
        M / 2 * (2 * (K ^ 2 + 1) / (K * (t + K ^ 2 + 2))) ^ 2 ≤
      2 * M * (K ^ 2 + 1) / (t + 1 + K ^ 2 + 2) *
        (1 + 2 * (K ^ 2 + 1) / (K * (t + K ^ 2 + 2)) / K) := by
  have hs : 0 < t + K ^ 2 + 2 := by positivity
  have e : 2 * M * (K ^ 2 + 1) / (t + 1 + K ^ 2 + 2) *
        (1 + 2 * (K ^ 2 + 1) / (K * (t + K ^ 2 + 2)) / K) -
      (2 * M * (K ^ 2 + 1) / (t + K ^ 2 + 2) +
        M / 2 * (2 * (K ^ 2 + 1) / (K * (t + K ^ 2 + 2))) ^ 2) =
      2 * M * (K ^ 2 + 1) * (t + 1) /
        (K ^ 2 * (t + K ^ 2 + 2) ^ 2 * (t + 1 + K ^ 2 + 2)) := by
    field_simp
    ring
  have h0 : 0 ≤ 2 * M * (K ^ 2 + 1) * (t + 1) /
      (K ^ 2 * (t + K ^ 2 + 2) ^ 2 * (t + 1 + K ^ 2 + 2)) := by positivity
  linarith

theorem lcg_rate : LCGRate.{u} := by
  intro E _ _ P f C K x Φ hP hconv hdiff hcurv hK hrun xStar hxs h1 t ht
  set γ : ℕ → ℝ := fun t => 2 * (K ^ 2 + 1) / (K * ((t : ℝ) + K ^ 2 + 2)) with hγ
  have hK0 : 0 < K := by linarith
  have hγ0 : ∀ t : ℕ, 0 ≤ γ t := fun t => by simp only [hγ]; positivity
  have hγ1 : ∀ t : ℕ, 1 ≤ t → γ t ≤ 1 := fun t ht => by
    simp only [hγ]
    rw [div_le_one (by positivity)]
    have ht' : (1 : ℝ) ≤ t := by exact_mod_cast ht
    have h1 : 0 ≤ (K - 1) * (K ^ 2 - K + 2) :=
      mul_nonneg (by linarith) (by nlinarith [sq_nonneg (K - 1 / 2)])
    have h2 : 0 ≤ K * ((t : ℝ) - 1) := mul_nonneg hK0.le (by linarith)
    nlinarith
  -- the iterates stay in `P`
  have hxP : ∀ t, 1 ≤ t → x t ∈ P := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => exact hrun.1
    | succ t ht ih =>
      rcases (hrun.2 t ht).2 with ⟨v, hv, -, hx'⟩ | ⟨-, hx'⟩
      · rw [hx']
        exact hP ih hv (by linarith [hγ1 t ht]) (hγ0 t) (by ring)
      · rw [hx']
        exact ih
  -- the primal gap stays below `Φ_{t-1}`
  have hinv : ∀ t, 1 ≤ t → f (x t) - f xStar ≤ Φ (t - 1) := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => simpa using h1
    | succ t ht ih =>
      obtain ⟨hΦ, hans⟩ := hrun.2 t ht
      rw [show t + 1 - 1 = t by omega]
      have hden : 0 < 1 + γ t / K := by have := hγ0 t; positivity
      rcases hans with ⟨v, hv, hgt, hx'⟩ | ⟨hle, hx'⟩
      · have hstep : x (t + 1) = x t + γ t • (v - x t) := by rw [hx']; module
        have hc := hcurv (x t) (hxP t ht) v hv (γ t) ⟨hγ0 t, hγ1 t ht⟩
        rw [← hstep] at hc
        have hgv : fderiv ℝ f (x t) (v - x t) = -fderiv ℝ f (x t) (x t - v) := by
          rw [← map_neg, neg_sub]
        rw [hgv] at hc
        have hm : γ t * (Φ t / K) ≤ γ t * fderiv ℝ f (x t) (x t - v) :=
          mul_le_mul_of_nonneg_left hgt.le (hγ0 t)
        have hΦ' : Φ t * (1 + γ t / K) = Φ (t - 1) + C / 2 * γ t ^ 2 := by
          rw [hΦ, div_mul_cancel₀ _ hden.ne']
        have : γ t * (Φ t / K) = Φ t * (γ t / K) := by ring
        nlinarith
      · rw [hx']
        have h2 := add_fderiv_le_of_convexOn hconv hdiff (x t) xStar
        have h3 := hle xStar hxs.1
        have h4 : fderiv ℝ f (x t) (xStar - x t) = -fderiv ℝ f (x t) (x t - xStar) := by
          rw [← map_neg, neg_sub]
        rw [h4] at h2
        linarith
  -- the bound on `Φ`
  set M := max C (Φ 0) with hM
  have hM0 : 0 ≤ M := by
    have : 0 ≤ f (x 1) - f xStar := by linarith [hxs.2 _ (hxP 1 le_rfl)]
    exact le_trans (by linarith) (le_max_right C (Φ 0))
  have hΦb : ∀ t, 1 ≤ t → Φ (t - 1) ≤ 2 * M * (K ^ 2 + 1) / ((t : ℝ) + K ^ 2 + 2) := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base =>
      simp only [Nat.sub_self, Nat.cast_one]
      rw [le_div_iff₀ (by positivity)]
      have h2 : Φ 0 ≤ M := le_max_right _ _
      nlinarith [mul_nonneg (sub_nonneg.mpr h2) (by positivity : (0 : ℝ) ≤ K ^ 2 + 3),
        mul_nonneg hM0 (by nlinarith : (0 : ℝ) ≤ K ^ 2 - 1)]
    | succ t ht ih =>
      obtain ⟨hΦ, -⟩ := hrun.2 t ht
      rw [show t + 1 - 1 = t by omega, hΦ]
      have hden : 0 < 1 + γ t / K := by have := hγ0 t; positivity
      rw [div_le_iff₀ hden]
      have hCM : C / 2 * γ t ^ 2 ≤ M / 2 * γ t ^ 2 :=
        mul_le_mul_of_nonneg_right (by linarith [le_max_left C (Φ 0)]) (sq_nonneg _)
      have key := lcg_phi_step M K t hM0 hK0 (Nat.cast_nonneg t)
      simp only [hγ] at hCM hden ⊢
      push_cast
      linarith
  calc f (x t) - f xStar ≤ Φ (t - 1) := hinv t ht
    _ ≤ _ := hΦb t ht

end Proof

end Lemmata.LazyCG
