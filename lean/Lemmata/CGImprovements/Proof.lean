module

public import Lemmata.CGImprovements.Statement
public import Lemmata.CGBasics.Vanilla

@[expose] public section

/-!
# Adaptive step sizes: proofs

The short step for `M` minimizes `-s g + s² M ‖x - v‖²/2` over `s ∈ [0, 1]`, so a step that passes
the test does at least as well as every `s ∈ [0, 1]` in the smoothness bound for any `K ≥ M`, and
the rates of vanilla Frank–Wolfe apply with `K`.
-/

namespace Lemmata.CGImprovements

open Lemmata.FrankWolfe

universe u

namespace Proof

/-- The clipped short step minimizes the quadratic model over `[0, 1]`. -/
theorem adaStep_le {g a s : ℝ} (_hg : 0 ≤ g) (ha : 0 ≤ a) (hga : a = 0 → g = 0)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    -(min (g / a) 1 * g) + min (g / a) 1 ^ 2 * a / 2 ≤ -(s * g) + s ^ 2 * a / 2 := by
  rcases eq_or_lt_of_le ha with ha0 | hapos
  · subst ha0; rw [hga rfl]; simp
  rcases le_total (g / a) 1 with h | h
  · rw [min_eq_left h]
    have e : -(g / a * g) + (g / a) ^ 2 * a / 2 = -(g ^ 2 / (2 * a)) := by field_simp; ring
    rw [e]
    have : 0 ≤ (s * a - g) ^ 2 / (2 * a) := by positivity
    have e2 : (s * a - g) ^ 2 / (2 * a) = -(s * g) + s ^ 2 * a / 2 + g ^ 2 / (2 * a) := by
      field_simp; ring
    linarith
  · rw [min_eq_right h]
    have hag : a ≤ g := by rwa [le_div_iff₀ hapos, one_mul] at h
    have h1 : 0 ≤ (1 - s) * (g - a) := mul_nonneg (by linarith [hs.2]) (by linarith)
    have h2 : 0 ≤ (1 - s) ^ 2 * a := by positivity
    nlinarith [h1, h2]

theorem smooth_passes_test : SmoothPassesTest.{u} := by
  intro E _ _ f L M hsm hLM x v
  unfold SufficientDecrease
  set γ := adaStep f M x v
  have hq := hsm.le_quadratic x (x + γ • (v - x))
  rw [add_sub_cancel_left, map_smul, smul_eq_mul, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    norm_sub_rev v x] at hq
  have : (L : ℝ) / 2 * (γ ^ 2 * ‖x - v‖ ^ 2) ≤ γ ^ 2 * M / 2 * ‖x - v‖ ^ 2 := by
    have := mul_le_mul_of_nonneg_right hLM (by positivity : (0 : ℝ) ≤ γ ^ 2 * ‖x - v‖ ^ 2)
    linarith
  linarith

theorem adaptive_step_terminates : AdaptiveStepTerminates.{u} := by
  intro E _ _ f L M₀ τ x v hsm hM₀ hτ
  classical
  have hbig : ∀ k : ℕ, (L : ℝ) ≤ M₀ * τ ^ k → SufficientDecrease f (M₀ * τ ^ k) x v :=
    fun k hk => smooth_passes_test f L _ hsm hk x v
  set k₁ := ⌈Real.logb τ (L / M₀)⌉₊ with hk₁
  have hk₁L : (L : ℝ) ≤ M₀ * τ ^ k₁ := by
    rcases eq_or_lt_of_le (NNReal.coe_nonneg L) with hL0 | hLpos
    · rw [← hL0]; positivity
    have h1 : Real.logb τ (L / M₀) ≤ k₁ := Nat.le_ceil _
    have h2 : L / M₀ ≤ τ ^ (k₁ : ℝ) := by
      rw [← Real.logb_le_logb hτ (by positivity) (by positivity), Real.logb_rpow (by linarith)
        hτ.ne']
      exact h1
    rw [Real.rpow_natCast] at h2
    rw [div_le_iff₀ hM₀] at h2
    linarith
  have hex : ∃ k, SufficientDecrease f (M₀ * τ ^ k) x v := ⟨k₁, hbig k₁ hk₁L⟩
  refine ⟨Nat.find hex, Nat.find_spec hex, fun j hj => Nat.find_min hex hj, ?_, ?_⟩
  · exact Nat.find_min' hex (hbig k₁ hk₁L)
  · -- the first estimate reaching `L` passes, so the returned one is at most that
    have hexL : ∃ k : ℕ, (L : ℝ) ≤ M₀ * τ ^ k := ⟨k₁, hk₁L⟩
    have hle : Nat.find hex ≤ Nat.find hexL := Nat.find_min' hex (hbig _ (Nat.find_spec hexL))
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · rw [h0, pow_zero, mul_one]; exact le_max_left _ _
    · have hprev : ¬ ((L : ℝ) ≤ M₀ * τ ^ (Nat.find hex - 1)) :=
        Nat.find_min hexL (by omega)
      push Not at hprev
      have e : M₀ * τ ^ Nat.find hex = τ * (M₀ * τ ^ (Nat.find hex - 1)) := by
        rw [← mul_assoc, mul_comm τ M₀, mul_assoc, ← pow_succ']
        congr 2; omega
      rw [e]
      exact le_max_of_le_right (mul_le_mul_of_nonneg_left hprev.le (by linarith))

theorem adaptive_rate : AdaptiveRate.{u} := by
  intro E _ _ C f L K x v M hC hCc hconv hsm hLK hx0 hrun xStar hxs t ht
  have hsmK : IsSmooth f K := ⟨hsm.1, hsm.2.weaken hLK⟩
  have hγ : ∀ t, x t ∈ C →
      0 ≤ adaStep f (M t) (x t) (v t) ∧ adaStep f (M t) (x t) (v t) ≤ 1 := fun t hx => by
    have hg : 0 ≤ fderiv ℝ f (x t) (x t - v t) := by
      rw [map_sub]; linarith [(hrun t).2.1 (x t) hx]
    have hM := (hrun t).2.2.1
    exact ⟨le_min (div_nonneg hg (by positivity)) zero_le_one, min_le_right _ _⟩
  have hxC : ∀ t, x t ∈ C := by
    intro t
    induction t with
    | zero => exact hx0
    | succ t ih =>
      rw [(hrun t).2.2.2.2.2]
      exact hCc.add_smul_sub_mem ih (hrun t).1 ⟨(hγ t ih).1, (hγ t ih).2⟩
  refine Lemmata.CGBasics.Proof.vanilla_rate C f K x v (fun t => adaStep f (M t) (x t) (v t)) hC
    hCc hconv hsmK hx0 (fun t => ⟨(hrun t).1, (hrun t).2.1, ⟨(hγ t (hxC t)).1, (hγ t (hxC t)).2⟩,
      (hrun t).2.2.2.2.2, fun s hs => ?_⟩) xStar hxs t ht
  obtain ⟨-, -, hM0, hMK, htest, hx'⟩ := hrun t
  have hg : 0 ≤ fderiv ℝ f (x t) (x t - v t) := by
    rw [map_sub]; linarith [(hrun t).2.1 (x t) (hxC t)]
  unfold SufficientDecrease at htest
  rw [← hx'] at htest
  have hle := adaStep_le (s := s) hg (by positivity : 0 ≤ M t * ‖x t - v t‖ ^ 2) (fun h0 => by
    have : ‖x t - v t‖ ^ 2 = 0 := by
      rcases mul_eq_zero.mp h0 with h | h
      · exact absurd h hM0.ne'
      · exact h
    have : x t - v t = 0 := norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this)
    rw [this, map_zero]) hs
  have hvx : fderiv ℝ f (x t) (v t - x t) = -fderiv ℝ f (x t) (x t - v t) := by
    rw [← map_neg, neg_sub]
  have hMK' : s ^ 2 * M t / 2 * ‖x t - v t‖ ^ 2 ≤ s ^ 2 * K / 2 * ‖x t - v t‖ ^ 2 := by
    have := mul_le_mul_of_nonneg_right hMK (by positivity : (0 : ℝ) ≤ s ^ 2 * ‖x t - v t‖ ^ 2)
    nlinarith
  rw [norm_sub_rev (v t) (x t)]
  unfold adaStep at htest
  rw [hvx] at htest
  nlinarith

end Proof

end Lemmata.CGImprovements
