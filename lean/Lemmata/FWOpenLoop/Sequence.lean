module

public import Lemmata.FWOpenLoop.Statement

@[expose] public section

/-!
# The sequence lemma (Lemma 3.5)

Facts about the step sizes `η_t = 4/(t + 4)` and the induction of Lemma 3.5, which bounds every
nonnegative sequence that obeys the recursion
`h_{t+1} ≤ (1 - η_t/2) h_t - η_t A C_t h_t^{1-ψ} + η_t² B C_t`.
-/

namespace Lemmata.FWOpenLoop

open Lemmata.FrankWolfe

universe u

theorem eta4_nat_sub (t : ℕ) (k : ℕ) :
    eta 4 ((t : ℤ) - k) = 4 / ((t : ℝ) + (4 - k)) := by
  simp only [eta]
  push_cast
  ring_nf

theorem eta4_pos (t : ℤ) (ht : -3 < t) : 0 < eta 4 t := by
  have : (-3 : ℝ) < t := by exact_mod_cast ht
  unfold eta
  apply div_pos (by norm_num)
  linarith

theorem eta4_anti (t : ℤ) (ht : -2 < t) : eta 4 t ≤ eta 4 (t - 1) := by
  have : (-2 : ℝ) < t := by exact_mod_cast ht
  unfold eta
  push_cast
  apply div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)

/-- `1 - η_t/2 = η_t/η_{t-2}`. -/
theorem one_sub_half_eta (t : ℤ) (ht : 0 ≤ t) :
    1 - eta 4 t / 2 = eta 4 t / eta 4 (t - 2) := by
  have : (0 : ℝ) ≤ t := by exact_mod_cast ht
  unfold eta
  push_cast
  field_simp
  ring

/-- `η_{t-1} η_t = (η_t/η_{t-2}) (η_{t-2} η_{t-1})`. -/
theorem eta_shift (t : ℤ) (ht : 0 ≤ t) :
    eta 4 (t + 1 - 2) * eta 4 (t + 1 - 1) =
      eta 4 t / eta 4 (t - 2) * (eta 4 (t - 2) * eta 4 (t - 1)) := by
  have h2 : 0 < eta 4 (t - 2) := eta4_pos _ (by omega)
  have e1 : t + 1 - 2 = t - 1 := by ring
  have e2 : t + 1 - 1 = t := by ring
  rw [e1, e2]
  field_simp

/-- `r ≤ r^e` for `r ∈ [0, 1]` and `e ∈ [0, 1]`. -/
theorem le_rpow_of_le_one {r e : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (he1 : e ≤ 1) :
    r ≤ r ^ e := by
  rcases hr0.eq_or_lt with h | h
  · rw [← h]; exact Real.rpow_nonneg le_rfl e
  calc r = r ^ (1 : ℝ) := (Real.rpow_one r).symm
    _ ≤ r ^ e := Real.rpow_le_rpow_of_exponent_ge h hr1 he1

/-- **Lemma 3.5** (sequence lemma). -/
theorem sequence_bound (ψ A B C : ℝ) (S T : ℕ) (Cs h : ℕ → ℝ) (hψ : ψ ∈ Set.Icc (0 : ℝ) (1 / 2))
    (hS : 1 ≤ S) (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hCs : ∀ t, S ≤ t → t < T → 0 ≤ Cs t ∧ Cs t ≤ C) (hh : ∀ t, S ≤ t → t ≤ T → 0 ≤ h t)
    (hrec : ∀ t, S ≤ t → t < T → h (t + 1) ≤ (1 - eta 4 t / 2) * h t -
      eta 4 t * A * Cs t * h t ^ (1 - ψ) + eta 4 t ^ 2 * B * Cs t) :
    ∀ t, S ≤ t → t ≤ T →
      h t ≤ max ((eta 4 ((t : ℤ) - 2) / eta 4 ((S : ℤ) - 1)) ^ (1 / (1 - ψ)) * h S)
      ((eta 4 ((t : ℤ) - 2) * B / A) ^ (1 / (1 - ψ)) + eta 4 ((t : ℤ) - 2) ^ 2 * B * C) := by
  obtain ⟨hψ0, hψ1⟩ := hψ
  set e : ℝ := 1 / (2 * (1 - ψ)) with he
  have h1ψ : 0 < 1 - ψ := by linarith
  have he0 : 0 ≤ e := by rw [he]; positivity
  have he1 : e ≤ 1 := by
    rw [he, div_le_one (by positivity)]; linarith
  have h2e : 2 * e = 1 / (1 - ψ) := by rw [he]; field_simp
  set η : ℤ → ℝ := eta 4 with hη
  set Q := η ((S : ℤ) - 2) * η ((S : ℤ) - 1) with hQ
  have hQpos : 0 < Q := mul_pos (eta4_pos _ (by omega)) (eta4_pos _ (by omega))
  -- the invariant (3.5)
  let X : ℕ → ℝ := fun t => ((η ((t : ℤ) - 2) * η ((t : ℤ) - 1)) / Q) ^ e * h S
  let Y : ℕ → ℝ := fun t => ((η ((t : ℤ) - 2) * η ((t : ℤ) - 1)) * B ^ 2 / A ^ 2) ^ e +
    η ((t : ℤ) - 2) * η ((t : ℤ) - 1) * B * C
  have hinv : ∀ t, S ≤ t → t ≤ T → h t ≤ max (X t) (Y t) := by
    intro t hSt
    induction t, hSt using Nat.le_induction with
    | base =>
      intro _
      refine le_max_of_le_left ?_
      simp only [X]
      rw [div_self hQpos.ne', Real.one_rpow, one_mul]
    | succ t hSt ih =>
      intro htT
      have ih := ih (by omega)
      obtain ⟨hC0, hCC⟩ := hCs t hSt (by omega)
      have hht := hh t hSt (by omega)
      have hS0 : 0 ≤ h S := hh S le_rfl (by omega)
      have hrec := hrec t hSt (by omega)
      have ηt : 0 < η t := eta4_pos _ (by omega)
      have ηt1 : 0 < η ((t : ℤ) - 1) := eta4_pos _ (by omega)
      have ηt2 : 0 < η ((t : ℤ) - 2) := eta4_pos _ (by omega)
      have hanti1 : η t ≤ η ((t : ℤ) - 1) := eta4_anti _ (by omega)
      have hanti2 : η ((t : ℤ) - 1) ≤ η ((t : ℤ) - 2) := by
        have := eta4_anti ((t : ℤ) - 1) (by omega)
        rwa [show (t : ℤ) - 1 - 1 = (t : ℤ) - 2 by ring] at this
      have hidx1 : ((t + 1 : ℕ) : ℤ) - 2 = (t : ℤ) - 1 := by push_cast; ring
      have hidx2 : ((t + 1 : ℕ) : ℤ) - 1 = (t : ℤ) := by push_cast; ring
      have hXs : X (t + 1) = ((η ((t : ℤ) - 1) * η t) / Q) ^ e * h S := by
        simp only [X]; rw [hidx1, hidx2]
      have hYs : Y (t + 1) = ((η ((t : ℤ) - 1) * η t) * B ^ 2 / A ^ 2) ^ e +
          η ((t : ℤ) - 1) * η t * B * C := by
        simp only [Y]; rw [hidx1, hidx2]
      set K := (η t * B / A) ^ (1 / (1 - ψ)) with hK
      by_cases hcase : h t ≤ K
      · -- small primal gap
        have hterm : 0 ≤ η t * A * Cs t * h t ^ (1 - ψ) := by
          have := Real.rpow_nonneg hht (1 - ψ)
          positivity
        have hsq : η t ^ 2 ≤ η ((t : ℤ) - 1) * η t := by
          rw [sq]; exact mul_le_mul_of_nonneg_right hanti1 ηt.le
        have h1 : h (t + 1) ≤ K + η t ^ 2 * B * C := by
          have hcoef : 0 ≤ η t / 2 * h t := by positivity
          have : η t ^ 2 * B * Cs t ≤ η t ^ 2 * B * C :=
            mul_le_mul_of_nonneg_left hCC (by positivity)
          linarith
        refine le_max_of_le_right ?_
        rw [hYs]
        have hK' : K ≤ ((η ((t : ℤ) - 1) * η t) * B ^ 2 / A ^ 2) ^ e := by
          have hbase : 0 ≤ η t * B / A := by positivity
          calc K = ((η t * B / A) ^ (2 : ℝ)) ^ e := by
                rw [hK, ← Real.rpow_mul hbase, h2e]
            _ ≤ ((η ((t : ℤ) - 1) * η t) * B ^ 2 / A ^ 2) ^ e := by
                apply Real.rpow_le_rpow (by positivity) _ he0
                rw [Real.rpow_two, div_pow, mul_pow]
                apply div_le_div_of_nonneg_right _ (by positivity)
                exact mul_le_mul_of_nonneg_right hsq (sq_nonneg B)
        have : η t ^ 2 * B * C ≤ η ((t : ℤ) - 1) * η t * B * C :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsq hB.le) hC.le
        linarith
      · -- large primal gap: contraction by `η_t/η_{t-2}`
        replace hcase := lt_of_not_ge hcase
        have hKpow : η t * B / A ≤ h t ^ (1 - ψ) := by
          have hbase : 0 ≤ η t * B / A := by positivity
          have := Real.rpow_le_rpow (by positivity) hcase.le h1ψ.le
          rwa [hK, ← Real.rpow_mul hbase, one_div_mul_cancel h1ψ.ne', Real.rpow_one] at this
        have hdrop : η t ^ 2 * B * Cs t ≤ η t * A * Cs t * h t ^ (1 - ψ) := by
          have : η t * A * Cs t * (η t * B / A) ≤ η t * A * Cs t * h t ^ (1 - ψ) :=
            mul_le_mul_of_nonneg_left hKpow (by positivity)
          have heq : η t * A * Cs t * (η t * B / A) = η t ^ 2 * B * Cs t := by
            field_simp
          linarith
        have hcontr : h (t + 1) ≤ (η t / η ((t : ℤ) - 2)) * h t := by
          rw [← one_sub_half_eta t (by omega)]
          linarith
        set r := η t / η ((t : ℤ) - 2) with hr
        have hr0 : 0 ≤ r := by positivity
        have hr1 : r ≤ 1 := by
          rw [hr, div_le_one ηt2]; linarith
        have hshift : η ((t : ℤ) - 1) * η t = r * (η ((t : ℤ) - 2) * η ((t : ℤ) - 1)) := by
          rw [hr]; field_simp
        have hre : r ≤ r ^ e := le_rpow_of_le_one hr0 hr1 he1
        have hmax : r * max (X t) (Y t) ≤ max (X (t + 1)) (Y (t + 1)) := by
          rw [mul_max_of_nonneg _ _ hr0]
          apply max_le_max
          · rw [hXs, hshift]
            show r * (((η ((t : ℤ) - 2) * η ((t : ℤ) - 1)) / Q) ^ e * h S) ≤ _
            have hP : 0 ≤ η ((t : ℤ) - 2) * η ((t : ℤ) - 1) / Q := by positivity
            have hsplit : r * (η ((t : ℤ) - 2) * η ((t : ℤ) - 1)) / Q =
                r * (η ((t : ℤ) - 2) * η ((t : ℤ) - 1) / Q) := by ring
            rw [hsplit, Real.mul_rpow hr0 hP]
            have hPe := Real.rpow_nonneg hP e
            calc r * ((η ((t : ℤ) - 2) * η ((t : ℤ) - 1) / Q) ^ e * h S)
                = r * (η ((t : ℤ) - 2) * η ((t : ℤ) - 1) / Q) ^ e * h S := by ring
              _ ≤ r ^ e * (η ((t : ℤ) - 2) * η ((t : ℤ) - 1) / Q) ^ e * h S :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hre hPe) hS0
          · rw [hYs, hshift]
            show r * ((η ((t : ℤ) - 2) * η ((t : ℤ) - 1) * B ^ 2 / A ^ 2) ^ e +
              η ((t : ℤ) - 2) * η ((t : ℤ) - 1) * B * C) ≤ _
            have hP : 0 ≤ η ((t : ℤ) - 2) * η ((t : ℤ) - 1) * B ^ 2 / A ^ 2 := by positivity
            have hsplit : r * (η ((t : ℤ) - 2) * η ((t : ℤ) - 1)) * B ^ 2 / A ^ 2 =
                r * (η ((t : ℤ) - 2) * η ((t : ℤ) - 1) * B ^ 2 / A ^ 2) := by ring
            rw [hsplit, Real.mul_rpow hr0 hP]
            have hPe := Real.rpow_nonneg hP e
            have : r * (η ((t : ℤ) - 2) * η ((t : ℤ) - 1) * B ^ 2 / A ^ 2) ^ e ≤
                r ^ e * (η ((t : ℤ) - 2) * η ((t : ℤ) - 1) * B ^ 2 / A ^ 2) ^ e :=
              mul_le_mul_of_nonneg_right hre hPe
            have h2 : r * (η ((t : ℤ) - 2) * η ((t : ℤ) - 1) * B * C) =
                r * (η ((t : ℤ) - 2) * η ((t : ℤ) - 1)) * B * C := by ring
            linarith
        calc h (t + 1) ≤ r * h t := hcontr
          _ ≤ r * max (X t) (Y t) := mul_le_mul_of_nonneg_left ih hr0
          _ ≤ max (X (t + 1)) (Y (t + 1)) := hmax
  -- from (3.5) to (3.4)
  intro t hSt htT
  have hinvt := hinv t hSt htT
  have hS0 : 0 ≤ h S := hh S le_rfl (by omega)
  have ηt1 : 0 < η ((t : ℤ) - 1) := eta4_pos _ (by omega)
  have ηt2 : 0 < η ((t : ℤ) - 2) := eta4_pos _ (by omega)
  have ηS1 : 0 < η ((S : ℤ) - 1) := eta4_pos _ (by omega)
  have ηS2 : 0 < η ((S : ℤ) - 2) := eta4_pos _ (by omega)
  have hanti_t : η ((t : ℤ) - 1) ≤ η ((t : ℤ) - 2) := by
    have := eta4_anti ((t : ℤ) - 1) (by omega)
    rwa [show (t : ℤ) - 1 - 1 = (t : ℤ) - 2 by ring] at this
  have hanti_S : η ((S : ℤ) - 1) ≤ η ((S : ℤ) - 2) := by
    have := eta4_anti ((S : ℤ) - 1) (by omega)
    rwa [show (S : ℤ) - 1 - 1 = (S : ℤ) - 2 by ring] at this
  refine le_trans hinvt (max_le_max ?_ ?_)
  · show ((η ((t : ℤ) - 2) * η ((t : ℤ) - 1)) / Q) ^ e * h S ≤ _
    apply mul_le_mul_of_nonneg_right _ hS0
    have hbase : 0 ≤ η ((t : ℤ) - 2) / η ((S : ℤ) - 1) := by positivity
    calc ((η ((t : ℤ) - 2) * η ((t : ℤ) - 1)) / Q) ^ e
        ≤ ((η ((t : ℤ) - 2) / η ((S : ℤ) - 1)) ^ (2 : ℝ)) ^ e := by
          apply Real.rpow_le_rpow (by positivity) _ he0
          rw [Real.rpow_two, div_pow, hQ]
          rw [div_le_div_iff₀ hQpos (by positivity)]
          have h1 : η ((t : ℤ) - 2) * η ((t : ℤ) - 1) ≤ η ((t : ℤ) - 2) ^ 2 := by
            rw [sq]; exact mul_le_mul_of_nonneg_left hanti_t ηt2.le
          have h2 : η ((S : ℤ) - 1) ^ 2 ≤ η ((S : ℤ) - 2) * η ((S : ℤ) - 1) := by
            rw [sq]; exact mul_le_mul_of_nonneg_right hanti_S ηS1.le
          calc η ((t : ℤ) - 2) * η ((t : ℤ) - 1) * η ((S : ℤ) - 1) ^ 2
              ≤ η ((t : ℤ) - 2) ^ 2 * η ((S : ℤ) - 1) ^ 2 := by
                apply mul_le_mul_of_nonneg_right h1 (by positivity)
            _ ≤ η ((t : ℤ) - 2) ^ 2 * (η ((S : ℤ) - 2) * η ((S : ℤ) - 1)) := by
                apply mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = (η ((t : ℤ) - 2) / η ((S : ℤ) - 1)) ^ (1 / (1 - ψ)) := by
          rw [← Real.rpow_mul hbase, h2e]
  · show ((η ((t : ℤ) - 2) * η ((t : ℤ) - 1)) * B ^ 2 / A ^ 2) ^ e +
      η ((t : ℤ) - 2) * η ((t : ℤ) - 1) * B * C ≤ _
    apply add_le_add
    · have hbase : 0 ≤ η ((t : ℤ) - 2) * B / A := by positivity
      calc ((η ((t : ℤ) - 2) * η ((t : ℤ) - 1)) * B ^ 2 / A ^ 2) ^ e
          ≤ ((η ((t : ℤ) - 2) * B / A) ^ (2 : ℝ)) ^ e := by
            apply Real.rpow_le_rpow (by positivity) _ he0
            rw [Real.rpow_two, div_pow, mul_pow]
            apply div_le_div_of_nonneg_right _ (by positivity)
            have : η ((t : ℤ) - 2) * η ((t : ℤ) - 1) ≤ η ((t : ℤ) - 2) ^ 2 := by
              rw [sq]; exact mul_le_mul_of_nonneg_left hanti_t ηt2.le
            exact mul_le_mul_of_nonneg_right this (sq_nonneg B)
        _ = (η ((t : ℤ) - 2) * B / A) ^ (1 / (1 - ψ)) := by
            rw [← Real.rpow_mul hbase, h2e]
    · have : η ((t : ℤ) - 2) * η ((t : ℤ) - 1) ≤ η ((t : ℤ) - 2) ^ 2 := by
        rw [sq]; exact mul_le_mul_of_nonneg_left hanti_t ηt2.le
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this hB.le) hC.le

namespace Proof

theorem sequence_lemma : SequenceLemma := by
  intro ψ A B C S T Cs h hψ hS hA hB hC hCs hh hrec t hSt htT
  exact sequence_bound ψ A B C S T Cs h hψ hS hA hB hC hCs hh hrec t hSt htT

end Proof

end Lemmata.FWOpenLoop
