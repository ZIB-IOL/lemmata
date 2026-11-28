module

public import Lemmata.FWOpenLoop.Statement

@[expose] public section

/-!
# The sequence lemma for `η_t = ℓ/(t + ℓ)`, one step at a time

The induction of Lemma 3.5, for every `ℓ > 2`, with the contraction `1 - (2/ℓ) η_t = η_t/η_{t-2}`:
`seq_step` moves the invariant `h ≤ max (X_k, Y_k)` from `k` to `k + 1`, and `seq_final` turns it
into the bound of Lemma 3.5. Section 5 uses it for `ℓ = 8` (decomposition-invariant pairwise
Frank–Wolfe) and along the progress steps of away-step Frank–Wolfe (`ℓ = 4`).
-/

namespace Lemmata.FWOpenLoop

theorem etaL_pos {ℓ : ℝ} (hℓ : 2 < ℓ) (t : ℤ) (ht : -2 ≤ t) : 0 < eta ℓ t := by
  have : (-2 : ℝ) ≤ t := by exact_mod_cast ht
  unfold eta
  apply div_pos (by linarith)
  linarith

theorem etaL_anti {ℓ : ℝ} (hℓ : 2 < ℓ) (t : ℤ) (ht : -1 ≤ t) : eta ℓ t ≤ eta ℓ (t - 1) := by
  have : (-1 : ℝ) ≤ t := by exact_mod_cast ht
  unfold eta
  push_cast
  apply div_le_div_of_nonneg_left (by linarith) (by linarith) (by linarith)

/-- `1 - (2/ℓ) η_t = η_t/η_{t-2}`. -/
theorem one_sub_etaL {ℓ : ℝ} (hℓ : 2 < ℓ) (t : ℤ) (ht : 0 ≤ t) :
    1 - 2 / ℓ * eta ℓ t = eta ℓ t / eta ℓ (t - 2) := by
  have : (0 : ℝ) ≤ t := by exact_mod_cast ht
  have h1 : (t : ℝ) + ℓ ≠ 0 := by linarith
  have h2 : (t : ℝ) - 2 + ℓ ≠ 0 := by linarith
  have h3 : ℓ ≠ 0 := by linarith
  unfold eta
  push_cast
  field_simp
  ring

theorem le_rpow_self_of_le_one {r e : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (he1 : e ≤ 1) :
    r ≤ r ^ e := by
  rcases hr0.eq_or_lt with h | h
  · rw [← h]; exact Real.rpow_nonneg le_rfl e
  calc r = r ^ (1 : ℝ) := (Real.rpow_one r).symm
    _ ≤ r ^ e := Real.rpow_le_rpow_of_exponent_ge h hr1 he1

/-- The two halves of the invariant of the sequence lemma at index `k`, for the step sizes
`η_t = ℓ/(t + ℓ)`, a base constant `K₀` and the normalization `Q = η_{S-2} η_{S-1}`. -/
noncomputable def seqX (ℓ e Q K₀ : ℝ) (k : ℕ) : ℝ :=
  ((eta ℓ ((k : ℤ) - 2) * eta ℓ ((k : ℤ) - 1)) / Q) ^ e * K₀

noncomputable def seqY (ℓ e A B C : ℝ) (k : ℕ) : ℝ :=
  ((eta ℓ ((k : ℤ) - 2) * eta ℓ ((k : ℤ) - 1)) * B ^ 2 / A ^ 2) ^ e +
    eta ℓ ((k : ℤ) - 2) * eta ℓ ((k : ℤ) - 1) * B * C

/-- One step of the sequence lemma: if `h ≤ max (X_k, Y_k)` and
`h' ≤ (1 - 2η_k/ℓ) h - η_k A C_k h^{1-ψ} + η_k² B C_k`, then `h' ≤ max (X_{k+1}, Y_{k+1})`. -/
theorem seq_step {ℓ ψ A B C Q K₀ Ck h h' : ℝ} (k : ℕ) (hℓ : 2 < ℓ)
    (hψ : ψ ∈ Set.Icc (0 : ℝ) (1 / 2)) (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hQ : 0 < Q)
    (hK₀ : 0 ≤ K₀) (hCk : 0 ≤ Ck ∧ Ck ≤ C) (hh : 0 ≤ h)
    (hrec : h' ≤ (1 - 2 / ℓ * eta ℓ k) * h - eta ℓ k * A * Ck * h ^ (1 - ψ) +
      eta ℓ k ^ 2 * B * Ck)
    (hinv : h ≤ max (seqX ℓ (1 / (2 * (1 - ψ))) Q K₀ k) (seqY ℓ (1 / (2 * (1 - ψ))) A B C k)) :
    h' ≤ max (seqX ℓ (1 / (2 * (1 - ψ))) Q K₀ (k + 1))
      (seqY ℓ (1 / (2 * (1 - ψ))) A B C (k + 1)) := by
  obtain ⟨hψ0, hψ1⟩ := hψ
  obtain ⟨hC0, hCC⟩ := hCk
  set e : ℝ := 1 / (2 * (1 - ψ)) with he
  have h1ψ : 0 < 1 - ψ := by linarith
  have he0 : 0 ≤ e := by rw [he]; positivity
  have he1 : e ≤ 1 := by rw [he, div_le_one (by positivity)]; linarith
  have h2e : 2 * e = 1 / (1 - ψ) := by rw [he]; field_simp
  set η : ℤ → ℝ := eta ℓ with hη
  have ηt : 0 < η k := etaL_pos hℓ _ (by omega)
  have ηt1 : 0 < η ((k : ℤ) - 1) := etaL_pos hℓ _ (by omega)
  have ηt2 : 0 < η ((k : ℤ) - 2) := etaL_pos hℓ _ (by omega)
  have hanti1 : η k ≤ η ((k : ℤ) - 1) := etaL_anti hℓ _ (by omega)
  have hidx1 : ((k + 1 : ℕ) : ℤ) - 2 = (k : ℤ) - 1 := by push_cast; ring
  have hidx2 : ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) := by push_cast; ring
  have hXs : seqX ℓ e Q K₀ (k + 1) = ((η ((k : ℤ) - 1) * η k) / Q) ^ e * K₀ := by
    simp only [seqX]; rw [hidx1, hidx2]
  have hYs : seqY ℓ e A B C (k + 1) = ((η ((k : ℤ) - 1) * η k) * B ^ 2 / A ^ 2) ^ e +
      η ((k : ℤ) - 1) * η k * B * C := by
    simp only [seqY]; rw [hidx1, hidx2]
  have hsq : η k ^ 2 ≤ η ((k : ℤ) - 1) * η k := by
    rw [sq]; exact mul_le_mul_of_nonneg_right hanti1 ηt.le
  set K := (η k * B / A) ^ (1 / (1 - ψ)) with hK
  have hcoef : 1 - 2 / ℓ * η k ≤ 1 := by
    have : 0 ≤ 2 / ℓ * η k := by positivity
    linarith
  have hcoef0 : 0 ≤ 1 - 2 / ℓ * η k := by
    rw [one_sub_etaL hℓ _ (by omega)]; positivity
  by_cases hcase : h ≤ K
  · have hterm : 0 ≤ η k * A * Ck * h ^ (1 - ψ) := by
      have := Real.rpow_nonneg hh (1 - ψ)
      positivity
    have h1 : h' ≤ K + η k ^ 2 * B * C := by
      have : (1 - 2 / ℓ * η k) * h ≤ h := by nlinarith
      have : η k ^ 2 * B * Ck ≤ η k ^ 2 * B * C :=
        mul_le_mul_of_nonneg_left hCC (by positivity)
      linarith
    refine le_max_of_le_right ?_
    rw [hYs]
    have hK' : K ≤ ((η ((k : ℤ) - 1) * η k) * B ^ 2 / A ^ 2) ^ e := by
      have hbase : 0 ≤ η k * B / A := by positivity
      calc K = ((η k * B / A) ^ (2 : ℝ)) ^ e := by
            rw [hK, ← Real.rpow_mul hbase, h2e]
        _ ≤ ((η ((k : ℤ) - 1) * η k) * B ^ 2 / A ^ 2) ^ e := by
            apply Real.rpow_le_rpow (by positivity) _ he0
            rw [Real.rpow_two, div_pow, mul_pow]
            apply div_le_div_of_nonneg_right _ (by positivity)
            exact mul_le_mul_of_nonneg_right hsq (sq_nonneg B)
    have : η k ^ 2 * B * C ≤ η ((k : ℤ) - 1) * η k * B * C :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsq hB.le) hC.le
    linarith
  · replace hcase := lt_of_not_ge hcase
    have hKpow : η k * B / A ≤ h ^ (1 - ψ) := by
      have hbase : 0 ≤ η k * B / A := by positivity
      have := Real.rpow_le_rpow (by positivity) hcase.le h1ψ.le
      rwa [hK, ← Real.rpow_mul hbase, one_div_mul_cancel h1ψ.ne', Real.rpow_one] at this
    have hdrop : η k ^ 2 * B * Ck ≤ η k * A * Ck * h ^ (1 - ψ) := by
      have : η k * A * Ck * (η k * B / A) ≤ η k * A * Ck * h ^ (1 - ψ) :=
        mul_le_mul_of_nonneg_left hKpow (by positivity)
      have heq : η k * A * Ck * (η k * B / A) = η k ^ 2 * B * Ck := by
        field_simp
      linarith
    have hcontr : h' ≤ (η k / η ((k : ℤ) - 2)) * h := by
      rw [← one_sub_etaL hℓ _ (by omega)]
      linarith
    set r := η k / η ((k : ℤ) - 2) with hr
    have hr0 : 0 ≤ r := by positivity
    have hanti2 : η ((k : ℤ) - 1) ≤ η ((k : ℤ) - 2) := by
      have := etaL_anti hℓ ((k : ℤ) - 1) (by omega)
      rwa [show (k : ℤ) - 1 - 1 = (k : ℤ) - 2 by ring] at this
    have hr1 : r ≤ 1 := by
      rw [hr, div_le_one ηt2]; linarith
    have hshift : η ((k : ℤ) - 1) * η k = r * (η ((k : ℤ) - 2) * η ((k : ℤ) - 1)) := by
      rw [hr]; field_simp
    have hre : r ≤ r ^ e := le_rpow_self_of_le_one hr0 hr1 he1
    have hmax : r * max (seqX ℓ e Q K₀ k) (seqY ℓ e A B C k) ≤
        max (seqX ℓ e Q K₀ (k + 1)) (seqY ℓ e A B C (k + 1)) := by
      rw [mul_max_of_nonneg _ _ hr0]
      apply max_le_max
      · rw [hXs, hshift]
        show r * (((η ((k : ℤ) - 2) * η ((k : ℤ) - 1)) / Q) ^ e * K₀) ≤ _
        have hP : 0 ≤ η ((k : ℤ) - 2) * η ((k : ℤ) - 1) / Q := by positivity
        have hsplit : r * (η ((k : ℤ) - 2) * η ((k : ℤ) - 1)) / Q =
            r * (η ((k : ℤ) - 2) * η ((k : ℤ) - 1) / Q) := by ring
        rw [hsplit, Real.mul_rpow hr0 hP]
        have hPe := Real.rpow_nonneg hP e
        calc r * ((η ((k : ℤ) - 2) * η ((k : ℤ) - 1) / Q) ^ e * K₀)
            = r * (η ((k : ℤ) - 2) * η ((k : ℤ) - 1) / Q) ^ e * K₀ := by ring
          _ ≤ r ^ e * (η ((k : ℤ) - 2) * η ((k : ℤ) - 1) / Q) ^ e * K₀ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hre hPe) hK₀
      · rw [hYs, hshift]
        show r * ((η ((k : ℤ) - 2) * η ((k : ℤ) - 1) * B ^ 2 / A ^ 2) ^ e +
          η ((k : ℤ) - 2) * η ((k : ℤ) - 1) * B * C) ≤ _
        have hP : 0 ≤ η ((k : ℤ) - 2) * η ((k : ℤ) - 1) * B ^ 2 / A ^ 2 := by positivity
        have hsplit : r * (η ((k : ℤ) - 2) * η ((k : ℤ) - 1)) * B ^ 2 / A ^ 2 =
            r * (η ((k : ℤ) - 2) * η ((k : ℤ) - 1) * B ^ 2 / A ^ 2) := by ring
        rw [hsplit, Real.mul_rpow hr0 hP]
        have hPe := Real.rpow_nonneg hP e
        have : r * (η ((k : ℤ) - 2) * η ((k : ℤ) - 1) * B ^ 2 / A ^ 2) ^ e ≤
            r ^ e * (η ((k : ℤ) - 2) * η ((k : ℤ) - 1) * B ^ 2 / A ^ 2) ^ e :=
          mul_le_mul_of_nonneg_right hre hPe
        have h2 : r * (η ((k : ℤ) - 2) * η ((k : ℤ) - 1) * B * C) =
            r * (η ((k : ℤ) - 2) * η ((k : ℤ) - 1)) * B * C := by ring
        linarith
    calc h' ≤ r * h := hcontr
      _ ≤ r * max (seqX ℓ e Q K₀ k) (seqY ℓ e A B C k) := mul_le_mul_of_nonneg_left hinv hr0
      _ ≤ _ := hmax

/-- The invariant implies the bound of Lemma 3.5, for `k ≥ S ≥ 1` with `Q = η_{S-2} η_{S-1}`. -/
theorem seq_final {ℓ ψ A B C K₀ : ℝ} (S k : ℕ) (hℓ : 2 < ℓ) (hψ : ψ ∈ Set.Icc (0 : ℝ) (1 / 2))
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hK₀ : 0 ≤ K₀) (hS : 1 ≤ S) :
    max (seqX ℓ (1 / (2 * (1 - ψ))) (eta ℓ ((S : ℤ) - 2) * eta ℓ ((S : ℤ) - 1)) K₀ k)
        (seqY ℓ (1 / (2 * (1 - ψ))) A B C k) ≤
      max ((eta ℓ ((k : ℤ) - 2) / eta ℓ ((S : ℤ) - 1)) ^ (1 / (1 - ψ)) * K₀)
        ((eta ℓ ((k : ℤ) - 2) * B / A) ^ (1 / (1 - ψ)) + eta ℓ ((k : ℤ) - 2) ^ 2 * B * C) := by
  obtain ⟨hψ0, hψ1⟩ := hψ
  set e : ℝ := 1 / (2 * (1 - ψ)) with he
  have he0 : 0 ≤ e := by rw [he]; apply div_nonneg zero_le_one; linarith
  have h2e : 2 * e = 1 / (1 - ψ) := by
    rw [he]; have : 1 - ψ ≠ 0 := by linarith
    field_simp
  set η : ℤ → ℝ := eta ℓ with hη
  have ηt1 : 0 < η ((k : ℤ) - 1) := etaL_pos hℓ _ (by omega)
  have ηt2 : 0 < η ((k : ℤ) - 2) := etaL_pos hℓ _ (by omega)
  have ηS1 : 0 < η ((S : ℤ) - 1) := etaL_pos hℓ _ (by omega)
  have ηS2 : 0 < η ((S : ℤ) - 2) := etaL_pos hℓ _ (by omega)
  have hanti_t : η ((k : ℤ) - 1) ≤ η ((k : ℤ) - 2) := by
    have := etaL_anti hℓ ((k : ℤ) - 1) (by omega)
    rwa [show (k : ℤ) - 1 - 1 = (k : ℤ) - 2 by ring] at this
  have hanti_S : η ((S : ℤ) - 1) ≤ η ((S : ℤ) - 2) := by
    have := etaL_anti hℓ ((S : ℤ) - 1) (by omega)
    rwa [show (S : ℤ) - 1 - 1 = (S : ℤ) - 2 by ring] at this
  have hQpos : 0 < η ((S : ℤ) - 2) * η ((S : ℤ) - 1) := mul_pos ηS2 ηS1
  apply max_le_max
  · show ((η ((k : ℤ) - 2) * η ((k : ℤ) - 1)) / (η ((S : ℤ) - 2) * η ((S : ℤ) - 1))) ^ e * K₀ ≤ _
    apply mul_le_mul_of_nonneg_right _ hK₀
    have hbase : 0 ≤ η ((k : ℤ) - 2) / η ((S : ℤ) - 1) := by positivity
    calc ((η ((k : ℤ) - 2) * η ((k : ℤ) - 1)) / (η ((S : ℤ) - 2) * η ((S : ℤ) - 1))) ^ e
        ≤ ((η ((k : ℤ) - 2) / η ((S : ℤ) - 1)) ^ (2 : ℝ)) ^ e := by
          apply Real.rpow_le_rpow (by positivity) _ he0
          rw [Real.rpow_two, div_pow, div_le_div_iff₀ hQpos (by positivity)]
          have h1 : η ((k : ℤ) - 2) * η ((k : ℤ) - 1) ≤ η ((k : ℤ) - 2) ^ 2 := by
            rw [sq]; exact mul_le_mul_of_nonneg_left hanti_t ηt2.le
          have h2 : η ((S : ℤ) - 1) ^ 2 ≤ η ((S : ℤ) - 2) * η ((S : ℤ) - 1) := by
            rw [sq]; exact mul_le_mul_of_nonneg_right hanti_S ηS1.le
          calc η ((k : ℤ) - 2) * η ((k : ℤ) - 1) * η ((S : ℤ) - 1) ^ 2
              ≤ η ((k : ℤ) - 2) ^ 2 * η ((S : ℤ) - 1) ^ 2 :=
                mul_le_mul_of_nonneg_right h1 (by positivity)
            _ ≤ η ((k : ℤ) - 2) ^ 2 * (η ((S : ℤ) - 2) * η ((S : ℤ) - 1)) :=
                mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = (η ((k : ℤ) - 2) / η ((S : ℤ) - 1)) ^ (1 / (1 - ψ)) := by
          rw [← Real.rpow_mul hbase, h2e]
  · show ((η ((k : ℤ) - 2) * η ((k : ℤ) - 1)) * B ^ 2 / A ^ 2) ^ e +
      η ((k : ℤ) - 2) * η ((k : ℤ) - 1) * B * C ≤ _
    have hsq : η ((k : ℤ) - 2) * η ((k : ℤ) - 1) ≤ η ((k : ℤ) - 2) ^ 2 := by
      rw [sq]; exact mul_le_mul_of_nonneg_left hanti_t ηt2.le
    apply add_le_add
    · have hbase : 0 ≤ η ((k : ℤ) - 2) * B / A := by positivity
      calc ((η ((k : ℤ) - 2) * η ((k : ℤ) - 1)) * B ^ 2 / A ^ 2) ^ e
          ≤ ((η ((k : ℤ) - 2) * B / A) ^ (2 : ℝ)) ^ e := by
            apply Real.rpow_le_rpow (by positivity) _ he0
            rw [Real.rpow_two, div_pow, mul_pow]
            apply div_le_div_of_nonneg_right _ (by positivity)
            exact mul_le_mul_of_nonneg_right hsq (sq_nonneg B)
        _ = (η ((k : ℤ) - 2) * B / A) ^ (1 / (1 - ψ)) := by
            rw [← Real.rpow_mul hbase, h2e]
    · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsq hB.le) hC.le

end Lemmata.FWOpenLoop
