module

public import Lemmata.FWRestart.Interior

@[expose] public section

/-!
# The appendices: one run with a large `γ`, and a recurrence

While fractional away-step Frank–Wolfe takes Frank–Wolfe steps, each step with exact line search
gives `h_{t+1} ≤ h_t - η h_t + η² L D²/2` for every `η ∈ [0, 1]`, so `h_t ≤ 2 L D²/(t + 2)` as for
Frank–Wolfe (Lemma A.1). For the recurrence of Lemma B.1, the chord of the convex map
`y ↦ y^{1/β}` gives `(1 + x)^{1/β} ≤ 1 + x/(2^β - 1)` for `x ∈ [0, 2^β - 1]`, which is what the
induction needs once `1/(t + k) ≤ 2^β - 1`, that is `k ≥ 1/(2^β - 1)`.
-/

namespace Lemmata.FWRestart

open Lemmata.FrankWolfe Lemmata.AwayStepFW Lemmata.AwayStepFW.Proof

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The chord bound for `y ↦ y^{1/β}` on `[1, 2^β]`. -/
theorem chord_rpow {β x : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) (hx0 : 0 ≤ x) (hx : x ≤ 2 ^ β - 1) :
    (1 + x) ^ (1 / β) ≤ 1 + x / (2 ^ β - 1) := by
  have hp : 1 ≤ 1 / β := by rw [le_div_iff₀ hβ]; linarith
  have h2 : 1 < (2 : ℝ) ^ β := Real.one_lt_rpow (by norm_num) hβ
  set m := x / (2 ^ β - 1) with hm
  have hm0 : 0 ≤ m := div_nonneg hx0 (by linarith)
  have hm1 : m ≤ 1 := (div_le_one (by linarith)).mpr hx
  have hconv := (convexOn_rpow hp).2 (Set.mem_Ici.mpr zero_le_one)
    (Set.mem_Ici.mpr (by positivity : (0 : ℝ) ≤ 2 ^ β)) (by linarith : 0 ≤ 1 - m) hm0
    (by ring)
  simp only [smul_eq_mul, Real.one_rpow, mul_one] at hconv
  rw [← Real.rpow_mul (by norm_num), mul_one_div_cancel hβ.ne', Real.rpow_one] at hconv
  have e : 1 - m + m * 2 ^ β = 1 + x := by
    rw [hm]
    field_simp
    ring
  rw [e] at hconv
  linarith

namespace Proof

theorem one_shot_rate : OneShotRate.{u} := by
  intro E _ _ V f L D γ w₀ x S lam T hconv hsm hD hrun hfw y hy
  obtain ⟨hst, hit⟩ := hrun
  set Cf : ℝ := (L : ℝ) * D ^ 2 with hCf
  have hCf0 : 0 ≤ Cf := by positivity
  have h0 := inv_of_weighted hst
  have hinv : ∀ t ≤ T, Inv V (x t) (S t) (lam t) := by
    intro t ht
    have := segment_inv hconv hsm hD (t₀ := 0) (by simpa using h0) t
      (fun i hi => by simpa using hit i (by omega))
    simpa using this
  -- one step: `h_{t+1} ≤ h_t - η h_t + η² Cf/2` for `η ∈ [0, 1]`
  have hstep : ∀ t < T, ∀ η ∈ Set.Icc (0 : ℝ) 1,
      f (x (t + 1)) - f y ≤ (f (x t) - f y) - η * (f (x t) - f y) + η ^ 2 * Cf / 2 := by
    intro t ht η hη
    obtain ⟨v, hvV, hv, a, ha, haS, hgap, hstep⟩ := hit t ht
    have hinvt := hinv t ht.le
    have hxC := mem_hull_of_inv hinvt
    have hvC : v ∈ convexHull ℝ (↑V : Set E) := subset_convexHull ℝ _ (Finset.mem_coe.mpr hvV)
    have hFW := hfw t ht v hvV hv
    unfold IsFAFWStep at hstep
    rw [ite_eq_left hFW] at hstep
    obtain ⟨η', hη', hmin, hx', -, -⟩ := hstep
    have h1 := smooth_curv hsm hD (x t) hxC v hvC (x t) hxC η hη
    rw [show x t + η • (v - x t) = x t - η • (x t - v) by
      rw [← neg_sub (x t) v, smul_neg, ← sub_eq_add_neg]] at h1
    have h2 : fderiv ℝ f (x t) (v - x t) = -fderiv ℝ f (x t) (x t - v) := by
      rw [← map_neg, neg_sub]
    rw [h2] at h1
    -- the Frank–Wolfe gap is at least the primal gap
    have hgy : f (x t) - f y ≤ fderiv ℝ f (x t) (x t - v) := by
      have hc := Lemmata.FrankWolfe.convexOn_add_fderiv_le hconv (Set.mem_univ (x t))
        (hsm.1 (x t)) (Set.mem_univ y)
      have := Proof.le_of_min_vertex (fderiv ℝ f (x t)) hv hy
      rw [map_sub] at hc ⊢
      linarith
    have h3 : η * (f (x t) - f y) ≤ η * fderiv ℝ f (x t) (x t - v) :=
      mul_le_mul_of_nonneg_left hgy hη.1
    rw [hx']
    have := hmin η hη
    linarith
  -- the rate `h_t ≤ 2 Cf/(t + 2)` for `1 ≤ t ≤ T`
  have hrate : ∀ t : ℕ, 1 ≤ t → t ≤ T → f (x t) - f y ≤ 2 * Cf / (t + 2) := by
    intro t
    induction t with
    | zero => intro h; omega
    | succ t ih =>
      intro _ ht
      rcases Nat.eq_zero_or_pos t with rfl | htpos
      · have := hstep 0 (by omega) 1 ⟨zero_le_one, le_rfl⟩
        push_cast
        nlinarith
      · have ih' := ih htpos (by omega)
        set h := f (x t) - f y with hh
        have hdec := hstep t (by omega) 0 ⟨le_rfl, zero_le_one⟩
        simp only [zero_mul, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
          zero_pow, zero_div, add_zero] at hdec
        have ht2 : (0 : ℝ) < (t : ℝ) + 2 := by positivity
        rcases le_or_gt h 0 with hneg | hpos
        · have : (0 : ℝ) ≤ 2 * Cf / (((t + 1 : ℕ) : ℝ) + 2) := by positivity
          linarith
        · have hCfpos : 0 < Cf := by
            by_contra hC
            have hC0 : Cf = 0 := le_antisymm (not_lt.mp hC) hCf0
            rw [hC0, mul_zero, zero_div] at ih'
            linarith
          have hhC : h ≤ Cf := by
            have : 2 * Cf / ((t : ℝ) + 2) ≤ Cf := by
              rw [div_le_iff₀ ht2]
              have : (1 : ℝ) ≤ t := by exact_mod_cast htpos
              nlinarith
            linarith
          have hη : h / Cf ∈ Set.Icc (0 : ℝ) 1 :=
            ⟨div_nonneg hpos.le hCfpos.le, (div_le_one hCfpos).mpr hhC⟩
          have h1 := hstep t (by omega) _ hη
          have e : h - h / Cf * h + (h / Cf) ^ 2 * Cf / 2 = h - h ^ 2 / (2 * Cf) := by
            field_simp; ring
          rw [e] at h1
          -- monotonicity of `φ(u) = u - u²/(2 Cf)` on `[0, Cf]`
          set b := 2 * Cf / ((t : ℝ) + 2) with hb
          have hbC : b ≤ Cf := by
            rw [hb, div_le_iff₀ ht2]
            have : (1 : ℝ) ≤ t := by exact_mod_cast htpos
            nlinarith
          have hmono : h - h ^ 2 / (2 * Cf) ≤ b - b ^ 2 / (2 * Cf) := by
            have : (b - h) * (1 - (h + b) / (2 * Cf)) ≥ 0 := by
              apply mul_nonneg (by linarith)
              rw [sub_nonneg, div_le_one (by positivity)]
              linarith
            have e2 : b - b ^ 2 / (2 * Cf) - (h - h ^ 2 / (2 * Cf)) =
                (b - h) * (1 - (h + b) / (2 * Cf)) := by
              field_simp; ring
            linarith
          have hfin : b - b ^ 2 / (2 * Cf) ≤ 2 * Cf / (((t + 1 : ℕ) : ℝ) + 2) := by
            have e3 : b - b ^ 2 / (2 * Cf) = 2 * Cf * ((t : ℝ) + 1) / ((t : ℝ) + 2) ^ 2 := by
              rw [hb]
              field_simp
              ring
            rw [e3]
            push_cast
            rw [div_le_div_iff₀ (by positivity) (by positivity)]
            nlinarith [hCfpos]
          linarith
  intro t ht1 htT
  have h1 := hrate t ht1 htT
  have ht : (0 : ℝ) < t := by exact_mod_cast ht1
  have h2 : 2 * Cf / ((t : ℝ) + 2) ≤ 2 * Cf / t :=
    div_le_div_of_nonneg_left (by positivity) ht (by linarith)
  linarith

theorem recurrence_rate : RecurrenceRate := by
  intro h M β k C' C hh hM hβ hβ1 hrec hk hC' h0 hC
  have h2 : 1 < (2 : ℝ) ^ β := Real.one_lt_rpow (by norm_num) hβ
  have h2p : (0 : ℝ) < 2 ^ β - 1 := by linarith
  have hk0 : 0 < k := lt_of_lt_of_le (by positivity) hk
  have hC'0 : 0 < C' := lt_of_lt_of_le (by positivity) hC'
  have hC0 : 0 ≤ C := le_trans (by positivity) hC
  -- `C' ≤ M (C/2)^β`
  have hCM : C' ≤ M * (C / 2) ^ β := by
    have h1 : (C' / M) ^ (1 / β) ≤ C / 2 := by linarith
    have h3 := Real.rpow_le_rpow (by positivity) h1 hβ.le
    rw [← Real.rpow_mul (by positivity), one_div_mul_cancel hβ.ne', Real.rpow_one,
      div_le_iff₀ hM] at h3
    linarith
  intro t
  induction t with
  | zero =>
    simp only [Nat.cast_zero, zero_add]
    rw [le_div_iff₀ (Real.rpow_pos_of_pos hk0 _)]
    exact h0
  | succ t ih =>
    have htk : 0 < (t : ℝ) + k := by positivity
    set A := ((t : ℝ) + k) ^ (1 / β) with hAdef
    have hA : 0 < A := Real.rpow_pos_of_pos htk _
    set x := 1 / ((t : ℝ) + k) with hxdef
    have hx0 : 0 ≤ x := by positivity
    have hx1 : x ≤ 2 ^ β - 1 := by
      rw [hxdef, div_le_iff₀ htk]
      have h3 : 1 ≤ (2 ^ β - 1) * k := by
        rw [div_le_iff₀ (by linarith)] at hk
        linarith
      have : (0 : ℝ) ≤ t := Nat.cast_nonneg t
      nlinarith
    have hA' : (((t + 1 : ℕ) : ℝ) + k) ^ (1 / β) = A * (1 + x) ^ (1 / β) := by
      rw [hAdef, ← Real.mul_rpow htk.le (by positivity)]
      congr 1
      rw [hxdef]
      push_cast
      field_simp
      ring
    have hchord := chord_rpow hβ hβ1 hx0 hx1
    have h1x : (1 + x) ^ (1 / β) ≤ 2 := by
      have : x / (2 ^ β - 1) ≤ 1 := (div_le_one (by linarith)).mpr hx1
      linarith
    have hpow0 : 0 ≤ (1 + x) ^ (1 / β) := by positivity
    rw [hA', le_div_iff₀ (by positivity)]
    have ihA : h t * A ≤ C := by rwa [le_div_iff₀ hA] at ih
    have hht := hh t
    by_cases hcase : h t * A ≤ C / 2
    · have hmax : max (1 / 2) (1 - M * h t ^ β) ≤ 1 :=
        max_le (by norm_num) (by have := Real.rpow_nonneg hht β; nlinarith)
      have hle : h (t + 1) ≤ h t := le_trans (hrec t) (by nlinarith)
      calc h (t + 1) * (A * (1 + x) ^ (1 / β)) ≤ h t * (A * 2) := by
            apply mul_le_mul hle (mul_le_mul_of_nonneg_left h1x hA.le) (by positivity) hht
        _ ≤ C := by nlinarith
    · push Not at hcase
      -- `M h_t^β ≥ C' x`
      have hbig : C / (2 * A) ≤ h t := by
        rw [div_le_iff₀ (by positivity)]
        linarith
      have hpowA : A ^ β = (t : ℝ) + k := by
        rw [hAdef, ← Real.rpow_mul htk.le, one_div_mul_cancel hβ.ne', Real.rpow_one]
      have hhβ : (C / 2) ^ β * x ≤ h t ^ β := by
        have h3 := Real.rpow_le_rpow (by positivity) hbig hβ.le
        rw [show C / (2 * A) = (C / 2) / A by ring, Real.div_rpow (by positivity) hA.le,
          hpowA] at h3
        rw [hxdef, ← div_eq_mul_one_div]
        exact h3
      have hMx : C' * x ≤ M * h t ^ β := by
        have := mul_le_mul_of_nonneg_right hCM hx0
        have := mul_le_mul_of_nonneg_left hhβ hM.le
        nlinarith
      -- `h_{t+1} ≤ h_t m` with `m = max (1/2) (1 - C' x)`, and `m (1 + x)^{1/β} ≤ 1`
      have hstep : h (t + 1) ≤ h t * max (1 / 2) (1 - C' * x) := by
        refine le_trans (hrec t) (mul_le_mul_of_nonneg_left ?_ hht)
        exact max_le_max le_rfl (by linarith)
      have hm : max (1 / 2) (1 - C' * x) * (1 + x) ^ (1 / β) ≤ 1 := by
        rcases le_total (1 - C' * x) (1 / 2) with hle | hle
        · rw [max_eq_left hle]
          linarith
        · rw [max_eq_right hle]
          have h4 : x / (2 ^ β - 1) ≤ C' * x := by
            rw [div_le_iff₀ (by linarith)]
            have h5 : 1 ≤ C' * (2 ^ β - 1) := by
              rw [div_le_iff₀ (by linarith)] at hC'
              linarith
            nlinarith
          have h6 : (1 + x) ^ (1 / β) ≤ 1 + C' * x := by linarith
          have h7 : (1 - C' * x) * (1 + x) ^ (1 / β) ≤ (1 - C' * x) * (1 + C' * x) :=
            mul_le_mul_of_nonneg_left h6 (by linarith)
          nlinarith [sq_nonneg (C' * x)]
      have hm0 : 0 ≤ max (1 / 2) (1 - C' * x) := le_max_of_le_left (by norm_num)
      calc h (t + 1) * (A * (1 + x) ^ (1 / β)) ≤
            h t * max (1 / 2) (1 - C' * x) * (A * (1 + x) ^ (1 / β)) :=
            mul_le_mul_of_nonneg_right hstep (by positivity)
        _ = h t * A * (max (1 / 2) (1 - C' * x) * (1 + x) ^ (1 / β)) := by ring
        _ ≤ h t * A * 1 := mul_le_mul_of_nonneg_left hm (by positivity)
        _ ≤ C := by linarith

end Proof

end Lemmata.FWRestart
