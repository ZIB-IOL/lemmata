module

public import Lemmata.CGImprovements.NEP

@[expose] public section

/-!
# Blended conditional gradients (Theorem 3.42)

As for lazy conditional gradients, `φ_t ≥ h_t/2` throughout. A simplex descent step gains at least
`φ_t²/(L_S k)` and a Frank–Wolfe step at least `φ_t²/(2 K² L D²)`, so every step that does not drop
a vertex gains at least `h_t²/Q`; drop steps are at most as many as Frank–Wolfe steps.
-/

namespace Lemmata.CGImprovements

open Lemmata.FrankWolfe

universe u

namespace Proof

/-- One step of the potential `h (P + 8) ≤ Q` along `h' ≤ h - h²/Q`. -/
theorem potential_step {h h' Q : ℝ} {P : ℕ} (hQ : 0 < Q) (_h0 : 0 ≤ h)
    (hstep : h' ≤ h - h ^ 2 / Q)
    (hbd : h * ((P : ℝ) + 8) ≤ Q) : h' * (((P + 1 : ℕ) : ℝ) + 8) ≤ Q := by
  set b := Q / ((P : ℝ) + 8) with hb
  have hP8 : (0 : ℝ) < (P : ℝ) + 8 := by positivity
  have hhb : h ≤ b := by rw [hb, le_div_iff₀ hP8]; exact hbd
  have hbQ : b ≤ Q / 2 := by
    rw [hb, div_le_div_iff₀ hP8 (by norm_num)]
    have : (0 : ℝ) ≤ P := Nat.cast_nonneg P
    nlinarith
  have hmon : h - h ^ 2 / Q ≤ b - b ^ 2 / Q := by
    have e : (b - b ^ 2 / Q) - (h - h ^ 2 / Q) = (b - h) * (Q - (b + h)) / Q := by
      field_simp; ring
    have : 0 ≤ (b - h) * (Q - (b + h)) / Q :=
      div_nonneg (mul_nonneg (by linarith) (by linarith)) hQ.le
    linarith
  have hfin : (b - b ^ 2 / Q) * ((P : ℝ) + 9) ≤ Q := by
    have e : b - b ^ 2 / Q = Q * ((P : ℝ) + 7) / ((P : ℝ) + 8) ^ 2 := by
      rw [hb]; field_simp; ring
    rw [e, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  have h1 : h' ≤ b - b ^ 2 / Q := hstep.trans hmon
  have h2 : 0 ≤ (P : ℝ) + 9 := by positivity
  push_cast
  nlinarith [mul_le_mul_of_nonneg_right h1 h2]

theorem bcg_rate : BCGRate.{u} := by
  intro E _ _ V f L LS K k x S φ hconv hsm hK hLS hrun hk xStar hxs hφ0 hφ0' ε hε t ht
  classical
  set D := Metric.diam (↑V : Set E) with hD
  set P := convexHull ℝ (↑V : Set E) with hP
  set Q : ℝ := max (8 * K ^ 2 * L * D ^ 2) (4 * LS * k) with hQ
  set h : ℕ → ℝ := fun t => f (x t) - f xStar with hh
  have hK0 : 0 < K := by linarith
  have hPc : IsCompact P := V.finite_toSet.isCompact_convexHull (𝕜 := ℝ)
  have hxP : ∀ t, x t ∈ P := fun t =>
    convexHull_mono (by exact_mod_cast (hrun.2.2 t).1) (hrun.2.2 t).2.1
  have hSne : ∀ t, (S t).Nonempty := fun t => by
    rcases (S t).eq_empty_or_nonempty with h0 | h0
    · have := (hrun.2.2 t).2.1; rw [h0] at this; simp at this
    · exact h0
  have hk1 : 1 ≤ k := lt_of_lt_of_le (Finset.card_pos.mpr (hSne 0)) (hk 0)
  have hk1R : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hQpos : 0 < Q :=
    lt_of_lt_of_le (mul_pos (mul_pos (by norm_num) hLS) (by linarith)) (le_max_right _ _)
  have hh0 : ∀ t, 0 ≤ h t := fun t => by simp only [hh]; linarith [hxs.2 _ (hxP t)]
  have hdist : ∀ y ∈ P, ∀ z ∈ P, ‖y - z‖ ≤ D := fun y hy z hz => by
    rw [← dist_eq_norm, hD, ← convexHull_diam]
    exact Metric.dist_le_diam_of_mem hPc.isBounded hy hz
  have hcertgap : ∀ t, (∀ z ∈ V, fderiv ℝ f (x t) (x t - z) ≤ φ t) → h t ≤ φ t := fun t hc => by
    obtain ⟨w, hwV, hwmin⟩ := V.exists_min_image (fderiv ℝ f (x t)) ⟨x 0, hrun.1⟩
    have h1 := add_fderiv_le_of_convexOn hconv hsm.1 (x t) xStar
    have h2 := Lemmata.CGBasics.Proof.le_on_hull (fderiv ℝ f (x t)) hwmin hxs.1
    have h3 := hc w hwV
    simp only [hh]
    rw [map_sub] at h1 h3
    linarith
  -- `φ` stays in `[0, φ₀]`
  have hφb : ∀ t, 0 ≤ φ t ∧ φ t ≤ φ 0 := by
    intro t
    induction t with
    | zero => exact ⟨by linarith [hh0 0], le_rfl⟩
    | succ t ih =>
      rcases (hrun.2.2 t).2.2 with ⟨-, -, -, hφ'⟩ |
          ⟨-, ⟨-, -, -, -, -, -, -, -, hφ'⟩ | ⟨-, -, -, hφ'⟩⟩
      · rw [hφ']; exact ih
      · rw [hφ']; exact ih
      · rw [hφ']; exact ⟨by linarith [ih.1], by linarith [ih.1, ih.2]⟩
  -- outcomes: negative, drop, or a good step gaining `h²/Q`
  have hout : ∀ t, ((∀ z ∈ V, fderiv ℝ f (x t) (x t - z) ≤ φ t) ∧ x (t + 1) = x t ∧
        S (t + 1) = S t ∧ φ (t + 1) = φ t / 2) ∨
      (h (t + 1) ≤ h t ∧ (S (t + 1)).card + 1 ≤ (S t).card ∧ φ (t + 1) = φ t) ∨
      (h (t + 1) * Q ≤ h t * Q - 4 * φ t ^ 2 ∧ (S (t + 1)).card ≤ (S t).card ∧
        φ (t + 1) = φ t) ∨
      (h (t + 1) * Q ≤ h t * Q - 4 * φ t ^ 2 ∧ (S (t + 1)).card ≤ (S t).card + 1 ∧
        φ (t + 1) = φ t) := by
    intro t
    rcases (hrun.2.2 t).2.2 with ⟨⟨a, ha, s, hs, hga⟩, hsub, hsido, hφ'⟩ |
        ⟨-, ⟨v, hv, hgv, γ, hγ, hx', hq, hS', hφ'⟩ | ⟨hcV, hx', hS', hφ'⟩⟩
    · rcases hsido with ⟨hle, hne⟩ | hdesc
      · right; left
        refine ⟨by simp only [hh]; linarith, ?_, hφ'⟩
        have := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)
        omega
      · right; right; left
        refine ⟨?_, Finset.card_le_card hsub, hφ'⟩
        have hS0 : (0 : ℝ) < (S t).card := by exact_mod_cast Finset.card_pos.mpr (hSne t)
        have hSk : ((S t).card : ℝ) ≤ k := by exact_mod_cast hk t
        have h1 := hdesc a ha s hs
        have hφ0t := (hφb t).1
        have h2 : φ t ^ 2 ≤ fderiv ℝ f (x t) (a - s) ^ 2 := pow_le_pow_left₀ hφ0t hga 2
        have hΔ : 0 ≤ f (x t) - f (x (t + 1)) := by
          have h0 := hdesc a ha a ha
          rw [sub_self, map_zero] at h0
          by_contra hneg; push Not at hneg
          have : LS * (S t).card * (f (x t) - f (x (t + 1))) < 0 :=
            mul_neg_of_pos_of_neg (by positivity) hneg
          nlinarith
        have h3 : 4 * φ t ^ 2 ≤ (f (x t) - f (x (t + 1))) * Q := by
          have h4 : LS * (S t).card * (f (x t) - f (x (t + 1))) ≤
              LS * k * (f (x t) - f (x (t + 1))) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hSk hLS.le) hΔ
          have h5 : (4 * LS * k) * (f (x t) - f (x (t + 1))) ≤ Q * (f (x t) - f (x (t + 1))) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) hΔ
          nlinarith
        simp only [hh]
        nlinarith
    · right; right; right
      refine ⟨?_, by rw [hS']; split_ifs <;> simp [Finset.card_insert_le], hφ'⟩
      -- the Frank–Wolfe step gains at least `φ²/(2 K² L D²)`
      rcases eq_or_lt_of_le (by positivity : (0 : ℝ) ≤ L * D ^ 2) with hK0' | hKpos
      · have hφz : φ t = 0 := by
          have := (hφb t).2; have := (hφb t).1; rw [← hK0'] at hφ0'; linarith
        have := hq 0 ⟨le_rfl, zero_le_one⟩
        simp only [hh, hφz]; simp at this; nlinarith
      · set s := φ t / (K * (L * D ^ 2)) with hs
        have hs0 : 0 ≤ s := div_nonneg (hφb t).1 (by positivity)
        have hs1 : s ≤ 1 := by
          rw [hs, div_le_one (by positivity)]
          have h1 := (hφb t).2
          have h2 : L * D ^ 2 ≤ K * (L * D ^ 2) := le_mul_of_one_le_left hKpos.le hK
          linarith
        have h1 := hq s ⟨hs0, hs1⟩
        have hd : ‖v - x t‖ ≤ D :=
          hdist v (subset_convexHull ℝ _ (by exact_mod_cast hv)) (x t) (hxP t)
        have hd2 : s ^ 2 * L / 2 * ‖v - x t‖ ^ 2 ≤ s ^ 2 * (L * D ^ 2) / 2 := by
          have := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hd 2)
            (by positivity : (0 : ℝ) ≤ s ^ 2 * L)
          nlinarith
        have hg : s * (φ t / K) ≤ s * fderiv ℝ f (x t) (x t - v) :=
          mul_le_mul_of_nonneg_left hgv.le hs0
        have he : s * (φ t / K) - s ^ 2 * (L * D ^ 2) / 2 =
            φ t ^ 2 / (2 * K ^ 2 * (L * D ^ 2)) := by
          rw [hs]; field_simp; ring
        have hprog : φ t ^ 2 / (2 * K ^ 2 * (L * D ^ 2)) ≤ f (x t) - f (x (t + 1)) := by linarith
        have h3 : 4 * φ t ^ 2 ≤ (f (x t) - f (x (t + 1))) * Q := by
          have h4 := mul_le_mul_of_nonneg_left hprog
            (by positivity : (0 : ℝ) ≤ 8 * K ^ 2 * L * D ^ 2)
          have e : 8 * K ^ 2 * L * D ^ 2 * (φ t ^ 2 / (2 * K ^ 2 * (L * D ^ 2))) = 4 * φ t ^ 2 := by
            rw [show (8 : ℝ) * K ^ 2 * L * D ^ 2 = 4 * (2 * K ^ 2 * (L * D ^ 2)) by ring, mul_assoc,
              mul_div_cancel₀ _ (mul_pos (mul_pos (by norm_num) (pow_pos hK0 2)) hKpos).ne']
          rw [e] at h4
          have h5 : (8 * K ^ 2 * L * D ^ 2) * (f (x t) - f (x (t + 1))) ≤
              Q * (f (x t) - f (x (t + 1))) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith [hprog,
              (by positivity : (0 : ℝ) ≤ φ t ^ 2 / (2 * K ^ 2 * (L * D ^ 2)))])
          linarith
        simp only [hh]
        nlinarith
    · left
      exact ⟨hcV, hx', hS', hφ'⟩
  have hmono : ∀ t, h (t + 1) ≤ h t := fun t => by
    rcases hout t with ⟨-, hx', -, -⟩ | ⟨h1, -, -⟩ | ⟨h1, -, -⟩ | ⟨h1, -, -⟩
    · simp only [hh, hx', le_refl]
    · exact h1
    · have : 0 ≤ 4 * φ t ^ 2 := by positivity
      have h2 : h (t + 1) * Q ≤ h t * Q := by linarith
      exact le_of_mul_le_mul_right h2 hQpos
    · have : 0 ≤ 4 * φ t ^ 2 := by positivity
      have h2 : h (t + 1) * Q ≤ h t * Q := by linarith
      exact le_of_mul_le_mul_right h2 hQpos
  have hinv : ∀ t, h t ≤ 2 * φ t := by
    intro t
    induction t with
    | zero => simp only [hh]; linarith
    | succ t ih =>
      rcases hout t with ⟨hcV, hx', -, hφ'⟩ | ⟨h1, -, hφ'⟩ | ⟨-, -, hφ'⟩ | ⟨-, -, hφ'⟩
      · rw [hφ']
        have h1 := hcertgap t hcV
        have e : h (t + 1) = h t := by simp only [hh, hx']
        linarith
      · rw [hφ']; linarith
      · rw [hφ']; linarith [hmono t]
      · rw [hφ']; linarith [hmono t]
  have hgood : ∀ t, h (t + 1) * Q ≤ h t * Q - 4 * φ t ^ 2 → h (t + 1) ≤ h t - h t ^ 2 / Q :=
    fun t hle => by
      have h2 : h t ^ 2 ≤ 4 * φ t ^ 2 := by
        have := pow_le_pow_left₀ (hh0 t) (hinv t) 2
        nlinarith
      have h3 : h t ^ 2 / Q ≤ h t - h (t + 1) := by rw [div_le_iff₀ hQpos]; linarith
      linarith
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
  have hstate : ∀ t, ∃ n dr gd nfw : ℕ, n + dr + gd = t ∧ nfw ≤ gd ∧
      (S t).card + dr ≤ 1 + nfw ∧ h t * ((gd : ℝ) + 8) ≤ Q ∧ φ t = φ 0 / 2 ^ n ∧
      (n₀ + 1 ≤ n → h t ≤ ε) := by
    intro t
    induction t with
    | zero =>
      refine ⟨0, 0, 0, 0, rfl, le_rfl, by rw [hrun.2.1]; simp, ?_, by simp,
        fun h => absurd h (by omega)⟩
      have h1 := hinv 0
      have h2 : (1 : ℝ) ≤ K ^ 2 := by nlinarith
      have h3 : L * D ^ 2 ≤ K ^ 2 * (L * D ^ 2) := le_mul_of_one_le_left (by positivity) h2
      have h4 : 8 * K ^ 2 * L * D ^ 2 ≤ Q := le_max_left _ _
      push_cast
      nlinarith [(hφb 0).2]
    | succ t ih =>
      obtain ⟨n, dr, gd, nfw, hsum, hfw, hcard, hpot, hφn, hε'⟩ := ih
      rcases hout t with ⟨hcV, hx', hS', hφ'⟩ | ⟨h1, hc, hφ'⟩ | ⟨h1, hc, hφ'⟩ | ⟨h1, hc, hφ'⟩
      · have e : h (t + 1) = h t := by simp only [hh, hx']
        refine ⟨n + 1, dr, gd, nfw, by omega, hfw, by rw [hS']; exact hcard, by rw [e]; exact hpot,
          by rw [hφ', hφn, pow_succ]; field_simp, fun hN => ?_⟩
        rw [e]
        rcases Nat.lt_or_ge n (n₀ + 1) with hlt | hge
        · have hN0 : n = n₀ := by omega
          calc h t ≤ φ t := hcertgap t hcV
            _ = φ 0 / 2 ^ n := hφn
            _ = φ 0 / 2 ^ n₀ := by rw [hN0]
            _ ≤ ε := hφε
        · exact hε' hge
      · refine ⟨n, dr + 1, gd, nfw, by omega, hfw, by omega, ?_, by rw [hφ', hφn],
          fun hN => h1.trans (hε' hN)⟩
        exact le_trans (mul_le_mul_of_nonneg_right h1 (by positivity)) hpot
      · refine ⟨n, dr, gd + 1, nfw, by omega, by omega, by omega,
          potential_step hQpos (hh0 t) (hgood t h1) hpot, by rw [hφ', hφn],
          fun hN => (hmono t).trans (hε' hN)⟩
      · refine ⟨n, dr, gd + 1, nfw + 1, by omega, by omega, by omega,
          potential_step hQpos (hh0 t) (hgood t h1) hpot, by rw [hφ', hφn],
          fun hN => (hmono t).trans (hε' hN)⟩
  obtain ⟨n, dr, gd, nfw, hsum, hfw, hcard, hpot, -, hεn⟩ := hstate t
  set P₀ := ⌈Q / ε⌉₊ with hP₀
  have hS1 : 1 ≤ (S t).card := Finset.card_pos.mpr (hSne t)
  rcases Nat.lt_or_ge gd P₀ with hlt | hge
  · rcases Nat.lt_or_ge n (n₀ + 1) with hn | hn
    · exfalso; omega
    · simpa [hh] using hεn hn
  · have h1 : Q ≤ ε * P₀ := by
      have := Nat.le_ceil (Q / ε)
      rw [div_le_iff₀ hε] at this
      linarith
    have h2 : (P₀ : ℝ) ≤ gd := by exact_mod_cast hge
    have h3 : h t * ((gd : ℝ) + 8) ≤ ε * ((gd : ℝ) + 8) := by nlinarith
    have hP8 : (0 : ℝ) < (gd : ℝ) + 8 := by positivity
    have := le_of_mul_le_mul_right h3 hP8
    simpa [hh] using this

end Proof

end Lemmata.CGImprovements
