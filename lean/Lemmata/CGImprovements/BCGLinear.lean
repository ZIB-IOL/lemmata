module

public import Lemmata.CGImprovements.BCG

@[expose] public section

/-!
# Blended conditional gradients for strongly convex objectives (Theorem 3.42)

At a negative answer of the weak separation oracle the simplex descent criterion failed too, so
`f'(x)(a - w) < 2 φ` and geometric strong convexity gives `μ δ² h ≤ 2 φ²`; after the halving
`μ δ² h ≤ 8 φ²`. Steps that do not drop a vertex gain at least `4 φ²/Q`.
-/

namespace Lemmata.CGImprovements

open Lemmata.FrankWolfe

universe u

namespace Proof

set_option maxHeartbeats 1000000 in
theorem bcg_linear_rate : BCGLinearRate.{u} := by
  intro E _ _ V f L μ δ LS K k x S φ hμ hδ hsc hconv hsm hstrong hK hLS hrun hk xStar hxs hφ0 hφ0'
    ε hε t ht
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
  have hout : ∀ t, ((∀ a ∈ S t, ∀ s ∈ S t, fderiv ℝ f (x t) (a - s) < φ t) ∧
        (∀ z ∈ V, fderiv ℝ f (x t) (x t - z) ≤ φ t) ∧ x (t + 1) = x t ∧
        S (t + 1) = S t ∧ φ (t + 1) = φ t / 2) ∨
      (h (t + 1) ≤ h t ∧ (S (t + 1)).card + 1 ≤ (S t).card ∧ φ (t + 1) = φ t) ∨
      (h (t + 1) * Q ≤ h t * Q - 4 * φ t ^ 2 ∧ (S (t + 1)).card ≤ (S t).card ∧
        φ (t + 1) = φ t) ∨
      (h (t + 1) * Q ≤ h t * Q - 4 * φ t ^ 2 ∧ (S (t + 1)).card ≤ (S t).card + 1 ∧
        φ (t + 1) = φ t) := by
    intro t
    rcases (hrun.2.2 t).2.2 with ⟨⟨a, ha, s, hs, hga⟩, hsub, hsido, hφ'⟩ |
        ⟨hbr, ⟨v, hv, hgv, γ, hγ, hx', hq, hS', hφ'⟩ | ⟨hcV, hx', hS', hφ'⟩⟩
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
      exact ⟨hbr, hcV, hx', hS', hφ'⟩
  have hout3 : ∀ t, (h t ≤ φ t ∧ μ * δ ^ 2 * h t ≤ 2 * φ t ^ 2 ∧ h (t + 1) = h t ∧
        S (t + 1) = S t ∧ φ (t + 1) = φ t / 2) ∨
      (h (t + 1) ≤ h t ∧ (S (t + 1)).card + 1 ≤ (S t).card ∧ φ (t + 1) = φ t) ∨
      (h (t + 1) ≤ h t - 4 * φ t ^ 2 / Q ∧ (S (t + 1)).card ≤ (S t).card + 1 ∧
        φ (t + 1) = φ t) := by
    intro t
    have hdivQ : ∀ {a b c : ℝ}, a * Q ≤ b * Q - c → a ≤ b - c / Q := fun {a b c} hle => by
      have h3 : c / Q ≤ b - a := by
        rw [div_le_iff₀ hQpos]; linarith
      linarith
    rcases hout t with ⟨hbr, hcV, hx', hS', hφ'⟩ | ⟨h1, hc, hφ'⟩ | ⟨h1, hc, hφ'⟩ | ⟨h1, hc, hφ'⟩
    · left
      set g := fderiv ℝ f (x t) with hg
      obtain ⟨a, ha, haS⟩ := (S t).exists_max_image g (hSne t)
      obtain ⟨s, hs, hsS⟩ := (S t).exists_min_image g (hSne t)
      obtain ⟨w, hw, hwV⟩ := V.exists_min_image g ⟨x 0, hrun.1⟩
      have hgeo := Lemmata.AwayStepFW.Proof.geometric_strong_convexity V f μ δ hμ hδ hsc hstrong
        xStar hxs (S t) (hrun.2.2 t).1 (x t) (hrun.2.2 t).2.1 a ha haS w hw hwV
      have hsx : g s ≤ g (x t) := Lemmata.CGBasics.Proof.le_on_hull (V := S t) g hsS
        (hrun.2.2 t).2.1
      have hax : g (x t) ≤ g a := by
        have := Lemmata.CGBasics.Proof.le_on_hull (V := S t) (-g)
          (fun u hu => by simp only [neg_apply, neg_le_neg_iff]; exact haS u hu)
          (hrun.2.2 t).2.1
        simpa using this
      have hwx : g w ≤ g (x t) := Lemmata.CGBasics.Proof.le_on_hull g hwV (hxP t)
      have h1 := hbr a ha s hs
      have h2 := hcV w hw
      have hgaw : g (a - w) ≤ 2 * φ t := by rw [map_sub] at h1 h2 ⊢; linarith
      have hgaw0 : 0 ≤ g (a - w) := by rw [map_sub]; linarith
      have h5 := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * μ * δ ^ 2)).mp hgeo
      have h6 := pow_le_pow_left₀ hgaw0 hgaw 2
      have h7 : (2 * φ t) ^ 2 = 4 * φ t ^ 2 := by ring
      refine ⟨hcertgap t hcV, ?_, by simp only [hh, hx'], hS', hφ'⟩
      simp only [hh] at h5 ⊢
      linarith
    · right; left; exact ⟨h1, hc, hφ'⟩
    · right; right; exact ⟨hdivQ h1, by omega, hφ'⟩
    · right; right; exact ⟨hdivQ h1, hc, hφ'⟩
  have hmono : ∀ t, h (t + 1) ≤ h t := fun t => by
    rcases hout3 t with ⟨-, -, he, -, -⟩ | ⟨h1, -, -⟩ | ⟨h1, -, -⟩
    · rw [he]
    · exact h1
    · have : 0 ≤ 4 * φ t ^ 2 / Q := by positivity
      linarith
  have hanti : Antitone h := antitone_nat_of_succ_le hmono
  set c := μ * δ ^ 2 / (2 * Q) with hc
  set q₀ := 4 * φ 0 ^ 2 / Q with hq₀
  set n₀ := ⌈Real.logb 2 (φ 0 / ε)⌉₊ with hn₀
  have hc0 : 0 ≤ c := by positivity
  clear_value c q₀ Q
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
  have hstate : ∀ t, ∃ n dr gpre gpost : ℕ, n + dr + gpre + gpost = t ∧
      (S t).card + dr ≤ 1 + gpre + gpost ∧ φ t = φ 0 / 2 ^ n ∧ (n₀ + 1 ≤ n → h t ≤ ε) ∧
      (n = 0 → gpost = 0 ∧ (gpre : ℝ) * q₀ ≤ h 0 - h t) ∧ (gpre : ℝ) * q₀ ≤ h 0 ∧
      (1 ≤ n → μ * δ ^ 2 * h t ≤ 8 * φ t ^ 2) ∧ h t ≤ Real.exp (-(c * gpost)) * h 0 := by
    intro t
    induction t with
    | zero =>
      refine ⟨0, 0, 0, 0, rfl, by rw [hrun.2.1]; simp, by simp, fun h => absurd h (by omega),
        fun _ => ⟨rfl, by simp⟩, by simp [hh0 0], fun h => absurd h (by omega), by simp⟩
    | succ t ih =>
      obtain ⟨n, dr, gpre, gpost, hsum, hcard, hφn, hε', hpre, hpre', hlin, hexp⟩ := ih
      rcases hout3 t with ⟨hcert, hgeo2, he, hS', hφ'⟩ | ⟨hle, hc', hφ'⟩ | ⟨hle, hc', hφ'⟩
      · refine ⟨n + 1, dr, gpre, gpost, by omega, by rw [hS']; omega,
          by rw [hφ', hφn, pow_succ]; field_simp, fun hN => ?_, fun h => absurd h (by omega),
          hpre', fun _ => ?_, by rw [he]; exact hexp⟩
        · rw [he]
          rcases Nat.lt_or_ge n (n₀ + 1) with hlt | hge
          · have hN0 : n = n₀ := by omega
            calc h t ≤ φ t := hcert
              _ = φ 0 / 2 ^ n := hφn
              _ = φ 0 / 2 ^ n₀ := by rw [hN0]
              _ ≤ ε := hφε
          · exact hε' hge
        · rw [he, hφ']
          have e : 8 * (φ t / 2) ^ 2 = 2 * φ t ^ 2 := by ring
          linarith
      · refine ⟨n, dr + 1, gpre, gpost, by omega, by omega, by rw [hφ', hφn],
          fun hN => hle.trans (hε' hN), fun h0 => ⟨(hpre h0).1, by linarith [(hpre h0).2]⟩,
          hpre', fun h1 => ?_, hle.trans hexp⟩
        rw [hφ']
        have := hlin h1
        have := mul_le_mul_of_nonneg_left hle (by positivity : (0 : ℝ) ≤ μ * δ ^ 2)
        linarith
      · rcases Nat.eq_zero_or_pos n with hn0 | hn1
        · have hφt : φ t = φ 0 := by rw [hφn, hn0, pow_zero, div_one]
          have hq : h (t + 1) ≤ h t - q₀ := by rw [hq₀, ← hφt]; exact hle
          obtain ⟨hgp, hpre0⟩ := hpre hn0
          refine ⟨n, dr, gpre + 1, gpost, by omega, by omega, by rw [hφ', hφn],
            fun hN => absurd hN (by omega), fun _ => ⟨hgp, ?_⟩, ?_, fun h => absurd h (by omega),
            ?_⟩
          · push_cast; linarith
          · push_cast; linarith [hh0 (t + 1)]
          · rw [hgp]; simp only [Nat.cast_zero, mul_zero, neg_zero, Real.exp_zero, one_mul]
            linarith [hanti (Nat.zero_le (t + 1))]
        · have hl := hlin hn1
          have hprog : c * h t ≤ 4 * φ t ^ 2 / Q := by
            rw [hc, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hQpos]
            have h8 := mul_le_mul_of_nonneg_right hl hQpos.le
            linarith only [h8]
          have hstep : h (t + 1) ≤ Real.exp (-c) * h t := by
            have h9 := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-c)) (hh0 t)
            calc h (t + 1) ≤ h t - 4 * φ t ^ 2 / Q := hle
              _ ≤ h t - c * h t := by linarith only [hprog]
              _ = (-c + 1) * h t := by ring
              _ ≤ Real.exp (-c) * h t := h9
          refine ⟨n, dr, gpre, gpost + 1, by omega, by omega, by rw [hφ', hφn],
            fun hN => (hmono t).trans (hε' hN), fun h => absurd h (by omega),
            hpre', fun _ => ?_, ?_⟩
          · rw [hφ']
            have := mul_le_mul_of_nonneg_left (hmono t) (by positivity : (0 : ℝ) ≤ μ * δ ^ 2)
            linarith
          · calc h (t + 1) ≤ Real.exp (-c) * h t := hstep
              _ ≤ Real.exp (-c) * (Real.exp (-(c * gpost)) * h 0) :=
                mul_le_mul_of_nonneg_left hexp (Real.exp_pos _).le
              _ = Real.exp (-(c * ((gpost + 1 : ℕ) : ℝ))) * h 0 := by
                rw [← mul_assoc, ← Real.exp_add]; push_cast; ring_nf
  obtain ⟨n, dr, gpre, gpost, hsum, hcard, -, hε', -, hpre', -, hexp⟩ := hstate t
  by_cases hsmall : h 0 ≤ ε
  · have := hanti (Nat.zero_le t)
    have : h t ≤ ε := by linarith
    simpa [hh] using this
  push Not at hsmall
  have hh0pos : 0 < h 0 := lt_trans hε hsmall
  have hφ0pos : 0 < φ 0 := by
    have : 0 < f (x 0) - f xStar := hh0pos
    linarith
  set A := ⌈Q / (2 * φ 0)⌉₊ with hA
  set B := ⌈2 * Q / (μ * δ ^ 2) * Real.log ((f (x 0) - f xStar) / ε)⌉₊ with hB
  clear_value A B
  rcases Nat.lt_or_ge n (n₀ + 1) with hn | hn
  swap
  · simpa [hh] using hε' hn
  rcases Nat.lt_or_ge gpost B with hgp | hgp
  swap
  · have hcinv : c * (2 * Q / (μ * δ ^ 2)) = 1 := by
      rw [hc, div_mul_div_comm, show μ * δ ^ 2 * (2 * Q) = 2 * Q * (μ * δ ^ 2) by ring]
      exact div_self (mul_pos (mul_pos two_pos hQpos) (mul_pos hμ (pow_pos hδ 2))).ne'
    have h1 : 2 * Q / (μ * δ ^ 2) * Real.log ((f (x 0) - f xStar) / ε) ≤ B := by
      rw [hB]; exact Nat.le_ceil _
    have h2 : (B : ℝ) ≤ gpost := by exact_mod_cast hgp
    have hcB : Real.log ((f (x 0) - f xStar) / ε) ≤ c * gpost := by
      calc Real.log ((f (x 0) - f xStar) / ε) =
            c * (2 * Q / (μ * δ ^ 2) * Real.log ((f (x 0) - f xStar) / ε)) := by
            rw [← mul_assoc, hcinv, one_mul]
        _ ≤ c * B := mul_le_mul_of_nonneg_left h1 hc0
        _ ≤ c * gpost := mul_le_mul_of_nonneg_left h2 hc0
    have h3 : Real.exp (-(c * gpost)) ≤ Real.exp (-Real.log ((f (x 0) - f xStar) / ε)) :=
      Real.exp_le_exp.mpr (by linarith)
    have hpos : 0 < (f (x 0) - f xStar) / ε := div_pos hh0pos hε
    rw [show Real.exp (-Real.log ((f (x 0) - f xStar) / ε)) = ((f (x 0) - f xStar) / ε)⁻¹ by
      rw [Real.exp_neg, Real.exp_log hpos]] at h3
    have h4 : Real.exp (-(c * gpost)) * h 0 ≤ ε := by
      calc Real.exp (-(c * gpost)) * h 0 ≤ ((f (x 0) - f xStar) / ε)⁻¹ * h 0 :=
            mul_le_mul_of_nonneg_right h3 hh0pos.le
        _ = ε := by
            have : h 0 = f (x 0) - f xStar := rfl
            rw [this, inv_div]
            exact div_mul_cancel₀ ε hh0pos.ne'
    simpa [hh] using hexp.trans h4
  exfalso
  have hgpre : gpre ≤ A := by
    have h0' : h 0 ≤ 2 * φ 0 := by simp only [hh]; linarith only [hφ0]
    have h1 : (gpre : ℝ) * q₀ ≤ 2 * φ 0 := by linarith only [hpre', h0']
    have h3 : (gpre : ℝ) * (4 * φ 0 ^ 2) ≤ 2 * φ 0 * Q := by
      rw [hq₀, mul_div_assoc', div_le_iff₀ hQpos] at h1
      exact h1
    have h2φ : (0 : ℝ) < 2 * φ 0 := by linarith only [hφ0pos]
    have h4 : (gpre : ℝ) * (2 * φ 0) * (2 * φ 0) ≤ Q * (2 * φ 0) := by
      have e1 : (gpre : ℝ) * (2 * φ 0) * (2 * φ 0) = (gpre : ℝ) * (4 * φ 0 ^ 2) := by ring
      have e2 : Q * (2 * φ 0) = 2 * φ 0 * Q := by ring
      rw [e1, e2]; exact h3
    have h5 : (gpre : ℝ) * (2 * φ 0) ≤ Q := le_of_mul_le_mul_right h4 h2φ
    have h6 : (gpre : ℝ) ≤ Q / (2 * φ 0) := by rw [le_div_iff₀ h2φ]; exact h5
    have h7 : (gpre : ℝ) ≤ (A : ℝ) := h6.trans (by rw [hA]; exact Nat.le_ceil _)
    exact_mod_cast h7
  have hS1 : 1 ≤ (S t).card := Finset.card_pos.mpr (hSne t)
  omega

end Proof

end Lemmata.CGImprovements
