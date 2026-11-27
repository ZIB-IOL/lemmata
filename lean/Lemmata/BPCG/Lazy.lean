module

public import Lemmata.BPCG.Proof

@[expose] public section

/-!
# Lazified BPCG (Theorem 3.6, case (B))

A gap step certifies `h_t ≤ Φ_t`, so `Φ_t ≥ h_t/2` throughout. A local pairwise step that does not
drop a vertex gains at least `Φ_t²/(2 L D²)`, a Frank–Wolfe step at least `Φ_t²/(2 J² L D²)`, so
every such step gains at least `h_t²/(8 J² L D²)`; drop steps are at most as many as Frank–Wolfe
steps.
-/

namespace Lemmata.BPCG

open Lemmata.FrankWolfe Lemmata.AwayStepFW

namespace Proof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- One step of the potential `h (P + 8) ≤ Q` along `h' ≤ h - h²/Q`. -/
theorem potential_step' {h h' Q : ℝ} {P : ℕ} (hQ : 0 < Q) (hstep : h' ≤ h - h ^ 2 / Q)
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

open Classical in
theorem lazy_bpcg_run_inv {V : Finset E} {f : E → ℝ} {J : ℝ} {x : ℕ → E} {S : ℕ → Finset E}
    {lam : ℕ → E → ℝ} {Φ : ℕ → ℝ} (h : IsLazyBPCGRun V f J x S lam Φ) :
    ∀ t, Lemmata.AwayStepFW.Proof.Inv V (x t) (S t) (lam t) := by
  obtain ⟨hx0, hS0, hlam0, hsteps⟩ := h
  intro t
  induction t with
  | zero =>
    refine ⟨by rw [hS0]; simpa using hx0, fun w => ?_, fun w hw => ?_, ?_, ?_⟩
    · rw [hlam0]; dsimp only; split_ifs <;> norm_num
    · rw [hS0, Finset.mem_singleton] at hw; rw [hlam0]; simp [hw]
    · rw [hS0, hlam0]; simp
    · rw [hS0, hlam0]; simp
  | succ t ih =>
    obtain ⟨a, ha, -, s, hs, -, hstep⟩ := hsteps t
    unfold IsLazyBPCGStep at hstep
    split_ifs at hstep with hsel
    · obtain ⟨⟨γ, hγ, -, hx', hlam', hS'⟩, -⟩ := hstep
      rw [hx', hlam', hS']
      exact inv_local_step ih ha hs hγ
    · obtain ⟨w, hw, -, hrest⟩ := hstep
      split_ifs at hrest with hfw
      · obtain ⟨⟨γ, hγ, -, hx', hlam', hS'⟩, -⟩ := hrest
        rw [hx', hlam', hS']
        exact inv_fw_step ih hw hγ
      · obtain ⟨hx', hS', hlam', -⟩ := hrest
        rw [hx', hS', hlam']
        exact ih

universe u

theorem lazy_convex_rate : LazyConvexRate.{u} := by
  intro E _ _ V f L J x S lam Φ hconv hsm hJ hrun xStar hxs hΦ0 hΦ0' ε hε t ht
  classical
  set D := Metric.diam (↑V : Set E) with hD
  set P := convexHull ℝ (↑V : Set E) with hP
  set Q : ℝ := 8 * J ^ 2 * L * D ^ 2 with hQ
  set h : ℕ → ℝ := fun t => f (x t) - f xStar with hh
  have hJ0 : 0 < J := by linarith
  have inv := lazy_bpcg_run_inv hrun
  have hxP : ∀ t, x t ∈ P := fun t =>
    convexHull_mono (by exact_mod_cast (inv t).sub) (inv t).mem_convexHull
  have hPc : IsCompact P := V.finite_toSet.isCompact_convexHull (𝕜 := ℝ)
  have hh0 : ∀ t, 0 ≤ h t := fun t => by simp only [hh]; linarith [hxs.2 _ (hxP t)]
  have hdist : ∀ y ∈ P, ∀ z ∈ P, ‖y - z‖ ≤ D := fun y hy z hz => by
    rw [← dist_eq_norm, hD, ← convexHull_diam]
    exact Metric.dist_le_diam_of_mem hPc.isBounded hy hz
  have hgapw : ∀ t (w : E), (∀ u ∈ V, fderiv ℝ f (x t) w ≤ fderiv ℝ f (x t) u) →
      h t ≤ fderiv ℝ f (x t) (x t - w) := fun t w hwV => by
    have h1 := add_fderiv_le_of_convexOn hconv hsm.1 (x t) xStar
    have h2 := Lemmata.CGBasics.Proof.le_on_hull (fderiv ℝ f (x t)) hwV hxs.1
    simp only [hh]
    rw [map_sub] at h1 ⊢
    linarith
  -- each step: monotone, and `Φ` stays or halves
  have hbasic : ∀ t, h (t + 1) ≤ h t ∧ (Φ (t + 1) = Φ t ∨ Φ (t + 1) = Φ t / 2) := by
    intro t
    obtain ⟨a, ha, -, s, hs, -, hstep⟩ := hrun.2.2.2 t
    unfold IsLazyBPCGStep at hstep
    split_ifs at hstep with hsel
    · obtain ⟨⟨γ, hγ, hls, hx', -, -⟩, hΦ'⟩ := hstep
      refine ⟨?_, Or.inl hΦ'⟩
      have := hls 0 ⟨le_rfl, (inv t).nonneg a⟩
      simp only [hh, hx']; simp at this; linarith
    · obtain ⟨w, hw, -, hrest⟩ := hstep
      split_ifs at hrest with hfw
      · obtain ⟨⟨γ, hγ, hls, hx', -, -⟩, hΦ'⟩ := hrest
        refine ⟨?_, Or.inl hΦ'⟩
        have := hls 0 ⟨le_rfl, zero_le_one⟩
        simp only [hh, hx']; simp at this; linarith
      · obtain ⟨hx', -, -, hΦ'⟩ := hrest
        exact ⟨by simp only [hh, hx', le_refl], Or.inr hΦ'⟩
  have hmono : ∀ t, h (t + 1) ≤ h t := fun t => (hbasic t).1
  have hanti : Antitone h := antitone_nat_of_succ_le hmono
  have hΦb : ∀ t, 0 ≤ Φ t ∧ Φ t ≤ Φ 0 := by
    intro t
    induction t with
    | zero => exact ⟨by linarith [hh0 0], le_rfl⟩
    | succ t ih =>
      rcases (hbasic t).2 with hΦ' | hΦ'
      · rw [hΦ']; exact ih
      · rw [hΦ']; exact ⟨by linarith [ih.1], by linarith [ih.1, ih.2]⟩
  -- the degenerate case `L D² = 0`
  rcases eq_or_lt_of_le (by positivity : (0 : ℝ) ≤ L * D ^ 2) with hK0 | hKpos
  · have h1 : h 0 ≤ 0 := by simp only [hh]; rw [← hK0] at hΦ0'; linarith
    have h2 := hanti (Nat.zero_le t)
    have h3 : h t ≤ ε := by linarith
    simpa [hh] using h3
  have hLpos : 0 < (L : ℝ) := by
    rcases eq_or_lt_of_le (NNReal.coe_nonneg L) with h0 | h0
    · rw [← h0, zero_mul] at hKpos; exact absurd hKpos (lt_irrefl 0)
    · exact h0
  have hQpos : 0 < Q := by
    rw [hQ]; have := pow_pos hJ0 2
    nlinarith
  have hΦK : ∀ t, Φ t ≤ J * (L * D ^ 2) := fun t => by
    have h1 := (hΦb t).2
    have h2 : L * D ^ 2 ≤ J * (L * D ^ 2) := le_mul_of_one_le_left hKpos.le hJ
    linarith
  have hout : ∀ t, (h t ≤ Φ t ∧ x (t + 1) = x t ∧ S (t + 1) = S t ∧ Φ (t + 1) = Φ t / 2) ∨
      (h (t + 1) ≤ h t ∧ (S (t + 1)).card + 1 = (S t).card ∧ Φ (t + 1) = Φ t) ∨
      (h (t + 1) * Q ≤ h t * Q - 4 * Φ t ^ 2 ∧ (S (t + 1)).card ≤ (S t).card ∧
        Φ (t + 1) = Φ t) ∨
      (h (t + 1) * Q ≤ h t * Q - 4 * Φ t ^ 2 ∧ (S (t + 1)).card ≤ (S t).card + 1 ∧
        Φ (t + 1) = Φ t) := by
    intro t
    obtain ⟨a, ha, -, s, hs, -, hstep⟩ := hrun.2.2.2 t
    have haP : a ∈ P := subset_convexHull ℝ _ (by exact_mod_cast (inv t).sub ha)
    have hsP : s ∈ P := subset_convexHull ℝ _ (by exact_mod_cast (inv t).sub hs)
    unfold IsLazyBPCGStep at hstep
    split_ifs at hstep with hsel
    · obtain ⟨⟨γ, hγ, hls, hx', -, hS'⟩, hΦ'⟩ := hstep
      by_cases hdrop : γ = lam t a ∧ a ≠ s
      · right; left
        exact ⟨hmono t, by rw [hS', ite_eq_left hdrop]; exact Finset.card_erase_add_one ha, hΦ'⟩
      · right; right; left
        refine ⟨?_, by rw [hS', ite_eq_right hdrop], hΦ'⟩
        by_cases has : a = s
        · subst has
          have hΦ0t : Φ t = 0 := le_antisymm (by simpa using hsel) (hΦb t).1
          have e : h (t + 1) = h t := by simp only [hh, hx', sub_self, smul_zero, sub_zero]
          rw [hΦ0t, e]; simp
        · have hγlt : γ < lam t a := lt_of_le_of_ne hγ.2 (fun e => hdrop ⟨e, has⟩)
          have hray := ray_opt hconv hγlt hls hγ.1
          set G := fderiv ℝ f (x t) (a - s) with hG
          have hd : 0 < ‖a - s‖ := norm_pos_iff.mpr (sub_ne_zero.mpr has)
          have hdD : ‖a - s‖ ≤ D := hdist a haP s hsP
          have hc : 0 < (L : ℝ) * ‖a - s‖ ^ 2 := by positivity
          set σ := G / (L * ‖a - s‖ ^ 2) with hσ
          have hσ0 : 0 ≤ σ := div_nonneg ((hΦb t).1.trans hsel) hc.le
          have h1 := hray σ hσ0
          have h2 := quad_along hsm (x t) (a - s) σ
          rw [← hG] at h2
          have e : σ * G - σ ^ 2 * L / 2 * ‖a - s‖ ^ 2 = G ^ 2 / (2 * (L * ‖a - s‖ ^ 2)) := by
            rw [hσ]; field_simp; ring
          have hdD2 : (L : ℝ) * ‖a - s‖ ^ 2 ≤ L * D ^ 2 :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hd.le hdD 2) hLpos.le
          have h3 : Φ t ^ 2 / (2 * (L * D ^ 2)) ≤ G ^ 2 / (2 * (L * ‖a - s‖ ^ 2)) :=
            calc Φ t ^ 2 / (2 * (L * D ^ 2)) ≤ G ^ 2 / (2 * (L * D ^ 2)) :=
                  div_le_div_of_nonneg_right (pow_le_pow_left₀ (hΦb t).1 hsel 2) (by positivity)
              _ ≤ G ^ 2 / (2 * (L * ‖a - s‖ ^ 2)) :=
                  div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by linarith)
          have hprog : Φ t ^ 2 / (2 * (L * D ^ 2)) ≤ h t - h (t + 1) := by
            simp only [hh, hx']; linarith
          have e2 : Φ t ^ 2 / (2 * (L * D ^ 2)) * Q = 4 * J ^ 2 * Φ t ^ 2 := by
            rw [hQ, div_mul_eq_mul_div, div_eq_iff (mul_pos two_pos hKpos).ne']; ring
          have h5 := mul_le_mul_of_nonneg_right hprog hQpos.le
          rw [e2] at h5
          have hJ2 : (1 : ℝ) ≤ J ^ 2 := by nlinarith
          have h6 := mul_le_mul_of_nonneg_right hJ2 (sq_nonneg (Φ t))
          linarith
    · obtain ⟨w, hw, hwV, hrest⟩ := hstep
      have hwP : w ∈ P := subset_convexHull ℝ _ (by exact_mod_cast hw)
      split_ifs at hrest with hfw
      · obtain ⟨⟨γ, hγ, hls, hx', -, hS'⟩, hΦ'⟩ := hrest
        right; right; right
        refine ⟨?_, by rw [hS']; split_ifs <;> simp [Finset.card_insert_le], hΦ'⟩
        set G := fderiv ℝ f (x t) (x t - w) with hG
        have hdD : ‖x t - w‖ ≤ D := hdist (x t) (hxP t) w hwP
        set σ := Φ t / (J * (L * D ^ 2)) with hσ
        have hσ0 : 0 ≤ σ := div_nonneg (hΦb t).1 (by positivity)
        have hσ1 : σ ≤ 1 := by rw [hσ, div_le_one (by positivity)]; exact hΦK t
        have h1 := hls σ ⟨hσ0, hσ1⟩
        have h2 := quad_along hsm (x t) (x t - w) σ
        rw [← hG] at h2
        have hd2 : σ ^ 2 * L / 2 * ‖x t - w‖ ^ 2 ≤ σ ^ 2 * (L * D ^ 2) / 2 := by
          have := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hdD 2)
            (by positivity : (0 : ℝ) ≤ σ ^ 2 * L)
          nlinarith
        have hg : σ * (Φ t / J) ≤ σ * G := mul_le_mul_of_nonneg_left hfw hσ0
        have he : σ * (Φ t / J) - σ ^ 2 * (L * D ^ 2) / 2 =
            Φ t ^ 2 / (2 * J ^ 2 * (L * D ^ 2)) := by
          rw [hσ]; field_simp; ring
        have hprog : Φ t ^ 2 / (2 * J ^ 2 * (L * D ^ 2)) ≤ h t - h (t + 1) := by
          simp only [hh, hx']; linarith
        have e2 : Φ t ^ 2 / (2 * J ^ 2 * (L * D ^ 2)) * Q = 4 * Φ t ^ 2 := by
          rw [hQ, div_mul_eq_mul_div,
            div_eq_iff (mul_pos (mul_pos two_pos (pow_pos hJ0 2)) hKpos).ne']
          ring
        have h5 := mul_le_mul_of_nonneg_right hprog hQpos.le
        rw [e2] at h5
        linarith
      · obtain ⟨hx', hS', -, hΦ'⟩ := hrest
        left
        refine ⟨?_, hx', hS', hΦ'⟩
        push Not at hfw
        have h1 := hgapw t w hwV
        have h2 : Φ t / J ≤ Φ t := div_le_self (hΦb t).1 hJ
        linarith
  have hinv2 : ∀ t, h t ≤ 2 * Φ t := by
    intro t
    induction t with
    | zero => simp only [hh]; linarith
    | succ t ih =>
      rcases hout t with ⟨hc, hx', -, hΦ'⟩ | ⟨h1, -, hΦ'⟩ | ⟨-, -, hΦ'⟩ | ⟨-, -, hΦ'⟩
      · rw [hΦ']
        have e : h (t + 1) = h t := by simp only [hh, hx']
        linarith
      · rw [hΦ']; linarith
      · rw [hΦ']; linarith [hmono t]
      · rw [hΦ']; linarith [hmono t]
  have hgood : ∀ t, h (t + 1) * Q ≤ h t * Q - 4 * Φ t ^ 2 → h (t + 1) ≤ h t - h t ^ 2 / Q :=
    fun t hle => by
      have h2 : h t ^ 2 ≤ 4 * Φ t ^ 2 := by
        have := pow_le_pow_left₀ (hh0 t) (hinv2 t) 2
        nlinarith
      have h3 : h t ^ 2 / Q ≤ h t - h (t + 1) := by rw [div_le_iff₀ hQpos]; linarith
      linarith
  set n₀ := ⌈Real.logb 2 (Φ 0 / ε)⌉₊ with hn₀
  have hφε : Φ 0 / 2 ^ n₀ ≤ ε := by
    rcases le_or_gt (Φ 0) 0 with hφ | hφ
    · have : Φ 0 / 2 ^ n₀ ≤ 0 := div_nonpos_of_nonpos_of_nonneg hφ (by positivity)
      linarith
    · rw [div_le_iff₀ (by positivity)]
      have h1 : Real.logb 2 (Φ 0 / ε) ≤ n₀ := Nat.le_ceil _
      have h2 : Φ 0 / ε ≤ (2 : ℝ) ^ (n₀ : ℝ) := by
        rw [← Real.logb_le_logb (b := 2) (by norm_num) (div_pos hφ hε) (by positivity),
          Real.logb_rpow (by norm_num) (by norm_num)]
        exact h1
      rw [Real.rpow_natCast, div_le_iff₀ hε] at h2
      linarith
  have hstate : ∀ t, ∃ n dr gd nfw : ℕ, n + dr + gd = t ∧ nfw ≤ gd ∧
      (S t).card + dr ≤ 1 + nfw ∧ h t * ((gd : ℝ) + 8) ≤ Q ∧ Φ t = Φ 0 / 2 ^ n ∧
      (n₀ + 1 ≤ n → h t ≤ ε) := by
    intro t
    induction t with
    | zero =>
      refine ⟨0, 0, 0, 0, rfl, le_rfl, by rw [hrun.2.1]; simp, ?_, by simp,
        fun h => absurd h (by omega)⟩
      have h1 := hinv2 0
      have h2 : (1 : ℝ) ≤ J ^ 2 := by nlinarith
      have h3 : L * D ^ 2 ≤ J ^ 2 * (L * D ^ 2) := le_mul_of_one_le_left hKpos.le h2
      push_cast
      rw [hQ]
      nlinarith [(hΦb 0).2]
    | succ t ih =>
      obtain ⟨n, dr, gd, nfw, hsum, hfw, hcard, hpot, hφn, hε'⟩ := ih
      rcases hout t with ⟨hc, hx', hS', hΦ'⟩ | ⟨h1, hc', hΦ'⟩ | ⟨h1, hc', hΦ'⟩ | ⟨h1, hc', hΦ'⟩
      · have e : h (t + 1) = h t := by simp only [hh, hx']
        refine ⟨n + 1, dr, gd, nfw, by omega, hfw, by rw [hS']; exact hcard,
          by rw [e]; exact hpot, by rw [hΦ', hφn, pow_succ]; field_simp, fun hN => ?_⟩
        rw [e]
        rcases Nat.lt_or_ge n (n₀ + 1) with hlt | hge
        · have hN0 : n = n₀ := by omega
          calc h t ≤ Φ t := hc
            _ = Φ 0 / 2 ^ n := hφn
            _ = Φ 0 / 2 ^ n₀ := by rw [hN0]
            _ ≤ ε := hφε
        · exact hε' hge
      · refine ⟨n, dr + 1, gd, nfw, by omega, hfw, by omega, ?_, by rw [hΦ', hφn],
          fun hN => h1.trans (hε' hN)⟩
        exact le_trans (mul_le_mul_of_nonneg_right h1 (by positivity)) hpot
      · refine ⟨n, dr, gd + 1, nfw, by omega, by omega, by omega,
          potential_step' hQpos (hgood t h1) hpot, by rw [hΦ', hφn],
          fun hN => (hmono t).trans (hε' hN)⟩
      · refine ⟨n, dr, gd + 1, nfw + 1, by omega, by omega, by omega,
          potential_step' hQpos (hgood t h1) hpot, by rw [hΦ', hφn],
          fun hN => (hmono t).trans (hε' hN)⟩
  obtain ⟨n, dr, gd, nfw, hsum, hfw, hcard, hpot, -, hεn⟩ := hstate t
  set P₀ := ⌈Q / ε⌉₊ with hP₀
  have hS1 : 1 ≤ (S t).card := by
    rcases Nat.eq_zero_or_pos (S t).card with h0 | h0
    · have := (inv t).sum
      rw [Finset.card_eq_zero.mp h0, Finset.sum_empty] at this
      norm_num at this
    · exact h0
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

end Lemmata.BPCG
