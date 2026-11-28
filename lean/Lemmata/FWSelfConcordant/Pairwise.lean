module

public import Lemmata.FWSelfConcordant.Away
public import Lemmata.BPCG.Proof

@[expose] public section

/-!
# Blended pairwise conditional gradients with backtracking

The analysis of away-step Frank–Wolfe with backtracking carries over to blended pairwise
conditional gradients: in both branches the chosen gap is at least half of `f'(x)(a - w)`, since
the local Frank–Wolfe vertex `s` satisfies `f'(x)(s) ≤ f'(x)(x)`. A pairwise step with maximal step
size drops the away vertex; every other step contracts the primal gap. The invariants of the state
come from the BPCG entry.
-/

namespace Lemmata.FWSelfConcordant

open Lemmata.FrankWolfe Lemmata.AwayStepFW Lemmata.AwayStepFW.Proof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
/-- A step of blended pairwise conditional gradients with backtracking preserves the invariant. -/
theorem inv_bbstep {V : Finset E} {L : ℝ} (hL : 0 < L) {g : StrongDual ℝ E} {x : E}
    {S : Finset E} {lam : E → ℝ} (h : Inv V x S lam) {a s w x' : E} {S' : Finset E}
    {lam' : E → ℝ} (ha : a ∈ S) (hs : s ∈ S) (hw : w ∈ V) (hwV : ∀ u ∈ V, g w ≤ g u)
    (hstep : IsBBPCGStep L g x S lam a s w x' S' lam') : Inv V x' S' lam' := by
  classical
  have hgFW : 0 ≤ g (x - w) := by rw [map_sub]; linarith [h.le_apply g hwV]
  unfold IsBBPCGStep at hstep
  split_ifs at hstep with hsel
  · dsimp only at hstep
    obtain ⟨rfl, rfl, rfl⟩ := hstep
    apply Lemmata.BPCG.Proof.inv_local_step h ha hs
    exact ⟨le_min (div_nonneg (by linarith) (by positivity)) (h.nonneg a), min_le_right _ _⟩
  · dsimp only at hstep
    obtain ⟨rfl, rfl, rfl⟩ := hstep
    apply Lemmata.BPCG.Proof.inv_fw_step h hw
    exact ⟨le_min (div_nonneg hgFW (by positivity)) zero_le_one, min_le_right _ _⟩

set_option maxHeartbeats 1000000 in
open Classical in
/-- One step of blended pairwise conditional gradients with backtracking is a good step, which
contracts the primal gap by `1 - min {1/2, μ δ²/(4 L̃ D²)}` and adds at most one vertex, or a drop
step, which does not increase `f` and removes a vertex. -/
theorem bbpcg_step_outcome {V : Finset E} {f : E → ℝ} {L Lmax μ δ : ℝ} (hL : 0 < L)
    (hLm : L ≤ Lmax) (hμ : 0 < μ) (hδ : 0 < δ) (hsc : IsScaling V δ) {xStar : E}
    (hxsV : xStar ∈ convexHull ℝ (↑V : Set E)) {x : E} {S : Finset E} {lam : E → ℝ}
    (h : Inv V x S lam) (hh0 : 0 ≤ f x - f xStar)
    (hpair : f x + fderiv ℝ f x (xStar - x) + μ / 2 * ‖xStar - x‖ ^ 2 ≤ f xStar)
    {a s w : E} (ha : a ∈ S) (haS : ∀ u ∈ S, fderiv ℝ f x u ≤ fderiv ℝ f x a) (hs : s ∈ S)
    (hsS : ∀ u ∈ S, fderiv ℝ f x s ≤ fderiv ℝ f x u) (hw : w ∈ V)
    (hwV : ∀ u ∈ V, fderiv ℝ f x w ≤ fderiv ℝ f x u) {x' : E} {S' : Finset E} {lam' : E → ℝ}
    (hstep : IsBBPCGStep L (fderiv ℝ f x) x S lam a s w x' S' lam')
    (hdec : f x' ≤ f x + fderiv ℝ f x (x' - x) + L / 2 * ‖x' - x‖ ^ 2) :
    (f x' - f xStar ≤ (1 - min (1 / 2) (μ * δ ^ 2 / (4 * Lmax * Metric.diam (↑V : Set E) ^ 2))) *
        (f x - f xStar) ∧ S'.card ≤ S.card + 1) ∨
      (f x' ≤ f x ∧ S'.card + 1 = S.card) := by
  classical
  set ρ := min (1 / 2) (μ * δ ^ 2 / (4 * Lmax * Metric.diam (↑V : Set E) ^ 2)) with hρ
  set D := Metric.diam (↑V : Set E) with hD
  set g := fderiv ℝ f x with hg
  have hLm0 : 0 < Lmax := lt_of_lt_of_le hL hLm
  have hxV : x ∈ convexHull ℝ (↑V : Set E) :=
    convexHull_mono (by exact_mod_cast h.sub) h.mem_convexHull
  have hbdd : Bornology.IsBounded (convexHull ℝ (↑V : Set E)) :=
    isBounded_convexHull.mpr V.finite_toSet.isBounded
  have hdist : ∀ y ∈ convexHull ℝ (↑V : Set E), ∀ z ∈ convexHull ℝ (↑V : Set E), ‖y - z‖ ≤ D :=
    fun y hy z hz => by
      rw [← dist_eq_norm, hD, ← convexHull_diam]; exact Metric.dist_le_diam_of_mem hbdd hy hz
  have hwC : w ∈ convexHull ℝ (↑V : Set E) := subset_convexHull ℝ _ (by exact_mod_cast hw)
  have haC : a ∈ convexHull ℝ (↑V : Set E) := subset_convexHull ℝ _ (by exact_mod_cast h.sub ha)
  have hsC : s ∈ convexHull ℝ (↑V : Set E) := subset_convexHull ℝ _ (by exact_mod_cast h.sub hs)
  have hgFW : 0 ≤ g (x - w) := by rw [map_sub]; linarith [h.le_apply g hwV]
  have hsx : g s ≤ g x := Lemmata.CGBasics.Proof.le_on_hull (V := S) g hsS h.mem_convexHull
  have hax : g (a - x) ≤ g (a - s) := by rw [map_sub, map_sub]; linarith
  have hgeo := geo_pair hμ hδ hsc hxsV h.sub h.mem_convexHull hpair ha haS hw hwV
  have hsplit : g (a - w) = g (a - x) + g (x - w) := by rw [map_sub, map_sub, map_sub]; ring
  have hρ1 : ρ ≤ 1 / 2 := min_le_left _ _
  have hρ2 : ρ ≤ μ * δ ^ 2 / (4 * Lmax * D ^ 2) := min_le_right _ _
  have hgood : ∀ G : ℝ, 0 ≤ G → g (a - w) ≤ 2 * G → 0 < D →
      f x - f xStar - G ^ 2 / (2 * Lmax * D ^ 2) ≤ (1 - ρ) * (f x - f xStar) := by
    intro G hG hGa hDpos
    have h1 : 2 * μ * δ ^ 2 * (f x - f xStar) ≤ g (a - w) ^ 2 := by
      have := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * μ * δ ^ 2)).mp hgeo
      linarith
    have hga0 : 0 ≤ g (a - w) := by
      have : 0 ≤ g (a - x) := by rw [map_sub]; linarith [h.apply_le g haS]
      linarith
    have h2 : g (a - w) ^ 2 ≤ 4 * G ^ 2 := by
      have := pow_le_pow_left₀ hga0 hGa 2
      nlinarith [this]
    have h3 : μ * δ ^ 2 / (4 * Lmax * D ^ 2) * (f x - f xStar) ≤ G ^ 2 / (2 * Lmax * D ^ 2) := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
      have := mul_le_mul_of_nonneg_right (h1.trans h2) (by positivity : (0 : ℝ) ≤ Lmax * D ^ 2)
      nlinarith [this]
    have h4 := mul_le_mul_of_nonneg_right hρ2 hh0
    linarith
  have hcmp : ∀ G d : ℝ, 0 < d → d ≤ D →
      G ^ 2 / (2 * Lmax * D ^ 2) ≤ G ^ 2 / (2 * (L * d ^ 2)) := by
    intro G d hd hdD
    apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
    have : d ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ hd.le hdD 2
    nlinarith [mul_le_mul hLm this (by positivity) hLm0.le]
  have hFWgap : f x - f xStar ≤ g (x - w) := by
    have h2 := le_of_min_vertex g hwV hxsV
    have e2 : g (xStar - x) = g xStar - g x := map_sub _ _ _
    rw [map_sub]
    nlinarith [sq_nonneg ‖xStar - x‖]
  unfold IsBBPCGStep at hstep
  split_ifs at hstep with hsel
  · -- the pairwise step
    dsimp only at hstep
    obtain ⟨hx', -, hS'⟩ := hstep
    set G := g (a - s) with hG
    have hGa : g (a - w) ≤ 2 * G := by linarith
    have hG0 : 0 < G := lt_of_le_of_lt hgFW hsel
    have hne : a ≠ s := by
      intro e; rw [hG, e, sub_self, map_zero] at hG0; exact lt_irrefl _ hG0
    have hdpos : 0 < ‖a - s‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    have hc : 0 < L * ‖a - s‖ ^ 2 := by positivity
    have hdD : ‖a - s‖ ≤ D := hdist a haC s hsC
    have hDpos : 0 < D := lt_of_lt_of_le hdpos hdD
    set γ := min (G / (L * ‖a - s‖ ^ 2)) (lam a) with hγ
    have hγ0 : 0 ≤ γ := le_min (div_nonneg hG0.le hc.le) (h.nonneg a)
    have hγle : γ ≤ G / (L * ‖a - s‖ ^ 2) := min_le_left _ _
    have hprog : f x' ≤ f x - γ * G + γ ^ 2 * L / 2 * ‖a - s‖ ^ 2 := by
      have e1 : x' - x = -(γ • (a - s)) := by rw [hx']; abel
      rw [e1, map_neg, map_smul, smul_eq_mul, norm_neg, norm_smul, Real.norm_of_nonneg hγ0,
        mul_pow] at hdec
      linarith
    have hdec' : γ ^ 2 * L / 2 * ‖a - s‖ ^ 2 ≤ γ * G / 2 := by
      have : γ * (L * ‖a - s‖ ^ 2) ≤ G := by rwa [le_div_iff₀ hc] at hγle
      calc γ ^ 2 * L / 2 * ‖a - s‖ ^ 2 = γ / 2 * (γ * (L * ‖a - s‖ ^ 2)) := by ring
        _ ≤ γ / 2 * G := mul_le_mul_of_nonneg_left this (by positivity)
        _ = γ * G / 2 := by ring
    rcases eq_or_ne γ (lam a) with hdrop | hdrop
    · right
      have : 0 ≤ γ * G := mul_nonneg hγ0 hG0.le
      refine ⟨by linarith, ?_⟩
      rw [hS', ite_eq_left ⟨hdrop, hne⟩]
      exact Finset.card_erase_add_one ha
    · left
      have hγv : γ = G / (L * ‖a - s‖ ^ 2) := by
        rcases min_choice (G / (L * ‖a - s‖ ^ 2)) (lam a) with h1 | h1
        · rw [hγ, h1]
        · exact absurd (by rw [hγ, h1]) hdrop
      refine ⟨?_, ?_⟩
      · have hval : γ * G - γ ^ 2 * L / 2 * ‖a - s‖ ^ 2 = G ^ 2 / (2 * (L * ‖a - s‖ ^ 2)) := by
          rw [hγv]; field_simp; ring
        have := hgood G hG0.le hGa hDpos
        have := hcmp G ‖a - s‖ hdpos hdD
        linarith
      · rw [hS', ite_eq_right (fun hc => hdrop hc.1)]; omega
  · -- the Frank–Wolfe step
    dsimp only at hstep
    obtain ⟨hx', -, hS'⟩ := hstep
    left
    refine ⟨?_, ?_⟩
    · set G := g (x - w) with hG
      have hGa : g (a - w) ≤ 2 * G := by linarith [not_lt.mp hsel]
      rcases eq_or_lt_of_le (norm_nonneg (x - w)) with hd0 | hdpos
      · have hxw : x - w = 0 := norm_eq_zero.mp hd0.symm
        have hG0 : G = 0 := by rw [hG, hxw, map_zero]
        have hx'x : x' = x := by rw [hx', hxw, smul_zero, sub_zero]
        rw [hx'x]; nlinarith
      · have hc : 0 < L * ‖x - w‖ ^ 2 := by positivity
        have hdD : ‖x - w‖ ≤ D := hdist x hxV w hwC
        have hDpos : 0 < D := lt_of_lt_of_le hdpos hdD
        set γ := min (G / (L * ‖x - w‖ ^ 2)) 1 with hγ
        have hγ0 : 0 ≤ γ := le_min (div_nonneg hgFW hc.le) zero_le_one
        have hprog : f x' ≤ f x - γ * G + γ ^ 2 * L / 2 * ‖x - w‖ ^ 2 := by
          have e1 : x' - x = -(γ • (x - w)) := by rw [hx']; abel
          rw [e1, map_neg, map_smul, smul_eq_mul, norm_neg, norm_smul, Real.norm_of_nonneg hγ0,
            mul_pow] at hdec
          linarith
        rcases le_total (G / (L * ‖x - w‖ ^ 2)) 1 with hle | hle
        · rw [min_eq_left hle] at hγ
          have hval : γ * G - γ ^ 2 * L / 2 * ‖x - w‖ ^ 2 = G ^ 2 / (2 * (L * ‖x - w‖ ^ 2)) := by
            rw [hγ]; field_simp; ring
          have := hgood G hgFW hGa hDpos
          have := hcmp G ‖x - w‖ hdpos hdD
          linarith
        · rw [min_eq_right hle] at hγ
          rw [hγ] at hprog
          have hcG : L * ‖x - w‖ ^ 2 ≤ G := by
            rwa [le_div_iff₀ hc, one_mul] at hle
          have h5 : f x' ≤ f x - G / 2 := by nlinarith [hprog, hcG]
          have h6 := mul_le_mul_of_nonneg_right hρ1 hh0
          linarith
    · rw [hS']
      split_ifs
      · simp
      · exact Finset.card_insert_le w S

/-- The invariant of the state along a run of blended pairwise conditional gradients with
backtracking. -/
theorem bbpcg_inv {V : Finset E} {D : Set E} {f : E → ℝ} {Lmax : ℝ} {x : ℕ → E}
    {S : ℕ → Finset E} {lam : ℕ → E → ℝ} (h : IsBBPCGRun V D f Lmax x S lam) :
    ∀ t, Inv V (x t) (S t) (lam t) := by
  classical
  obtain ⟨hx0, -, hS0, hlam0, hsteps⟩ := h
  intro t
  induction t with
  | zero =>
    refine ⟨by rw [hS0]; simpa using hx0, fun w => ?_, fun w hw => ?_, ?_, ?_⟩
    · rw [hlam0]; dsimp only; split_ifs <;> norm_num
    · rw [hS0, Finset.mem_singleton] at hw; rw [hlam0]; simp [hw]
    · rw [hS0, hlam0]; simp
    · rw [hS0, hlam0]; simp
  | succ t ih =>
    obtain ⟨L, hL, -, a, ha, -, s, hs, -, w, hw, hwV, hstep, -, -⟩ := hsteps t
    exact inv_bbstep hL ih ha hs hw hwV hstep

/-- Counting good steps along a run of blended pairwise conditional gradients with backtracking. -/
theorem bbpcg_bound {V : Finset E} {D : Set E} {f : E → ℝ} {Lmax μ δ : ℝ} {x : ℕ → E}
    {S : ℕ → Finset E} {lam : ℕ → E → ℝ} {xStar : E}
    (hxs : xStar ∈ minimizers (convexHull ℝ (↑V : Set E) ∩ D) f) (hμ : 0 < μ) (hδ : 0 < δ)
    (hsc : IsScaling V δ)
    (hstr : ∀ y ∈ convexHull ℝ (↑V : Set E) ∩ D, f y ≤ f (x 0) →
      ∀ z ∈ convexHull ℝ (↑V : Set E) ∩ D, f z ≤ f (x 0) →
        f y + fderiv ℝ f y (z - y) + μ / 2 * ‖z - y‖ ^ 2 ≤ f z)
    (hrun : IsBBPCGRun V D f Lmax x S lam) (hLm : 0 < Lmax) :
    ∀ t : ℕ, ∃ G : ℕ, (S t).card + t ≤ 1 + 2 * G ∧ f (x t) ≤ f (x 0) ∧ x t ∈ D ∧
      f (x t) - f xStar ≤
        (1 - min (1 / 2) (μ * δ ^ 2 / (4 * Lmax * Metric.diam (↑V : Set E) ^ 2))) ^ G *
          (f (x 0) - f xStar) := by
  classical
  set ρ := min (1 / 2) (μ * δ ^ 2 / (4 * Lmax * Metric.diam (↑V : Set E) ^ 2)) with hρ
  have hρ0 : 0 ≤ ρ := le_min (by norm_num) (by positivity)
  have hρ1 : ρ ≤ 1 / 2 := min_le_left _ _
  have hinv := bbpcg_inv hrun
  have hxC : ∀ t, x t ∈ convexHull ℝ (↑V : Set E) := fun t =>
    convexHull_mono (by exact_mod_cast (hinv t).sub) (hinv t).mem_convexHull
  have hx0D : x 0 ∈ D := hrun.2.1
  have hs0 : f xStar ≤ f (x 0) := hxs.2 _ ⟨hxC 0, hx0D⟩
  intro t
  induction t with
  | zero =>
    refine ⟨0, ?_, le_rfl, hx0D, by simp⟩
    rw [hrun.2.2.1]; simp
  | succ t ih =>
    obtain ⟨G, hcard, hft, hxD, hb⟩ := ih
    obtain ⟨L, hL, hLL, a, ha, haS, s, hs, hsS, w, hw, hwV, hstep, hxD', hdec⟩ :=
      hrun.2.2.2.2 t
    have hh0 : 0 ≤ f (x t) - f xStar := sub_nonneg.mpr (hxs.2 _ ⟨hxC t, hxD⟩)
    have hpair := hstr (x t) ⟨hxC t, hxD⟩ hft xStar hxs.1 hs0
    rcases bbpcg_step_outcome hL hLL hμ hδ hsc hxs.1.1 (hinv t) hh0 hpair ha haS hs hsS hw hwV
      hstep hdec with ⟨hgood, hc⟩ | ⟨hdrop, hc⟩
    · refine ⟨G + 1, by omega, ?_, hxD', ?_⟩
      · have : (1 - ρ) * (f (x t) - f xStar) ≤ f (x t) - f xStar := by nlinarith
        linarith
      · calc f (x (t + 1)) - f xStar ≤ (1 - ρ) * (f (x t) - f xStar) := hgood
          _ ≤ (1 - ρ) * ((1 - ρ) ^ G * (f (x 0) - f xStar)) :=
            mul_le_mul_of_nonneg_left hb (by linarith)
          _ = (1 - ρ) ^ (G + 1) * (f (x 0) - f xStar) := by ring
    · exact ⟨G, by omega, le_trans hdrop hft, hxD', by linarith⟩

/-- Theorem 3.2 for blended pairwise conditional gradients with backtracking. -/
theorem pairwise_linear_bound {V : Finset E} {D : Set E} {f : E → ℝ} {Lmax μ δ : ℝ} {x : ℕ → E}
    {S : ℕ → Finset E} {lam : ℕ → E → ℝ} {xStar : E}
    (hxs : xStar ∈ minimizers (convexHull ℝ (↑V : Set E) ∩ D) f) (hLm : 0 < Lmax) (hμ : 0 < μ)
    (hδ : 0 < δ) (hsc : IsScaling V δ)
    (hstr : ∀ y ∈ convexHull ℝ (↑V : Set E) ∩ D, f y ≤ f (x 0) →
      ∀ z ∈ convexHull ℝ (↑V : Set E) ∩ D, f z ≤ f (x 0) →
        f y + fderiv ℝ f y (z - y) + μ / 2 * ‖z - y‖ ^ 2 ≤ f z)
    (hrun : IsBBPCGRun V D f Lmax x S lam) (t : ℕ) :
    f (x t) - f xStar ≤
      (1 - min (1 / 2) (μ * δ ^ 2 / (4 * Lmax * Metric.diam (↑V : Set E) ^ 2))) ^
        ⌈((t : ℝ) - 1) / 2⌉₊ * (f (x 0) - f xStar) := by
  set ρ := min (1 / 2) (μ * δ ^ 2 / (4 * Lmax * Metric.diam (↑V : Set E) ^ 2)) with hρ
  have hρ0 : 0 ≤ ρ := le_min (by norm_num) (by positivity)
  have hρ1 : ρ ≤ 1 / 2 := min_le_left _ _
  obtain ⟨G, hcard, -, -, hb⟩ := bbpcg_bound hxs hμ hδ hsc hstr hrun hLm t
  have hS1 : 1 ≤ (S t).card := by
    have : (S t).Nonempty :=
      Finset.nonempty_of_sum_ne_zero (by rw [(bbpcg_inv hrun t).sum]; norm_num)
    exact Finset.card_pos.mpr this
  have hG : ⌈((t : ℝ) - 1) / 2⌉₊ ≤ G := by
    rw [Nat.ceil_le]
    have : (t : ℝ) ≤ 2 * G := by exact_mod_cast (by omega : t ≤ 2 * G)
    linarith
  have hx0 : x 0 ∈ convexHull ℝ (↑V : Set E) :=
    convexHull_mono (by exact_mod_cast (bbpcg_inv hrun 0).sub) (bbpcg_inv hrun 0).mem_convexHull
  have h0 : 0 ≤ f (x 0) - f xStar := sub_nonneg.mpr (hxs.2 _ ⟨hx0, hrun.2.1⟩)
  calc f (x t) - f xStar ≤ (1 - ρ) ^ G * (f (x 0) - f xStar) := hb
    _ ≤ (1 - ρ) ^ ⌈((t : ℝ) - 1) / 2⌉₊ * (f (x 0) - f xStar) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one (by linarith) (by linarith) hG) h0

namespace Proof

theorem pairwise_linear_rate : PairwiseLinearRate.{u} := by
  intro E _ _ V D f Lmax μ δ x S lam xStar hxs hLm hμ hδ hsc hstr hrun t
  exact pairwise_linear_bound hxs hLm hμ hδ hsc hstr hrun t

end Proof

end Lemmata.FWSelfConcordant
