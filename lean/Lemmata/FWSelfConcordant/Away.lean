module

public import Lemmata.FWSelfConcordant.Statement
public import Lemmata.AwayStepFW.Progress

@[expose] public section

/-!
# Away-step Frank–Wolfe with backtracking

The analysis of away-step Frank–Wolfe with the short step (`AwayStepFW.Proof.step_outcome`) carries
over to the backtracking line search: the sufficient decrease condition with an estimate
`L_t ≤ L̃` replaces global smoothness, and strong convexity is only used at the pair `(x_t, x⋆)`,
both of which lie in the sublevel set of `x₀`. Each step is a good step, which contracts the
primal gap, or a drop step, which removes a vertex from the active set; since the active set starts
with one vertex, at least half of the steps are good.
-/

namespace Lemmata.FWSelfConcordant

open Lemmata.FrankWolfe Lemmata.AwayStepFW Lemmata.AwayStepFW.Proof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Geometric strong convexity from the scaling property and strong convexity at the pair
`(x, x⋆)`: `f(x) - f(x⋆) ≤ f'(x)(a - v)²/(2 μ δ²)`. -/
theorem geo_pair {V : Finset E} {f : E → ℝ} {μ δ : ℝ} (hμ : 0 < μ) (hδ : 0 < δ)
    (hsc : IsScaling V δ) {xStar : E} (hxsV : xStar ∈ convexHull ℝ (↑V : Set E)) {S : Finset E}
    (hS : S ⊆ V) {x : E} (hx : x ∈ convexHull ℝ (↑S : Set E))
    (hpair : f x + fderiv ℝ f x (xStar - x) + μ / 2 * ‖xStar - x‖ ^ 2 ≤ f xStar)
    {a : E} (ha : a ∈ S) (haS : ∀ w ∈ S, fderiv ℝ f x w ≤ fderiv ℝ f x a) {v : E} (hvV : v ∈ V)
    (hv : ∀ w ∈ V, fderiv ℝ f x v ≤ fderiv ℝ f x w) :
    f x - f xStar ≤ fderiv ℝ f x (a - v) ^ 2 / (2 * μ * δ ^ 2) := by
  have hscale := hsc S hS x hx xStar hxsV (fderiv ℝ f x) a ha haS v hvV hv
  set A := fderiv ℝ f x (x - xStar) with hA
  set B := fderiv ℝ f x (a - v) with hB
  have e : fderiv ℝ f x (xStar - x) = -A := by rw [hA, ← map_neg, neg_sub]
  rw [e] at hpair
  rcases eq_or_lt_of_le (norm_nonneg (x - xStar)) with hd | hd
  · have hx' : x = xStar := by rw [← sub_eq_zero, ← norm_eq_zero]; exact hd.symm
    rw [hx', sub_self]; positivity
  · set d := ‖x - xStar‖ with hdd
    have hnd : ‖xStar - x‖ = d := norm_sub_rev _ _
    rw [hnd] at hpair
    rcases le_or_gt 0 A with hA0 | hA0
    · have h1 : f x - f xStar ≤ A ^ 2 / (2 * μ * d ^ 2) := by
        have : A - μ / 2 * d ^ 2 ≤ A ^ 2 / (2 * μ * d ^ 2) := by
          rw [le_div_iff₀ (by positivity)]; nlinarith [sq_nonneg (A - μ * d ^ 2)]
        linarith
      have hsq : (δ * A) ^ 2 ≤ (B * d) ^ 2 := pow_le_pow_left₀ (by positivity) hscale 2
      have h3 : A ^ 2 / (2 * μ * d ^ 2) ≤ B ^ 2 / (2 * μ * δ ^ 2) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hsq]
      linarith
    · have h1 : f x - f xStar < 0 := by nlinarith [sq_nonneg d]
      have h2 : 0 ≤ B ^ 2 / (2 * μ * δ ^ 2) := by positivity
      linarith

set_option maxHeartbeats 1000000 in
open Classical in
/-- One step of away-step Frank–Wolfe with backtracking is a good step, which contracts the primal
gap by `1 - min {1/2, μ δ²/(4 L̃ D²)}` and adds at most one vertex, or a drop step, which does not
increase `f` and removes a vertex. -/
theorem bafw_step_outcome {V : Finset E} {f : E → ℝ} {L Lmax μ δ : ℝ} (hL : 0 < L)
    (hLm : L ≤ Lmax) (hμ : 0 < μ) (hδ : 0 < δ) (hsc : IsScaling V δ) {xStar : E}
    (hxsV : xStar ∈ convexHull ℝ (↑V : Set E)) {x : E} {S : Finset E} {lam : E → ℝ}
    (h : Inv V x S lam) (hh0 : 0 ≤ f x - f xStar)
    (hpair : f x + fderiv ℝ f x (xStar - x) + μ / 2 * ‖xStar - x‖ ^ 2 ≤ f xStar)
    {v a : E} (hvV : v ∈ V) (hv : ∀ w ∈ V, fderiv ℝ f x v ≤ fderiv ℝ f x w) (ha : a ∈ S)
    (haS : ∀ w ∈ S, fderiv ℝ f x w ≤ fderiv ℝ f x a) {x' : E} {S' : Finset E} {lam' : E → ℝ}
    (hstep : IsAFWStep L (fderiv ℝ f x) x S lam v a x' S' lam')
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
  have hvC : v ∈ convexHull ℝ (↑V : Set E) := subset_convexHull ℝ _ (by exact_mod_cast hvV)
  have haC : a ∈ convexHull ℝ (↑V : Set E) := subset_convexHull ℝ _ (by exact_mod_cast h.sub ha)
  have hgFW : 0 ≤ g (x - v) := by rw [map_sub]; linarith [h.le_apply g hv]
  have hgA : 0 ≤ g (a - x) := by rw [map_sub]; linarith [h.apply_le g haS]
  have hgeo := geo_pair hμ hδ hsc hxsV h.sub h.mem_convexHull hpair ha haS hvV hv
  have hsplit : g (a - v) = g (a - x) + g (x - v) := by rw [map_sub, map_sub, map_sub]; ring
  have hρ1 : ρ ≤ 1 / 2 := min_le_left _ _
  have hρ2 : ρ ≤ μ * δ ^ 2 / (4 * Lmax * D ^ 2) := min_le_right _ _
  -- the progress `G² / (2 L̃ D²)` with gap `G ≥ ½ g(a - v)` beats `ρ h`
  have hgood : ∀ G : ℝ, 0 ≤ G → g (a - v) ≤ 2 * G → 0 < D →
      f x - f xStar - G ^ 2 / (2 * Lmax * D ^ 2) ≤ (1 - ρ) * (f x - f xStar) := by
    intro G hG hGa hDpos
    have h1 : 2 * μ * δ ^ 2 * (f x - f xStar) ≤ g (a - v) ^ 2 := by
      have := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * μ * δ ^ 2)).mp hgeo
      linarith
    have h2 : g (a - v) ^ 2 ≤ 4 * G ^ 2 := by
      have := pow_le_pow_left₀ (by linarith [hsplit, hgA, hgFW]) hGa 2
      nlinarith [this]
    have h3 : μ * δ ^ 2 / (4 * Lmax * D ^ 2) * (f x - f xStar) ≤ G ^ 2 / (2 * Lmax * D ^ 2) := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
      have := mul_le_mul_of_nonneg_right (h1.trans h2) (by positivity : (0 : ℝ) ≤ Lmax * D ^ 2)
      nlinarith [this]
    have h4 := mul_le_mul_of_nonneg_right hρ2 hh0
    linarith
  -- a full step `G²/(2 L ‖d‖²)` beats `G²/(2 L̃ D²)`
  have hcmp : ∀ G d : ℝ, 0 < d → d ≤ D →
      G ^ 2 / (2 * Lmax * D ^ 2) ≤ G ^ 2 / (2 * (L * d ^ 2)) := by
    intro G d hd hdD
    apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
    have : d ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ hd.le hdD 2
    nlinarith [mul_le_mul hLm this (by positivity) hLm0.le]
  unfold IsAFWStep at hstep
  split_ifs at hstep with hfw
  · dsimp only at hstep
    obtain ⟨hx', -, hS'⟩ := hstep
    left
    refine ⟨?_, ?_⟩
    · set G := g (x - v) with hG
      have hGa : g (a - v) ≤ 2 * G := by linarith
      rcases eq_or_lt_of_le (norm_nonneg (x - v)) with hd0 | hdpos
      · have hxv : x - v = 0 := norm_eq_zero.mp hd0.symm
        have hG0 : G = 0 := by rw [hG, hxv, map_zero]
        have hx'x : x' = x := by rw [hx', hxv, smul_zero, sub_zero]
        have hzero : f x - f xStar ≤ 0 := by
          have hga0 : g (a - v) = 0 := by
            have : g (a - v) ≤ 0 := by linarith
            linarith
          rw [hga0] at hgeo; simpa using hgeo
        rw [hx'x]; nlinarith
      · have hc : 0 < L * ‖x - v‖ ^ 2 := by positivity
        have hdD : ‖x - v‖ ≤ D := hdist x hxV v hvC
        have hDpos : 0 < D := lt_of_lt_of_le hdpos hdD
        set γ := min (G / (L * ‖x - v‖ ^ 2)) 1 with hγ
        have hγ0 : 0 ≤ γ := le_min (div_nonneg hgFW hc.le) zero_le_one
        have hprog : f x' ≤ f x - γ * G + γ ^ 2 * L / 2 * ‖x - v‖ ^ 2 := by
          have e1 : x' - x = -(γ • (x - v)) := by rw [hx']; abel
          rw [e1, map_neg, map_smul, smul_eq_mul, norm_neg, norm_smul, Real.norm_of_nonneg hγ0,
            mul_pow] at hdec
          linarith
        rcases le_total (G / (L * ‖x - v‖ ^ 2)) 1 with hle | hle
        · rw [min_eq_left hle] at hγ
          have hval : γ * G - γ ^ 2 * L / 2 * ‖x - v‖ ^ 2 = G ^ 2 / (2 * (L * ‖x - v‖ ^ 2)) := by
            rw [hγ]; field_simp; ring
          have := hgood G hgFW hGa hDpos
          have := hcmp G ‖x - v‖ hdpos hdD
          linarith
        · rw [min_eq_right hle] at hγ
          rw [hγ] at hprog
          have hcG : L * ‖x - v‖ ^ 2 ≤ G := by
            rwa [le_div_iff₀ hc, one_mul] at hle
          have h5 : f x' ≤ f x - G / 2 := by nlinarith [hprog, hcG]
          have hFWgap : f x - f xStar ≤ G := by
            have h2 := le_of_min_vertex g hv hxsV
            have e2 : g (xStar - x) = g xStar - g x := map_sub _ _ _
            rw [hG, map_sub]
            nlinarith [sq_nonneg ‖xStar - x‖]
          have h6 := mul_le_mul_of_nonneg_right hρ1 hh0
          linarith
    · rw [hS']
      split_ifs
      · simp
      · exact Finset.card_insert_le v S
  · dsimp only at hstep
    obtain ⟨hx', -, hS'⟩ := hstep
    set G := g (a - x) with hG
    have hGFW : g (x - v) < G := lt_of_not_ge hfw
    have hGa : g (a - v) ≤ 2 * G := by linarith
    have hdpos : 0 < ‖a - x‖ := by
      rcases eq_or_lt_of_le (norm_nonneg (a - x)) with hd0 | hd0
      · exfalso
        apply hfw
        rw [hG, show a - x = 0 from norm_eq_zero.mp hd0.symm, map_zero]
        exact hgFW
      · exact hd0
    have hc : 0 < L * ‖a - x‖ ^ 2 := by positivity
    have hdD : ‖a - x‖ ≤ D := hdist a haC x hxV
    have hDpos : 0 < D := lt_of_lt_of_le hdpos hdD
    set γmax := lam a / (1 - lam a) with hγmax
    set γ := min (G / (L * ‖a - x‖ ^ 2)) γmax with hγ
    have hγ0 : 0 ≤ γ := le_min (div_nonneg hgA hc.le)
      (div_nonneg (h.nonneg a) (by linarith [h.lam_lt_one g hv ha hfw]))
    have hγle : γ ≤ G / (L * ‖a - x‖ ^ 2) := min_le_left _ _
    have hprog : f x' ≤ f x - γ * G + γ ^ 2 * L / 2 * ‖a - x‖ ^ 2 := by
      have e1 : x' - x = -(γ • (a - x)) := by rw [hx']; abel
      rw [e1, map_neg, map_smul, smul_eq_mul, norm_neg, norm_smul, Real.norm_of_nonneg hγ0,
        mul_pow] at hdec
      linarith
    have hdec' : γ ^ 2 * L / 2 * ‖a - x‖ ^ 2 ≤ γ * G / 2 := by
      have : γ * (L * ‖a - x‖ ^ 2) ≤ G := by rwa [le_div_iff₀ hc] at hγle
      calc γ ^ 2 * L / 2 * ‖a - x‖ ^ 2 = γ / 2 * (γ * (L * ‖a - x‖ ^ 2)) := by ring
        _ ≤ γ / 2 * G := mul_le_mul_of_nonneg_left this (by positivity)
        _ = γ * G / 2 := by ring
    rcases eq_or_ne γ γmax with hdrop | hdrop
    · right
      have : 0 ≤ γ * G := mul_nonneg hγ0 hgA
      refine ⟨by linarith, ?_⟩
      rw [hS', ite_eq_left hdrop]
      exact Finset.card_erase_add_one ha
    · left
      have hγv : γ = G / (L * ‖a - x‖ ^ 2) := by
        rcases min_choice (G / (L * ‖a - x‖ ^ 2)) γmax with h1 | h1
        · rw [hγ, h1]
        · exact absurd (by rw [hγ, h1]) hdrop
      refine ⟨?_, ?_⟩
      · have hval : γ * G - γ ^ 2 * L / 2 * ‖a - x‖ ^ 2 = G ^ 2 / (2 * (L * ‖a - x‖ ^ 2)) := by
          rw [hγv]; field_simp; ring
        have := hgood G hgA hGa hDpos
        have := hcmp G ‖a - x‖ hdpos hdD
        linarith
      · rw [hS', ite_eq_right hdrop]; omega

/-- The invariant of the state along a run of away-step Frank–Wolfe with backtracking. -/
theorem bafw_inv {V : Finset E} {D : Set E} {f : E → ℝ} {Lmax : ℝ} {x : ℕ → E}
    {S : ℕ → Finset E} {lam : ℕ → E → ℝ} (h : IsBAFWRun V D f Lmax x S lam) :
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
    obtain ⟨L, hL, -, v, hvV, hv, a, ha, haS, hstep, -, -⟩ := hsteps t
    exact ih.step hL.le hvV hv ha haS hstep

/-- Counting good steps: after `t` steps there are `G` good steps with `|S_t| + t ≤ 1 + 2G`, the
iterate stays in the sublevel set and in `D`, and the primal gap is at most `(1 - ρ)^G h₀`. -/
theorem bafw_bound {V : Finset E} {D : Set E} {f : E → ℝ} {Lmax μ δ : ℝ} {x : ℕ → E}
    {S : ℕ → Finset E} {lam : ℕ → E → ℝ} {xStar : E}
    (hxs : xStar ∈ minimizers (convexHull ℝ (↑V : Set E) ∩ D) f) (hμ : 0 < μ) (hδ : 0 < δ)
    (hsc : IsScaling V δ)
    (hstr : ∀ y ∈ convexHull ℝ (↑V : Set E) ∩ D, f y ≤ f (x 0) →
      ∀ z ∈ convexHull ℝ (↑V : Set E) ∩ D, f z ≤ f (x 0) →
        f y + fderiv ℝ f y (z - y) + μ / 2 * ‖z - y‖ ^ 2 ≤ f z)
    (hrun : IsBAFWRun V D f Lmax x S lam) (hLm : 0 < Lmax) :
    ∀ t : ℕ, ∃ G : ℕ, (S t).card + t ≤ 1 + 2 * G ∧ f (x t) ≤ f (x 0) ∧ x t ∈ D ∧
      f (x t) - f xStar ≤
        (1 - min (1 / 2) (μ * δ ^ 2 / (4 * Lmax * Metric.diam (↑V : Set E) ^ 2))) ^ G *
          (f (x 0) - f xStar) := by
  classical
  set ρ := min (1 / 2) (μ * δ ^ 2 / (4 * Lmax * Metric.diam (↑V : Set E) ^ 2)) with hρ
  have hρ0 : 0 ≤ ρ := le_min (by norm_num) (by positivity)
  have hinv := bafw_inv hrun
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
    obtain ⟨L, hL, hLL, v, hvV, hv, a, ha, haS, hstep, hxD', hdec⟩ := hrun.2.2.2.2 t
    have hh0 : 0 ≤ f (x t) - f xStar := sub_nonneg.mpr (hxs.2 _ ⟨hxC t, hxD⟩)
    have hpair := hstr (x t) ⟨hxC t, hxD⟩ hft xStar hxs.1 hs0
    rcases bafw_step_outcome hL hLL hμ hδ hsc hxs.1.1 (hinv t) hh0 hpair hvV hv ha haS hstep
      hdec with ⟨hgood, hc⟩ | ⟨hdrop, hc⟩
    · refine ⟨G + 1, by omega, ?_, hxD', ?_⟩
      · have : (1 - ρ) * (f (x t) - f xStar) ≤ f (x t) - f xStar := by nlinarith
        linarith
      · calc f (x (t + 1)) - f xStar ≤ (1 - ρ) * (f (x t) - f xStar) := hgood
          _ ≤ (1 - ρ) * ((1 - ρ) ^ G * (f (x 0) - f xStar)) :=
            mul_le_mul_of_nonneg_left hb (by linarith [min_le_left (1 / 2 : ℝ) (μ * δ ^ 2 /
              (4 * Lmax * Metric.diam (↑V : Set E) ^ 2))])
          _ = (1 - ρ) ^ (G + 1) * (f (x 0) - f xStar) := by ring
    · exact ⟨G, by omega, le_trans hdrop hft, hxD', by linarith⟩

/-- Theorem 3.2 for away-step Frank–Wolfe with backtracking. -/
theorem away_linear_bound {V : Finset E} {D : Set E} {f : E → ℝ} {Lmax μ δ : ℝ} {x : ℕ → E}
    {S : ℕ → Finset E} {lam : ℕ → E → ℝ} {xStar : E}
    (hxs : xStar ∈ minimizers (convexHull ℝ (↑V : Set E) ∩ D) f) (hLm : 0 < Lmax) (hμ : 0 < μ)
    (hδ : 0 < δ) (hsc : IsScaling V δ)
    (hstr : ∀ y ∈ convexHull ℝ (↑V : Set E) ∩ D, f y ≤ f (x 0) →
      ∀ z ∈ convexHull ℝ (↑V : Set E) ∩ D, f z ≤ f (x 0) →
        f y + fderiv ℝ f y (z - y) + μ / 2 * ‖z - y‖ ^ 2 ≤ f z)
    (hrun : IsBAFWRun V D f Lmax x S lam) (t : ℕ) :
    f (x t) - f xStar ≤
      (1 - min (1 / 2) (μ * δ ^ 2 / (4 * Lmax * Metric.diam (↑V : Set E) ^ 2))) ^
        ⌈((t : ℝ) - 1) / 2⌉₊ * (f (x 0) - f xStar) := by
  set ρ := min (1 / 2) (μ * δ ^ 2 / (4 * Lmax * Metric.diam (↑V : Set E) ^ 2)) with hρ
  have hρ0 : 0 ≤ ρ := le_min (by norm_num) (by positivity)
  have hρ1 : ρ ≤ 1 / 2 := min_le_left _ _
  obtain ⟨G, hcard, -, -, hb⟩ := bafw_bound hxs hμ hδ hsc hstr hrun hLm t
  have hS1 : 1 ≤ (S t).card := by
    have : (S t).Nonempty :=
      Finset.nonempty_of_sum_ne_zero (by rw [(bafw_inv hrun t).sum]; norm_num)
    exact Finset.card_pos.mpr this
  have hG : ⌈((t : ℝ) - 1) / 2⌉₊ ≤ G := by
    rw [Nat.ceil_le]
    have : (t : ℝ) ≤ 2 * G := by exact_mod_cast (by omega : t ≤ 2 * G)
    linarith
  have hx0 : x 0 ∈ convexHull ℝ (↑V : Set E) :=
    convexHull_mono (by exact_mod_cast (bafw_inv hrun 0).sub) (bafw_inv hrun 0).mem_convexHull
  have h0 : 0 ≤ f (x 0) - f xStar := sub_nonneg.mpr (hxs.2 _ ⟨hx0, hrun.2.1⟩)
  calc f (x t) - f xStar ≤ (1 - ρ) ^ G * (f (x 0) - f xStar) := hb
    _ ≤ (1 - ρ) ^ ⌈((t : ℝ) - 1) / 2⌉₊ * (f (x 0) - f xStar) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one (by linarith) (by linarith) hG) h0

namespace Proof

theorem away_linear_rate : AwayLinearRate.{u} := by
  intro E _ _ V D f Lmax μ δ x S lam xStar hxs hLm hμ hδ hsc hstr hrun t
  exact away_linear_bound hxs hLm hμ hδ hsc hstr hrun t

end Proof

end Lemmata.FWSelfConcordant
