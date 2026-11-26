module

public import Lemmata.AwayStepFW.Progress

@[expose] public section

/-!
# Pairwise Frank–Wolfe: invariants

A pairwise step moves weight from the away vertex to the Frank–Wolfe vertex, so the weights stay
nonnegative, vanish outside the active set, sum to `1` and represent the iterate.
-/

namespace Lemmata.AwayStepFW

open Lemmata.FrankWolfe

namespace Proof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem Inv.pstep {V : Finset E} {L : ℝ} (hL : 0 ≤ L) {g : StrongDual ℝ E} {x : E} {S : Finset E}
    {lam : E → ℝ} (h : Inv V x S lam) {v a : E} (hvV : v ∈ V) (hv : ∀ w ∈ V, g v ≤ g w)
    (ha : a ∈ S) (haS : ∀ w ∈ S, g w ≤ g a) {x' : E} {S' : Finset E} {lam' : E → ℝ}
    (hstep : IsPFWStep L g x S lam v a x' S' lam') : Inv V x' S' lam' := by
  classical
  unfold IsPFWStep at hstep
  dsimp only at hstep
  obtain ⟨hx', hlam', hS'⟩ := hstep
  set γ := min (g (a - v) / (L * ‖a - v‖ ^ 2)) (lam a) with hγ
  have hgav : 0 ≤ g (a - v) := by
    rw [map_sub]; linarith [h.apply_le g haS, h.le_apply g hv]
  have hγ0 : 0 ≤ γ := le_min (div_nonneg hgav (by positivity)) (h.nonneg a)
  have hγa : γ ≤ lam a := min_le_right _ _
  have hsub : S ⊆ insert v S := Finset.subset_insert v S
  have hsumlam : ∑ w ∈ insert v S, lam w = 1 := by
    rw [← h.sum]; symm
    exact Finset.sum_subset hsub (fun w _ hw => h.supp w hw)
  have hsumx : ∑ w ∈ insert v S, lam w • w = x := by
    rw [h.rep]; symm
    exact Finset.sum_subset hsub (fun w _ hw => by rw [h.supp w hw, zero_smul])
  have haI : a ∈ insert v S := Finset.mem_insert_of_mem ha
  have hvI : v ∈ insert v S := Finset.mem_insert_self v S
  have hsumI : ∑ w ∈ insert v S, lam' w = 1 := by
    rw [hlam']
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq', haI, hvI,
      ite_true, hsumlam]
    ring
  have hrepI : ∑ w ∈ insert v S, lam' w • w = x' := by
    rw [hlam', hx']
    simp only [add_smul, sub_smul, Finset.sum_add_distrib, Finset.sum_sub_distrib, ite_smul,
      zero_smul, Finset.sum_ite_eq', haI, hvI, ite_true, hsumx]
    module
  have hnn : ∀ w, 0 ≤ lam' w := by
    intro w
    rw [hlam']
    dsimp only
    have h1 : 0 ≤ (if w = v then γ else 0) := by split_ifs <;> linarith
    have h2 : 0 ≤ lam w - (if w = a then γ else 0) := by
      split_ifs with hwa
      · rw [hwa]; linarith
      · simpa using h.nonneg w
    linarith
  have hsuppI : ∀ w ∉ insert v S, lam' w = 0 := by
    intro w hw
    rw [Finset.mem_insert, not_or] at hw
    have hwa : w ≠ a := fun e => hw.2 (e ▸ ha)
    rw [hlam']
    simp [hwa, hw.1, h.supp w hw.2]
  by_cases hdrop : γ = lam a
  · rw [ite_eq_left hdrop] at hS'
    subst hS'
    have hza : lam' a = 0 := by
      rw [hlam']
      by_cases hav : a = v
      · -- then `γ = 0`, so `lam a = 0`
        have hγz : γ = 0 := by
          rw [hγ, hav, sub_self, map_zero, zero_div]; exact min_eq_left (hav ▸ h.nonneg a)
        simp [hav, hγz] at hdrop ⊢
        linarith [hdrop]
      · simp [hav, hdrop]
    refine ⟨(Finset.erase_subset a _).trans (Finset.insert_subset hvV h.sub), hnn,
      fun w hw => ?_, ?_, ?_⟩
    · by_cases hwa : w = a
      · rw [hwa]; exact hza
      · exact hsuppI w (fun hwI => hw (Finset.mem_erase.mpr ⟨hwa, hwI⟩))
    · rw [Finset.sum_erase _ hza]; exact hsumI
    · rw [Finset.sum_erase _ (by rw [hza, zero_smul])]; exact hrepI.symm
  · rw [ite_eq_right hdrop] at hS'
    subst hS'
    exact ⟨Finset.insert_subset hvV h.sub, hnn, hsuppI, hsumI, hrepI.symm⟩

theorem pfw_run_inv {V : Finset E} {f : E → ℝ} {L : ℝ} (hL : 0 ≤ L) {x : ℕ → E}
    {S : ℕ → Finset E} {lam : ℕ → E → ℝ} (h : IsPFWRun V f L x S lam) :
    ∀ t, Inv V (x t) (S t) (lam t) := by
  classical
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
    obtain ⟨v, hvV, hv, a, ha, haS, hstep⟩ := hsteps t
    exact ih.pstep hL hvV hv ha haS hstep

/-- Positivity of `g(a - v)` while the primal gap is positive. -/
theorem pgap_pos {V : Finset E} {f : E → ℝ} {μ δ : ℝ} (hμ : 0 < μ) (hδ : 0 < δ)
    (hsc : IsScaling V δ)
    (hstrong : ∀ x ∈ convexHull ℝ (↑V : Set E), ∀ y ∈ convexHull ℝ (↑V : Set E),
      f x + fderiv ℝ f x (y - x) + μ / 2 * ‖y - x‖ ^ 2 ≤ f y)
    {xStar : E} (hxs : xStar ∈ minimizers (convexHull ℝ (↑V : Set E)) f)
    {x : E} {S : Finset E} {lam : E → ℝ} (h : Inv V x S lam) {v a : E} (hvV : v ∈ V)
    (hv : ∀ w ∈ V, fderiv ℝ f x v ≤ fderiv ℝ f x w) (ha : a ∈ S)
    (haS : ∀ w ∈ S, fderiv ℝ f x w ≤ fderiv ℝ f x a) (hh : 0 < f x - f xStar) :
    0 < fderiv ℝ f x (a - v) := by
  have hgeo := geometric_strong_convexity V f μ δ hμ hδ hsc hstrong xStar hxs S h.sub x
    h.mem_convexHull a ha haS v hvV hv
  have hnn : 0 ≤ fderiv ℝ f x (a - v) := by
    rw [map_sub]; linarith [h.apply_le (fderiv ℝ f x) haS, h.le_apply (fderiv ℝ f x) hv]
  rcases eq_or_lt_of_le hnn with h0 | hpos
  · rw [← h0] at hgeo; simp at hgeo; linarith
  · exact hpos

open Classical in
/-- The outcome of one pairwise step with positive weights and a positive primal gap: good (the gap
contracts), drop (the active set shrinks), or swap (the weights are permuted by a transposition). -/
theorem pstep_outcome {V : Finset E} {f : E → ℝ} {L : NNReal} {μ δ : ℝ} (hL : 0 < (L : ℝ))
    (hμ : 0 < μ) (hδ : 0 < δ) (hsc : IsScaling V δ) (hsm : IsSmooth f L)
    (hstrong : ∀ x ∈ convexHull ℝ (↑V : Set E), ∀ y ∈ convexHull ℝ (↑V : Set E),
      f x + fderiv ℝ f x (y - x) + μ / 2 * ‖y - x‖ ^ 2 ≤ f y)
    {xStar : E} (hxs : xStar ∈ minimizers (convexHull ℝ (↑V : Set E)) f)
    {x : E} {S : Finset E} {lam : E → ℝ} (h : Inv V x S lam) (hposw : ∀ w ∈ S, 0 < lam w)
    (hh : 0 < f x - f xStar) {v a : E} (hvV : v ∈ V)
    (hv : ∀ w ∈ V, fderiv ℝ f x v ≤ fderiv ℝ f x w) (ha : a ∈ S)
    (haS : ∀ w ∈ S, fderiv ℝ f x w ≤ fderiv ℝ f x a) {x' : E} {S' : Finset E} {lam' : E → ℝ}
    (hstep : IsPFWStep L (fderiv ℝ f x) x S lam v a x' S' lam') :
    (f x' - f xStar ≤ (1 - min (1 / 2) (μ * δ ^ 2 / (L * Metric.diam (↑V : Set E) ^ 2))) *
        (f x - f xStar) ∧ S'.card ≤ S.card + 1) ∨
      (f x' ≤ f x ∧ S'.card + 1 = S.card) ∨
      (f x' < f x ∧ S'.card = S.card ∧ lam' = fun w => lam (Equiv.swap a v w)) := by
  classical
  set g := fderiv ℝ f x with hg
  set D := Metric.diam (↑V : Set E) with hD
  have hgd := pgap_pos hμ hδ hsc hstrong hxs h hvV hv ha haS hh
  have hav : a ≠ v := fun e => by rw [e, sub_self, map_zero] at hgd; exact lt_irrefl _ hgd
  have hd : 0 < ‖a - v‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hav)
  have hc : 0 < (L : ℝ) * ‖a - v‖ ^ 2 := by positivity
  unfold IsPFWStep at hstep
  dsimp only at hstep
  obtain ⟨hx', hlam', hS'⟩ := hstep
  set γ := min (g (a - v) / (L * ‖a - v‖ ^ 2)) (lam a) with hγ
  have hla := hposw a ha
  have hγ0 : 0 < γ := lt_min (div_pos hgd hc) hla
  have hγs : γ ≤ g (a - v) / (L * ‖a - v‖ ^ 2) := min_le_left _ _
  have hγa : γ ≤ lam a := min_le_right _ _
  have hprog : f x' ≤ f x - γ * g (a - v) + γ ^ 2 * L / 2 * ‖a - v‖ ^ 2 := by
    have := hsm.le_quadratic x x'
    rw [hx', show x - γ • (a - v) - x = -(γ • (a - v)) by abel, map_neg, map_smul, smul_eq_mul,
      norm_neg, norm_smul, Real.norm_of_nonneg hγ0.le, mul_pow] at this
    rw [hx']
    have e : fderiv ℝ f x (a - v) = g (a - v) := rfl
    rw [e] at this
    linarith
  have hhalf : γ ^ 2 * L / 2 * ‖a - v‖ ^ 2 ≤ γ * g (a - v) / 2 := by
    have : γ * (L * ‖a - v‖ ^ 2) ≤ g (a - v) := by rwa [le_div_iff₀ hc] at hγs
    calc γ ^ 2 * L / 2 * ‖a - v‖ ^ 2 = γ / 2 * (γ * (L * ‖a - v‖ ^ 2)) := by ring
      _ ≤ γ / 2 * g (a - v) := mul_le_mul_of_nonneg_left this (by positivity)
      _ = γ * g (a - v) / 2 := by ring
  have hdecr : f x' < f x := by nlinarith [mul_pos hγ0 hgd]
  by_cases hdrop : γ = lam a
  · rw [ite_eq_left hdrop] at hS'
    by_cases hvS : v ∈ S
    · right; left
      refine ⟨hdecr.le, ?_⟩
      rw [hS', Finset.insert_eq_of_mem hvS]
      exact Finset.card_erase_add_one ha
    · right; right
      refine ⟨hdecr, ?_, ?_⟩
      · rw [hS', Finset.card_erase_of_mem (Finset.mem_insert_of_mem ha),
          Finset.card_insert_of_notMem hvS]
        simp
      · rw [hlam']
        funext w
        have hlv : lam v = 0 := h.supp v hvS
        by_cases hwa : w = a
        · subst hwa
          rw [Equiv.swap_apply_left, hlv]
          simp [hav, hdrop]
        · by_cases hwv : w = v
          · subst hwv
            rw [Equiv.swap_apply_right]
            simp [hwa, hdrop, hlv]
          · rw [Equiv.swap_apply_of_ne_of_ne hwa hwv]
            simp [hwa, hwv]
  · left
    rw [ite_eq_right hdrop] at hS'
    have hγv : γ = g (a - v) / (L * ‖a - v‖ ^ 2) := by
      rcases min_choice (g (a - v) / (L * ‖a - v‖ ^ 2)) (lam a) with h1 | h1
      · rw [hγ, h1]
      · exact absurd (by rw [hγ, h1]) hdrop
    refine ⟨?_, by rw [hS']; exact Finset.card_insert_le v S⟩
    have hval : γ * g (a - v) - γ ^ 2 * L / 2 * ‖a - v‖ ^ 2 =
        g (a - v) ^ 2 / (2 * (L * ‖a - v‖ ^ 2)) := by
      rw [hγv]; field_simp; ring
    have hbdd : Bornology.IsBounded (convexHull ℝ (↑V : Set E)) :=
      isBounded_convexHull.mpr V.finite_toSet.isBounded
    have hdD : ‖a - v‖ ≤ D := by
      rw [← dist_eq_norm, hD, ← convexHull_diam]
      exact Metric.dist_le_diam_of_mem hbdd
        (subset_convexHull ℝ _ (by exact_mod_cast h.sub ha))
        (subset_convexHull ℝ _ (by exact_mod_cast hvV))
    have hDpos : 0 < D := lt_of_lt_of_le hd hdD
    have hgeo := geometric_strong_convexity V f μ δ hμ hδ hsc hstrong xStar hxs S h.sub x
      h.mem_convexHull a ha haS v hvV hv
    have h1 : 2 * μ * δ ^ 2 * (f x - f xStar) ≤ g (a - v) ^ 2 := by
      have := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * μ * δ ^ 2)).mp hgeo
      linarith
    have hcmp : g (a - v) ^ 2 / (2 * (L * D ^ 2)) ≤ g (a - v) ^ 2 / (2 * (L * ‖a - v‖ ^ 2)) :=
      div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
        (by nlinarith [pow_le_pow_left₀ (norm_nonneg _) hdD 2])
    have h2 : μ * δ ^ 2 / (L * D ^ 2) * (f x - f xStar) ≤ g (a - v) ^ 2 / (2 * (L * D ^ 2)) := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
      have := mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ L * D ^ 2)
      linarith
    have h3 := mul_le_mul_of_nonneg_right
      (min_le_right (1 / 2 : ℝ) (μ * δ ^ 2 / (L * D ^ 2))) hh.le
    linarith

/-- Every pairwise step decreases `f` weakly. -/
theorem pstep_mono {V : Finset E} {f : E → ℝ} {L : NNReal} (hL : 0 < (L : ℝ)) (hsm : IsSmooth f L)
    {x : E} {S : Finset E} {lam : E → ℝ} (h : Inv V x S lam) {v a : E}
    (hv : ∀ w ∈ V, fderiv ℝ f x v ≤ fderiv ℝ f x w)
    (haS : ∀ w ∈ S, fderiv ℝ f x w ≤ fderiv ℝ f x a) {x' : E} {S' : Finset E} {lam' : E → ℝ}
    (hstep : IsPFWStep L (fderiv ℝ f x) x S lam v a x' S' lam') : f x' ≤ f x := by
  classical
  unfold IsPFWStep at hstep
  dsimp only at hstep
  obtain ⟨hx', -, -⟩ := hstep
  set g := fderiv ℝ f x with hg
  set γ := min (g (a - v) / (L * ‖a - v‖ ^ 2)) (lam a) with hγ
  have hgav : 0 ≤ g (a - v) := by
    rw [map_sub]; linarith [h.apply_le g haS, h.le_apply g hv]
  rcases eq_or_lt_of_le (norm_nonneg (a - v)) with hd0 | hd
  · have : a - v = 0 := norm_eq_zero.mp hd0.symm
    rw [hx', this, smul_zero, sub_zero]
  · have hc : 0 < (L : ℝ) * ‖a - v‖ ^ 2 := by positivity
    have hγ0 : 0 ≤ γ := le_min (div_nonneg hgav hc.le) (h.nonneg a)
    have hγs : γ ≤ g (a - v) / (L * ‖a - v‖ ^ 2) := min_le_left _ _
    have hq := hsm.le_quadratic x x'
    rw [hx', show x - γ • (a - v) - x = -(γ • (a - v)) by abel, map_neg, map_smul, smul_eq_mul,
      norm_neg, norm_smul, Real.norm_of_nonneg hγ0, mul_pow] at hq
    have e : fderiv ℝ f x (a - v) = g (a - v) := rfl
    rw [e] at hq
    have : γ * (L * ‖a - v‖ ^ 2) ≤ g (a - v) := by rwa [le_div_iff₀ hc] at hγs
    rw [hx']
    nlinarith [mul_nonneg hγ0 hgav]

theorem pfw_pos {V : Finset E} {f : E → ℝ} {L : NNReal} {μ δ : ℝ} (hL : 0 < (L : ℝ))
    (hμ : 0 < μ) (hδ : 0 < δ) (hsc : IsScaling V δ)
    (hstrong : ∀ x ∈ convexHull ℝ (↑V : Set E), ∀ y ∈ convexHull ℝ (↑V : Set E),
      f x + fderiv ℝ f x (y - x) + μ / 2 * ‖y - x‖ ^ 2 ≤ f y)
    {xStar : E} (hxs : xStar ∈ minimizers (convexHull ℝ (↑V : Set E)) f)
    {x : ℕ → E} {S : ℕ → Finset E} {lam : ℕ → E → ℝ} (h : IsPFWRun V f L x S lam) :
    ∀ t, (∀ s ≤ t, 0 < f (x s) - f xStar) → ∀ w ∈ S t, 0 < lam t w := by
  classical
  have inv := pfw_run_inv (NNReal.coe_nonneg L) h
  intro t
  induction t with
  | zero =>
    intro _ w hw
    rw [h.2.1, Finset.mem_singleton] at hw
    rw [h.2.2.1, hw]
    simp
  | succ t ih =>
    intro hpos w hw
    have ih' := ih (fun s hs => hpos s (by omega))
    obtain ⟨v, hvV, hv, a, ha, haS, hstep⟩ := h.2.2.2 t
    have hgd := pgap_pos hμ hδ hsc hstrong hxs (inv t) hvV hv ha haS (hpos t (by omega))
    have hav : a ≠ v := fun e => by rw [e, sub_self, map_zero] at hgd; exact lt_irrefl _ hgd
    have hc : 0 < (L : ℝ) * ‖a - v‖ ^ 2 := by
      have : 0 < ‖a - v‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hav)
      positivity
    unfold IsPFWStep at hstep
    dsimp only at hstep
    obtain ⟨-, hlam', hS'⟩ := hstep
    set γ := min (fderiv ℝ f (x t) (a - v) / (L * ‖a - v‖ ^ 2)) (lam t a) with hγ
    have hla := ih' a ha
    have hγ0 : 0 < γ := lt_min (div_pos hgd hc) hla
    have hγa : γ ≤ lam t a := min_le_right _ _
    rw [hlam']
    have hvnn := (inv t).nonneg v
    by_cases hdrop : γ = lam t a
    · rw [ite_eq_left hdrop] at hS'
      rw [hS'] at hw
      obtain ⟨hwa, hwI⟩ := Finset.mem_erase.mp hw
      by_cases hwv : w = v
      · subst hwv; simp only [hwa, ite_false, ite_true, sub_zero]; linarith
      · have hwS : w ∈ S t := (Finset.mem_insert.mp hwI).resolve_left hwv
        simp only [hwa, hwv, ite_false, sub_zero, add_zero]; exact ih' w hwS
    · rw [ite_eq_right hdrop] at hS'
      rw [hS'] at hw
      by_cases hwv : w = v
      · subst hwv
        have hva : w ≠ a := fun e => hav e.symm
        simp only [hva, ite_false, ite_true, sub_zero]; linarith
      · have hwS : w ∈ S t := (Finset.mem_insert.mp hw).resolve_left hwv
        by_cases hwa : w = a
        · subst hwa
          have hlt : γ < lam t w := lt_of_le_of_ne hγa hdrop
          simp only [ite_true, hwv, ite_false, add_zero]; linarith
        · simp only [hwa, hwv, ite_false, sub_zero, add_zero]; exact ih' w hwS

/-- The first pairwise step from a vertex gives `h₁ ≤ L D²/2`. -/
theorem pfw_first_step {V : Finset E} {f : E → ℝ} {L : NNReal} (hL : 0 < (L : ℝ))
    (hconv : ConvexOn ℝ Set.univ f) (hsm : IsSmooth f L) {xStar : E}
    (hxs : xStar ∈ minimizers (convexHull ℝ (↑V : Set E)) f) {x : ℕ → E} {S : ℕ → Finset E}
    {lam : ℕ → E → ℝ} (h : IsPFWRun V f L x S lam) :
    f (x 1) - f xStar ≤ L * Metric.diam (↑V : Set E) ^ 2 / 2 := by
  classical
  have inv := pfw_run_inv (NNReal.coe_nonneg L) h
  obtain ⟨hx0, hS0, hlam0, hsteps⟩ := h
  obtain ⟨v, hvV, hv, a, ha, haS, hstep⟩ := hsteps 0
  rw [hS0, Finset.mem_singleton] at ha
  subst ha
  unfold IsPFWStep at hstep
  dsimp only at hstep
  obtain ⟨hx', -, -⟩ := hstep
  rw [hlam0] at hx'
  simp only [ite_true] at hx'
  set g := fderiv ℝ f (x 0) with hg
  set G := g (x 0 - v) with hG
  have hxV : x 0 ∈ convexHull ℝ (↑V : Set E) := subset_convexHull ℝ _ (by exact_mod_cast hx0)
  have hvC : v ∈ convexHull ℝ (↑V : Set E) := subset_convexHull ℝ _ (by exact_mod_cast hvV)
  have hbdd : Bornology.IsBounded (convexHull ℝ (↑V : Set E)) :=
    isBounded_convexHull.mpr V.finite_toSet.isBounded
  have hdD : ‖x 0 - v‖ ≤ Metric.diam (↑V : Set E) := by
    rw [← dist_eq_norm, ← convexHull_diam]; exact Metric.dist_le_diam_of_mem hbdd hxV hvC
  have hGh : f (x 0) - f xStar ≤ G := by
    have h1 := add_fderiv_le_of_convexOn hconv hsm.1 (x 0) xStar
    have h2 := le_of_min_vertex g hv hxs.1
    have e : fderiv ℝ f (x 0) (xStar - x 0) = g xStar - g (x 0) := by rw [hg, map_sub]
    rw [e] at h1
    rw [hG, map_sub]
    linarith
  have hG0 : 0 ≤ G := by rw [hG, map_sub]; linarith [le_of_min_vertex g hv hxV]
  rcases eq_or_lt_of_le (norm_nonneg (x 0 - v)) with hd0 | hd
  · have hxv : x 0 - v = 0 := norm_eq_zero.mp hd0.symm
    have hGz : G = 0 := by rw [hG, hxv, map_zero]
    rw [hx', hxv, smul_zero, sub_zero]
    have : 0 ≤ (L : ℝ) * Metric.diam (↑V : Set E) ^ 2 / 2 := by positivity
    linarith
  · have hc : 0 < (L : ℝ) * ‖x 0 - v‖ ^ 2 := by positivity
    set γ := min (G / (L * ‖x 0 - v‖ ^ 2)) 1 with hγ
    have hγ0 : 0 ≤ γ := le_min (div_nonneg hG0 hc.le) zero_le_one
    have hq := hsm.le_quadratic (x 0) (x 1)
    rw [hx', show x 0 - γ • (x 0 - v) - x 0 = -(γ • (x 0 - v)) by abel, map_neg, map_smul,
      smul_eq_mul, norm_neg, norm_smul, Real.norm_of_nonneg hγ0, mul_pow] at hq
    have e : fderiv ℝ f (x 0) (x 0 - v) = G := rfl
    rw [e] at hq
    have hcD : (L : ℝ) * ‖x 0 - v‖ ^ 2 ≤ L * Metric.diam (↑V : Set E) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hdD 2) (NNReal.coe_nonneg L)
    rw [hx']
    rcases le_total (G / (L * ‖x 0 - v‖ ^ 2)) 1 with hle | hle
    · rw [min_eq_left hle] at hγ
      have hval : γ * G - γ ^ 2 * (↑L * ‖x 0 - v‖ ^ 2) / 2 = G ^ 2 / (2 * (L * ‖x 0 - v‖ ^ 2)) := by
        rw [hγ]; field_simp; ring
      have hsq : G - G ^ 2 / (2 * (L * ‖x 0 - v‖ ^ 2)) ≤ L * ‖x 0 - v‖ ^ 2 / 2 := by
        rw [sub_le_iff_le_add, div_add_div _ _ (by positivity) (by positivity),
          le_div_iff₀ (by positivity)]
        nlinarith [sq_nonneg (G - L * ‖x 0 - v‖ ^ 2)]
      nlinarith
    · rw [min_eq_right hle] at hγ
      have hcG : (L : ℝ) * ‖x 0 - v‖ ^ 2 ≤ G := by rwa [le_div_iff₀ hc, one_mul] at hle
      rw [hγ] at hq ⊢
      simp only [one_smul, one_pow, one_mul] at hq ⊢
      linarith

open Classical in
/-- Along `r` consecutive swap steps the weights are permuted and `f` strictly decreases, so no
weight vector repeats: `r < |V|!`. -/
theorem swap_run_bound {V : Finset E} {f : E → ℝ} {x : ℕ → E} {S : ℕ → Finset E}
    {lam : ℕ → E → ℝ} (hinv : ∀ t, Inv V (x t) (S t) (lam t)) (t0 r : ℕ)
    (hswap : ∀ k < r, f (x (t0 + k + 1)) < f (x (t0 + k)) ∧ ∃ a ∈ V, ∃ v ∈ V,
      lam (t0 + k + 1) = fun w => lam (t0 + k) (Equiv.swap a v w)) :
    r < V.card.factorial := by
  have hperm : ∀ k ≤ r, ∃ σ : Equiv.Perm {w // w ∈ V},
      lam (t0 + k) = fun w => lam t0 (Equiv.Perm.ofSubtype σ w) := by
    intro k
    induction k with
    | zero => intro _; exact ⟨1, by funext w; simp⟩
    | succ k ih =>
      intro hk
      obtain ⟨σ, hσ⟩ := ih (by omega)
      obtain ⟨-, a, ha, v, hv, he⟩ := hswap k (by omega)
      refine ⟨σ * Equiv.swap ⟨a, ha⟩ ⟨v, hv⟩, ?_⟩
      rw [show t0 + (k + 1) = t0 + k + 1 by omega, he, hσ]
      funext w
      simp only [map_mul, Equiv.Perm.mul_apply, Equiv.Perm.ofSubtype_swap_eq]
  have hxV : ∀ t, x t = ∑ w ∈ V, lam t w • w := fun t => by
    rw [(hinv t).rep]
    exact Finset.sum_subset (hinv t).sub (fun w _ hw => by rw [(hinv t).supp w hw, zero_smul])
  have hdec : ∀ j ≤ r, ∀ i < j, f (x (t0 + j)) < f (x (t0 + i)) := by
    intro j
    induction j with
    | zero => intro _ i hi; omega
    | succ j ih =>
      intro hj i hi
      have hstep := (hswap j (by omega)).1
      rw [show t0 + (j + 1) = t0 + j + 1 by omega]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
      · exact hstep.trans (ih (by omega) i hlt)
      · rw [heq]; exact hstep
  have hinj : Set.InjOn (fun k => lam (t0 + k)) ↑(Finset.range (r + 1)) := by
    intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    by_contra hne
    have hx : x (t0 + i) = x (t0 + j) := by rw [hxV, hxV]; simp only at hij; rw [hij]
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact absurd (congrArg f hx) (ne_of_gt (hdec j (by omega) i hlt))
    · exact absurd (congrArg f hx) (ne_of_lt (hdec i (by omega) j hlt))
  have hsub : (Finset.range (r + 1)).image (fun k => lam (t0 + k)) ⊆
      Finset.univ.image
        (fun σ : Equiv.Perm {w // w ∈ V} => fun w => lam t0 (Equiv.Perm.ofSubtype σ w)) := by
    intro l hl
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hl
    obtain ⟨σ, hσ⟩ := hperm k (by simpa [Nat.lt_succ_iff] using hk)
    exact Finset.mem_image.mpr ⟨σ, Finset.mem_univ _, hσ.symm⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj, Finset.card_range] at hcard
  have hle := hcard.trans Finset.card_image_le
  rw [Finset.card_univ, Fintype.card_perm, Fintype.card_coe] at hle
  omega

end Proof

end Lemmata.AwayStepFW
