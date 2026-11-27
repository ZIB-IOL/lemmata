module

public import Lemmata.BPCG.Statement
public import Lemmata.AwayStepFW.Pairwise
public import Lemmata.CGBasics.Wolfe

@[expose] public section

/-!
# Blended pairwise conditional gradients: invariants

Both kinds of steps keep the weights nonnegative, supported on the active set, summing to `1` and
representing the iterate.
-/

namespace Lemmata.BPCG

open Lemmata.FrankWolfe Lemmata.AwayStepFW Lemmata.AwayStepFW.Proof

namespace Proof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
theorem inv_local_step {V : Finset E} {x : E} {S : Finset E} {lam : E → ℝ}
    (h : Lemmata.AwayStepFW.Proof.Inv V x S lam)
    {a s : E} (ha : a ∈ S) (hs : s ∈ S) {γ : ℝ} (hγ : γ ∈ Set.Icc (0 : ℝ) (lam a)) :
    Lemmata.AwayStepFW.Proof.Inv V (x - γ • (a - s)) (if γ = lam a ∧ a ≠ s then S.erase a else S)
      (fun u => lam u - (if u = a then γ else 0) + (if u = s then γ else 0)) := by
  classical
  set lam' : E → ℝ := fun u => lam u - (if u = a then γ else 0) + (if u = s then γ else 0)
    with hlam'
  have hnn : ∀ u, 0 ≤ lam' u := fun u => by
    simp only [hlam']
    have h1 : 0 ≤ (if u = s then γ else 0) := by split_ifs <;> linarith [hγ.1]
    have h2 : 0 ≤ lam u - (if u = a then γ else 0) := by
      split_ifs with hua
      · rw [hua]; linarith [hγ.2]
      · simpa using h.nonneg u
    linarith
  have hsupp : ∀ u ∉ S, lam' u = 0 := fun u hu => by
    have hua : u ≠ a := fun e => hu (e ▸ ha)
    have hus : u ≠ s := fun e => hu (e ▸ hs)
    simp [hlam', hua, hus, h.supp u hu]
  have hsum : ∑ u ∈ S, lam' u = 1 := by
    simp only [hlam', Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq', ha, hs,
      ite_true, h.sum]
    ring
  have hrep : ∑ u ∈ S, lam' u • u = x - γ • (a - s) := by
    simp only [hlam', add_smul, sub_smul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ite_smul, zero_smul, Finset.sum_ite_eq', ha, hs, ite_true, ← h.rep]
    rw [smul_sub]
    abel
  by_cases hdrop : γ = lam a ∧ a ≠ s
  · rw [ite_eq_left hdrop]
    have hza : lam' a = 0 := by simp [hlam', hdrop.2, hdrop.1]
    refine ⟨(Finset.erase_subset a S).trans h.sub, hnn, fun u hu => ?_, ?_, ?_⟩
    · by_cases hua : u = a
      · rw [hua]; exact hza
      · exact hsupp u (fun huS => hu (Finset.mem_erase.mpr ⟨hua, huS⟩))
    · rw [Finset.sum_erase _ hza]; exact hsum
    · rw [Finset.sum_erase _ (by rw [hza, zero_smul])]; exact hrep.symm
  · rw [ite_eq_right hdrop]
    exact ⟨h.sub, hnn, hsupp, hsum, hrep.symm⟩

open Classical in
theorem inv_fw_step {V : Finset E} {x : E} {S : Finset E} {lam : E → ℝ}
    (h : Lemmata.AwayStepFW.Proof.Inv V x S lam)
    {w : E} (hw : w ∈ V) {γ : ℝ} (hγ : γ ∈ Set.Icc (0 : ℝ) 1) :
    Lemmata.AwayStepFW.Proof.Inv V (x - γ • (x - w)) (if γ = 1 then {w} else insert w S)
      (fun u => (1 - γ) * lam u + (if u = w then γ else 0)) := by
  classical
  set lam' : E → ℝ := fun u => (1 - γ) * lam u + (if u = w then γ else 0) with hlam'
  have hnn : ∀ u, 0 ≤ lam' u := fun u => by
    simp only [hlam']
    have := h.nonneg u
    have : 0 ≤ (if u = w then γ else 0) := by split_ifs <;> linarith [hγ.1]
    nlinarith [hγ.2]
  by_cases h1 : γ = 1
  · rw [ite_eq_left h1]
    have hlw : lam' w = 1 := by simp [hlam', h1]
    have hlo : ∀ u, u ≠ w → lam' u = 0 := fun u hu => by simp [hlam', h1, hu]
    refine ⟨Finset.singleton_subset_iff.mpr hw, hnn, fun u hu => hlo u
      (by simpa using hu), by simp [hlw], ?_⟩
    simp [hlw, h1]
  · rw [ite_eq_right h1]
    have hsumI : ∑ u ∈ insert w S, lam u = 1 := by
      rw [← h.sum]; symm
      exact Finset.sum_subset (Finset.subset_insert w S) (fun u _ hu => h.supp u hu)
    have hrepI : ∑ u ∈ insert w S, lam u • u = x := by
      rw [h.rep]; symm
      exact Finset.sum_subset (Finset.subset_insert w S)
        (fun u _ hu => by rw [h.supp u hu, zero_smul])
    have hwI : w ∈ insert w S := Finset.mem_insert_self w S
    refine ⟨Finset.insert_subset hw h.sub, hnn, fun u hu => ?_, ?_, ?_⟩
    · rw [Finset.mem_insert, not_or] at hu
      simp [hlam', hu.1, h.supp u hu.2]
    · simp only [hlam', Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq', hwI,
        ite_true, hsumI]
      ring
    · simp only [hlam', add_smul, mul_smul, Finset.sum_add_distrib, ← Finset.smul_sum, ite_smul,
        zero_smul, Finset.sum_ite_eq', hwI, ite_true, hrepI]
      rw [smul_sub, sub_smul, one_smul]
      abel

open Classical in
theorem inv_bstep {V : Finset E} {f : E → ℝ} {x : E} {S : Finset E} {lam : E → ℝ}
    
    (h : Lemmata.AwayStepFW.Proof.Inv V x S lam) {a s w x' : E} {S' : Finset E}
    {lam' : E → ℝ} (ha : a ∈ S) (hs : s ∈ S)
    (hw : w ∈ V) (hstep : IsBPCGStep f x S lam a s w x' S' lam') :
    Lemmata.AwayStepFW.Proof.Inv V x' S' lam' := by
  classical
  unfold IsBPCGStep at hstep
  split_ifs at hstep with hsel
  · obtain ⟨γ, hγ, -, rfl, rfl, rfl⟩ := hstep
    exact inv_local_step h ha hs hγ
  · obtain ⟨γ, hγ, -, rfl, rfl, rfl⟩ := hstep
    exact inv_fw_step h hw hγ

open Classical in
theorem bpcg_run_inv {V : Finset E} {f : E → ℝ} {x : ℕ → E} {S : ℕ → Finset E}
    {lam : ℕ → E → ℝ} (h : IsBPCGRun V f x S lam) :
    ∀ t, Lemmata.AwayStepFW.Proof.Inv V (x t) (S t) (lam t) := by
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
    obtain ⟨a, ha, -, s, hs, -, w, hw, -, hstep⟩ := hsteps t
    exact inv_bstep ih ha hs hw hstep

/-- Exact line search on `[0, Λ]` with a result below `Λ` is optimal along the whole ray. -/
theorem ray_opt {f : E → ℝ} (hconv : ConvexOn ℝ Set.univ f) {x d : E} {Λ γ : ℝ} (hγΛ : γ < Λ)
    (hmin : ∀ σ ∈ Set.Icc (0 : ℝ) Λ, f (x - γ • d) ≤ f (x - σ • d)) (hγ0 : 0 ≤ γ) :
    ∀ σ : ℝ, 0 ≤ σ → f (x - γ • d) ≤ f (x - σ • d) := by
  intro σ hσ
  rcases le_or_gt σ Λ with h | h
  · exact hmin σ ⟨hσ, h⟩
  set θ := (Λ - γ) / (σ - γ) with hθ
  have hσγ : 0 < σ - γ := by linarith
  have hθ0 : 0 < θ := div_pos (by linarith) hσγ
  have hθ1 : θ ≤ 1 := (div_le_one hσγ).mpr (by linarith)
  have hc := hconv.2 (Set.mem_univ (x - γ • d)) (Set.mem_univ (x - σ • d)) (sub_nonneg.mpr hθ1)
    hθ0.le (by ring)
  have hcoef : (1 - θ) * γ + θ * σ = Λ := by rw [hθ]; field_simp; ring
  have hpt : (1 - θ) • (x - γ • d) + θ • (x - σ • d) = x - ((1 - θ) * γ + θ * σ) • d := by
    module
  rw [hpt, hcoef, smul_eq_mul, smul_eq_mul] at hc
  have h1 := hmin Λ ⟨by linarith, le_rfl⟩
  nlinarith

/-- The smoothness bound along a direction. -/
theorem quad_along {f : E → ℝ} {L : NNReal} (hsm : IsSmooth f L) (x d : E) (σ : ℝ) :
    f (x - σ • d) ≤ f x - σ * fderiv ℝ f x d + σ ^ 2 * L / 2 * ‖d‖ ^ 2 := by
  have hq := hsm.le_quadratic x (x - σ • d)
  rw [show x - σ • d - x = -(σ • d) by abel, map_neg, map_smul, smul_eq_mul, norm_neg,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at hq
  linarith

open Classical in
/-- One BPCG step is a drop step (the active set shrinks) or a good step with gap `G`. -/
theorem bstep_outcome {V : Finset E} {f : E → ℝ} {L : NNReal} (hL : 0 < (L : ℝ))
    (hconv : ConvexOn ℝ Set.univ f) (hsm : IsSmooth f L) {xStar : E}
    (hxs : xStar ∈ minimizers (convexHull ℝ (↑V : Set E)) f) {x : E} {S : Finset E}
    {lam : E → ℝ} (h : Lemmata.AwayStepFW.Proof.Inv V x S lam) {a s w x' : E} {S' : Finset E}
    {lam' : E → ℝ} (ha : a ∈ S) (_haS : ∀ u ∈ S, fderiv ℝ f x u ≤ fderiv ℝ f x a) (hs : s ∈ S)
    (hsS : ∀ u ∈ S, fderiv ℝ f x s ≤ fderiv ℝ f x u) (hw : w ∈ V)
    (hwV : ∀ u ∈ V, fderiv ℝ f x w ≤ fderiv ℝ f x u)
    (hstep : IsBPCGStep f x S lam a s w x' S' lam') :
    (f x' ≤ f x ∧ S'.card + 1 = S.card) ∨
      (S'.card ≤ S.card + 1 ∧ ∃ G, f x - f xStar ≤ G ∧ fderiv ℝ f x (a - w) ≤ 2 * G ∧
        f x' ≤ f x - min (G / 2) (G ^ 2 / (2 * L * Metric.diam (↑V : Set E) ^ 2)) ∧
        f x' - f xStar ≤ L * Metric.diam (↑V : Set E) ^ 2 / 2) := by
  set g := fderiv ℝ f x with hg
  set D := Metric.diam (↑V : Set E) with hD
  have hP : IsCompact (convexHull ℝ (↑V : Set E)) := V.finite_toSet.isCompact_convexHull (𝕜 := ℝ)
  have hxP : x ∈ convexHull ℝ (↑V : Set E) :=
    convexHull_mono (by exact_mod_cast h.sub) h.mem_convexHull
  have hdist : ∀ y ∈ convexHull ℝ (↑V : Set E), ∀ z ∈ convexHull ℝ (↑V : Set E), ‖y - z‖ ≤ D :=
    fun y hy z hz => by
      rw [← dist_eq_norm, hD, ← convexHull_diam]
      exact Metric.dist_le_diam_of_mem hP.isBounded hy hz
  have hVP : ∀ u ∈ V, u ∈ convexHull ℝ (↑V : Set E) := fun u hu =>
    subset_convexHull ℝ _ (by exact_mod_cast hu)
  have hSP : ∀ u ∈ S, u ∈ convexHull ℝ (↑V : Set E) := fun u hu => hVP u (h.sub hu)
  -- the Frank–Wolfe gap bounds the primal gap
  have hgap : f x - f xStar ≤ g (x - w) := by
    have h1 := add_fderiv_le_of_convexOn hconv hsm.1 x xStar
    have h2 := Lemmata.CGBasics.Proof.le_on_hull g hwV hxs.1
    rw [map_sub] at h1 ⊢
    linarith
  have hsx : g s ≤ g x := Lemmata.CGBasics.Proof.le_on_hull (V := S) g hsS h.mem_convexHull
  have hfw0 : 0 ≤ g (x - w) := by
    rw [map_sub]; linarith [Lemmata.CGBasics.Proof.le_on_hull g hwV hxP]
  have hDsq : 0 ≤ (L : ℝ) * D ^ 2 := by positivity
  -- generic progress from `∀ σ ∈ [0, Λ]`-optimality with `Λ ≥ 1` or the full ray
  have hfin : ∀ G : ℝ, 0 ≤ G → ∀ d : E, ‖d‖ ≤ D → g d = G →
      (∀ σ ∈ Set.Icc (0 : ℝ) 1, f x' ≤ f (x - σ • d)) →
      f x' ≤ f x - min (G / 2) (G ^ 2 / (2 * L * D ^ 2)) ∧ f x' ≤ f x - G + L * D ^ 2 / 2 := by
    intro G hG d hd hgd hls
    have hq : ∀ σ ∈ Set.Icc (0 : ℝ) 1, f x' ≤ f x - σ * G + σ ^ 2 * (L * D ^ 2) / 2 := by
      intro σ hσ
      have h1 := hls σ hσ
      have h2 := quad_along hsm x d σ
      rw [hgd] at h2
      have h3 : σ ^ 2 * L / 2 * ‖d‖ ^ 2 ≤ σ ^ 2 * (L * D ^ 2) / 2 := by
        have := pow_le_pow_left₀ (norm_nonneg d) hd 2
        have := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ σ ^ 2 * L)
        nlinarith
      linarith
    refine ⟨?_, by have := hq 1 ⟨zero_le_one, le_rfl⟩; linarith⟩
    rcases eq_or_lt_of_le hDsq with hK0 | hKpos
    · rw [show (2 : ℝ) * L * D ^ 2 = 2 * (L * D ^ 2) by ring, ← hK0, mul_zero, div_zero,
        min_eq_right (by linarith)]
      have := hq 0 ⟨le_rfl, zero_le_one⟩
      simp at this; linarith
    rcases le_total G (L * D ^ 2) with hGK | hGK
    · have := hq (G / (L * D ^ 2)) ⟨by positivity, (div_le_one hKpos).mpr hGK⟩
      have e : G / (L * D ^ 2) * G - (G / (L * D ^ 2)) ^ 2 * (L * D ^ 2) / 2 =
          G ^ 2 / (2 * (L * D ^ 2)) := by field_simp; ring
      have hm := min_le_right (G / 2) (G ^ 2 / (2 * L * D ^ 2))
      rw [show 2 * (L : ℝ) * D ^ 2 = 2 * (L * D ^ 2) by ring] at hm ⊢
      linarith
    · have := hq 1 ⟨zero_le_one, le_rfl⟩
      have hm := min_le_left (G / 2) (G ^ 2 / (2 * L * D ^ 2))
      linarith
  have hinv' := inv_bstep h ha hs hw hstep
  have hlow : f xStar ≤ f x' :=
    hxs.2 _ (convexHull_mono (by exact_mod_cast hinv'.sub) hinv'.mem_convexHull)
  have hlin : ∀ u v : E, g (u - v) = g u - g v := fun u v => map_sub g u v
  unfold IsBPCGStep at hstep
  split_ifs at hstep with hsel
  · obtain ⟨γ, hγ, hls, rfl, rfl, rfl⟩ := hstep
    by_cases hdrop : γ = lam a ∧ a ≠ s
    · left
      refine ⟨by simpa using hls 0 ⟨le_rfl, h.nonneg a⟩, ?_⟩
      rw [ite_eq_left hdrop]
      exact Finset.card_erase_add_one ha
    · right
      rw [ite_eq_right hdrop]
      refine ⟨Nat.le_succ _, g (a - s), hgap.trans hsel, ?_, ?_⟩
      · rw [hlin a w, hlin a s]
        rw [hlin x w, hlin a s] at hsel
        linarith
      · by_cases has : a = s
        · subst has
          simp only [sub_self, smul_zero, sub_zero, map_zero]
          have hh : f x - f xStar ≤ 0 := by
            have := hgap.trans hsel; simpa using this
          refine ⟨by simp, by linarith⟩
        · have hγlt : γ < lam a := lt_of_le_of_ne hγ.2 (fun e => hdrop ⟨e, has⟩)
          have hray := ray_opt hconv hγlt hls hγ.1
          have hG0 : 0 ≤ g (a - s) := hfw0.trans hsel
          obtain ⟨h1, h2⟩ := hfin (g (a - s)) hG0 (a - s) (hdist a (hSP a ha) s (hSP s hs)) rfl
            (fun σ hσ => hray σ hσ.1)
          refine ⟨h1, ?_⟩
          have := hgap.trans hsel
          linarith
  · obtain ⟨γ, hγ, hls, rfl, rfl, rfl⟩ := hstep
    right
    refine ⟨?_, g (x - w), hgap, ?_, ?_⟩
    · split_ifs
      · simp
      · exact Finset.card_insert_le w S
    · push Not at hsel
      rw [hlin a w, hlin x w]
      rw [hlin a s, hlin x w] at hsel
      linarith
    · obtain ⟨h1, h2⟩ := hfin (g (x - w)) hfw0 (x - w) (hdist x hxP w (hVP w hw)) rfl hls
      refine ⟨h1, ?_⟩
      linarith

universe u

theorem bpcg_convex_rate : ConvexRate.{u} := by
  intro E _ _ V f L x S lam hL hconv hsm hrun xStar hxs T hT
  classical
  set D := Metric.diam (↑V : Set E) with hD
  set K : ℝ := L * D ^ 2 with hK
  have hK0 : 0 ≤ K := by positivity
  have inv := bpcg_run_inv hrun
  have hout : ∀ t, (f (x (t + 1)) ≤ f (x t) ∧ (S (t + 1)).card + 1 = (S t).card) ∨
      ((S (t + 1)).card ≤ (S t).card + 1 ∧ ∃ G, f (x t) - f xStar ≤ G ∧
        f (x (t + 1)) ≤ f (x t) - min (G / 2) (G ^ 2 / (2 * K)) ∧
        f (x (t + 1)) - f xStar ≤ K / 2) := by
    intro t
    obtain ⟨a, ha, haS, s, hs, hsS, w, hw, hwV, hstep⟩ := hrun.2.2.2 t
    rcases bstep_outcome hL hconv hsm hxs (inv t) ha haS hs hsS hw hwV hstep with
      h | ⟨hc, G, h1, -, h3, h4⟩
    · exact Or.inl h
    · refine Or.inr ⟨hc, G, h1, ?_, by rw [hK]; exact h4⟩
      have e : (2 : ℝ) * L * D ^ 2 = 2 * K := by rw [hK]; ring
      rw [e] at h3
      exact h3
  have hstate : ∀ t, ∃ G Dr : ℕ, G + Dr = t ∧ (S t).card + Dr ≤ 1 + G ∧
      (1 ≤ G → f (x t) - f xStar ≤ 2 * K / G) := by
    intro t
    induction t with
    | zero => exact ⟨0, 0, rfl, by rw [hrun.2.1]; simp, fun h => absurd h (by omega)⟩
    | succ t ih =>
      obtain ⟨G, Dr, hsum, hcard, hbd⟩ := ih
      rcases hout t with ⟨hm, hc⟩ | ⟨hc, Gap, h1, h2, h3⟩
      · refine ⟨G, Dr + 1, by omega, by omega, fun hG => ?_⟩
        have := hbd hG
        linarith
      · refine ⟨G + 1, Dr, by omega, by omega, fun _ => ?_⟩
        rcases Nat.lt_or_ge G 2 with hG | hG
        · have : K / 2 ≤ 2 * K / ((G + 1 : ℕ) : ℝ) := by
            rw [div_le_div_iff₀ (by norm_num) (by positivity)]
            have : ((G + 1 : ℕ) : ℝ) ≤ 2 := by exact_mod_cast (show G + 1 ≤ 2 by omega)
            nlinarith
          linarith
        · have hG1 : (1 : ℝ) ≤ G := by exact_mod_cast (show 1 ≤ G by omega)
          have hG2 : (2 : ℝ) ≤ G := by exact_mod_cast hG
          have hb := hbd (by omega)
          rcases eq_or_lt_of_le hK0 with hKz | hKpos
          · rw [← hKz] at h3 ⊢; simp at h3 ⊢; linarith
          set h0 := f (x t) - f xStar with hh0
          have hh0n : 0 ≤ h0 := by
            have := hxs.2 _ (convexHull_mono (by exact_mod_cast (inv t).sub) (inv t).mem_convexHull)
            linarith
          set b := 2 * K / (G : ℝ) with hbdef
          have hbK : b ≤ K := by rw [hbdef, div_le_iff₀ (by linarith)]; nlinarith
          -- progress at least `h0²/(2K)`
          have hprog : f (x (t + 1)) - f xStar ≤ h0 - h0 ^ 2 / (2 * K) := by
            have hm : h0 ^ 2 / (2 * K) ≤ min (Gap / 2) (Gap ^ 2 / (2 * K)) := by
              apply le_min
              · rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
              · exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hh0n h1 2) (by positivity)
            linarith
          -- `φ(h) = h - h²/(2K)` is increasing on `[0, K]`
          have hphi : h0 - h0 ^ 2 / (2 * K) ≤ b - b ^ 2 / (2 * K) := by
            have e : (b - b ^ 2 / (2 * K)) - (h0 - h0 ^ 2 / (2 * K)) =
                (b - h0) * (2 * K - (b + h0)) / (2 * K) := by field_simp; ring
            have : 0 ≤ (b - h0) * (2 * K - (b + h0)) / (2 * K) :=
              div_nonneg (mul_nonneg (by linarith) (by linarith)) (by positivity)
            linarith
          have hfin : b - b ^ 2 / (2 * K) ≤ 2 * K / ((G + 1 : ℕ) : ℝ) := by
            have e : b - b ^ 2 / (2 * K) = 2 * K * (G - 1) / (G : ℝ) ^ 2 := by
              rw [hbdef]; field_simp
            rw [e]
            push_cast
            rw [div_le_div_iff₀ (by positivity) (by positivity)]
            nlinarith
          linarith
  obtain ⟨G, Dr, hsum, hcard, hbd⟩ := hstate T
  have hS1 : 1 ≤ (S T).card := by
    rcases Nat.eq_zero_or_pos (S T).card with h0 | h0
    · have := (inv T).sum
      rw [Finset.card_eq_zero.mp h0, Finset.sum_empty] at this
      norm_num at this
    · exact h0
  have hG : 1 ≤ G := by omega
  have hb := hbd hG
  have hTG : (T : ℝ) ≤ 2 * G := by exact_mod_cast (show T ≤ 2 * G by omega)
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hG0 : (0 : ℝ) < G := by exact_mod_cast hG
  calc f (x T) - f xStar ≤ 2 * K / G := hb
    _ ≤ 4 * L * D ^ 2 / T := by
      rw [div_le_div_iff₀ hG0 hT0, hK]
      nlinarith [mul_le_mul_of_nonneg_left hTG (by positivity : (0 : ℝ) ≤ 2 * (L * D ^ 2))]

theorem bpcg_linear_rate : LinearRate.{u} := by
  intro E _ _ V f L μ δ x S lam hL hμ hδ hsc hconv hsm hstrong hrun xStar hxs T
  classical
  set D := Metric.diam (↑V : Set E) with hD
  set q := min (1 / 2 : ℝ) (μ * δ ^ 2 / (4 * L * D ^ 2)) with hq
  have hq0 : 0 ≤ q := le_min (by norm_num) (by positivity)
  have hq1 : q ≤ 1 / 2 := min_le_left _ _
  have inv := bpcg_run_inv hrun
  have hxP : ∀ t, x t ∈ convexHull ℝ (↑V : Set E) := fun t =>
    convexHull_mono (by exact_mod_cast (inv t).sub) (inv t).mem_convexHull
  have hh : ∀ t, 0 ≤ f (x t) - f xStar := fun t => by have := hxs.2 _ (hxP t); linarith
  have hout : ∀ t, (f (x (t + 1)) ≤ f (x t) ∧ (S (t + 1)).card + 1 = (S t).card) ∨
      ((S (t + 1)).card ≤ (S t).card + 1 ∧
        f (x (t + 1)) - f xStar ≤ (1 - q) * (f (x t) - f xStar)) := by
    intro t
    obtain ⟨a, ha, haS, s, hs, hsS, w, hw, hwV, hstep⟩ := hrun.2.2.2 t
    rcases bstep_outcome hL hconv hsm hxs (inv t) ha haS hs hsS hw hwV hstep with
      h | ⟨hc, G, h1, h2, h3, -⟩
    · exact Or.inl h
    refine Or.inr ⟨hc, ?_⟩
    set g := fderiv ℝ f (x t) with hg
    set h0 := f (x t) - f xStar with hh0
    have hgeo := geometric_strong_convexity V f μ δ hμ hδ hsc hstrong xStar hxs (S t) (inv t).sub
      (x t) (inv t).mem_convexHull a ha haS w hw hwV
    have hG0 : 0 ≤ G := le_trans (hh t) h1
    have hgaw0 : 0 ≤ g (a - w) := by
      have h1' := (inv t).apply_le g haS
      have h2' := Lemmata.CGBasics.Proof.le_on_hull g hwV (hxP t)
      rw [map_sub]; linarith
    have hsq : 2 * μ * δ ^ 2 * h0 ≤ 4 * G ^ 2 := by
      have h4 := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * μ * δ ^ 2)).mp hgeo
      have h5 : g (a - w) ^ 2 ≤ (2 * G) ^ 2 := pow_le_pow_left₀ hgaw0 h2 2
      nlinarith
    have hmin : q * h0 ≤ min (G / 2) (G ^ 2 / (2 * L * D ^ 2)) := by
      apply le_min
      · nlinarith [hh t]
      · rcases eq_or_lt_of_le (by positivity : (0 : ℝ) ≤ L * D ^ 2) with hK | hK
        · have : q ≤ 0 := by
            rw [hq]; refine (min_le_right _ _).trans ?_
            rw [show (4 : ℝ) * L * D ^ 2 = 4 * (L * D ^ 2) by ring, ← hK]; simp
          rw [show (2 : ℝ) * L * D ^ 2 = 2 * (L * D ^ 2) by ring, ← hK]
          simp only [mul_zero, div_zero]
          nlinarith [hh t]
        · have hqle : q ≤ μ * δ ^ 2 / (4 * L * D ^ 2) := min_le_right _ _
          calc q * h0 ≤ μ * δ ^ 2 / (4 * L * D ^ 2) * h0 := mul_le_mul_of_nonneg_right hqle (hh t)
            _ ≤ G ^ 2 / (2 * L * D ^ 2) := by
              rw [div_mul_eq_mul_div, div_le_div_iff₀ (by linarith) (by linarith)]
              nlinarith
    linarith
  have hstate : ∀ t, ∃ G Dr : ℕ, G + Dr = t ∧ (S t).card + Dr ≤ 1 + G ∧
      f (x t) - f xStar ≤ (1 - q) ^ G * (f (x 0) - f xStar) := by
    intro t
    induction t with
    | zero => exact ⟨0, 0, rfl, by rw [hrun.2.1]; simp, by simp⟩
    | succ t ih =>
      obtain ⟨G, Dr, hsum, hcard, hbd⟩ := ih
      rcases hout t with ⟨hm, hc⟩ | ⟨hc, hc2⟩
      · exact ⟨G, Dr + 1, by omega, by omega, by linarith⟩
      · refine ⟨G + 1, Dr, by omega, by omega, ?_⟩
        calc f (x (t + 1)) - f xStar ≤ (1 - q) * (f (x t) - f xStar) := hc2
          _ ≤ (1 - q) * ((1 - q) ^ G * (f (x 0) - f xStar)) :=
            mul_le_mul_of_nonneg_left hbd (by linarith)
          _ = (1 - q) ^ (G + 1) * (f (x 0) - f xStar) := by ring
  obtain ⟨G, Dr, hsum, hcard, hbd⟩ := hstate T
  have hS1 : 1 ≤ (S T).card := by
    rcases Nat.eq_zero_or_pos (S T).card with h0 | h0
    · have := (inv T).sum
      rw [Finset.card_eq_zero.mp h0, Finset.sum_empty] at this
      norm_num at this
    · exact h0
  have hTG : (T : ℝ) ≤ 2 * G := by exact_mod_cast (show T ≤ 2 * G by omega)
  have h1 : (1 - q) ^ G ≤ Real.exp (-q) ^ G :=
    pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp (-q)]) G
  rw [← Real.exp_nat_mul] at h1
  have h2 : Real.exp (G * -q) ≤ Real.exp (-(1 / 2 * q) * T) :=
    Real.exp_le_exp.mpr (by nlinarith)
  calc f (x T) - f xStar ≤ (1 - q) ^ G * (f (x 0) - f xStar) := hbd
    _ ≤ Real.exp (-(1 / 2 * q) * T) * (f (x 0) - f xStar) :=
      mul_le_mul_of_nonneg_right (h1.trans h2) (hh 0)
    _ = (f (x 0) - f xStar) * Real.exp (-(1 / 2 * q) * T) := by ring

end Proof

end Lemmata.BPCG
