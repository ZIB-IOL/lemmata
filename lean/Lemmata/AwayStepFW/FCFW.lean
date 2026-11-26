module

public import Lemmata.AwayStepFW.Progress
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

@[expose] public section

/-!
# Linear convergence of fully-corrective Frank–Wolfe (Theorem 2.34)

An iterate that minimizes `f` over the convex hull of its active set satisfies `f'(x)(w) ≥ f'(x)(x)`
for every vertex `w` of the active set, with equality on the vertices that carry weight, so it lies
in the convex hull of vertices on which the away gap vanishes. Geometric strong convexity then
bounds the primal gap by the squared Frank–Wolfe gap, and a Frank–Wolfe step contracts it.
-/

namespace Lemmata.AwayStepFW

open Lemmata.FrankWolfe

universe u

namespace Proof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem first_order_nonneg {f : E → ℝ} (hf : Differentiable ℝ f) {K : Set E} (hK : Convex ℝ K)
    {x : E} (hx : x ∈ K) (hmin : ∀ y ∈ K, f x ≤ f y) {y : E} (hy : y ∈ K) :
    0 ≤ fderiv ℝ f x (y - x) := by
  have hloc : IsLocalMinOn f K x := (show IsMinOn f K x from fun z hz => hmin z hz).isLocalMinOn
  exact hloc.hasFDerivWithinAt_nonneg (hf x).hasFDerivAt.hasFDerivWithinAt
    (sub_mem_posTangentConeAt_of_segment_subset (hK.segment_subset hx hy))

theorem mem_convexHull_filter {S : Finset E} (g : StrongDual ℝ E) {x : E}
    (hx : x ∈ convexHull ℝ (↑S : Set E)) (hge : ∀ w ∈ S, g x ≤ g w) :
    x ∈ convexHull ℝ (↑(S.filter (fun w => g w = g x)) : Set E) := by
  classical
  obtain ⟨c, hc0, hc1, hcx⟩ := Finset.mem_convexHull'.mp hx
  have hzero : ∀ w ∈ S, c w * (g w - g x) = 0 := by
    have hsum : ∑ w ∈ S, c w * (g w - g x) = 0 := by
      have e1 : ∑ w ∈ S, c w * g w = g x := by
        rw [← hcx, map_sum]; simp [map_smul, smul_eq_mul]
      simp only [mul_sub, Finset.sum_sub_distrib, e1, ← Finset.sum_mul, hc1, one_mul, sub_self]
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun w hw =>
      mul_nonneg (hc0 w hw) (by linarith [hge w hw]))).mp hsum
  have hc' : ∀ w ∈ S, w ∉ S.filter (fun w => g w = g x) → c w = 0 := by
    intro w hw hwf
    have hne : g w - g x ≠ 0 := by
      intro h; exact hwf (Finset.mem_filter.mpr ⟨hw, by linarith⟩)
    exact (mul_eq_zero.mp (hzero w hw)).resolve_right hne
  rw [Finset.mem_convexHull']
  refine ⟨c, fun w hw => hc0 w (Finset.mem_of_mem_filter w hw), ?_, ?_⟩
  · exact (Finset.sum_subset (Finset.filter_subset _ _) (fun w hw hwf => hc' w hw hwf)).trans hc1
  · exact (Finset.sum_subset (Finset.filter_subset _ _)
      (fun w hw hwf => by rw [hc' w hw hwf, zero_smul])).trans hcx

theorem fully_corrective_convergence : FullyCorrectiveConvergence.{u} := by
  intro E _ _ V f L μ δ x S hL hμ hδ hsc hconv hsm hstrong h xStar hxs t ht
  classical
  set D := Metric.diam (↑V : Set E) with hD
  set ρ := min (1 / 2) (μ * δ ^ 2 / (L * D ^ 2)) with hρ
  have hρ1 : ρ ≤ 1 / 2 := min_le_left _ _
  have hρ2 : ρ ≤ μ * δ ^ 2 / (L * D ^ 2) := min_le_right _ _
  have hq0 : 0 ≤ 1 - ρ := by linarith
  have hbdd : Bornology.IsBounded (convexHull ℝ (↑V : Set E)) :=
    isBounded_convexHull.mpr V.finite_toSet.isBounded
  have hdist : ∀ y ∈ convexHull ℝ (↑V : Set E), ∀ z ∈ convexHull ℝ (↑V : Set E), ‖y - z‖ ≤ D :=
    fun y hy z hz => by
      rw [← dist_eq_norm, hD, ← convexHull_diam]; exact Metric.dist_le_diam_of_mem hbdd hy hz
  have hxV : ∀ s, x s ∈ convexHull ℝ (↑V : Set E) := fun s =>
    convexHull_mono (by exact_mod_cast (h.2.2 s).1) (h.2.2 s).2.1
  -- one step: `h_{s+1} ≤ h_s - γ G + γ² L D²/2` for all `γ ∈ [0, 1]`, with `G ≥ h_s` and
  -- `G² ≥ 2 μ δ² h_s`
  have hstep : ∀ s, ∃ G : ℝ, 0 ≤ G ∧ f (x s) - f xStar ≤ G ∧
      2 * μ * δ ^ 2 * (f (x s) - f xStar) ≤ G ^ 2 ∧
      ∀ γ ∈ Set.Icc (0 : ℝ) 1, f (x (s + 1)) ≤ f (x s) - γ * G + γ ^ 2 * L / 2 * D ^ 2 := by
    intro s
    obtain ⟨hSV, hxS, hmin, v, hvV, hv, hnext⟩ := h.2.2 s
    set g := fderiv ℝ f (x s) with hg
    have hvC : v ∈ convexHull ℝ (↑V : Set E) := subset_convexHull ℝ _ (by exact_mod_cast hvV)
    have hge : ∀ w ∈ S s, g (x s) ≤ g w := by
      intro w hw
      have := first_order_nonneg hsm.1 (convex_convexHull ℝ _) hxS hmin
        (subset_convexHull ℝ _ (by exact_mod_cast hw))
      rw [map_sub] at this; linarith
    set S' := (S s).filter (fun w => g w = g (x s)) with hS'
    have hxS' : x s ∈ convexHull ℝ (↑S' : Set E) := mem_convexHull_filter g hxS hge
    obtain ⟨a, ha⟩ : S'.Nonempty := by
      by_contra hne
      rw [Finset.not_nonempty_iff_eq_empty] at hne
      rw [hne, Finset.coe_empty, convexHull_empty] at hxS'
      exact hxS'
    have haS : ∀ w ∈ S', g w ≤ g a := by
      intro w hw
      rw [(Finset.mem_filter.mp hw).2, (Finset.mem_filter.mp ha).2]
    have hS'V : S' ⊆ V := (Finset.filter_subset _ _).trans hSV
    have hgeo := geometric_strong_convexity V f μ δ hμ hδ hsc hstrong xStar hxs S' hS'V (x s) hxS'
      a ha haS v hvV hv
    have hGa : g (a - v) = g (x s - v) := by
      rw [map_sub, map_sub, (Finset.mem_filter.mp ha).2]
    refine ⟨g (x s - v), ?_, ?_, ?_, ?_⟩
    · rw [map_sub]; linarith [le_of_min_vertex g hv (hxV s)]
    · have h1 := add_fderiv_le_of_convexOn hconv hsm.1 (x s) xStar
      have h2 := le_of_min_vertex g hv hxs.1
      rw [map_sub] at h1 ⊢
      linarith
    · rw [hGa] at hgeo
      have := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * μ * δ ^ 2)).mp hgeo
      linarith
    · intro γ hγ
      have h1 := hnext γ hγ
      have h2 := hsm.progress (x s) v γ
      have h3 : ‖v - x s‖ ^ 2 ≤ D ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hdist v hvC (x s) (hxV s)) 2
      have h4 : γ ^ 2 * L / 2 * ‖v - x s‖ ^ 2 ≤ γ ^ 2 * L / 2 * D ^ 2 :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
      linarith
  have hcontract : ∀ s, f (x (s + 1)) - f xStar ≤ (1 - ρ) * (f (x s) - f xStar) := by
    intro s
    obtain ⟨G, hG0, hGh, hGsq, hprog⟩ := hstep s
    have hh0 : 0 ≤ f (x s) - f xStar := sub_nonneg.mpr (hxs.2 _ (hxV s))
    rcases le_or_gt G (L * D ^ 2) with hle | hlt
    · rcases eq_or_lt_of_le (by positivity : (0 : ℝ) ≤ L * D ^ 2) with hK0 | hKpos
      · have hG : G = 0 := by linarith
        have : f (x s) - f xStar ≤ 0 := by rw [hG] at hGh; exact hGh
        have h1 := hprog 0 ⟨le_rfl, zero_le_one⟩
        nlinarith
      · have hγ : G / (L * D ^ 2) ∈ Set.Icc (0 : ℝ) 1 :=
          ⟨div_nonneg hG0 hKpos.le, (div_le_one hKpos).mpr hle⟩
        have h1 := hprog _ hγ
        have hval : G / (L * D ^ 2) * G - (G / (L * D ^ 2)) ^ 2 * L / 2 * D ^ 2 =
            G ^ 2 / (2 * (L * D ^ 2)) := by field_simp; ring
        have h2 : ρ * (f (x s) - f xStar) ≤ G ^ 2 / (2 * (L * D ^ 2)) := by
          calc ρ * (f (x s) - f xStar) ≤ μ * δ ^ 2 / (L * D ^ 2) * (f (x s) - f xStar) :=
                mul_le_mul_of_nonneg_right hρ2 hh0
            _ ≤ G ^ 2 / (2 * (L * D ^ 2)) := by
                rw [div_mul_eq_mul_div, div_le_div_iff₀ hKpos (by positivity)]
                nlinarith
        linarith
    · have h1 := hprog 1 ⟨zero_le_one, le_rfl⟩
      have h2 := mul_le_mul_of_nonneg_right hρ1 hh0
      nlinarith
  have hbase : f (x 1) - f xStar ≤ L * D ^ 2 / 2 := by
    obtain ⟨G, hG0, hGh, -, hprog⟩ := hstep 0
    have := hprog 1 ⟨zero_le_one, le_rfl⟩
    linarith
  induction t, ht using Nat.le_induction with
  | base => simpa using hbase
  | succ t ht ih =>
    calc f (x (t + 1)) - f xStar ≤ (1 - ρ) * (f (x t) - f xStar) := hcontract t
      _ ≤ (1 - ρ) * ((1 - ρ) ^ (t - 1) * (L * D ^ 2 / 2)) := mul_le_mul_of_nonneg_left ih hq0
      _ = (1 - ρ) ^ (t + 1 - 1) * (L * D ^ 2 / 2) := by
        rw [show t + 1 - 1 = (t - 1) + 1 by omega, pow_succ]; ring

end Proof

end Lemmata.AwayStepFW
