module

public import Lemmata.FWRestart.Statement
public import Lemmata.FWUniformlyConvex.Main
public import Lemmata.AwayStepFW.Main

@[expose] public section

/-!
# The strong Wolfe gap and strong Wolfe primal bounds

The strong Wolfe gap `w(x, S) = f'(x)(a - v)` of an iterate with active set `S` is the sum of the
away gap `f'(x)(a - x)` and the Frank–Wolfe gap `f'(x)(x - v)`; it bounds the primal gap and
vanishes exactly at the minimizers when the weights are positive (Lemma 2.3). Under a Hölderian
error bound, the scaling property of the pyramidal width turns it into a primal bound with exponent
`1/(1-θ)` (Lemma 3.6). Over strongly convex sets, the rate of vanilla Frank–Wolfe under a Hölderian
error bound (Theorem 7.3) is the case `q = 2` of the rate over uniformly convex sets.
-/

namespace Lemmata.FWRestart

open Lemmata.FrankWolfe Lemmata.CGBasics Lemmata.AwayStepFW

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Lemma 2.3.** -/
theorem strong_wolfe_gap_bound {V S : Finset E} {f : E → ℝ} {lam : E → ℝ} {x a v : E}
    (hSV : S ⊆ V) (hpos : ∀ y ∈ S, 0 < lam y) (hsum : ∑ y ∈ S, lam y = 1)
    (hx : x = ∑ y ∈ S, lam y • y) (hconv : ConvexOn ℝ (convexHull ℝ (↑V : Set E)) f)
    (hdiff : ∀ y ∈ convexHull ℝ (↑V : Set E), DifferentiableAt ℝ f y)
    (ha : a ∈ S) (haS : ∀ y ∈ S, fderiv ℝ f x y ≤ fderiv ℝ f x a)
    (hv : v ∈ V) (hvV : ∀ y ∈ V, fderiv ℝ f x v ≤ fderiv ℝ f x y) :
    (∀ xStar ∈ minimizers (convexHull ℝ (↑V : Set E)) f, f x - f xStar ≤ fderiv ℝ f x (a - v)) ∧
    (fderiv ℝ f x (a - v) = 0 ↔ x ∈ minimizers (convexHull ℝ (↑V : Set E)) f) := by
  set C := convexHull ℝ (↑V : Set E) with hCdef
  set g := fderiv ℝ f x with hg
  have hxS : x ∈ convexHull ℝ (↑S : Set E) := by
    rw [hx]
    exact (convex_convexHull ℝ _).sum_mem (fun y hy => (hpos y hy).le) hsum
      (fun y hy => subset_convexHull ℝ _ (Finset.mem_coe.mpr hy))
  have hxC : x ∈ C := convexHull_mono (by exact_mod_cast hSV) hxS
  have hax : g x ≤ g a := apply_le_of_mem_convexHull g haS hxS
  have hvy : ∀ y ∈ C, g v ≤ g y := fun y hy => Proof.le_of_min_vertex g hvV hy
  have hsplit : g (a - v) = g (a - x) + g (x - v) := by simp only [map_sub]; ring
  refine ⟨fun xStar hxs => ?_, ⟨fun h0 => ?_, fun hxmin => ?_⟩⟩
  · have hc := Lemmata.FrankWolfe.convexOn_add_fderiv_le hconv hxC (hdiff x hxC) hxs.1
    have h1 := hvy xStar hxs.1
    rw [map_sub] at hc
    rw [hsplit, map_sub, map_sub]
    linarith
  · -- the Frank–Wolfe gap vanishes, so `x` is a minimizer
    refine ⟨hxC, fun y hy => ?_⟩
    have hc := Lemmata.FrankWolfe.convexOn_add_fderiv_le hconv hxC (hdiff x hxC) hy
    have h1 := hvy y hy
    rw [hsplit, map_sub, map_sub] at h0
    rw [map_sub] at hc
    linarith
  · -- at a minimizer both gaps vanish
    have hfo : ∀ y ∈ C, 0 ≤ g (y - x) := by
      intro y hy
      have hloc : IsLocalMinOn f C x := (isMinOn_iff.mpr hxmin.2).isLocalMinOn
      exact hloc.hasFDerivWithinAt_nonneg (hdiff x hxC).hasFDerivAt.hasFDerivWithinAt
        (sub_mem_posTangentConeAt_of_segment_subset ((convex_convexHull ℝ _).segment_subset hxC hy))
    have hvC : v ∈ C := subset_convexHull ℝ _ (Finset.mem_coe.mpr hv)
    have hFW : g (x - v) = 0 := by
      have h1 := hfo v hvC
      have h2 := hvy x hxC
      rw [map_sub] at h1 ⊢
      linarith
    -- `∑ λ_y g(y - x) = 0` with nonnegative terms
    have hterms : ∀ y ∈ S, 0 ≤ g (y - x) := fun y hy =>
      hfo y (subset_convexHull ℝ _ (Finset.mem_coe.mpr (hSV hy)))
    have hzero : ∑ y ∈ S, lam y * g (y - x) = 0 := by
      have : ∑ y ∈ S, lam y * g (y - x) = g (∑ y ∈ S, lam y • y) - g x := by
        simp only [map_sub, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, one_mul,
          map_sum, map_smul, smul_eq_mul]
      rw [this, ← hx, sub_self]
    have heach := (Finset.sum_eq_zero_iff_of_nonneg (fun y hy =>
      mul_nonneg (hpos y hy).le (hterms y hy))).mp hzero
    have haway : g (a - x) = 0 := by
      have := heach a ha
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h (hpos a ha).ne'
      · exact h
    rw [hsplit, haway, hFW, add_zero]

/-- **Lemma 3.6.** -/
theorem heb_strong_wolfe {V S : Finset E} {f : E → ℝ} {c θ δ : ℝ} {x a v xStar : E}
    (hconv : ConvexOn ℝ (convexHull ℝ (↑V : Set E)) f)
    (hdiff : ∀ y ∈ convexHull ℝ (↑V : Set E), DifferentiableAt ℝ f y)
    (heb : IsHolderErrorBound (convexHull ℝ (↑V : Set E)) f c θ) (hc : 0 < c)
    (hθ : θ ∈ Set.Icc (0 : ℝ) (1 / 2)) (hδ : 0 < δ) (hsc : IsScaling V δ)
    (hxs : xStar ∈ minimizers (convexHull ℝ (↑V : Set E)) f) (hSV : S ⊆ V)
    (hx : x ∈ convexHull ℝ (↑S : Set E)) (ha : a ∈ S)
    (haS : ∀ y ∈ S, fderiv ℝ f x y ≤ fderiv ℝ f x a) (hv : v ∈ V)
    (hvV : ∀ y ∈ V, fderiv ℝ f x v ≤ fderiv ℝ f x y) :
    f x - f xStar ≤ (c / δ) ^ (1 / (1 - θ)) * fderiv ℝ f x (a - v) ^ (1 / (1 - θ)) := by
  set C := convexHull ℝ (↑V : Set E) with hCdef
  set g := fderiv ℝ f x with hg
  set w := g (a - v) with hw
  have hxC : x ∈ C := convexHull_mono (by exact_mod_cast hSV) hx
  have h1θ : 0 < 1 - θ := by linarith [hθ.2]
  have hw0 : 0 ≤ w := by
    have h1 := apply_le_of_mem_convexHull g haS hx
    have h2 := Proof.le_of_min_vertex g hvV hxC
    rw [hw, map_sub]; linarith
  set h := f x - f xStar with hh
  have hh0 : 0 ≤ h := sub_nonneg.mpr (hxs.2 x hxC)
  have hR : 0 ≤ (c / δ) ^ (1 / (1 - θ)) * w ^ (1 / (1 - θ)) := by positivity
  rcases eq_or_lt_of_le hh0 with hz | hpos
  · rw [← hz]; exact hR
  -- `δ h ≤ w (c h^θ + ε)` for every `ε > 0`
  have hkey : ∀ ε > 0, δ * h ≤ w * (c * h ^ θ + ε) := by
    intro ε hε
    obtain ⟨y, hy, hyd⟩ := (Metric.infDist_lt_iff ⟨xStar, hxs⟩).mp
      (lt_of_le_of_lt (heb x hxC xStar hxs) (lt_add_of_pos_right _ hε))
    have hfy : f y = f xStar := le_antisymm (hy.2 xStar hxs.1) (hxs.2 y hy.1)
    have hcv := Lemmata.FrankWolfe.convexOn_add_fderiv_le hconv hxC (hdiff x hxC) hy.1
    have hsc' := hsc S hSV x hx y hy.1 g a ha haS v hv hvV
    have h1 : h ≤ g (x - y) := by
      rw [hh, ← hfy, map_sub]
      have : g (y - x) = g y - g x := map_sub _ _ _
      linarith
    have h2 : ‖x - y‖ ≤ c * h ^ θ + ε := by rw [← dist_eq_norm]; exact hyd.le
    calc δ * h ≤ δ * g (x - y) := mul_le_mul_of_nonneg_left h1 hδ.le
      _ ≤ w * ‖x - y‖ := hsc'
      _ ≤ w * (c * h ^ θ + ε) := mul_le_mul_of_nonneg_left h2 hw0
  have hle : δ * h ≤ w * (c * h ^ θ) := by
    by_contra hlt
    push Not at hlt
    have := hkey ((δ * h - w * (c * h ^ θ)) / (2 * (w + 1))) (div_pos (by linarith) (by positivity))
    have e : w * ((δ * h - w * (c * h ^ θ)) / (2 * (w + 1))) ≤ (δ * h - w * (c * h ^ θ)) / 2 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    nlinarith
  have hθpos : 0 < h ^ θ := Real.rpow_pos_of_pos hpos θ
  have h2 : h ^ (1 - θ) ≤ c / δ * w := by
    rw [Real.rpow_sub hpos, Real.rpow_one, div_le_iff₀ hθpos]
    have e : c / δ * w * h ^ θ = w * (c * h ^ θ) / δ := by field_simp
    rw [e, le_div_iff₀ hδ]
    linarith
  have h3 := Real.rpow_le_rpow (Real.rpow_nonneg hh0 _) h2 (by positivity : 0 ≤ 1 / (1 - θ))
  rwa [← Real.rpow_mul hh0, mul_one_div_cancel h1θ.ne', Real.rpow_one,
    Real.mul_rpow (by positivity) hw0] at h3

namespace Proof

theorem strong_wolfe_gap : StrongWolfeGap.{u} := by
  intro E _ _ V S f lam x a v hSV hpos hsum hx hconv hdiff ha haS hv hvV
  exact strong_wolfe_gap_bound hSV hpos hsum hx hconv hdiff ha haS hv hvV

theorem heb_strong_wolfe_bound : HEBStrongWolfeBound.{u} := by
  intro E _ _ V S f c θ δ x a v xStar hconv hdiff heb hc hθ hδ hsc hxs hSV hx ha haS hv hvV
  exact heb_strong_wolfe hconv hdiff heb hc hθ hδ hsc hxs hSV hx ha haS hv hvV

theorem strongly_convex_set_rate : StronglyConvexSetRate.{u} := by
  intro E _ _ C f L α c θ x v γ hCc hC hUC hα hL hD hconv hsm heb hc hθ hrun xStar hxs K t₀ t ht
  have h := Lemmata.FWUniformlyConvex.Proof.heb_rate C f L α 2 c θ x v γ hCc hC hUC le_rfl hα hL
    hD hconv hsm heb hc hθ hrun xStar hxs t ht
  have e1 : (1 : ℝ) - 2 * θ / 2 = 1 - θ := by ring
  have e2 : (2 : ℝ) / 2 = 1 := by norm_num
  simp only [e1, e2, Real.rpow_one] at h
  exact h

end Proof

end Lemmata.FWRestart
