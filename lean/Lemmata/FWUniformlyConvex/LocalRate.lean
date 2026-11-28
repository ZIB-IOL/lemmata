module

public import Lemmata.FWUniformlyConvex.Heb

@[expose] public section

/-!
# Rates under the local scaling inequality (Lemma 2.7, Theorem 2.5)

The local scaling inequality at `x⋆`, with `‖f'(x⋆)‖ ≥ c`, gives
`(cα/2) ‖x⋆ - y‖^q ≤ f'(x⋆)(y - x⋆)` on `C`. Applied at `x` with convexity, it bounds `‖x - x⋆‖`
by a power of the primal gap; applied at the Frank–Wolfe vertex `v` with the optimality of `v` and
the Lipschitz derivative, it bounds `‖v - x⋆‖` by a power of `‖x - x⋆‖`. Together,
`‖x - v‖ ≤ H h^{1/(q(q-1))}` once `h ≤ 1`, which is a scaling inequality
`H^{-q(q-1)} ‖x - v‖^{q(q-1)} ≤ h ≤ g` with exponent `q(q-1)`; the progress estimate and the
contraction lemma of the basics entry then give the rates.
-/

namespace Lemmata.FWUniformlyConvex

open Lemmata.FrankWolfe Lemmata.CGBasics

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Lemma 2.7.** -/
theorem fw_vertex_distance_bound {C : Set E} {f : E → ℝ} {L c α q : ℝ} {xStar x v : E}
    (hconv : ConvexOn ℝ C f) (hdiff : ∀ y ∈ C, DifferentiableAt ℝ f y) (hL : 0 ≤ L)
    (hlip : ∀ y ∈ C, ∀ z ∈ C, ‖fderiv ℝ f y - fderiv ℝ f z‖ ≤ L * ‖y - z‖) (hc : 0 < c)
    (hgrad : ∀ y ∈ C, c ≤ ‖fderiv ℝ f y‖) (hα : 0 < α) (hq : 2 ≤ q) (hxs : xStar ∈ C)
    (hls : IsLocalScaling C f α q xStar) (hx : x ∈ C) (hh1 : f x - f xStar ≤ 1) (hv : v ∈ C)
    (hvmin : ∀ y ∈ C, fderiv ℝ f x v ≤ fderiv ℝ f x y) :
    ‖x - v‖ ≤ 2 * max ((2 * L / (c * α)) ^ (1 / (q - 1)) * (2 / (c * α)) ^ (1 / (q * (q - 1))))
      ((2 / (c * α)) ^ (1 / q)) * (f x - f xStar) ^ (1 / (q * (q - 1))) := by
  set h := f x - f xStar with hh
  set κ := c * α / 2 with hκdef
  have hκ : 0 < κ := by positivity
  have hq0 : 0 < q := by linarith
  have hq1 : 0 < q - 1 := by linarith
  -- the local scaling inequality with the gradient bound
  have hls' : ∀ y ∈ C, κ * ‖xStar - y‖ ^ q ≤ fderiv ℝ f xStar (y - xStar) := by
    intro y hy
    have h1 := hls y hy
    have hg := hgrad xStar hxs
    have hn : 0 ≤ ‖xStar - y‖ ^ q := Real.rpow_nonneg (norm_nonneg _) q
    calc κ * ‖xStar - y‖ ^ q = α / 2 * c * ‖xStar - y‖ ^ q := by rw [hκdef]; ring
      _ ≤ α / 2 * ‖fderiv ℝ f xStar‖ * ‖xStar - y‖ ^ q := by gcongr
      _ ≤ _ := h1
  -- `κ ‖x - x⋆‖^q ≤ h`
  have hconvx := Lemmata.FrankWolfe.convexOn_add_fderiv_le hconv hxs (hdiff _ hxs) hx
  have hd1q : κ * ‖x - xStar‖ ^ q ≤ h := by
    have := hls' x hx
    rw [norm_sub_rev] at this
    linarith
  have hh0 : 0 ≤ h := le_trans (by positivity) hd1q
  -- `κ ‖v - x⋆‖^q ≤ L ‖x - x⋆‖ ‖v - x⋆‖`
  have hd2q : κ * ‖v - xStar‖ ^ q ≤ L * ‖x - xStar‖ * ‖v - xStar‖ := by
    have h1 := hls' v hv
    rw [norm_sub_rev] at h1
    have hfw : fderiv ℝ f x (v - xStar) ≤ 0 := by rw [map_sub]; linarith [hvmin xStar hxs]
    have h2 : (fderiv ℝ f xStar - fderiv ℝ f x) (v - xStar) ≤
        ‖fderiv ℝ f xStar - fderiv ℝ f x‖ * ‖v - xStar‖ :=
      (le_abs_self _).trans (by rw [← Real.norm_eq_abs]; exact ContinuousLinearMap.le_opNorm _ _)
    have h3 : ‖fderiv ℝ f xStar - fderiv ℝ f x‖ ≤ L * ‖x - xStar‖ := by
      rw [norm_sub_rev x xStar]; exact hlip _ hxs _ hx
    have h4 : (fderiv ℝ f xStar - fderiv ℝ f x) (v - xStar) =
        fderiv ℝ f xStar (v - xStar) - fderiv ℝ f x (v - xStar) := by
      simp only [sub_apply]
    calc κ * ‖v - xStar‖ ^ q ≤ fderiv ℝ f xStar (v - xStar) := h1
      _ ≤ (fderiv ℝ f xStar - fderiv ℝ f x) (v - xStar) := by rw [h4]; linarith
      _ ≤ ‖fderiv ℝ f xStar - fderiv ℝ f x‖ * ‖v - xStar‖ := h2
      _ ≤ L * ‖x - xStar‖ * ‖v - xStar‖ := mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
  set e := 1 / (q * (q - 1)) with he
  have he0 : 0 < e := by positivity
  set A := 2 / (c * α) with hA
  set B := 2 * L / (c * α) with hB
  have hA0 : 0 < A := by positivity
  have hB0 : 0 ≤ B := by positivity
  have hκA : 1 / κ = A := by rw [hκdef, hA]; field_simp
  -- `‖x - x⋆‖ ≤ A^{1/q} h^{1/q}`
  have hd1 : ‖x - xStar‖ ≤ A ^ (1 / q) * h ^ (1 / q) := by
    have h1 : ‖x - xStar‖ ^ q ≤ A * h := by
      rw [← hκA, one_div, ← div_eq_inv_mul, le_div_iff₀ hκ]; linarith
    have h2 := Real.rpow_le_rpow (Real.rpow_nonneg (norm_nonneg _) q) h1
      (by positivity : 0 ≤ 1 / q)
    rwa [← Real.rpow_mul (norm_nonneg _), mul_one_div_cancel hq0.ne', Real.rpow_one,
      Real.mul_rpow hA0.le hh0] at h2
  -- `‖v - x⋆‖ ≤ B^{1/(q-1)} ‖x - x⋆‖^{1/(q-1)}`
  have hd2 : ‖v - xStar‖ ≤ B ^ (1 / (q - 1)) * ‖x - xStar‖ ^ (1 / (q - 1)) := by
    rcases eq_or_lt_of_le (norm_nonneg (v - xStar)) with h0 | hpos
    · rw [← h0]; positivity
    have hsplit : ‖v - xStar‖ ^ q = ‖v - xStar‖ ^ (q - 1) * ‖v - xStar‖ := by
      rw [← Real.rpow_add_one hpos.ne']; congr 1; ring
    have h1 : ‖v - xStar‖ ^ (q - 1) ≤ B * ‖x - xStar‖ := by
      rw [hsplit] at hd2q
      have h2 : κ * ‖v - xStar‖ ^ (q - 1) ≤ L * ‖x - xStar‖ :=
        le_of_mul_le_mul_right (by linarith) hpos
      rw [hB, show 2 * L / (c * α) = L / κ by rw [hκdef]; field_simp, div_mul_eq_mul_div,
        le_div_iff₀ hκ]
      linarith
    have h2 := Real.rpow_le_rpow (Real.rpow_nonneg (norm_nonneg _) _) h1
      (by positivity : 0 ≤ 1 / (q - 1))
    rwa [← Real.rpow_mul (norm_nonneg _), mul_one_div_cancel hq1.ne', Real.rpow_one,
      Real.mul_rpow hB0 (norm_nonneg _)] at h2
  -- `‖x - x⋆‖^{1/(q-1)} ≤ A^e h^e`
  have hd1e : ‖x - xStar‖ ^ (1 / (q - 1)) ≤ A ^ e * h ^ e := by
    have h1 := Real.rpow_le_rpow (norm_nonneg _) hd1 (by positivity : 0 ≤ 1 / (q - 1))
    rw [Real.mul_rpow (Real.rpow_nonneg hA0.le _) (Real.rpow_nonneg hh0 _),
      ← Real.rpow_mul hA0.le, ← Real.rpow_mul hh0] at h1
    have e1 : 1 / q * (1 / (q - 1)) = e := by rw [he]; field_simp
    rwa [e1] at h1
  -- `h^{1/q} ≤ h^e` since `h ≤ 1`
  have hpow : h ^ (1 / q) ≤ h ^ e := by
    rcases eq_or_lt_of_le hh0 with h0 | hpos
    · rw [← h0, Real.zero_rpow (by positivity), Real.zero_rpow he0.ne']
    · apply Real.rpow_le_rpow_of_exponent_ge hpos hh1
      rw [he, div_le_div_iff₀ (by positivity) hq0]
      nlinarith
  have hfin : ‖x - v‖ ≤ (A ^ (1 / q) + B ^ (1 / (q - 1)) * A ^ e) * h ^ e := by
    calc ‖x - v‖ ≤ ‖x - xStar‖ + ‖v - xStar‖ := by
          rw [show x - v = (x - xStar) - (v - xStar) by abel]; exact norm_sub_le _ _
      _ ≤ A ^ (1 / q) * h ^ (1 / q) + B ^ (1 / (q - 1)) * (A ^ e * h ^ e) := by
          exact add_le_add hd1 (hd2.trans (mul_le_mul_of_nonneg_left hd1e (by positivity)))
      _ ≤ A ^ (1 / q) * h ^ e + B ^ (1 / (q - 1)) * (A ^ e * h ^ e) := by
          gcongr
      _ = (A ^ (1 / q) + B ^ (1 / (q - 1)) * A ^ e) * h ^ e := by ring
  refine hfin.trans (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hh0 _))
  have h1 := le_max_left (B ^ (1 / (q - 1)) * A ^ e) (A ^ (1 / q))
  have h2 := le_max_right (B ^ (1 / (q - 1)) * A ^ e) (A ^ (1 / q))
  linarith

set_option maxHeartbeats 1000000 in
/-- **Theorem 2.5**, corrected. -/
theorem local_scaling_rate_bound {C : Set E} {f : E → ℝ} {L : NNReal} {c α q : ℝ} {x v : ℕ → E}
    {γ : ℕ → ℝ} {xStar : E} {S : ℕ} (hC : Convex ℝ C) (hL : 0 < (L : ℝ))
    (hconv : ConvexOn ℝ Set.univ f) (hsm : IsSmooth f L) (hc : 0 < c)
    (hgrad : ∀ y ∈ C, c ≤ ‖fderiv ℝ f y‖) (hα : 0 < α) (hq : 2 ≤ q)
    (hxs : xStar ∈ minimizers C f) (hls : IsLocalScaling C f α q xStar)
    (hrun : IsShortStepRun C f L x v γ) (hS : f (x S) - f xStar ≤ 1) :
    let H := 2 * max ((2 * L / (c * α)) ^ (1 / (q - 1)) * (2 / (c * α)) ^ (1 / (q * (q - 1))))
      ((2 / (c * α)) ^ (1 / q))
    let a := 1 - 2 / (q * (q - 1))
    (∀ t : ℕ, S ≤ t → f (x (t + 1)) - f xStar ≤
      (f (x t) - f xStar) * max (1 / 2) (1 - (f (x t) - f xStar) ^ a / (2 * L * H ^ 2))) ∧
    (q = 2 → ∀ t : ℕ, S ≤ t → f (x t) - f xStar ≤
      max (1 / 2) (1 - 1 / (2 * L * H ^ 2)) ^ (t - S) * (f (x S) - f xStar)) ∧
    (2 < q →
      let K := ((L : ℝ) * H ^ 2) ^ (1 / a)
      let t₀ : ℤ := max (⌊Real.logb (1 / 2) K⌋ + 2) 1
      ∀ T : ℕ, 1 ≤ T →
        ((T : ℤ) < t₀ → f (x (S + T - 1)) - f xStar ≤ (1 / 2) ^ (T - 1)) ∧
        (t₀ ≤ (T : ℤ) → f (x (S + T - 1)) - f xStar ≤
          K / (1 + a / 2 * ((T : ℝ) - t₀)) ^ (1 / a))) := by
  intro H a
  have hq0 : 0 < q := by linarith
  have hq1 : 0 < q - 1 := by linarith
  set h : ℕ → ℝ := fun τ => f (x τ) - f xStar with hh
  have hfacts := Lemmata.CGBasics.Proof.run_step hC hconv hsm hrun hxs
  have h0 : ∀ τ, 0 ≤ h τ := fun τ => by simp only [hh]; linarith [hxs.2 _ (hfacts τ).1]
  have hmono : ∀ τ, h (τ + 1) ≤ h τ := fun τ => by
    have := (hfacts τ).2.2.2 0 ⟨le_rfl, zero_le_one⟩
    simp only [hh]; simp at this; linarith
  have hanti : ∀ τ, S ≤ τ → h τ ≤ h S := by
    intro τ hτ
    induction τ, hτ using Nat.le_induction with
    | base => exact le_rfl
    | succ τ _ ih => exact (hmono τ).trans ih
  have hconvC : ConvexOn ℝ C f := hconv.subset (Set.subset_univ C) hC
  have hdiffC : ∀ y ∈ C, DifferentiableAt ℝ f y := fun y _ => hsm.1 y
  have hlipC : ∀ y ∈ C, ∀ z ∈ C, ‖fderiv ℝ f y - fderiv ℝ f z‖ ≤ L * ‖y - z‖ := by
    intro y _ z _
    rw [← dist_eq_norm, ← dist_eq_norm]
    exact hsm.2.dist_le_mul y z
  have hHpos : 0 < H := by
    have : 0 < (2 / (c * α)) ^ (1 / q) := by positivity
    have := le_max_right ((2 * L / (c * α)) ^ (1 / (q - 1)) * (2 / (c * α)) ^ (1 / (q * (q - 1))))
      ((2 / (c * α)) ^ (1 / q))
    show 0 < 2 * max _ _
    linarith
  set Q := q * (q - 1) with hQ
  have hQpos : 0 < Q := by positivity
  have hQ2 : 2 ≤ Q := by rw [hQ]; nlinarith
  have ha : a = 1 - 2 / Q := rfl
  -- the progress of each step from `S` on
  have hprog : ∀ τ, S ≤ τ → h τ * min (1 / 2) (h τ ^ a / (2 * L * H ^ 2)) ≤ h τ - h (τ + 1) := by
    intro τ hτ
    obtain ⟨hxC, hhg, -, hs⟩ := hfacts τ
    obtain ⟨hvC, hvmin, -, -⟩ := hrun.2 τ
    have hh1 : h τ ≤ 1 := (hanti τ hτ).trans hS
    have hdist : ‖x τ - v τ‖ ≤ H * h τ ^ (1 / Q) :=
      fw_vertex_distance_bound hconvC hdiffC (NNReal.coe_nonneg L) hlipC hc hgrad hα hq hxs.1
        hls hxC hh1 hvC hvmin
    set β := H ^ (-Q) with hβdef
    have hβ : 0 < β := by positivity
    have hscal : β * ‖v τ - x τ‖ ^ Q ≤ fderiv ℝ f (x τ) (x τ - v τ) := by
      rw [norm_sub_rev]
      have h1 : ‖x τ - v τ‖ ^ Q ≤ (H * h τ ^ (1 / Q)) ^ Q :=
        Real.rpow_le_rpow (norm_nonneg _) hdist hQpos.le
      rw [Real.mul_rpow hHpos.le (Real.rpow_nonneg (h0 τ) _), ← Real.rpow_mul (h0 τ),
        one_div_mul_cancel hQpos.ne', Real.rpow_one] at h1
      calc β * ‖x τ - v τ‖ ^ Q ≤ β * (H ^ Q * h τ) := mul_le_mul_of_nonneg_left h1 hβ.le
        _ = h τ := by
          rw [hβdef, ← mul_assoc, ← Real.rpow_add hHpos, neg_add_cancel, Real.rpow_zero, one_mul]
        _ ≤ _ := hhg
    have hp := Lemmata.CGBasics.Proof.uc_progress hL hQ2 hβ hhg (h0 τ) (norm_nonneg _) hscal hs
    have e1 : β ^ (2 / Q) = (H ^ 2)⁻¹ := by
      rw [hβdef, ← Real.rpow_mul hHpos.le, show -Q * (2 / Q) = -2 by field_simp,
        Real.rpow_neg hHpos.le]
      norm_cast
    have e2 : β ^ (2 / Q) * h τ ^ (1 - 2 / Q) / (2 * L) = h τ ^ a / (2 * L * H ^ 2) := by
      rw [e1, ← ha]; field_simp
    rw [e2] at hp
    simp only [hh]
    linarith
  have hmaxmin : ∀ X : ℝ, 1 - min (1 / 2) X = max (1 / 2) (1 - X) := by
    intro X
    rcases le_total (1 / 2 : ℝ) X with hX | hX
    · rw [min_eq_left hX, max_eq_left (by linarith)]; norm_num
    · rw [min_eq_right hX, max_eq_right (by linarith)]
  have hrec : ∀ t : ℕ, S ≤ t → h (t + 1) ≤ h t * max (1 / 2) (1 - h t ^ a / (2 * L * H ^ 2)) := by
    intro t ht
    have := hprog t ht
    rw [← hmaxmin, mul_sub, mul_one]
    linarith
  refine ⟨hrec, fun hq2 => ?_, fun hq2 => ?_⟩
  · -- `q = 2`: linear convergence
    have ha0 : a = 0 := by rw [ha, hQ, hq2]; norm_num
    set ρ := max (1 / 2) (1 - 1 / (2 * (L : ℝ) * H ^ 2)) with hρ
    have hρ0 : 0 ≤ ρ := le_trans (by norm_num) (le_max_left _ _)
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => simp
    | succ t ht ih =>
      have h1 := hrec t ht
      rw [ha0] at h1
      simp only [Real.rpow_zero] at h1
      rw [show t + 1 - S = (t - S) + 1 by omega, pow_succ]
      calc h (t + 1) ≤ h t * ρ := h1
        _ ≤ ρ ^ (t - S) * h S * ρ := mul_le_mul_of_nonneg_right ih hρ0
        _ = ρ ^ (t - S) * ρ * h S := by ring
  · -- `q > 2`: the contraction lemma on the shifted sequence
    intro K t₀ T hT
    have hapos : 0 < a := by
      rw [ha]
      have : 2 / Q < 1 := by rw [div_lt_one hQpos, hQ]; nlinarith
      linarith
    set c₂ := 1 / (2 * (L : ℝ) * H ^ 2) with hc₂
    have hc₂pos : 0 < c₂ := by positivity
    set h' : ℕ → ℝ := fun τ => h (S + τ - 1) with hh'
    have h0' : ∀ τ, 0 ≤ h' τ := fun τ => h0 _
    have hmono' : ∀ τ, h' (τ + 1) ≤ h' τ := by
      intro τ
      simp only [hh']
      rcases Nat.eq_zero_or_pos (S + τ) with h00 | hpos
      · have : S + (τ + 1) - 1 = S + τ - 1 := by omega
        rw [this]
      · rw [show S + (τ + 1) - 1 = (S + τ - 1) + 1 by omega]; exact hmono _
    have h1' : h' 1 ≤ 1 := by simp only [hh']; rw [show S + 1 - 1 = S by omega]; exact hS
    have hstep' : ∀ τ, 1 ≤ τ → 0 < h' τ →
        h' τ * min (1 / 2) (c₂ * h' τ ^ a) ≤ h' τ - h' (τ + 1) := by
      intro τ hτ _
      have := hprog (S + τ - 1) (by omega)
      simp only [hh']
      rw [show S + (τ + 1) - 1 = (S + τ - 1) + 1 by omega]
      rw [show c₂ * h (S + τ - 1) ^ a = h (S + τ - 1) ^ a / (2 * L * H ^ 2) by rw [hc₂]; ring]
      exact this
    have hra := Lemmata.CGBasics.Proof.rate_assembly h' 1 c₂ a one_pos hc₂pos hapos h0' hmono'
      h1' hstep' T hT
    have eK : (1 / 2 / c₂) ^ (1 / a) = K := by
      show _ = ((L : ℝ) * H ^ 2) ^ (1 / a)
      congr 1
      rw [hc₂]; field_simp
    have e1 : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
    have ea : 1 / 2 * a = a / 2 := by ring
    simp only [e1, one_mul, div_one] at hra
    rw [eK, ea] at hra
    exact hra

namespace Proof

theorem fw_vertex_distance : FWVertexDistance.{u} := by
  intro E _ _ C f L c α q xStar x v hconv hdiff hL hlip hc hgrad hα hq hxs hls hx hh1 hv hvmin
  exact fw_vertex_distance_bound hconv hdiff hL hlip hc hgrad hα hq hxs hls hx hh1 hv hvmin

theorem local_scaling_rate : LocalScalingRate.{u} := by
  intro E _ _ C f L c α q x v γ xStar S _ hC hL hconv hsm hc hgrad hα hq hxs hls hrun hS
  exact local_scaling_rate_bound hC hL hconv hsm hc hgrad hα hq hxs hls hrun hS

end Proof

end Lemmata.FWUniformlyConvex
