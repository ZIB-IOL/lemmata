module

public import Lemmata.FWOpenLoop.Sequence
public import Lemmata.FrankWolfe.Proof.Run

@[expose] public section

/-!
# The baseline rate and minimizers in the relative interior

Proposition 3.1, Lemmas 3.2–3.4 and Theorem 3.6.

One step of a run gives `h_{t+1} ≤ h_t - η_t g_t + η_t² L/2 ‖v_t - x_t‖²` with the Frank–Wolfe gap
`g_t ≥ h_t`. With a ball of the affine hull around every minimizer inside `C`, the gap is at
least `(β/μ) h_t^{1-θ}` at every point, so Lemma 3.5 applies from every `S ≥ 1`.
-/

namespace Lemmata.FWOpenLoop

open Lemmata.FrankWolfe

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- One step of a run: the progress bound, primal gap ≤ Frank–Wolfe gap, and `‖v - x‖ ≤ δ`. -/
theorem basic_step {C : Set E} {f : E → ℝ} {L : ℝ} {x v : ℕ → E} {γ : ℕ → ℝ} {xStar : E}
    (hC : IsCompact C) (hconv : ConvexOn ℝ C f) (hdiff : ∀ y ∈ C, DifferentiableAt ℝ f y)
    (hsm : IsSmoothOn C f L) (hrun : IsFWRun C (fderiv ℝ f) x v γ)
    (hxs : xStar ∈ minimizers C f) (t : ℕ) :
    f (x (t + 1)) - f xStar ≤ (f (x t) - f xStar) - γ t * fderiv ℝ f (x t) (x t - v t) +
        γ t ^ 2 * L / 2 * ‖v t - x t‖ ^ 2 ∧
      f (x t) - f xStar ≤ fderiv ℝ f (x t) (x t - v t) ∧
      ‖v t - x t‖ ≤ Metric.diam C ∧ x t ∈ C ∧ v t ∈ C := by
  have hxC : x t ∈ C := Lemmata.FrankWolfe.Proof.fw_run_mem C _ x v γ hconv.1 hrun t
  obtain ⟨hvC, hvmin, -, -⟩ := hrun.2 t
  refine ⟨?_, ?_, ?_, hxC, hvC⟩
  · have := Lemmata.FrankWolfe.Proof.run_progress C f L x v γ hconv.1 hsm hrun t
    linarith
  · have h1 := convexOn_add_fderiv_le hconv hxC (hdiff _ hxC) hxs.1
    have h2 := hvmin xStar hxs.1
    have e1 : fderiv ℝ f (x t) (xStar - x t) = fderiv ℝ f (x t) xStar - fderiv ℝ f (x t) (x t) :=
      map_sub _ _ _
    have e2 : fderiv ℝ f (x t) (x t - v t) = fderiv ℝ f (x t) (x t) - fderiv ℝ f (x t) (v t) :=
      map_sub _ _ _
    linarith
  · rw [← dist_eq_norm]
    exact Metric.dist_le_diam_of_mem hC.isBounded hvC hxC

theorem eta4_nat (t : ℕ) : eta 4 (t : ℤ) = 4 / ((t : ℝ) + 4) := by
  simp [eta]

/-- **Proposition 3.1.** -/
theorem baseline_bound {C : Set E} {f : E → ℝ} {L : ℝ} {x v : ℕ → E}
    (hC : IsCompact C) (hconv : ConvexOn ℝ C f) (hdiff : ∀ y ∈ C, DifferentiableAt ℝ f y)
    (hsm : IsSmoothOn C f L) (hL : 0 ≤ L) (hrun : IsFWRun C (fderiv ℝ f) x v (fun t => eta 4 t))
    {xStar : E} (hxs : xStar ∈ minimizers C f) :
    ∀ t : ℕ, 1 ≤ t → f (x t) - f xStar ≤ 8 * L * Metric.diam C ^ 2 / (t + 3) := by
  set δ := Metric.diam C with hδ
  have hδ0 : 0 ≤ δ := Metric.diam_nonneg
  have hK : 0 ≤ L * δ ^ 2 := by positivity
  -- the recursion `h_{t+1} ≤ (1 - η_t) h_t + η_t² L δ² / 2`
  have hrec : ∀ t : ℕ, f (x (t + 1)) - f xStar ≤
      (1 - eta 4 t) * (f (x t) - f xStar) + eta 4 t ^ 2 * (L * δ ^ 2) / 2 := by
    intro t
    obtain ⟨h1, h2, h3, -, -⟩ := basic_step hC hconv hdiff hsm hrun hxs t
    obtain ⟨-, -, hγ, -⟩ := hrun.2 t
    have hγ0 : 0 ≤ eta 4 t := hγ.1
    have hsq : ‖v t - x t‖ ^ 2 ≤ δ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h3 2
    have : eta 4 t ^ 2 * L / 2 * ‖v t - x t‖ ^ 2 ≤ eta 4 t ^ 2 * (L * δ ^ 2) / 2 := by
      have := mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ eta 4 t ^ 2 * L / 2)
      linarith
    nlinarith
  intro t ht
  induction t, ht using Nat.le_induction with
  | base =>
    have h := hrec 0
    have h0 : eta 4 ((0 : ℕ) : ℤ) = 1 := by simp [eta]
    rw [h0] at h
    push_cast at h ⊢
    nlinarith
  | succ t ht ih =>
    have h := hrec t
    rw [eta4_nat] at h
    have ht0 : (1 : ℝ) ≤ t := by exact_mod_cast ht
    have hcoef : 0 ≤ 1 - 4 / ((t : ℝ) + 4) := by
      rw [sub_nonneg, div_le_one (by positivity)]; linarith
    have h2 := mul_le_mul_of_nonneg_left ih hcoef
    push_cast
    have key : (1 - 4 / ((t : ℝ) + 4)) * (8 * L * δ ^ 2 / (t + 3)) +
        (4 / ((t : ℝ) + 4)) ^ 2 * (L * δ ^ 2) / 2 ≤ 8 * L * δ ^ 2 / ((t : ℝ) + 1 + 3) := by
      have ht4 : (0 : ℝ) < t + 4 := by positivity
      have ht3 : (0 : ℝ) < t + 3 := by positivity
      have e1 : (1 - 4 / ((t : ℝ) + 4)) * (8 * L * δ ^ 2 / (t + 3)) =
          8 * (L * δ ^ 2) * t / ((t + 4) * (t + 3)) := by
        field_simp; ring
      have e2 : (4 / ((t : ℝ) + 4)) ^ 2 * (L * δ ^ 2) / 2 = 8 * (L * δ ^ 2) / (t + 4) ^ 2 := by
        field_simp; ring
      have e3 : 8 * L * δ ^ 2 / ((t : ℝ) + 1 + 3) = 8 * (L * δ ^ 2) / (t + 4) := by
        rw [show (t : ℝ) + 1 + 3 = t + 4 by ring]; ring
      rw [e1, e2, e3]
      have key0 : (t : ℝ) / ((t + 4) * (t + 3)) + 1 / (t + 4) ^ 2 ≤ 1 / (t + 4) := by
        rw [div_add_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) ht4]
        have ht0' : (0 : ℝ) ≤ t := by positivity
        nlinarith [mul_nonneg ht0' (sq_nonneg ((t : ℝ) + 4)), sq_nonneg ((t : ℝ) + 4),
          mul_nonneg (mul_nonneg ht0' ht0') ht0']
      have := mul_le_mul_of_nonneg_left key0 (by positivity : (0 : ℝ) ≤ 8 * (L * δ ^ 2))
      have r1 : 8 * (L * δ ^ 2) * ((t : ℝ) / ((t + 4) * (t + 3)) + 1 / (t + 4) ^ 2) =
          8 * (L * δ ^ 2) * t / ((t + 4) * (t + 3)) + 8 * (L * δ ^ 2) / (t + 4) ^ 2 := by ring
      have r2 : 8 * (L * δ ^ 2) * (1 / ((t : ℝ) + 4)) = 8 * (L * δ ^ 2) / (t + 4) := by ring
      rw [r1, r2] at this
      linarith
    linarith

/-- **Lemma 3.2**, corrected: the gradient is tested only against directions `u` of `aff(C)`. -/
theorem gm_scaling_bound {C : Set E} {f : E → ℝ} {β : ℝ} {xStar : E}
    (hC : IsCompact C) (hconv : ConvexOn ℝ C f) (hdiff : ∀ y ∈ C, DifferentiableAt ℝ f y)
    (hxs : xStar ∈ minimizers C f) (hβ : 0 < β)
    (hball : ∀ y ∈ affineSpan ℝ C, ‖y - xStar‖ ≤ β → y ∈ C)
    {x : E} (hx : x ∈ C) {p : E} (hp : p ∈ C) (hpmin : ∀ y ∈ C, fderiv ℝ f x p ≤ fderiv ℝ f x y)
    {u : E} (hu : u ∈ vectorSpan ℝ C) (hu1 : ‖u‖ ≤ 1) :
    β * ‖x - p‖ * fderiv ℝ f x u ≤ Metric.diam C * fderiv ℝ f x (x - p) := by
  have hmem : xStar - β • u ∈ C := by
    apply hball
    · have : xStar - β • u = (-(β • u)) +ᵥ xStar := by rw [vadd_eq_add]; abel
      rw [this]
      apply AffineSubspace.vadd_mem_of_mem_direction
      · rw [direction_affineSpan]; exact Submodule.neg_mem _ (Submodule.smul_mem _ _ hu)
      · exact subset_affineSpan ℝ C hxs.1
    · rw [sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hβ]
      calc β * ‖u‖ ≤ β * 1 := mul_le_mul_of_nonneg_left hu1 hβ.le
        _ = β := mul_one β
  have h1 := hpmin _ hmem
  have h2 := convexOn_add_fderiv_le hconv hx (hdiff x hx) hxs.1
  have h3 := hxs.2 x hx
  have hlin1 : fderiv ℝ f x (xStar - β • u) = fderiv ℝ f x xStar - β * fderiv ℝ f x u := by
    rw [map_sub, map_smul, smul_eq_mul]
  have hlin2 : fderiv ℝ f x (xStar - x) = fderiv ℝ f x xStar - fderiv ℝ f x x := map_sub _ _ _
  have hlin3 : fderiv ℝ f x (x - p) = fderiv ℝ f x x - fderiv ℝ f x p := map_sub _ _ _
  have hcore : β * fderiv ℝ f x u ≤ fderiv ℝ f x (x - p) := by linarith
  have hgap : 0 ≤ fderiv ℝ f x (x - p) := by have := hpmin x hx; linarith
  have hd : ‖x - p‖ ≤ Metric.diam C := by
    rw [← dist_eq_norm]; exact Metric.dist_le_diam_of_mem hC.isBounded hx hp
  by_cases hu0 : fderiv ℝ f x u ≤ 0
  · have : β * ‖x - p‖ * fderiv ℝ f x u ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hu0
    have : 0 ≤ Metric.diam C * fderiv ℝ f x (x - p) := mul_nonneg Metric.diam_nonneg hgap
    linarith
  · replace hu0 := lt_of_not_ge hu0
    calc β * ‖x - p‖ * fderiv ℝ f x u = ‖x - p‖ * (β * fderiv ℝ f x u) := by ring
      _ ≤ Metric.diam C * (β * fderiv ℝ f x u) := mul_le_mul_of_nonneg_right hd (by positivity)
      _ ≤ Metric.diam C * fderiv ℝ f x (x - p) :=
          mul_le_mul_of_nonneg_left hcore Metric.diam_nonneg

/-- The interior scaling used for Theorem 3.6: at every `x ∈ C`, `(β/μ) h^{1-θ} ≤ f'(x)(x - p)`. -/
theorem interior_gap {C : Set E} {f : E → ℝ} {μ θ β : ℝ}
    (hC : IsCompact C) (hconv : ConvexOn ℝ C f) (hdiff : ∀ y ∈ C, DifferentiableAt ℝ f y)
    (heb : IsHolderErrorBound C f μ θ) (hμ : 0 < μ) (hθ : θ < 1) (hβ : 0 < β)
    (hball : ∀ y ∈ minimizers C f, ∀ z ∈ affineSpan ℝ C, ‖z - y‖ ≤ β → z ∈ C)
    {xStar : E} (hxs : xStar ∈ minimizers C f) {x : E} (hx : x ∈ C) {p : E}
    (hpmin : ∀ y ∈ C, fderiv ℝ f x p ≤ fderiv ℝ f x y) :
    β / μ * (f x - f xStar) ^ (1 - θ) ≤ fderiv ℝ f x (x - p) := by
  have hgap : 0 ≤ fderiv ℝ f x (x - p) := by
    have := hpmin x hx; rw [map_sub]; linarith
  rcases (hxs.2 x hx).eq_or_lt with heq | hlt
  · rw [heq, sub_self, Real.zero_rpow (by linarith), mul_zero]; exact hgap
  obtain ⟨y, hyM, hxy, -, hmain, -⟩ :=
    Lemmata.FrankWolfe.Proof.heb_scaling C f μ θ hC hconv hdiff heb xStar hxs x hx hlt
  set d := ‖x - y‖ with hd
  have hdpos : 0 < d := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  set u := d⁻¹ • (x - y) with hu
  have hv : x - y ∈ vectorSpan ℝ C := by
    rw [← vsub_eq_sub]; exact vsub_mem_vectorSpan ℝ hx hyM.1
  have hmem : y - β • u ∈ C := by
    apply hball y hyM
    · have : y - β • u = (-(β • u)) +ᵥ y := by rw [vadd_eq_add]; abel
      rw [this]
      apply AffineSubspace.vadd_mem_of_mem_direction
      · rw [direction_affineSpan]
        exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (Submodule.smul_mem _ _ hv))
      · exact subset_affineSpan ℝ C hyM.1
    · rw [sub_sub_cancel_left, norm_neg, norm_smul, hu, norm_smul, norm_inv, norm_norm,
        inv_mul_cancel₀ hdpos.ne', Real.norm_eq_abs, abs_of_pos hβ, mul_one]
  have h1 := hpmin _ hmem
  set F := fderiv ℝ f x (x - y) with hF
  set H := (f x - f xStar) ^ (1 - θ) with hH
  have hH0 : 0 ≤ H := Real.rpow_nonneg (by linarith) _
  have hlin : fderiv ℝ f x (y - β • u) = fderiv ℝ f x y - β * (d⁻¹ * F) := by
    rw [map_sub, map_smul, hu, map_smul, smul_eq_mul, smul_eq_mul]
  have hlin2 : fderiv ℝ f x (x - p) = fderiv ℝ f x x - fderiv ℝ f x p := map_sub _ _ _
  have hlin3 : F = fderiv ℝ f x x - fderiv ℝ f x y := map_sub _ _ _
  have hF0 : 0 ≤ F := by
    have : 0 ≤ H * d := mul_nonneg hH0 hdpos.le
    have := le_trans this hmain
    exact nonneg_of_mul_nonneg_right (by linarith) hμ
  have hstep : β * (d⁻¹ * F) ≤ fderiv ℝ f x (x - p) := by
    have : 0 ≤ F := hF0
    linarith
  have key : β * H ≤ β * (d⁻¹ * F) * μ := by
    have := mul_le_mul_of_nonneg_left hmain (by positivity : 0 ≤ β * d⁻¹)
    calc β * H = β * d⁻¹ * (H * d) := by field_simp
      _ ≤ β * d⁻¹ * (μ * F) := this
      _ = β * (d⁻¹ * F) * μ := by ring
  rw [div_mul_eq_mul_div, div_le_iff₀ hμ]
  nlinarith

/-- A `β`-ball of `aff(C)` around a point of `C` fits in `C`, so `2β ≤ diam C`. -/
theorem two_beta_le_diam {C : Set E} (hC : IsCompact C) {β : ℝ} (hβ : 0 < β) {y : E}
    (hy : y ∈ C) (hball : ∀ z ∈ affineSpan ℝ C, ‖z - y‖ ≤ β → z ∈ C)
    (hdiam : 0 < Metric.diam C) : 2 * β ≤ Metric.diam C := by
  have hnt : C.Nontrivial := by
    by_contra hs
    rw [Set.not_nontrivial_iff] at hs
    rw [Metric.diam_subsingleton hs] at hdiam
    exact lt_irrefl _ hdiam
  obtain ⟨a, ha, b, hb, hab⟩ := hnt
  set d := ‖a - b‖ with hd
  have hdpos : 0 < d := norm_pos_iff.mpr (sub_ne_zero.mpr hab)
  set u := d⁻¹ • (a - b) with hu
  have hun : ‖u‖ = 1 := by
    rw [hu, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hdpos.ne']
  have hv : u ∈ vectorSpan ℝ C := by
    apply Submodule.smul_mem
    rw [← vsub_eq_sub]; exact vsub_mem_vectorSpan ℝ ha hb
  have hyA : y ∈ affineSpan ℝ C := subset_affineSpan ℝ C hy
  have hp : y + β • u ∈ C := by
    apply hball
    · have : y + β • u = (β • u) +ᵥ y := by rw [vadd_eq_add]; abel
      rw [this]
      apply AffineSubspace.vadd_mem_of_mem_direction _ hyA
      rw [direction_affineSpan]; exact Submodule.smul_mem _ _ hv
    · rw [add_sub_cancel_left, norm_smul, hun, Real.norm_eq_abs, abs_of_pos hβ, mul_one]
  have hm : y - β • u ∈ C := by
    apply hball
    · have : y - β • u = (-(β • u)) +ᵥ y := by rw [vadd_eq_add]; abel
      rw [this]
      apply AffineSubspace.vadd_mem_of_mem_direction _ hyA
      rw [direction_affineSpan]; exact Submodule.neg_mem _ (Submodule.smul_mem _ _ hv)
    · rw [sub_sub_cancel_left, norm_neg, norm_smul, hun, Real.norm_eq_abs, abs_of_pos hβ,
        mul_one]
  have hdist := Metric.dist_le_diam_of_mem hC.isBounded hp hm
  rw [dist_eq_norm] at hdist
  have : (y + β • u) - (y - β • u) = (2 * β) • u := by
    rw [mul_smul, two_smul]; abel
  rw [this, norm_smul, hun, Real.norm_eq_abs, abs_of_pos (by positivity), mul_one] at hdist
  exact hdist

/-- **Lemma 3.3.** -/
theorem near_optimum_bound {C : Set E} {f : E → ℝ} {L μ θ β : ℝ} {x v : ℕ → E}
    (hC : IsCompact C) (hconv : ConvexOn ℝ C f) (hdiff : ∀ y ∈ C, DifferentiableAt ℝ f y)
    (hsm : IsSmoothOn C f L) (hL : 0 < L) (hdiam : 0 < Metric.diam C)
    (heb : IsHolderErrorBound C f μ θ) (hμ : 0 < μ) (hθ : 0 < θ) (hβ : 0 < β)
    (hrun : IsFWRun C (fderiv ℝ f) x v (fun t => eta 4 t)) :
    ∀ t : ℕ, ⌈8 * L * Metric.diam C ^ 2 * (μ / β) ^ (1 / θ)⌉₊ ≤ t →
      Metric.infDist (x t) (minimizers C f) ≤ β := by
  intro t ht
  rcases (minimizers C f).eq_empty_or_nonempty with hM | ⟨xStar, hxs⟩
  · rw [hM, Metric.infDist_empty]; exact hβ.le
  set K := 8 * L * Metric.diam C ^ 2 with hK
  have hKpos : 0 < K := by positivity
  have hS : 0 < K * (μ / β) ^ (1 / θ) := by positivity
  have ht1 : 1 ≤ t := le_trans (Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr hS).ne') ht
  have hb := baseline_bound hC hconv hdiff hsm hL.le hrun hxs t ht1
  have hxt : x t ∈ C := Lemmata.FrankWolfe.Proof.fw_run_mem C _ x v _ hconv.1 hrun t
  have hh0 : 0 ≤ f (x t) - f xStar := sub_nonneg.mpr (hxs.2 _ hxt)
  have hP : 0 < (β / μ) ^ (1 / θ) := by positivity
  have hle : K / (t + 3) ≤ (β / μ) ^ (1 / θ) := by
    have h1 : K * (μ / β) ^ (1 / θ) ≤ t := le_trans (Nat.le_ceil _) (by exact_mod_cast ht)
    have hinv : (β / μ) ^ (1 / θ) * (μ / β) ^ (1 / θ) = 1 := by
      rw [← Real.mul_rpow (by positivity) (by positivity), div_mul_div_comm, mul_comm β μ,
        div_self (by positivity), Real.one_rpow]
    rw [div_le_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left h1 hP.le
    have e : (β / μ) ^ (1 / θ) * (K * (μ / β) ^ (1 / θ)) = K := by
      rw [mul_left_comm, hinv, mul_one]
    nlinarith
  calc Metric.infDist (x t) (minimizers C f) ≤ μ * (f (x t) - f xStar) ^ θ := heb _ hxt _ hxs
    _ ≤ μ * ((β / μ) ^ (1 / θ)) ^ θ :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hh0 (hb.trans hle) hθ.le) hμ.le
    _ = β := by
        rw [← Real.rpow_mul (by positivity), one_div_mul_cancel hθ.ne', Real.rpow_one]
        field_simp

/-- **Lemma 3.4** in the paper's form (unique minimizer). -/
theorem scaling_heb_bound {C : Set E} {f : E → ℝ} {μ θ : ℝ} {xStar : E}
    (hC : IsCompact C) (hconv : ConvexOn ℝ C f) (hdiff : ∀ y ∈ C, DifferentiableAt ℝ f y)
    (heb : IsHolderErrorBound C f μ θ) (hμ : 0 < μ) (huniq : minimizers C f = {xStar}) :
    ∀ x ∈ C, x ≠ xStar →
      (f x - f xStar) ^ (1 - θ) / μ ≤ fderiv ℝ f x (x - xStar) / ‖x - xStar‖ ∧
      fderiv ℝ f x (x - xStar) / ‖x - xStar‖ ≤ ‖fderiv ℝ f x‖ := by
  intro x hx hne
  have hxs : xStar ∈ minimizers C f := by rw [huniq]; rfl
  have hnpos : 0 < ‖x - xStar‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hlt : f xStar < f x := by
    by_contra hle
    replace hle := not_lt.mp hle
    have : x ∈ minimizers C f := ⟨hx, fun y hy => le_trans hle (hxs.2 y hy)⟩
    rw [huniq] at this
    exact hne this
  obtain ⟨y, hyM, -, -, hmain, -⟩ :=
    Lemmata.FrankWolfe.Proof.heb_scaling C f μ θ hC hconv hdiff heb xStar hxs x hx hlt
  rw [huniq] at hyM
  rw [Set.mem_singleton_iff] at hyM
  subst hyM
  refine ⟨?_, ?_⟩
  · rw [div_le_div_iff₀ hμ hnpos]
    linarith
  · rw [div_le_iff₀ hnpos]
    exact le_trans (le_abs_self _) (by
      rw [← Real.norm_eq_abs]; exact (fderiv ℝ f x).le_opNorm _)

/-- Turning a gap lower bound into the recursion of Lemma 3.5. -/
theorem rec_of_gap {h1 h g η L N A H : ℝ} (hη : 0 ≤ η)
    (hprog : h1 ≤ h - η * g + η ^ 2 * L / 2 * N) (hg1 : h ≤ g) (hg2 : N * A * H ≤ g) :
    h1 ≤ (1 - η / 2) * h - η * A * (N / 2) * H + η ^ 2 * L * (N / 2) := by
  have : h / 2 + N / 2 * A * H ≤ g := by linarith
  have h3 := mul_le_mul_of_nonneg_left this hη
  linarith

/-- `h₁ ≤ L δ²/2`, since `η₀ = 1`. -/
theorem first_gap {C : Set E} {f : E → ℝ} {L : ℝ} {x v : ℕ → E} {xStar : E}
    (hC : IsCompact C) (hconv : ConvexOn ℝ C f) (hdiff : ∀ y ∈ C, DifferentiableAt ℝ f y)
    (hsm : IsSmoothOn C f L) (hL : 0 ≤ L) (hrun : IsFWRun C (fderiv ℝ f) x v (fun t => eta 4 t))
    (hxs : xStar ∈ minimizers C f) :
    f (x 1) - f xStar ≤ L * Metric.diam C ^ 2 / 2 := by
  obtain ⟨h1, h2, h3, -, -⟩ := basic_step hC hconv hdiff hsm hrun hxs 0
  have h0 : eta 4 ((0 : ℕ) : ℤ) = 1 := by simp [eta]
  rw [h0] at h1
  have hsq : ‖v 0 - x 0‖ ^ 2 ≤ Metric.diam C ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h3 2
  have := mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ L / 2)
  simp only [zero_add] at h1
  nlinarith

/-- **Theorem 3.6**, for every `S ≥ 1`. -/
theorem interior_bound {C : Set E} {f : E → ℝ} {L μ θ β : ℝ} {x v : ℕ → E} {xStar : E}
    (hC : IsCompact C) (hconv : ConvexOn ℝ C f) (hdiff : ∀ y ∈ C, DifferentiableAt ℝ f y)
    (hsm : IsSmoothOn C f L) (hL : 0 < L) (hdiam : 0 < Metric.diam C)
    (heb : IsHolderErrorBound C f μ θ) (hμ : 0 < μ) (hθ : θ ∈ Set.Icc (0 : ℝ) (1 / 2))
    (hxs : xStar ∈ minimizers C f) (hβ : 0 < β)
    (hball : ∀ y ∈ minimizers C f, ∀ z ∈ affineSpan ℝ C, ‖z - y‖ ≤ β → z ∈ C)
    (hrun : IsFWRun C (fderiv ℝ f) x v (fun t => eta 4 t)) :
    ∀ S : ℕ, 1 ≤ S → ∀ t : ℕ, S ≤ t →
      f (x t) - f xStar ≤
        max ((eta 4 ((t : ℤ) - 2) / eta 4 ((S : ℤ) - 1)) ^ (1 / (1 - θ)) * (f (x S) - f xStar))
          ((eta 4 ((t : ℤ) - 2) * (2 * μ * L * Metric.diam C ^ 3 / β ^ 2)) ^ (1 / (1 - θ)) +
            eta 4 ((t : ℤ) - 2) ^ 2 * (L * Metric.diam C ^ 2 / 2)) := by
  intro S hS t hSt
  set δ := Metric.diam C with hδ
  set A := β ^ 2 / (4 * μ * δ) with hA
  set B := L * δ ^ 2 / 2 with hB
  have h2β : 2 * β ≤ δ := two_beta_le_diam hC hβ hxs.1 (hball xStar hxs) hdiam
  have hApos : 0 < A := by positivity
  have hBpos : 0 < B := by positivity
  have hθ1 : θ < 1 := by linarith [hθ.2]
  have hAle : 2 * A ≤ β / μ := by
    have e : 2 * A = β / μ * (β / (2 * δ)) := by rw [hA]; field_simp; ring
    rw [e]
    have : β / (2 * δ) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    calc β / μ * (β / (2 * δ)) ≤ β / μ * 1 := mul_le_mul_of_nonneg_left this (by positivity)
      _ = β / μ := mul_one _
  have hrec : ∀ τ, S ≤ τ → τ < t → f (x (τ + 1)) - f xStar ≤
      (1 - eta 4 τ / 2) * (f (x τ) - f xStar) - eta 4 τ * A * 1 * (f (x τ) - f xStar) ^ (1 - θ) +
        eta 4 τ ^ 2 * B * 1 := by
    intro τ _ _
    obtain ⟨h1, h2, h3, hxC, hvC⟩ := basic_step hC hconv hdiff hsm hrun hxs τ
    obtain ⟨-, hvmin, hγ, -⟩ := hrun.2 τ
    have hgap := interior_gap hC hconv hdiff heb hμ hθ1 hβ hball hxs hxC hvmin
    have hH : 0 ≤ (f (x τ) - f xStar) ^ (1 - θ) :=
      Real.rpow_nonneg (sub_nonneg.mpr (hxs.2 _ hxC)) _
    have hsq : ‖v τ - x τ‖ ^ 2 ≤ δ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h3 2
    have hη : 0 ≤ eta 4 τ := hγ.1
    have hq : eta 4 τ ^ 2 * L / 2 * ‖v τ - x τ‖ ^ 2 ≤ eta 4 τ ^ 2 * B := by
      rw [hB]
      have := mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ eta 4 τ ^ 2 * L / 2)
      linarith
    have hg2 : 2 * A * (f (x τ) - f xStar) ^ (1 - θ) ≤ fderiv ℝ f (x τ) (x τ - v τ) := by
      have := mul_le_mul_of_nonneg_right hAle hH
      linarith
    have hg : (f (x τ) - f xStar) / 2 + A * (f (x τ) - f xStar) ^ (1 - θ) ≤
        fderiv ℝ f (x τ) (x τ - v τ) := by linarith
    have h4 := mul_le_mul_of_nonneg_left hg hη
    linarith
  have hseq := sequence_bound θ A B 1 S t (fun _ => 1) (fun τ => f (x τ) - f xStar) hθ hS hApos
    hBpos one_pos (fun _ _ _ => ⟨zero_le_one, le_rfl⟩)
    (fun τ _ _ => sub_nonneg.mpr
      (hxs.2 _ (Lemmata.FrankWolfe.Proof.fw_run_mem C _ x v _ hconv.1 hrun τ)))
    hrec t hSt le_rfl
  have e1 : eta 4 ((t : ℤ) - 2) * B / A = eta 4 ((t : ℤ) - 2) * (2 * μ * L * δ ^ 3 / β ^ 2) := by
    rw [hA, hB]; field_simp; ring
  rw [e1, mul_one] at hseq
  exact hseq

namespace Proof

theorem baseline_rate : BaselineRate.{u} := by
  intro E _ _ C f L x v hC hconv hdiff hsm hL hrun xStar hxs t ht
  exact baseline_bound hC hconv hdiff hsm hL hrun hxs t ht

theorem guelat_marcotte_scaling : GuelatMarcotteScaling.{u} := by
  intro E _ _ C f β xStar hC hconv hdiff hxs hβ hball x hx p hp hpmin u hu hu1
  exact gm_scaling_bound hC hconv hdiff hxs hβ hball hx hp hpmin hu hu1

theorem iterates_near_optimum : IteratesNearOptimum.{u} := by
  intro E _ _ C f L μ θ β x v hC hconv hdiff hsm hL hdiam heb hμ hθ hβ hrun t ht
  exact near_optimum_bound hC hconv hdiff hsm hL hdiam heb hμ hθ hβ hrun t ht

theorem scaling_heb : ScalingHEB.{u} := by
  intro E _ _ C f μ θ xStar hC hconv hdiff heb hμ huniq x hx hne
  exact scaling_heb_bound hC hconv hdiff heb hμ huniq x hx hne

theorem interior_rate : InteriorRate.{u} := by
  intro E _ _ C f L μ θ β x v xStar hC hconv hdiff hsm hL hdiam heb hμ hθ hxs hβ hball hrun S hS
    t ht
  exact interior_bound hC hconv hdiff hsm hL hdiam heb hμ hθ hxs hβ hball hrun S hS t ht

end Proof

end Lemmata.FWOpenLoop
