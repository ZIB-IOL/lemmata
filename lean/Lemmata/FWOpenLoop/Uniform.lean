module

public import Lemmata.FWOpenLoop.Interior
public import Lemmata.CGBasics.UniformlyConvex

@[expose] public section

/-!
# Uniformly convex feasible regions (Lemma 3.9, Theorems 3.10 and 3.12)

The scaling inequality of a uniformly convex set bounds the Frank–Wolfe gap below by
`‖x_t - v_t‖² A h_t^{1-ψ}`, with `A` and `ψ` coming from lower-bounded gradients (Theorem 3.10)
or from a Hölderian error bound (Theorem 3.12); Lemma 3.5 turns this into the rates.
-/

namespace Lemmata.FWOpenLoop

open Lemmata.FrankWolfe

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Lemma 3.9**, in the paper's form. -/
theorem scaling_unif_bound {C : Set E} {f : E → ℝ} {α q : ℝ} {xStar : E}
    (hUC : IsUniformlyConvexSet C α q) (hα : 0 < α) (hq : 2 ≤ q) (hconv : ConvexOn ℝ C f)
    (hdiff : ∀ y ∈ C, DifferentiableAt ℝ f y) (hxs : xStar ∈ minimizers C f)
    {x : E} (hx : x ∈ C) {p : E} (hp : p ∈ C)
    (hpmin : ∀ y ∈ C, fderiv ℝ f x p ≤ fderiv ℝ f x y) :
    (α / 2 * ‖fderiv ℝ f x‖) ^ (2 / q) * (f x - f xStar) ^ (1 - 2 / q) * ‖x - p‖ ^ 2 ≤
      fderiv ℝ f x (x - p) := by
  set ψ := fderiv ℝ f x with hψ
  set g := ψ (x - p) with hg
  set h := f x - f xStar with hh
  have hq0 : 0 < q := by linarith
  have he1 : 0 < 2 / q := by positivity
  have he2 : 0 ≤ 1 - 2 / q := by rw [sub_nonneg, div_le_one hq0]; exact hq
  have hUCs := Lemmata.CGBasics.Proof.uniformly_convex_scaling C α q hUC ψ p hp hpmin x hx
  have hh0 : 0 ≤ h := sub_nonneg.mpr (hxs.2 x hx)
  have hhg : h ≤ g := by
    have h1 := convexOn_add_fderiv_le hconv hx (hdiff x hx) hxs.1
    have h2 := hpmin xStar hxs.1
    have e1 : ψ (xStar - x) = ψ xStar - ψ x := map_sub _ _ _
    have e2 : g = ψ x - ψ p := map_sub _ _ _
    linarith
  set a := α * ‖ψ‖ * ‖x - p‖ ^ q with ha
  have ha0 : 0 ≤ a := by positivity
  -- `(α ‖ψ‖)^{2/q} ‖x - p‖² = a^{2/q}`
  have hsplit : (α * ‖ψ‖) ^ (2 / q) * ‖x - p‖ ^ (2 : ℕ) = a ^ (2 / q) := by
    rw [ha, Real.mul_rpow (x := α * ‖ψ‖) (y := ‖x - p‖ ^ q) (by positivity) (by positivity),
      ← Real.rpow_mul (norm_nonneg _), mul_div_cancel₀ _ hq0.ne', Real.rpow_two]
  have hstep1 : (α / 2 * ‖ψ‖) ^ (2 / q) ≤ (α * ‖ψ‖) ^ (2 / q) :=
    Real.rpow_le_rpow (by positivity) (by nlinarith [norm_nonneg ψ]) he1.le
  have hstep2 : a ^ (2 / q) * h ^ (1 - 2 / q) ≤ g := by
    rcases (le_trans ha0 hUCs).eq_or_lt with hg0 | hgpos
    · have : a = 0 := le_antisymm (by rw [← hg0] at hUCs; exact hUCs) ha0
      rw [this, Real.zero_rpow he1.ne', zero_mul]; exact le_trans ha0 hUCs
    · calc a ^ (2 / q) * h ^ (1 - 2 / q) ≤ g ^ (2 / q) * g ^ (1 - 2 / q) :=
            mul_le_mul (Real.rpow_le_rpow ha0 hUCs he1.le) (Real.rpow_le_rpow hh0 hhg he2)
              (Real.rpow_nonneg hh0 _) (Real.rpow_nonneg hgpos.le _)
        _ = g := by rw [← Real.rpow_add hgpos, add_sub_cancel, Real.rpow_one]
  calc (α / 2 * ‖ψ‖) ^ (2 / q) * h ^ (1 - 2 / q) * ‖x - p‖ ^ 2
      ≤ (α * ‖ψ‖) ^ (2 / q) * h ^ (1 - 2 / q) * ‖x - p‖ ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_right hstep1 (Real.rpow_nonneg hh0 _)
    _ = a ^ (2 / q) * h ^ (1 - 2 / q) := by rw [← hsplit]; ring
    _ ≤ g := hstep2

/-- `η_{-1+1} = η_0 = 1`, used to start Lemma 3.5 at `S = 1`. -/
theorem eta_one_sub_one : eta 4 (((1 : ℕ) : ℤ) - 1) = 1 := by simp [eta]

/-- The common recursion of Theorems 3.10 and 3.12: if `‖x_t - v_t‖² A H_t ≤ g_t` at every step,
then `h_{t+1} ≤ (1 - η_t/2) h_t - η_t A C_t H_t + η_t² L C_t` with `C_t = ‖v_t - x_t‖²/2`. -/
theorem uc_rec {C : Set E} {f : E → ℝ} {L A : ℝ} {x v : ℕ → E} {xStar : E} {H : ℕ → ℝ}
    (hC : IsCompact C) (hconv : ConvexOn ℝ C f) (hdiff : ∀ y ∈ C, DifferentiableAt ℝ f y)
    (hsm : IsSmoothOn C f L) (hrun : IsFWRun C (fderiv ℝ f) x v (fun t => eta 4 t))
    (hxs : xStar ∈ minimizers C f)
    (hgap : ∀ τ, ‖v τ - x τ‖ ^ 2 * A * H τ ≤ fderiv ℝ f (x τ) (x τ - v τ)) (τ : ℕ) :
    f (x (τ + 1)) - f xStar ≤ (1 - eta 4 τ / 2) * (f (x τ) - f xStar) -
      eta 4 τ * A * (‖v τ - x τ‖ ^ 2 / 2) * H τ + eta 4 τ ^ 2 * L * (‖v τ - x τ‖ ^ 2 / 2) := by
  obtain ⟨h1, h2, -, -, -⟩ := basic_step hC hconv hdiff hsm hrun hxs τ
  obtain ⟨-, -, hγ, -⟩ := hrun.2 τ
  exact rec_of_gap hγ.1 h1 h2 (hgap τ)

/-- **Theorem 3.10.** -/
theorem exterior_bound {C : Set E} {f : E → ℝ} {L α q ν : ℝ} {x v : ℕ → E} {xStar : E}
    (hC : IsCompact C) (hUC : IsUniformlyConvexSet C α q) (hα : 0 < α) (hq : 2 ≤ q)
    (hconv : ConvexOn ℝ C f) (hdiff : ∀ y ∈ C, DifferentiableAt ℝ f y)
    (hsm : IsSmoothOn C f L) (hL : 0 < L) (hdiam : 0 < Metric.diam C)
    (hν : 0 < ν) (hgrad : ∀ y ∈ C, ν ≤ ‖fderiv ℝ f y‖) (hxs : xStar ∈ minimizers C f)
    (hrun : IsFWRun C (fderiv ℝ f) x v (fun t => eta 4 t)) :
    (4 ≤ q → ∀ t : ℕ, 1 ≤ t → f (x t) - f xStar ≤
      max (eta 4 ((t : ℤ) - 2) ^ (1 / (1 - 2 / q)) * (L * Metric.diam C ^ 2 / 2))
        ((eta 4 ((t : ℤ) - 2) * L * (2 / (α * ν)) ^ (2 / q)) ^ (1 / (1 - 2 / q)) +
          eta 4 ((t : ℤ) - 2) ^ 2 * (L * Metric.diam C ^ 2 / 2))) ∧
    (q < 4 → ∀ t : ℕ, ⌈8 * L * Metric.diam C ^ 2⌉₊ ≤ t → f (x t) - f xStar ≤
      max ((eta 4 ((t : ℤ) - 2) / eta 4 ((⌈8 * L * Metric.diam C ^ 2⌉₊ : ℤ) - 1)) ^ 2 *
          (f (x ⌈8 * L * Metric.diam C ^ 2⌉₊) - f xStar))
        ((eta 4 ((t : ℤ) - 2) * L * (2 / (α * ν)) ^ (2 / q)) ^ 2 +
          eta 4 ((t : ℤ) - 2) ^ 2 * (L * Metric.diam C ^ 2 / 2))) := by
  set δ := Metric.diam C with hδ
  set A := (α * ν / 2) ^ (2 / q) with hA
  have hq0 : 0 < q := by linarith
  have hApos : 0 < A := by positivity
  have hmem : ∀ τ, x τ ∈ C := Lemmata.FrankWolfe.Proof.fw_run_mem C _ x v _ hconv.1 hrun
  have hh0 : ∀ τ, 0 ≤ f (x τ) - f xStar := fun τ => sub_nonneg.mpr (hxs.2 _ (hmem τ))
  have hgap : ∀ τ, ‖v τ - x τ‖ ^ 2 * A * (f (x τ) - f xStar) ^ (1 - 2 / q) ≤
      fderiv ℝ f (x τ) (x τ - v τ) := by
    intro τ
    obtain ⟨hvC, hvmin, -, -⟩ := hrun.2 τ
    have hs := scaling_unif_bound hUC hα hq hconv hdiff hxs (hmem τ) hvC hvmin
    have hmono : A ≤ (α / 2 * ‖fderiv ℝ f (x τ)‖) ^ (2 / q) := by
      apply Real.rpow_le_rpow (by positivity) _ (by positivity)
      have := hgrad _ (hmem τ)
      nlinarith
    have hH := Real.rpow_nonneg (hh0 τ) (1 - 2 / q)
    rw [norm_sub_rev] at hs
    calc ‖v τ - x τ‖ ^ 2 * A * (f (x τ) - f xStar) ^ (1 - 2 / q)
        ≤ ‖v τ - x τ‖ ^ 2 * (α / 2 * ‖fderiv ℝ f (x τ)‖) ^ (2 / q) *
            (f (x τ) - f xStar) ^ (1 - 2 / q) := by
          apply mul_le_mul_of_nonneg_right _ hH
          exact mul_le_mul_of_nonneg_left hmono (by positivity)
      _ = _ := by ring
      _ ≤ _ := hs
  have hrec := uc_rec hC hconv hdiff hsm hrun hxs hgap
  have hCs : ∀ τ, 0 ≤ ‖v τ - x τ‖ ^ 2 / 2 ∧ ‖v τ - x τ‖ ^ 2 / 2 ≤ δ ^ 2 / 2 := by
    intro τ
    obtain ⟨-, -, h3, -, -⟩ := basic_step hC hconv hdiff hsm hrun hxs τ
    exact ⟨by positivity, by nlinarith [norm_nonneg (v τ - x τ)]⟩
  have hBA : ∀ η : ℝ, η * L / A = η * L * (2 / (α * ν)) ^ (2 / q) := by
    intro η
    rw [hA, show 2 / (α * ν) = (α * ν / 2)⁻¹ by rw [inv_div],
      Real.inv_rpow (by positivity), div_eq_mul_inv]
  refine ⟨fun hq4 t ht => ?_, fun hq4 t ht => ?_⟩
  · have hψ : 2 / q ∈ Set.Icc (0 : ℝ) (1 / 2) :=
      ⟨by positivity, by rw [div_le_div_iff₀ hq0 (by norm_num)]; linarith⟩
    have hseq := sequence_bound (2 / q) A L (δ ^ 2 / 2) 1 t (fun τ => ‖v τ - x τ‖ ^ 2 / 2)
      (fun τ => f (x τ) - f xStar) hψ le_rfl hApos hL (by positivity)
      (fun τ _ _ => hCs τ) (fun τ _ _ => hh0 τ) (fun τ _ _ => hrec τ) t ht le_rfl
    rw [eta_one_sub_one, div_one, hBA] at hseq
    have h1 := first_gap hC hconv hdiff hsm hL.le hrun hxs
    refine le_trans hseq (max_le_max ?_ (le_of_eq (by ring_nf)))
    exact mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg (le_of_lt (by
      simp only [eta]; push_cast; apply div_pos (by norm_num)
      have : (1 : ℝ) ≤ t := by exact_mod_cast ht
      linarith)) _)
  · set S := ⌈8 * L * δ ^ 2⌉₊ with hS
    have hKpos : 0 < 8 * L * δ ^ 2 := by positivity
    have hS1 : 1 ≤ S := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr hKpos).ne'
    have hsmall : ∀ τ, S ≤ τ → f (x τ) - f xStar ≤ 1 := by
      intro τ hτ
      have hb := baseline_bound hC hconv hdiff hsm hL.le hrun hxs τ (le_trans hS1 hτ)
      have : 8 * L * δ ^ 2 ≤ τ := le_trans (Nat.le_ceil _) (by exact_mod_cast hτ)
      refine le_trans hb ?_
      rw [div_le_one (by positivity)]
      linarith
    have hrec' : ∀ τ, S ≤ τ → τ < t → f (x (τ + 1)) - f xStar ≤
        (1 - eta 4 τ / 2) * (f (x τ) - f xStar) -
          eta 4 τ * A * (‖v τ - x τ‖ ^ 2 / 2) * (f (x τ) - f xStar) ^ (1 - 1 / 2 : ℝ) +
          eta 4 τ ^ 2 * L * (‖v τ - x τ‖ ^ 2 / 2) := by
      intro τ hτ _
      have h := hrec τ
      have hle : (f (x τ) - f xStar) ^ (1 - 1 / 2 : ℝ) ≤ (f (x τ) - f xStar) ^ (1 - 2 / q) := by
        rcases (hh0 τ).eq_or_lt with h0 | hpos
        · rw [← h0, Real.zero_rpow (by norm_num)]; exact Real.rpow_nonneg le_rfl _
        · apply Real.rpow_le_rpow_of_exponent_ge hpos (hsmall τ hτ)
          rw [show (1 - 1 / 2 : ℝ) = 1 / 2 by norm_num, sub_le_iff_le_add]
          have : 1 / 2 ≤ 2 / q := by rw [div_le_div_iff₀ (by norm_num) hq0]; linarith
          linarith
      have hη : 0 ≤ eta 4 τ := (hrun.2 τ).2.2.1.1
      have := mul_le_mul_of_nonneg_left hle
        (by positivity : 0 ≤ eta 4 τ * A * (‖v τ - x τ‖ ^ 2 / 2))
      linarith
    have hseq := sequence_bound (1 / 2) A L (δ ^ 2 / 2) S t (fun τ => ‖v τ - x τ‖ ^ 2 / 2)
      (fun τ => f (x τ) - f xStar) ⟨by norm_num, le_rfl⟩ hS1 hApos hL (by positivity)
      (fun τ _ _ => hCs τ) (fun τ _ _ => hh0 τ) hrec' t ht le_rfl
    have e2 : (1 / (1 - 1 / 2) : ℝ) = 2 := by norm_num
    rw [e2, hBA, Real.rpow_two, Real.rpow_two] at hseq
    refine le_trans hseq (max_le_max le_rfl (le_of_eq (by ring_nf)))

/-- **Theorem 3.12.** -/
theorem unrestricted_bound {C : Set E} {f : E → ℝ} {L α q μ θ : ℝ} {x v : ℕ → E} {xStar : E}
    (hC : IsCompact C) (hUC : IsUniformlyConvexSet C α q) (hα : 0 < α) (hq : 2 ≤ q)
    (hconv : ConvexOn ℝ C f) (hdiff : ∀ y ∈ C, DifferentiableAt ℝ f y)
    (hsm : IsSmoothOn C f L) (hL : 0 < L) (hdiam : 0 < Metric.diam C)
    (heb : IsHolderErrorBound C f μ θ) (hμ : 0 < μ) (hθ : θ ∈ Set.Icc (0 : ℝ) (1 / 2))
    (hxs : xStar ∈ minimizers C f) (hrun : IsFWRun C (fderiv ℝ f) x v (fun t => eta 4 t)) :
    ∀ t : ℕ, 1 ≤ t → f (x t) - f xStar ≤
      max (eta 4 ((t : ℤ) - 2) ^ (1 / (1 - 2 * θ / q)) * (L * Metric.diam C ^ 2 / 2))
        ((eta 4 ((t : ℤ) - 2) * L * (2 * μ / α) ^ (2 / q)) ^ (1 / (1 - 2 * θ / q)) +
          eta 4 ((t : ℤ) - 2) ^ 2 * (L * Metric.diam C ^ 2 / 2)) := by
  intro t ht
  set δ := Metric.diam C with hδ
  set A := (α / (2 * μ)) ^ (2 / q) with hA
  have hq0 : 0 < q := by linarith
  have hApos : 0 < A := by positivity
  have hθ0 := hθ.1
  have hθ1 := hθ.2
  have hexp : 0 < 1 - 2 * θ / q := by
    have : 2 * θ / q ≤ 1 / 2 := by rw [div_le_div_iff₀ hq0 (by norm_num)]; nlinarith
    linarith
  have hmem : ∀ τ, x τ ∈ C := Lemmata.FrankWolfe.Proof.fw_run_mem C _ x v _ hconv.1 hrun
  have hh0 : ∀ τ, 0 ≤ f (x τ) - f xStar := fun τ => sub_nonneg.mpr (hxs.2 _ (hmem τ))
  have hgap : ∀ τ, ‖v τ - x τ‖ ^ 2 * A * (f (x τ) - f xStar) ^ (1 - 2 * θ / q) ≤
      fderiv ℝ f (x τ) (x τ - v τ) := by
    intro τ
    obtain ⟨hvC, hvmin, -, -⟩ := hrun.2 τ
    have hg0 : 0 ≤ fderiv ℝ f (x τ) (x τ - v τ) := by
      have := hvmin (x τ) (hmem τ); rw [map_sub]; linarith
    rcases (hh0 τ).eq_or_lt with h0 | hpos
    · rw [← h0, Real.zero_rpow hexp.ne', mul_zero]; exact hg0
    have hs := scaling_unif_bound hUC hα hq hconv hdiff hxs (hmem τ) hvC hvmin
    obtain ⟨-, -, -, -, -, hnorm⟩ :=
      Lemmata.FrankWolfe.Proof.heb_scaling C f μ θ hC hconv hdiff heb xStar hxs (x τ) (hmem τ)
        (by linarith)
    set h := f (x τ) - f xStar with hh
    have hmono : A * h ^ ((1 - θ) * (2 / q)) ≤ (α / 2 * ‖fderiv ℝ f (x τ)‖) ^ (2 / q) := by
      rw [hA, Real.rpow_mul hpos.le, ← Real.mul_rpow (by positivity) (by positivity)]
      apply Real.rpow_le_rpow (by positivity) _ (by positivity)
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith
    have hcomb : h ^ ((1 - θ) * (2 / q)) * h ^ (1 - 2 / q) = h ^ (1 - 2 * θ / q) := by
      rw [← Real.rpow_add hpos]; ring_nf
    have hH := Real.rpow_nonneg hpos.le (1 - 2 / q)
    rw [norm_sub_rev] at hs
    calc ‖v τ - x τ‖ ^ 2 * A * h ^ (1 - 2 * θ / q)
        = ‖v τ - x τ‖ ^ 2 * (A * h ^ ((1 - θ) * (2 / q))) * h ^ (1 - 2 / q) := by
          rw [← hcomb]; ring
      _ ≤ ‖v τ - x τ‖ ^ 2 * (α / 2 * ‖fderiv ℝ f (x τ)‖) ^ (2 / q) * h ^ (1 - 2 / q) := by
          apply mul_le_mul_of_nonneg_right _ hH
          exact mul_le_mul_of_nonneg_left hmono (by positivity)
      _ = _ := by ring
      _ ≤ _ := hs
  have hrec := uc_rec hC hconv hdiff hsm hrun hxs hgap
  have hCs : ∀ τ, 0 ≤ ‖v τ - x τ‖ ^ 2 / 2 ∧ ‖v τ - x τ‖ ^ 2 / 2 ≤ δ ^ 2 / 2 := by
    intro τ
    obtain ⟨-, -, h3, -, -⟩ := basic_step hC hconv hdiff hsm hrun hxs τ
    exact ⟨by positivity, by nlinarith [norm_nonneg (v τ - x τ)]⟩
  have hψ : 2 * θ / q ∈ Set.Icc (0 : ℝ) (1 / 2) :=
    ⟨by positivity, by rw [div_le_div_iff₀ hq0 (by norm_num)]; nlinarith⟩
  have hseq := sequence_bound (2 * θ / q) A L (δ ^ 2 / 2) 1 t (fun τ => ‖v τ - x τ‖ ^ 2 / 2)
    (fun τ => f (x τ) - f xStar) hψ le_rfl hApos hL (by positivity)
    (fun τ _ _ => hCs τ) (fun τ _ _ => hh0 τ) (fun τ _ _ => hrec τ) t ht le_rfl
  have hBA : eta 4 ((t : ℤ) - 2) * L / A = eta 4 ((t : ℤ) - 2) * L * (2 * μ / α) ^ (2 / q) := by
    rw [hA, show 2 * μ / α = (α / (2 * μ))⁻¹ by rw [inv_div],
      Real.inv_rpow (by positivity), div_eq_mul_inv]
  rw [eta_one_sub_one, div_one, hBA] at hseq
  have h1 := first_gap hC hconv hdiff hsm hL.le hrun hxs
  refine le_trans hseq (max_le_max ?_ (le_of_eq (by ring_nf)))
  exact mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg (le_of_lt (by
    simp only [eta]; push_cast; apply div_pos (by norm_num)
    have : (1 : ℝ) ≤ t := by exact_mod_cast ht
    linarith)) _)

namespace Proof

theorem scaling_unif : ScalingUnif.{u} := by
  intro E _ _ C f α q xStar hUC hα hq hconv hdiff hxs x hx p hp hpmin
  exact scaling_unif_bound hUC hα hq hconv hdiff hxs hx hp hpmin

theorem exterior_rate : ExteriorRate.{u} := by
  intro E _ _ C f L α q ν x v xStar hC hUC hα hq hconv hdiff hsm hL hdiam hν hgrad hxs hrun
  exact exterior_bound hC hUC hα hq hconv hdiff hsm hL hdiam hν hgrad hxs hrun

theorem unrestricted_rate : UnrestrictedRate.{u} := by
  intro E _ _ C f L α q μ θ x v xStar hC hUC hα hq hconv hdiff hsm hL hdiam heb hμ hθ hxs hrun
  exact unrestricted_bound hC hUC hα hq hconv hdiff hsm hL hdiam heb hμ hθ hxs hrun

end Proof

end Lemmata.FWOpenLoop
