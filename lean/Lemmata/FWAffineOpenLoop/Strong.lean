module

public import Lemmata.FWAffineOpenLoop.Products
public import Lemmata.FrankWolfe.Proof.Run

@[expose] public section

/-!
# Strong growth: Theorems 3.1, 3.2 and 3.4

A Frank–Wolfe step changes the objective by `-η_t g_t + D_f(x_{t+1}, x_t)`, so the best duality
gap `pd_t` satisfies `pd_{t+1} ≤ pd_t - η_t g_t + D_f(x_{t+1}, x_t)`, and `pd_t ≤ g_t`. The strong
growth property bounds the Bregman term, and the rates follow by induction.
-/

namespace Lemmata.FWAffineOpenLoop

open Lemmata.FrankWolfe Lemmata.FWOpenLoop

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem pd_le_gap (f : E → ℝ) (x v : ℕ → E) (t : ℕ) :
    pdGap f x v t ≤ fderiv ℝ f (x t) (x t - v t) := by
  unfold pdGap
  calc _ ≤ f (x t) - f (x t) + fderiv ℝ f (x t) (x t - v t) :=
        Finset.inf'_le (fun k => f (x t) - f (x k) + fderiv ℝ f (x k) (x k - v k))
          (Finset.self_mem_range_succ t)
    _ = _ := by ring

theorem pd_zero (f : E → ℝ) (x v : ℕ → E) :
    pdGap f x v 0 = fderiv ℝ f (x 0) (x 0 - v 0) := by
  simp [pdGap]

theorem pd_succ_le (f : E → ℝ) (x v : ℕ → E) (t : ℕ) :
    pdGap f x v (t + 1) ≤ pdGap f x v t + (f (x (t + 1)) - f (x t)) := by
  have h : pdGap f x v (t + 1) - (f (x (t + 1)) - f (x t)) ≤ pdGap f x v t := by
    unfold pdGap
    apply Finset.le_inf'
    intro k hk
    have hk' : k ∈ Finset.range (t + 1 + 1) := by
      rw [Finset.mem_range] at hk ⊢; omega
    have := Finset.inf'_le
      (fun k => f (x (t + 1)) - f (x k) + fderiv ℝ f (x k) (x k - v k)) hk'
    linarith
  linarith

theorem f_step {C : Set E} {f : E → ℝ} {x v : ℕ → E} {γ : ℕ → ℝ}
    (hrun : IsFWRun C (fderiv ℝ f) x v γ) (t : ℕ) :
    f (x (t + 1)) - f (x t) =
      -(γ t) * fderiv ℝ f (x t) (x t - v t) + bregman f (x (t + 1)) (x t) := by
  obtain ⟨-, -, -, hx⟩ := hrun.2 t
  unfold bregman
  rw [hx, add_sub_cancel_left, map_smul, smul_eq_mul]
  have : fderiv ℝ f (x t) (v t - x t) = -fderiv ℝ f (x t) (x t - v t) := by
    rw [← map_neg, neg_sub]
  rw [this]; ring

/-- The basic recursion `pd_{t+1} ≤ pd_t - γ_t g_t + D_f(x_{t+1}, x_t)`. -/
theorem pd_step {C : Set E} {f : E → ℝ} {x v : ℕ → E} {γ : ℕ → ℝ}
    (hrun : IsFWRun C (fderiv ℝ f) x v γ) (t : ℕ) :
    pdGap f x v (t + 1) ≤ pdGap f x v t - γ t * fderiv ℝ f (x t) (x t - v t) +
      bregman f (x (t + 1)) (x t) := by
  have h1 := pd_succ_le f x v t
  have h2 := f_step hrun t
  linarith

theorem gap_nonneg {C : Set E} {f : E → ℝ} {x v : ℕ → E} {γ : ℕ → ℝ} (hC : Convex ℝ C)
    (hrun : IsFWRun C (fderiv ℝ f) x v γ) (t : ℕ) : 0 ≤ fderiv ℝ f (x t) (x t - v t) := by
  obtain ⟨-, hvmin, -, -⟩ := hrun.2 t
  have := hvmin (x t) (Lemmata.FrankWolfe.Proof.fw_run_mem C _ x v γ hC hrun t)
  rw [map_sub]; linarith

/-- The primal gap is at most the best duality gap, which is therefore nonnegative. -/
theorem pd_ge_subopt {C : Set E} {f : E → ℝ} {x v : ℕ → E} {γ : ℕ → ℝ} {xStar : E}
    (hconv : ConvexOn ℝ C f) (hdiff : ∀ y ∈ C, DifferentiableAt ℝ f y)
    (hxs : xStar ∈ minimizers C f) (hrun : IsFWRun C (fderiv ℝ f) x v γ) (t : ℕ) :
    f (x t) - f xStar ≤ pdGap f x v t := by
  have hmem := Lemmata.FrankWolfe.Proof.fw_run_mem C _ x v γ hconv.1 hrun
  unfold pdGap
  apply Finset.le_inf'
  intro k _
  obtain ⟨-, hvmin, -, -⟩ := hrun.2 k
  have h1 := convexOn_add_fderiv_le hconv (hmem k) (hdiff _ (hmem k)) hxs.1
  have h2 := hvmin xStar hxs.1
  have e1 : fderiv ℝ f (x k) (xStar - x k) = fderiv ℝ f (x k) xStar - fderiv ℝ f (x k) (x k) :=
    map_sub _ _ _
  have e2 : fderiv ℝ f (x k) (x k - v k) = fderiv ℝ f (x k) (x k) - fderiv ℝ f (x k) (v k) :=
    map_sub _ _ _
  linarith

theorem pd_nonneg {C : Set E} {f : E → ℝ} {x v : ℕ → E} {γ : ℕ → ℝ} {xStar : E}
    (hconv : ConvexOn ℝ C f) (hdiff : ∀ y ∈ C, DifferentiableAt ℝ f y)
    (hxs : xStar ∈ minimizers C f) (hrun : IsFWRun C (fderiv ℝ f) x v γ) (t : ℕ) :
    0 ≤ pdGap f x v t := by
  have := pd_ge_subopt hconv hdiff hxs hrun t
  have hmem := Lemmata.FrankWolfe.Proof.fw_run_mem C _ x v γ hconv.1 hrun t
  linarith [hxs.2 _ hmem]

theorem minGap_le (f : E → ℝ) (x v : ℕ → E) {t i : ℕ} (hi : i ≤ t) :
    minGap f x v t ≤ fderiv ℝ f (x i) (x i - v i) :=
  Finset.inf'_le (fun k => fderiv ℝ f (x k) (x k - v k)) (Finset.mem_range.mpr (by omega))

theorem eta_mem (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (t : ℕ) : eta ℓ t ∈ Set.Icc (0 : ℝ) 1 := by
  rw [eta_nat]
  have hℓr : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have ht0 : (0 : ℝ) ≤ t := by positivity
  have hpos : (0 : ℝ) < (t : ℝ) + ℓ := by linarith
  exact ⟨by positivity, by rw [div_le_one hpos]; linarith⟩

/-- **Theorem 3.1.** -/
theorem pd_rate_zero_bound {C : Set E} {f : E → ℝ} {M : ℝ} {ℓ : ℕ} {x v : ℕ → E}
    (hC : Convex ℝ C) (hM : 0 ≤ M) (hℓ : 2 ≤ ℓ) (hg : IsStrongGrowth C f M 0)
    (hrun : IsFWRun C (fderiv ℝ f) x v (fun t => eta ℓ t)) :
    ∀ t : ℕ, 1 ≤ t → pdGap f x v t ≤ eta ℓ t * M := by
  have hmem := Lemmata.FrankWolfe.Proof.fw_run_mem C _ x v _ hC hrun
  have hrec : ∀ t, pdGap f x v (t + 1) ≤ (1 - eta ℓ t) * pdGap f x v t + eta ℓ t ^ 2 * M / 2 := by
    intro t
    have h1 := pd_step hrun t
    obtain ⟨hvC, hvmin, hγ, hx⟩ := hrun.2 t
    have h3 := hg (x t) (hmem t) (v t) hvC hvmin (eta ℓ t) hγ
    rw [Real.rpow_zero, mul_one, ← hx] at h3
    have h4 := pd_le_gap f x v t
    have h5 : eta ℓ t * pdGap f x v t ≤ eta ℓ t * fderiv ℝ f (x t) (x t - v t) :=
      mul_le_mul_of_nonneg_left h4 hγ.1
    nlinarith
  have hℓr : (2 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  intro t ht
  induction t, ht using Nat.le_induction with
  | base =>
    have h := hrec 0
    have h0 : eta ℓ ((0 : ℕ) : ℤ) = 1 := by
      rw [eta_nat]; simp only [Nat.cast_zero, zero_add]; field_simp
    rw [h0] at h
    have h1 : eta ℓ ((1 : ℕ) : ℤ) = ℓ / (1 + ℓ) := by rw [eta_nat]; push_cast; ring
    rw [h1]
    have : (1 : ℝ) / 2 ≤ ℓ / (1 + ℓ) := by
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]; linarith
    nlinarith
  | succ t ht ih =>
    have h := hrec t
    have hη := eta_mem ℓ (by omega) t
    have h2 := mul_le_mul_of_nonneg_left ih (by linarith [hη.2] : (0 : ℝ) ≤ 1 - eta ℓ t)
    have key : eta ℓ t - eta ℓ t ^ 2 / 2 ≤ eta ℓ ((t + 1 : ℕ) : ℤ) := by
      rw [eta_nat, eta_nat]
      have ht0 : (0 : ℝ) ≤ t := by positivity
      have ha : (0 : ℝ) < (t : ℝ) + ℓ := by positivity
      have e : ((t + 1 : ℕ) : ℝ) + ℓ = ((t : ℝ) + ℓ) + 1 := by push_cast; ring
      rw [e]
      have hdiff : (ℓ : ℝ) / ((t : ℝ) + ℓ) - ((ℓ : ℝ) / ((t : ℝ) + ℓ)) ^ 2 / 2 -
          (ℓ : ℝ) / (((t : ℝ) + ℓ) + 1) = ((ℓ : ℝ) * ((t : ℝ) + ℓ) * (2 - ℓ) - (ℓ : ℝ) ^ 2) /
            (2 * ((t : ℝ) + ℓ) ^ 2 * (((t : ℝ) + ℓ) + 1)) := by
        field_simp; ring
      have hnum : (ℓ : ℝ) * ((t : ℝ) + ℓ) * (2 - ℓ) - (ℓ : ℝ) ^ 2 ≤ 0 := by
        have := mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ ℓ) ha.le)
          (by linarith : (0 : ℝ) ≤ ℓ - 2)
        nlinarith [sq_nonneg (ℓ : ℝ)]
      have := div_nonpos_of_nonpos_of_nonneg hnum (by positivity :
        (0 : ℝ) ≤ 2 * ((t : ℝ) + ℓ) ^ 2 * (((t : ℝ) + ℓ) + 1))
      linarith
    have := mul_le_mul_of_nonneg_right key hM
    nlinarith

/-- `η_i M/2 ≤ c` once `i ≥ ℓM/(2c) - ℓ`. -/
theorem eta_mul_le {ℓ : ℕ} {M c : ℝ} (hℓ : 1 ≤ ℓ) (hc : 0 < c) {i : ℕ}
    (hi : (ℓ : ℝ) * M / (2 * c) - ℓ ≤ i) : eta ℓ i * M / 2 ≤ c := by
  rw [eta_nat]
  have hℓr : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hpos : (0 : ℝ) < (i : ℝ) + ℓ := by positivity
  have h1 : (ℓ : ℝ) * M / (2 * c) ≤ i + ℓ := by linarith
  rw [div_le_iff₀ (by positivity)] at h1
  rw [div_mul_eq_mul_div, div_div, div_le_iff₀ (by positivity)]
  linarith

/-- `(η_t/η_{S-1})` in closed form for natural `t ≥ 1`. -/
theorem eta_pred_ratio (ℓ S t : ℕ) (hℓ : 1 ≤ ℓ) (hS : 1 ≤ S) (ht : 1 ≤ t) :
    eta ℓ ((t : ℤ) - 1) / eta ℓ ((S : ℤ) - 1) = ((S : ℝ) - 1 + ℓ) / (((t - 1 : ℕ) : ℝ) + ℓ) := by
  rw [eta_pred, eta_pred]
  have hℓr : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hSr : (1 : ℝ) ≤ S := by exact_mod_cast hS
  have htr : (1 : ℝ) ≤ t := by exact_mod_cast ht
  rw [Nat.cast_sub ht]
  have h1 : (0 : ℝ) < (t : ℝ) - 1 + ℓ := by linarith
  have h2 : (0 : ℝ) < (S : ℝ) - 1 + ℓ := by linarith
  push_cast
  field_simp

/-- **Theorem 3.2**, the first claim. -/
theorem pd_rate_one_bound {C : Set E} {f : E → ℝ} {M : ℝ} {ℓ : ℕ} {x v : ℕ → E} {xStar : E}
    (hconv : ConvexOn ℝ C f) (hdiff : ∀ y ∈ C, DifferentiableAt ℝ f y)
    (hxs : xStar ∈ minimizers C f) (hM : 0 < M) (hℓ : 1 ≤ ℓ) (hg : IsStrongGrowth C f M 1)
    (hrun : IsFWRun C (fderiv ℝ f) x v (fun t => eta ℓ t)) (S : ℕ)
    (hS : S = max 1 ⌈(ℓ : ℝ) * M / 2 - ℓ⌉₊) :
    ∀ t : ℕ, S ≤ t → pdGap f x v t ≤ pdGap f x v S *
      (eta ℓ ((t : ℤ) - 1) / eta ℓ ((S : ℤ) - 1)) ^ ℓ * Real.exp (M * ℓ ^ 2 / (2 * S)) := by
  have hmem := Lemmata.FrankWolfe.Proof.fw_run_mem C _ x v _ hconv.1 hrun
  have hS1 : 1 ≤ S := by rw [hS]; exact le_max_left _ _
  have hℓr : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hSr : (1 : ℝ) ≤ S := by exact_mod_cast hS1
  have hηM : ∀ i, S ≤ i → eta ℓ i * M / 2 ≤ 1 := by
    intro i hi
    apply eta_mul_le hℓ one_pos
    have h1 : ⌈(ℓ : ℝ) * M / 2 - ℓ⌉₊ ≤ i := le_trans (by rw [hS]; exact le_max_right _ _) hi
    have h2 := Nat.le_ceil ((ℓ : ℝ) * M / 2 - ℓ)
    have h3 : ((⌈(ℓ : ℝ) * M / 2 - ℓ⌉₊ : ℕ) : ℝ) ≤ i := by exact_mod_cast h1
    rw [mul_one]; linarith
  set c : ℕ → ℝ := fun i => 1 - eta ℓ i + eta ℓ i ^ 2 * M / 2 with hcdef
  have hc0 : ∀ i, 0 ≤ c i := by
    intro i
    have := eta_mem ℓ hℓ i
    have : 0 ≤ eta ℓ i ^ 2 * M / 2 := by positivity
    simp only [hcdef]; linarith [(eta_mem ℓ hℓ i).2]
  have hrec : ∀ i, S ≤ i → pdGap f x v (i + 1) ≤ c i * pdGap f x v i := by
    intro i hi
    have h1 := pd_step hrun i
    obtain ⟨hvC, hvmin, hγ, hx⟩ := hrun.2 i
    have h3 := hg (x i) (hmem i) (v i) hvC hvmin (eta ℓ i) hγ
    rw [Real.rpow_one, ← hx] at h3
    have h4 := pd_le_gap f x v i
    have hneg : eta ℓ i * (eta ℓ i * M / 2 - 1) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hγ.1 (by linarith [hηM i hi])
    have h5 := mul_le_mul_of_nonpos_left h4 hneg
    simp only [hcdef]
    nlinarith
  have hprod : ∀ t, S ≤ t → pdGap f x v t ≤ pdGap f x v S * ∏ i ∈ Finset.Ico S t, c i := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => simp
    | succ t ht ih =>
      rw [Finset.prod_Ico_succ_top ht]
      calc pdGap f x v (t + 1) ≤ c t * pdGap f x v t := hrec t ht
        _ ≤ c t * (pdGap f x v S * ∏ i ∈ Finset.Ico S t, c i) :=
            mul_le_mul_of_nonneg_left ih (hc0 t)
        _ = pdGap f x v S * ((∏ i ∈ Finset.Ico S t, c i) * c t) := by ring
  have hpdS : 0 ≤ pdGap f x v S := pd_nonneg hconv hdiff hxs hrun S
  have hηS : 0 < eta ℓ ((S : ℤ) - 1) := by
    rw [eta_pred]; apply div_pos (by positivity); linarith
  intro t ht
  refine le_trans (hprod t ht) ?_
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hpdS
  have hexp1 : 1 ≤ Real.exp (M * ℓ ^ 2 / (2 * S)) := Real.one_le_exp (by positivity)
  rcases eq_or_lt_of_le ht with heq | hlt
  · subst heq
    rw [Finset.Ico_self, Finset.prod_empty, div_self hηS.ne', one_pow, one_mul]
    exact hexp1
  · have hIco : Finset.Ico S t = Finset.Icc S (t - 1) := by
      ext i; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega
    rw [hIco]
    have hfac : ∀ i ∈ Finset.Icc S (t - 1),
        c i = (1 - eta ℓ i) * (1 + (ℓ : ℝ) * M / 2 * (1 / (i : ℝ) - 1 / ((i : ℝ) + ℓ))) := by
      intro i hi
      have hi1 : (1 : ℝ) ≤ i := by exact_mod_cast le_trans hS1 (Finset.mem_Icc.mp hi).1
      simp only [hcdef]
      rw [eta_nat]
      have : (0 : ℝ) < (i : ℝ) + ℓ := by positivity
      have : (0 : ℝ) < i := by linarith
      field_simp
      ring
    rw [Finset.prod_congr rfl hfac, Finset.prod_mul_distrib]
    have hP := product_bound_closed ℓ S hℓ hS1 (t - 1) (by omega)
    have hsum := sum_inv_sub_le ℓ S hℓ hS1 (t - 1) (by omega)
    have hnn : ∀ i ∈ Finset.Icc S (t - 1),
        0 ≤ (ℓ : ℝ) * M / 2 * (1 / (i : ℝ) - 1 / ((i : ℝ) + ℓ)) := by
      intro i hi
      have hi1 : (1 : ℝ) ≤ i := by exact_mod_cast le_trans hS1 (Finset.mem_Icc.mp hi).1
      apply mul_nonneg (by positivity)
      rw [sub_nonneg]
      apply div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
    have hE : ∏ i ∈ Finset.Icc S (t - 1), (1 + (ℓ : ℝ) * M / 2 * (1 / (i : ℝ) - 1 / ((i : ℝ) + ℓ)))
        ≤ Real.exp (M * ℓ ^ 2 / (2 * S)) := by
      refine le_trans (prod_one_add_le_exp hnn) (Real.exp_le_exp.mpr ?_)
      rw [← Finset.mul_sum]
      have h2 : (ℓ : ℝ) * (1 / (S : ℝ) - 1 / (((t - 1 : ℕ) : ℝ) + 1)) ≤ ℓ / S := by
        have : 0 ≤ (ℓ : ℝ) * (1 / (((t - 1 : ℕ) : ℝ) + 1)) := by positivity
        have e : (ℓ : ℝ) * (1 / (S : ℝ) - 1 / (((t - 1 : ℕ) : ℝ) + 1)) =
            ℓ / S - ℓ * (1 / (((t - 1 : ℕ) : ℝ) + 1)) := by ring
        linarith
      have h3 := mul_le_mul_of_nonneg_left (le_trans hsum h2) (by positivity : (0 : ℝ) ≤ ℓ * M / 2)
      have e : (ℓ : ℝ) * M / 2 * (ℓ / S) = M * ℓ ^ 2 / (2 * S) := by field_simp
      linarith
    have hratio := eta_pred_ratio ℓ S t hℓ hS1 (by omega)
    rw [hratio]
    have hq : 0 ≤ ((S : ℝ) - 1 + ℓ) / (((t - 1 : ℕ) : ℝ) + ℓ) := by
      apply div_nonneg (by linarith) (by positivity)
    exact mul_le_mul hP hE (Finset.prod_nonneg fun i hi => by linarith [hnn i hi]) (by positivity)

/-- The index `R = ⌊(t + ℓ)/c⌋ - ℓ` of the proofs of Theorems 3.2 and 3.4. -/
theorem floor_choice (ℓ t A : ℕ) {c : ℝ} (hc : 1 ≤ c) (h : c * ((A : ℝ) + ℓ) ≤ t + ℓ) :
    ∃ R : ℕ, A ≤ R ∧ R ≤ t ∧ c * ((R : ℝ) + ℓ) ≤ t + ℓ ∧ (t : ℝ) + ℓ < c * ((R : ℝ) + ℓ + 1) := by
  have hc0 : 0 < c := by linarith
  have hq0 : 0 ≤ ((t : ℝ) + ℓ) / c := by positivity
  have hfl : ((A + ℓ : ℕ) : ℝ) ≤ ((t : ℝ) + ℓ) / c := by
    push_cast; rw [le_div_iff₀ hc0]; linarith
  have hA : A + ℓ ≤ ⌊((t : ℝ) + ℓ) / c⌋₊ := Nat.le_floor hfl
  refine ⟨⌊((t : ℝ) + ℓ) / c⌋₊ - ℓ, by omega, ?_, ?_, ?_⟩
  · have h1 : (⌊((t : ℝ) + ℓ) / c⌋₊ : ℝ) ≤ ((t : ℝ) + ℓ) / c := Nat.floor_le hq0
    have h2 : ((t : ℝ) + ℓ) / c ≤ (t : ℝ) + ℓ := div_le_self (by positivity) hc
    have h3 : (⌊((t : ℝ) + ℓ) / c⌋₊ : ℝ) ≤ (t : ℝ) + ℓ := le_trans h1 h2
    have : ⌊((t : ℝ) + ℓ) / c⌋₊ ≤ t + ℓ := by exact_mod_cast h3
    omega
  · have h1 : (⌊((t : ℝ) + ℓ) / c⌋₊ : ℝ) ≤ ((t : ℝ) + ℓ) / c := Nat.floor_le hq0
    have e : ((⌊((t : ℝ) + ℓ) / c⌋₊ - ℓ : ℕ) : ℝ) + ℓ = (⌊((t : ℝ) + ℓ) / c⌋₊ : ℝ) := by
      rw [Nat.cast_sub (by omega)]; ring
    rw [e]
    rw [le_div_iff₀ hc0] at h1; linarith
  · have h1 := Nat.lt_floor_add_one (((t : ℝ) + ℓ) / c)
    have e : ((⌊((t : ℝ) + ℓ) / c⌋₊ - ℓ : ℕ) : ℝ) + ℓ + 1 = (⌊((t : ℝ) + ℓ) / c⌋₊ : ℝ) + 1 := by
      rw [Nat.cast_sub (by omega)]; ring
    rw [e]
    rw [div_lt_iff₀ hc0] at h1; linarith

/-- `(η_{R-1}/η_{t-1})^k ≤ c^k e^{2k/ℓ}` when `t + ℓ < c (R + ℓ + 1)` and `R ≥ 1`. -/
theorem ratio_le (ℓ R t : ℕ) {c k : ℝ} (hℓ : 1 ≤ ℓ) (hR : 1 ≤ R) (ht : 1 ≤ t) (hk : 0 ≤ k)
    (hc : 0 < c) (h : (t : ℝ) + ℓ < c * ((R : ℝ) + ℓ + 1)) :
    (eta ℓ ((R : ℤ) - 1) / eta ℓ ((t : ℤ) - 1)) ^ k ≤ c ^ k * Real.exp (2 * k / ℓ) := by
  have hℓr : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hRr : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have htr : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have e : eta ℓ ((R : ℤ) - 1) / eta ℓ ((t : ℤ) - 1) = ((t : ℝ) - 1 + ℓ) / ((R : ℝ) - 1 + ℓ) := by
    rw [eta_pred, eta_pred]
    have h1 : (0 : ℝ) < (t : ℝ) - 1 + ℓ := by linarith
    have h2 : (0 : ℝ) < (R : ℝ) - 1 + ℓ := by linarith
    field_simp
  have hpos : (0 : ℝ) < (R : ℝ) - 1 + ℓ := by linarith
  have hle : ((t : ℝ) - 1 + ℓ) / ((R : ℝ) - 1 + ℓ) ≤ c * (1 + 2 / (ℓ : ℝ)) := by
    rw [div_le_iff₀ hpos]
    have h1 : c * ((R : ℝ) + ℓ + 1) = c * (((R : ℝ) - 1 + ℓ) + 2) := by ring
    have h2 : (2 : ℝ) ≤ 2 / ℓ * ((R : ℝ) - 1 + ℓ) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]; nlinarith
    nlinarith
  rw [e]
  calc (((t : ℝ) - 1 + ℓ) / ((R : ℝ) - 1 + ℓ)) ^ k ≤ (c * (1 + 2 / (ℓ : ℝ))) ^ k :=
        Real.rpow_le_rpow (by apply div_nonneg (by linarith) hpos.le) hle hk
    _ = c ^ k * (1 + 2 / (ℓ : ℝ)) ^ k := Real.mul_rpow hc.le (by positivity)
    _ ≤ c ^ k * Real.exp (2 * k / ℓ) :=
        mul_le_mul_of_nonneg_left (one_add_two_div_rpow_le ℓ hℓ hk) (by positivity)

/-- `ℓ ∑_{j=R}^{t} 1/(j + ℓ) ≥ ℓ log c` when `c (R + ℓ) ≤ t + ℓ`. -/
theorem sum_eta_ge (ℓ R t : ℕ) {c : ℝ} (hℓ : 1 ≤ ℓ) (hRt : R ≤ t) (hc : 0 < c)
    (h : c * ((R : ℝ) + ℓ) ≤ t + ℓ) :
    ℓ * Real.log c ≤ ∑ j ∈ Finset.Icc R t, eta ℓ j := by
  have hℓr : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hlog := log_le_sum_inv ℓ R hℓ t hRt
  have hR0 : (0 : ℝ) < (R : ℝ) + ℓ := by positivity
  have hc' : c ≤ ((t : ℝ) + ℓ + 1) / ((R : ℝ) + ℓ) := by
    rw [le_div_iff₀ hR0]; linarith
  have h1 : Real.log c ≤ Real.log (((t : ℝ) + ℓ + 1) / ((R : ℝ) + ℓ)) :=
    Real.log_le_log hc hc'
  have e : ∑ j ∈ Finset.Icc R t, eta ℓ j = ℓ * ∑ j ∈ Finset.Icc R t, 1 / ((j : ℝ) + ℓ) := by
    rw [Finset.mul_sum]; congr 1; ext j; rw [eta_nat]; ring
  rw [e]
  exact mul_le_mul_of_nonneg_left (le_trans h1 hlog) (by positivity)

/-- **Theorem 3.2**, the second claim, with the threshold of the formal statement. -/
theorem gap_rate_one_bound {C : Set E} {f : E → ℝ} {M : ℝ} {ℓ : ℕ} {x v : ℕ → E} {xStar : E}
    (hconv : ConvexOn ℝ C f) (hdiff : ∀ y ∈ C, DifferentiableAt ℝ f y)
    (hxs : xStar ∈ minimizers C f) (hM : 0 < M) (hℓ : 1 ≤ ℓ) (hg : IsStrongGrowth C f M 1)
    (hrun : IsFWRun C (fderiv ℝ f) x v (fun t => eta ℓ t)) (S : ℕ)
    (hS : S = max 1 ⌈(ℓ : ℝ) * M / 2 - ℓ⌉₊) :
    ∀ ε ∈ Set.Ioo (0 : ℝ) 1, ∀ t : ℕ,
      Real.exp (1 / ℓ) * ((max S ⌈(ℓ : ℝ) * M / (2 * (1 - ε)) - ℓ⌉₊ : ℕ) + ℓ) ≤ t + ℓ →
      minGap f x v t ≤ pdGap f x v S * (eta ℓ ((t : ℤ) - 1) / eta ℓ ((S : ℤ) - 1)) ^ ℓ *
        Real.exp (3 + M * ℓ ^ 2 / (2 * S)) / ε := by
  intro ε hε t ht
  obtain ⟨hε0, hε1⟩ := hε
  have hmem := Lemmata.FrankWolfe.Proof.fw_run_mem C _ x v _ hconv.1 hrun
  have hℓr : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hS1 : 1 ≤ S := by rw [hS]; exact le_max_left _ _
  set c := Real.exp (1 / ℓ) with hc
  have hc1 : 1 ≤ c := Real.one_le_exp (by positivity)
  obtain ⟨R, hR₀, hRt, hRle, hRlt⟩ := floor_choice ℓ t _ hc1 ht
  have hRS : S ≤ R := le_trans (le_max_left _ _) hR₀
  have hR1 : 1 ≤ R := le_trans hS1 hRS
  have hηM : ∀ i, R ≤ i → eta ℓ i * M / 2 ≤ 1 - ε := by
    intro i hi
    apply eta_mul_le hℓ (by linarith)
    have h1 : ⌈(ℓ : ℝ) * M / (2 * (1 - ε)) - ℓ⌉₊ ≤ i :=
      le_trans (le_max_right _ _) (le_trans hR₀ hi)
    have h2 := Nat.le_ceil ((ℓ : ℝ) * M / (2 * (1 - ε)) - ℓ)
    have h3 : ((⌈(ℓ : ℝ) * M / (2 * (1 - ε)) - ℓ⌉₊ : ℕ) : ℝ) ≤ i := by exact_mod_cast h1
    linarith
  have hdec : ∀ i, R ≤ i → pdGap f x v (i + 1) ≤
      pdGap f x v i - ε * (eta ℓ i * fderiv ℝ f (x i) (x i - v i)) := by
    intro i hi
    have h1 := pd_step hrun i
    obtain ⟨hvC, hvmin, hγ, hx⟩ := hrun.2 i
    have h3 := hg (x i) (hmem i) (v i) hvC hvmin (eta ℓ i) hγ
    rw [Real.rpow_one, ← hx] at h3
    have hg0 := gap_nonneg hconv.1 hrun i
    have h4 : eta ℓ i * fderiv ℝ f (x i) (x i - v i) * (eta ℓ i * M / 2) ≤
        eta ℓ i * fderiv ℝ f (x i) (x i - v i) * (1 - ε) :=
      mul_le_mul_of_nonneg_left (hηM i hi) (mul_nonneg hγ.1 hg0)
    nlinarith
  have hsum : ∀ s, R ≤ s → pdGap f x v (s + 1) ≤
      pdGap f x v R - ε * ∑ j ∈ Finset.Icc R s, eta ℓ j * fderiv ℝ f (x j) (x j - v j) := by
    intro s hs
    induction s, hs using Nat.le_induction with
    | base =>
      rw [Finset.Icc_self, Finset.sum_singleton]; exact hdec R le_rfl
    | succ s hs ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      have := hdec (s + 1) (by omega)
      nlinarith
  set m := minGap f x v t with hm
  have hm0 : 0 ≤ m := by
    rw [hm]; unfold minGap
    exact Finset.le_inf' _ _ (fun k _ => gap_nonneg hconv.1 hrun k)
  have hsig : m * ∑ j ∈ Finset.Icc R t, eta ℓ j ≤
      ∑ j ∈ Finset.Icc R t, eta ℓ j * fderiv ℝ f (x j) (x j - v j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have := minGap_le f x v (Finset.mem_Icc.mp hj).2
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left this (eta_mem ℓ hℓ j).1
  have hηsum : 1 ≤ ∑ j ∈ Finset.Icc R t, eta ℓ j := by
    have := sum_eta_ge ℓ R t hℓ hRt (by positivity) hRle
    rw [hc, Real.log_exp] at this
    have e : (ℓ : ℝ) * (1 / ℓ) = 1 := by field_simp
    linarith
  have hfin := hsum t hRt
  have hpd0 := pd_nonneg hconv hdiff hxs hrun (t + 1)
  have hmR : ε * m ≤ pdGap f x v R := by
    have : ε * m ≤ ε * (m * ∑ j ∈ Finset.Icc R t, eta ℓ j) := by
      apply mul_le_mul_of_nonneg_left _ hε0.le
      nlinarith
    nlinarith
  have hpdR := pd_rate_one_bound hconv hdiff hxs hM hℓ hg hrun S hS R hRS
  have hpdS := pd_nonneg hconv hdiff hxs hrun S
  -- `(η_{R-1}/η_{S-1})^ℓ ≤ e³ (η_{t-1}/η_{S-1})^ℓ`
  have hratio := ratio_le ℓ R t hℓ hR1 (le_trans hR1 hRt) (by positivity : (0 : ℝ) ≤ ℓ)
    (by positivity) hRlt
  have hcℓ : c ^ (ℓ : ℝ) * Real.exp (2 * ℓ / ℓ) = Real.exp 3 := by
    rw [hc, ← Real.exp_mul, ← Real.exp_add]; congr 1; field_simp; ring
  rw [hcℓ, Real.rpow_natCast] at hratio
  have hηS : 0 < eta ℓ ((S : ℤ) - 1) := by
    rw [eta_pred]; have : (1 : ℝ) ≤ S := by exact_mod_cast hS1
    apply div_pos (by positivity); linarith
  have hηt : 0 < eta ℓ ((t : ℤ) - 1) := by
    rw [eta_pred]; have : (1 : ℝ) ≤ t := by exact_mod_cast le_trans hR1 hRt
    apply div_pos (by positivity); linarith
  have hsplit : (eta ℓ ((R : ℤ) - 1) / eta ℓ ((S : ℤ) - 1)) ^ ℓ =
      (eta ℓ ((R : ℤ) - 1) / eta ℓ ((t : ℤ) - 1)) ^ ℓ *
        (eta ℓ ((t : ℤ) - 1) / eta ℓ ((S : ℤ) - 1)) ^ ℓ := by
    rw [← mul_pow]; congr 1; field_simp
  have hb : (eta ℓ ((R : ℤ) - 1) / eta ℓ ((S : ℤ) - 1)) ^ ℓ ≤
      Real.exp 3 * (eta ℓ ((t : ℤ) - 1) / eta ℓ ((S : ℤ) - 1)) ^ ℓ := by
    rw [hsplit]; exact mul_le_mul_of_nonneg_right hratio (by positivity)
  rw [le_div_iff₀ hε0, Real.exp_add]
  calc m * ε = ε * m := by ring
    _ ≤ pdGap f x v R := hmR
    _ ≤ pdGap f x v S * (eta ℓ ((R : ℤ) - 1) / eta ℓ ((S : ℤ) - 1)) ^ ℓ *
          Real.exp (M * ℓ ^ 2 / (2 * S)) := hpdR
    _ ≤ pdGap f x v S * (Real.exp 3 * (eta ℓ ((t : ℤ) - 1) / eta ℓ ((S : ℤ) - 1)) ^ ℓ) *
          Real.exp (M * ℓ ^ 2 / (2 * S)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left hb hpdS
    _ = _ := by ring

end Lemmata.FWAffineOpenLoop
