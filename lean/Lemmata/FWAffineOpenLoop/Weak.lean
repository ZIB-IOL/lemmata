module

public import Lemmata.FWAffineOpenLoop.StrongR

@[expose] public section

/-!
# Weak growth: Theorem 4.1 and Lemma 4.2

With the threshold `T_i = (η_i ℓM/(2ε))^{1/(1-r)}`, a step whose primal gap is at most `T_i` leaves
a primal gap of at most `T_i + η_i² M/2` (strong `(M, 0)`-growth), and every other step contracts
the primal gap by `1 - (1 - ε/ℓ) η_i` (weak `(M, r)`-growth). The argument of Theorem 3.4 then runs
on primal gaps instead of best duality gaps.
-/

namespace Lemmata.FWAffineOpenLoop

open Lemmata.FrankWolfe Lemmata.FWOpenLoop

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The primal gap is at most the Frank–Wolfe gap. -/
theorem subopt_le_gap {C : Set E} {f : E → ℝ} {x v : ℕ → E} {γ : ℕ → ℝ} {xStar : E}
    (hconv : ConvexOn ℝ C f) (hdiff : ∀ y ∈ C, DifferentiableAt ℝ f y)
    (hxs : xStar ∈ minimizers C f) (hrun : IsFWRun C (fderiv ℝ f) x v γ) (t : ℕ) :
    f (x t) - f xStar ≤ fderiv ℝ f (x t) (x t - v t) := by
  have h := pd_ge_subopt hconv hdiff hxs hrun t
  exact le_trans h (pd_le_gap f x v t)

/-- A step below the threshold, under strong `(M, 0)`-growth. -/
theorem weak_small_step {C : Set E} {f : E → ℝ} {M : ℝ} {ℓ : ℕ} {x v : ℕ → E} {xStar : E}
    (hconv : ConvexOn ℝ C f) (hg0 : IsStrongGrowth C f M 0)
    (hrun : IsFWRun C (fderiv ℝ f) x v (fun t => eta ℓ t)) (i : ℕ) :
    f (x (i + 1)) - f xStar ≤ (f (x i) - f xStar) + eta ℓ i ^ 2 * M / 2 := by
  have hmem := Lemmata.FrankWolfe.Proof.fw_run_mem C _ x v _ hconv.1 hrun
  have h1 := f_step hrun i
  obtain ⟨hvC, hvmin, hγ, hx⟩ := hrun.2 i
  have h3 := hg0 (x i) (hmem i) (v i) hvC hvmin (eta ℓ i) hγ
  rw [Real.rpow_zero, mul_one, ← hx] at h3
  have hg := gap_nonneg hconv.1 hrun i
  have : 0 ≤ eta ℓ i * fderiv ℝ f (x i) (x i - v i) := mul_nonneg hγ.1 hg
  linarith

/-- A step above the threshold contracts the primal gap, under weak `(M, r)`-growth. -/
theorem weak_big_step {C : Set E} {f : E → ℝ} {M r ε : ℝ} {ℓ : ℕ} {x v : ℕ → E} {xStar : E}
    (hconv : ConvexOn ℝ C f) (hdiff : ∀ y ∈ C, DifferentiableAt ℝ f y)
    (hxs : xStar ∈ minimizers C f) (hM : 0 < M) (hℓ : 1 ≤ ℓ) (hr : r ∈ Set.Ico (0 : ℝ) 1)
    (hε : ε ∈ Set.Ioo (0 : ℝ) ℓ) (hw : IsWeakGrowth C f M r)
    (hrun : IsFWRun C (fderiv ℝ f) x v (fun t => eta ℓ t)) (i : ℕ)
    (hbig : (eta ℓ i * ℓ * M / (2 * ε)) ^ (1 / (1 - r)) < f (x i) - f xStar) :
    f (x (i + 1)) - f xStar ≤ (1 - (1 - ε / ℓ) * eta ℓ i) * (f (x i) - f xStar) := by
  obtain ⟨hr0, hr1⟩ := hr
  obtain ⟨hε0, hεℓ⟩ := hε
  have hmem := Lemmata.FrankWolfe.Proof.fw_run_mem C _ x v _ hconv.1 hrun
  have h1 := f_step hrun i
  obtain ⟨hvC, hvmin, hγ, hx⟩ := hrun.2 i
  have h3 := hw (x i) (hmem i) (v i) hvC hvmin xStar hxs (eta ℓ i) hγ
  rw [← hx] at h3
  have hsg := subopt_le_gap hconv hdiff hxs hrun i
  have hg0 := gap_nonneg hconv.1 hrun i
  set g := fderiv ℝ f (x i) (x i - v i) with hgdef
  set h := f (x i) - f xStar with hh
  set D := bregman f (x (i + 1)) (x i) with hD
  set η := eta ℓ i with hη
  have hηpos : 0 < η := by rw [hη, eta_nat]; positivity
  have hℓr : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have h1r : 0 < 1 - r := by linarith
  set A := η * ℓ * M / (2 * ε) with hA
  have hApos : 0 < A := by positivity
  have hT : (A ^ (1 / (1 - r))) ^ (1 - r) = A := by
    rw [← Real.rpow_mul hApos.le, one_div_mul_cancel h1r.ne', Real.rpow_one]
  have hhA : A ≤ h ^ (1 - r) := by
    rw [← hT]; exact Real.rpow_le_rpow (Real.rpow_nonneg hApos.le _) hbig.le h1r.le
  have hMA : M * η ^ 2 / 2 = A * (ε / ℓ * η) := by rw [hA]; field_simp
  have hDle : D ≤ ε / ℓ * η * g := by
    rcases le_or_gt D 0 with hDn | hDp
    · have : 0 ≤ ε / ℓ * η * g := by positivity
      linarith
    · have h4 : D * A ≤ D * h ^ (1 - r) := mul_le_mul_of_nonneg_left hhA hDp.le
      have h5 : D * A ≤ A * (ε / ℓ * η * g) := by
        calc D * A ≤ D * h ^ (1 - r) := h4
          _ ≤ M * η ^ 2 / 2 * g := h3
          _ = A * (ε / ℓ * η * g) := by rw [hMA]; ring
      have := le_of_mul_le_mul_left (by linarith [h5] : A * D ≤ A * (ε / ℓ * η * g)) hApos
      linarith
  have hcoef : 0 ≤ (1 - ε / ℓ) * η := by
    apply mul_nonneg _ hηpos.le
    rw [sub_nonneg, div_le_one hℓr]; exact hεℓ.le
  have := mul_le_mul_of_nonneg_left hsg hcoef
  nlinarith

/-- `h_1 ≤ M/2` under strong `(M, 0)`-growth. -/
theorem subopt_one_le {C : Set E} {f : E → ℝ} {M : ℝ} {ℓ : ℕ} {x v : ℕ → E} {xStar : E}
    (hconv : ConvexOn ℝ C f) (hdiff : ∀ y ∈ C, DifferentiableAt ℝ f y)
    (hxs : xStar ∈ minimizers C f) (hℓ : 1 ≤ ℓ) (hg0 : IsStrongGrowth C f M 0)
    (hrun : IsFWRun C (fderiv ℝ f) x v (fun t => eta ℓ t)) :
    f (x 1) - f xStar ≤ M / 2 := by
  have hmem := Lemmata.FrankWolfe.Proof.fw_run_mem C _ x v _ hconv.1 hrun
  have h1 := f_step hrun 0
  obtain ⟨hvC, hvmin, hγ, hx⟩ := hrun.2 0
  have h3 := hg0 (x 0) (hmem 0) (v 0) hvC hvmin (eta ℓ ((0 : ℕ) : ℤ)) hγ
  rw [Real.rpow_zero, mul_one] at h3
  simp only [zero_add] at hx h1
  rw [← hx] at h3
  have h0 : eta ℓ ((0 : ℕ) : ℤ) = 1 := by
    rw [eta_nat]; have : (ℓ : ℝ) ≠ 0 := by positivity
    field_simp; ring
  rw [h0] at h1 h3
  have hsg := subopt_le_gap hconv hdiff hxs hrun 0
  linarith

/-- Contraction over a stretch of big steps: `h_s ≤ h_R ∏_{i ∈ [R, s)} c_i`. -/
theorem weak_stretch {C : Set E} {f : E → ℝ} {M r ε : ℝ} {ℓ : ℕ} {x v : ℕ → E} {xStar : E}
    (hconv : ConvexOn ℝ C f) (hdiff : ∀ y ∈ C, DifferentiableAt ℝ f y)
    (hxs : xStar ∈ minimizers C f) (hM : 0 < M) (hℓ : 1 ≤ ℓ) (hr : r ∈ Set.Ico (0 : ℝ) 1)
    (hε : ε ∈ Set.Ioo (0 : ℝ) ℓ) (hw : IsWeakGrowth C f M r)
    (hrun : IsFWRun C (fderiv ℝ f) x v (fun t => eta ℓ t)) (R N : ℕ)
    (hbig : ∀ i, R ≤ i → i < N → (eta ℓ i * ℓ * M / (2 * ε)) ^ (1 / (1 - r)) < f (x i) - f xStar) :
    ∀ s, R ≤ s → s ≤ N → f (x s) - f xStar ≤
      (f (x R) - f xStar) * ∏ i ∈ Finset.Ico R s, (1 - (1 - ε / ℓ) * eta ℓ i) := by
  have hc0 : ∀ i : ℕ, 0 ≤ 1 - (1 - ε / ℓ) * eta ℓ i := by
    intro i
    have h0 : 0 ≤ ε / ℓ := by have := hε.1; positivity
    have h1 : 1 - ε / ℓ ≤ 1 := by linarith
    have := mul_le_mul h1 (eta_mem ℓ hℓ i).2 (eta_mem ℓ hℓ i).1 zero_le_one
    linarith
  intro s hs
  induction s, hs using Nat.le_induction with
  | base => intro _; simp
  | succ s hs ih =>
    intro hsN
    rw [Finset.prod_Ico_succ_top hs]
    have h1 := weak_big_step hconv hdiff hxs hM hℓ hr hε hw hrun s (hbig s hs (by omega))
    calc f (x (s + 1)) - f xStar ≤ (1 - (1 - ε / ℓ) * eta ℓ s) * (f (x s) - f xStar) := h1
      _ ≤ (1 - (1 - ε / ℓ) * eta ℓ s) * ((f (x R) - f xStar) *
            ∏ i ∈ Finset.Ico R s, (1 - (1 - ε / ℓ) * eta ℓ i)) :=
          mul_le_mul_of_nonneg_left (ih (by omega)) (hc0 s)
      _ = _ := by ring

/-- The product over `[R, t)` with Lemma 3.5. -/
theorem stretch_prod_le {ℓ R t : ℕ} {ε : ℝ} (hℓ : 1 ≤ ℓ) (hR : 1 ≤ R) (hRt : R ≤ t)
    (hε : ε ∈ Set.Ioo (0 : ℝ) ℓ) :
    ∏ i ∈ Finset.Ico R t, (1 - (1 - ε / ℓ) * eta ℓ i) ≤
      (eta ℓ ((t : ℤ) - 1) / eta ℓ ((R : ℤ) - 1)) ^ ((ℓ : ℝ) - ε) * Real.exp (ε * ℓ / R) := by
  rcases eq_or_lt_of_le hRt with heq | hlt
  · subst heq
    rw [Finset.Ico_self, Finset.prod_empty, div_self (eta_pos_nat ℓ hℓ R hR).ne', Real.one_rpow,
      one_mul]
    exact Real.one_le_exp (by have := hε.1; positivity)
  · have hIco : Finset.Ico R t = Finset.Icc R (t - 1) := by
      ext i; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega
    rw [hIco]
    have h := product_bound_eps_closed ℓ R (t - 1) ε hℓ hR (by omega) ⟨hε.1.le, hε.2.le⟩
    rwa [← eta_pred_ratio ℓ R t hℓ hR (by omega)] at h

/-- **Theorem 4.1**, the rate. -/
theorem weak_rate_bound {C : Set E} {f : E → ℝ} {M r ε : ℝ} {ℓ : ℕ} {x v : ℕ → E} {xStar : E}
    (hconv : ConvexOn ℝ C f) (hdiff : ∀ y ∈ C, DifferentiableAt ℝ f y)
    (hxs : xStar ∈ minimizers C f) (hM : 0 < M) (hℓ : 1 ≤ ℓ) (hr : r ∈ Set.Ico (0 : ℝ) 1)
    (hε : ε ∈ Set.Ioo (0 : ℝ) ℓ) (hg0 : IsStrongGrowth C f M 0) (hw : IsWeakGrowth C f M r)
    (hrun : IsFWRun C (fderiv ℝ f) x v (fun t => eta ℓ t)) :
    ∀ t : ℕ, 1 ≤ t → f (x t) - f xStar ≤ Real.exp (ε * ℓ) *
      max (eta ℓ ((t : ℤ) - 1) ^ ((ℓ : ℝ) - ε) * (M / 2))
        (eta ℓ ((t : ℤ) - 1) ^ (min ((ℓ : ℝ) - ε) (min (1 / (1 - r)) 2)) *
          ((ℓ * M / (2 * ε)) ^ (1 / (1 - r)) + M / 2)) := by
  obtain ⟨hr0, hr1⟩ := hr
  obtain ⟨hε0, hεℓ⟩ := hε
  have hmem := Lemmata.FrankWolfe.Proof.fw_run_mem C _ x v _ hconv.1 hrun
  have h1r : 0 < 1 - r := by linarith
  set a : ℝ := 1 / (1 - r) with ha
  have ha0 : 0 < a := by positivity
  set X : ℝ := ℓ * M / (2 * ε) with hX
  have hX0 : 0 ≤ X := by positivity
  set c : ℕ → ℝ := fun i => 1 - (1 - ε / ℓ) * eta ℓ i with hc
  have hc0 : ∀ i, 0 ≤ c i := by
    intro i
    have h0 : 0 ≤ ε / ℓ := by positivity
    have h1 : 1 - ε / ℓ ≤ 1 := by linarith
    have := mul_le_mul h1 (eta_mem ℓ hℓ i).2 (eta_mem ℓ hℓ i).1 zero_le_one
    simp only [hc]; linarith
  set term : ℕ → ℝ := fun R => if R = 1 then f (x 1) - f xStar else
    (eta ℓ ((R - 1 : ℕ) : ℤ) * ℓ * M / (2 * ε)) ^ a + eta ℓ ((R - 1 : ℕ) : ℤ) ^ 2 * M / 2 with hterm
  have hinv : ∀ t, 1 ≤ t → ∃ R, 1 ≤ R ∧ R ≤ t ∧
      f (x t) - f xStar ≤ term R * ∏ i ∈ Finset.Ico R t, c i := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => exact ⟨1, le_rfl, le_rfl, by simp [hterm]⟩
    | succ t ht ih =>
      obtain ⟨R, hR1, hRt, hR⟩ := ih
      by_cases hsmall : f (x t) - f xStar ≤ (eta ℓ t * ℓ * M / (2 * ε)) ^ a
      · refine ⟨t + 1, by omega, le_rfl, ?_⟩
        rw [Finset.Ico_self, Finset.prod_empty, mul_one]
        simp only [hterm, show t + 1 ≠ 1 by omega, ↓reduceIte, Nat.add_sub_cancel]
        have := weak_small_step (xStar := xStar) hconv hg0 hrun t
        linarith
      · refine ⟨R, hR1, by omega, ?_⟩
        rw [Finset.prod_Ico_succ_top hRt]
        have h := weak_big_step hconv hdiff hxs hM hℓ ⟨hr0, hr1⟩ ⟨hε0, hεℓ⟩ hw hrun t
          (lt_of_not_ge hsmall)
        calc f (x (t + 1)) - f xStar ≤ c t * (f (x t) - f xStar) := h
          _ ≤ c t * (term R * ∏ i ∈ Finset.Ico R t, c i) := mul_le_mul_of_nonneg_left hR (hc0 t)
          _ = term R * ((∏ i ∈ Finset.Ico R t, c i) * c t) := by ring
  intro t ht
  obtain ⟨R, hR1, hRt, hR⟩ := hinv t ht
  set q := eta ℓ ((t : ℤ) - 1) with hq
  have hq0 : 0 < q := eta_pos_nat ℓ hℓ t ht
  set p := eta ℓ ((R : ℤ) - 1) with hp
  have hp0 : 0 < p := eta_pos_nat ℓ hℓ R hR1
  have hp1 : p ≤ 1 := eta_pred_le_one ℓ hℓ R hR1
  have hqp : q ≤ p := eta_pred_anti ℓ hℓ hR1 hRt
  have hprod := stretch_prod_le hℓ hR1 hRt ⟨hε0, hεℓ⟩
  have hexpR : Real.exp (ε * ℓ / R) ≤ Real.exp (ε * ℓ) := by
    apply Real.exp_le_exp.mpr
    have : (1 : ℝ) ≤ R := by exact_mod_cast hR1
    exact div_le_self (by positivity) this
  have hprod' : ∏ i ∈ Finset.Ico R t, c i ≤ (q / p) ^ ((ℓ : ℝ) - ε) * Real.exp (ε * ℓ) :=
    le_trans hprod (mul_le_mul_of_nonneg_left hexpR (by positivity))
  have hexp0 : 0 < Real.exp (ε * ℓ) := Real.exp_pos _
  by_cases hR1' : R = 1
  · subst hR1'
    simp only [hterm, ↓reduceIte] at hR
    have hp1' : p = 1 := by
      rw [hp]; simp only [eta]; push_cast
      have : (ℓ : ℝ) ≠ 0 := by positivity
      field_simp; ring
    rw [hp1', div_one] at hprod'
    have h1 := subopt_one_le hconv hdiff hxs hℓ hg0 hrun
    have h1' : 0 ≤ f (x 1) - f xStar := sub_nonneg.mpr (hxs.2 _ (hmem 1))
    calc f (x t) - f xStar ≤ (f (x 1) - f xStar) * ∏ i ∈ Finset.Ico 1 t, c i := hR
      _ ≤ (M / 2) * (q ^ ((ℓ : ℝ) - ε) * Real.exp (ε * ℓ)) :=
          mul_le_mul h1 hprod' (Finset.prod_nonneg fun i _ => hc0 i) (by positivity)
      _ = Real.exp (ε * ℓ) * (q ^ ((ℓ : ℝ) - ε) * (M / 2)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_left _ _) hexp0.le
  · simp only [hterm, hR1', ↓reduceIte] at hR
    have hcast : ((R - 1 : ℕ) : ℤ) = (R : ℤ) - 1 := by omega
    rw [hcast] at hR
    set b : ℝ := min a 2 with hb
    have hb0 : 0 < b := lt_min ha0 (by norm_num)
    have hterm' : (p * ℓ * M / (2 * ε)) ^ a + p ^ 2 * M / 2 ≤ p ^ b * (X ^ a + M / 2) := by
      have e : (p * ℓ * M / (2 * ε)) ^ a = p ^ a * X ^ a := by
        rw [← Real.mul_rpow hp0.le hX0]; congr 1; rw [hX]; ring
      rw [e]
      have h1 : p ^ a ≤ p ^ b := Real.rpow_le_rpow_of_exponent_ge hp0 hp1 (min_le_left _ _)
      have h2 : p ^ 2 ≤ p ^ b := by
        rw [← Real.rpow_two]; exact Real.rpow_le_rpow_of_exponent_ge hp0 hp1 (min_le_right _ _)
      have := mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ X ^ a)
      have := mul_le_mul_of_nonneg_right h2 (by positivity : (0 : ℝ) ≤ M / 2)
      nlinarith
    have hmix := rpow_mix_le (a := b) (b := (ℓ : ℝ) - ε) hq0 hqp hp1
    calc f (x t) - f xStar ≤ ((p * ℓ * M / (2 * ε)) ^ a + p ^ 2 * M / 2) *
          ∏ i ∈ Finset.Ico R t, c i := hR
      _ ≤ (p ^ b * (X ^ a + M / 2)) * ((q / p) ^ ((ℓ : ℝ) - ε) * Real.exp (ε * ℓ)) :=
          mul_le_mul hterm' hprod' (Finset.prod_nonneg fun i _ => hc0 i) (by positivity)
      _ = Real.exp (ε * ℓ) * ((p ^ b * (q / p) ^ ((ℓ : ℝ) - ε)) * (X ^ a + M / 2)) := by ring
      _ ≤ Real.exp (ε * ℓ) * (q ^ (min ((ℓ : ℝ) - ε) b) * (X ^ a + M / 2)) := by
          apply mul_le_mul_of_nonneg_left _ hexp0.le
          exact mul_le_mul_of_nonneg_right hmix (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_right _ _) hexp0.le

/-- **Theorem 4.1**, the dichotomy. -/
theorem weak_dichotomy {C : Set E} {f : E → ℝ} {M r ε : ℝ} {ℓ : ℕ} {x v : ℕ → E} {xStar : E}
    (hconv : ConvexOn ℝ C f) (hdiff : ∀ y ∈ C, DifferentiableAt ℝ f y)
    (hxs : xStar ∈ minimizers C f) (hM : 0 < M) (hℓ : 1 ≤ ℓ) (hr : r ∈ Set.Ico (0 : ℝ) 1)
    (hε : ε ∈ Set.Ioo (0 : ℝ) ℓ) (hw : IsWeakGrowth C f M r)
    (hrun : IsFWRun C (fderiv ℝ f) x v (fun t => eta ℓ t)) :
    (∀ T : ℕ, ∃ t, T ≤ t ∧ f (x t) - f xStar ≤ (eta ℓ t * ℓ * M / (2 * ε)) ^ (1 / (1 - r))) ∨
      ∃ R : ℕ, 1 ≤ R ∧ ∀ t : ℕ, R + 1 ≤ t → f (x t) - f xStar ≤ (f (x R) - f xStar) *
        (eta ℓ ((t : ℤ) - 1) / eta ℓ ((R : ℤ) - 1)) ^ ((ℓ : ℝ) - ε) * Real.exp (ε * ℓ / R) := by
  by_cases h : ∀ T : ℕ, ∃ t, T ≤ t ∧
      f (x t) - f xStar ≤ (eta ℓ t * ℓ * M / (2 * ε)) ^ (1 / (1 - r))
  · exact Or.inl h
  right
  push Not at h
  obtain ⟨T, hT⟩ := h
  have hmem := Lemmata.FrankWolfe.Proof.fw_run_mem C _ x v _ hconv.1 hrun
  refine ⟨max T 1, le_max_right _ _, fun t ht => ?_⟩
  set R := max T 1 with hRdef
  have hR1 : 1 ≤ R := le_max_right _ _
  have hstr := weak_stretch hconv hdiff hxs hM hℓ hr hε hw hrun R t
    (fun i hi _ => hT i (le_trans (le_max_left _ _) hi)) t (by omega) le_rfl
  have hprod := stretch_prod_le hℓ hR1 (show R ≤ t by omega) hε
  have hR0 : 0 ≤ f (x R) - f xStar := sub_nonneg.mpr (hxs.2 _ (hmem R))
  calc f (x t) - f xStar ≤ (f (x R) - f xStar) *
        ∏ i ∈ Finset.Ico R t, (1 - (1 - ε / ℓ) * eta ℓ i) := hstr
    _ ≤ (f (x R) - f xStar) * ((eta ℓ ((t : ℤ) - 1) / eta ℓ ((R : ℤ) - 1)) ^ ((ℓ : ℝ) - ε) *
          Real.exp (ε * ℓ / R)) := mul_le_mul_of_nonneg_left hprod hR0
    _ = _ := by ring

/-- **Lemma 4.2.** -/
theorem weak_restart_bound {C : Set E} {f : E → ℝ} {M r ε : ℝ} {ℓ : ℕ} {x v : ℕ → E} {xStar : E}
    (hconv : ConvexOn ℝ C f) (hdiff : ∀ y ∈ C, DifferentiableAt ℝ f y)
    (hxs : xStar ∈ minimizers C f) (hM : 0 < M) (hℓ : 1 ≤ ℓ) (hr : r ∈ Set.Ico (0 : ℝ) 1)
    (_hℓa : 1 / (1 - r) < ℓ) (hε : ε ∈ Set.Ioo (0 : ℝ) (ℓ - 1 / (1 - r)))
    (hw : IsWeakGrowth C f M r) (hrun : IsFWRun C (fderiv ℝ f) x v (fun t => eta ℓ t)) :
    ∀ R : ℕ, 1 ≤ R →
      ∃ i, R ≤ i ∧ i ≤ max R ⌈ℓ * ((f (x R) - f xStar) * eta ℓ R ^ (ε - ℓ) *
          (2 * ε / (ℓ * M)) ^ (1 / (1 - r)) * Real.exp (ε * ℓ / R)) ^
          (1 / (ℓ - ε - 1 / (1 - r))) - ℓ⌉₊ ∧
        f (x i) - f xStar ≤ (eta ℓ i * ℓ * M / (2 * ε)) ^ (1 / (1 - r)) := by
  intro R hR
  obtain ⟨hr0, hr1⟩ := hr
  obtain ⟨hε0, hεa⟩ := hε
  have hmem := Lemmata.FrankWolfe.Proof.fw_run_mem C _ x v _ hconv.1 hrun
  have h1r : 0 < 1 - r := by linarith
  set a : ℝ := 1 / (1 - r) with ha
  have ha0 : 0 < a := by positivity
  have hεℓ : ε < ℓ := by linarith
  have hgap : 0 < (ℓ : ℝ) - ε - a := by linarith
  set e : ℝ := 1 / ((ℓ : ℝ) - ε - a) with he
  have he0 : 0 < e := by positivity
  set X : ℝ := ℓ * M / (2 * ε) with hX
  have hX0 : 0 < X := by positivity
  set hR0 := f (x R) - f xStar with hhR0
  have hRnn : 0 ≤ hR0 := sub_nonneg.mpr (hxs.2 _ (hmem R))
  set Y : ℝ := hR0 * eta ℓ R ^ (ε - ℓ) * (2 * ε / (ℓ * M)) ^ a * Real.exp (ε * ℓ / R) with hY
  set U : ℕ := ⌈ℓ * Y ^ e - ℓ⌉₊ with hU
  set N : ℕ := max R U with hN
  by_contra hcon
  push Not at hcon
  have hRN : R ≤ N := le_max_left _ _
  have hstr := weak_stretch hconv hdiff hxs hM hℓ ⟨hr0, hr1⟩ ⟨hε0, hεℓ⟩ hw hrun R N
    (fun i hi hiN => hcon i hi (le_of_lt hiN)) N hRN le_rfl
  have hprod := stretch_prod_le hℓ hR hRN ⟨hε0, hεℓ⟩
  have hℓr : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hRr : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hNr : (R : ℝ) ≤ N := by exact_mod_cast hRN
  set ηN := eta ℓ (N : ℤ) with hηN
  set ηR := eta ℓ (R : ℤ) with hηR
  have hηN0 : 0 < ηN := by rw [hηN, eta_nat]; positivity
  have hηR0 : 0 < ηR := by rw [hηR, eta_nat]; positivity
  -- `η_{N-1}/η_{R-1} ≤ η_N/η_R`
  have hratio : eta ℓ ((N : ℤ) - 1) / eta ℓ ((R : ℤ) - 1) ≤ ηN / ηR := by
    rw [eta_pred_ratio ℓ R N hℓ hR (le_trans hR hRN), hηN, hηR, eta_nat, eta_nat,
      Nat.cast_sub (le_trans hR hRN)]
    push_cast
    have h1 : (0 : ℝ) < (N : ℝ) - 1 + ℓ := by linarith
    rw [div_le_div_iff₀ h1 (by positivity)]
    field_simp
    nlinarith
  have hratio' : (eta ℓ ((N : ℤ) - 1) / eta ℓ ((R : ℤ) - 1)) ^ ((ℓ : ℝ) - ε) ≤
      (ηN / ηR) ^ ((ℓ : ℝ) - ε) :=
    Real.rpow_le_rpow (div_nonneg (eta_pos_nat ℓ hℓ N (le_trans hR hRN)).le
      (eta_pos_nat ℓ hℓ R hR).le) hratio (by linarith)
  have hstep1 : f (x N) - f xStar ≤ hR0 * (ηN / ηR) ^ ((ℓ : ℝ) - ε) * Real.exp (ε * ℓ / R) := by
    calc f (x N) - f xStar ≤ hR0 * ∏ i ∈ Finset.Ico R N, (1 - (1 - ε / ℓ) * eta ℓ i) := hstr
      _ ≤ hR0 * ((eta ℓ ((N : ℤ) - 1) / eta ℓ ((R : ℤ) - 1)) ^ ((ℓ : ℝ) - ε) *
            Real.exp (ε * ℓ / R)) := mul_le_mul_of_nonneg_left hprod hRnn
      _ ≤ hR0 * ((ηN / ηR) ^ ((ℓ : ℝ) - ε) * Real.exp (ε * ℓ / R)) := by
          apply mul_le_mul_of_nonneg_left _ hRnn
          exact mul_le_mul_of_nonneg_right hratio' (by positivity)
      _ = _ := by ring
  -- `h_R (η_N/η_R)^{ℓ-ε} exp(εℓ/R) = Y η_N^{ℓ-ε} X^a`
  have hrewrite : hR0 * (ηN / ηR) ^ ((ℓ : ℝ) - ε) * Real.exp (ε * ℓ / R) =
      Y * ηN ^ ((ℓ : ℝ) - ε) * X ^ a := by
    have h1 : (2 * ε / (ℓ * M)) ^ a * X ^ a = 1 := by
      rw [← Real.mul_rpow (by positivity) hX0.le, hX]
      have : 2 * ε / (ℓ * M) * (ℓ * M / (2 * ε)) = 1 := by field_simp
      rw [this, Real.one_rpow]
    have h2 : (ηN / ηR) ^ ((ℓ : ℝ) - ε) = ηN ^ ((ℓ : ℝ) - ε) * ηR ^ (ε - ℓ) := by
      rw [Real.div_rpow hηN0.le hηR0.le, div_eq_mul_inv, ← Real.rpow_neg hηR0.le]; ring_nf
    rw [h2, hY]
    calc hR0 * (ηN ^ ((ℓ : ℝ) - ε) * ηR ^ (ε - ℓ)) * Real.exp (ε * ℓ / R)
        = hR0 * ηR ^ (ε - ℓ) * ((2 * ε / (ℓ * M)) ^ a * X ^ a) * Real.exp (ε * ℓ / R) *
            ηN ^ ((ℓ : ℝ) - ε) := by rw [h1]; ring
      _ = _ := by ring
  -- `Y η_N^{ℓ-ε-a} ≤ 1`
  have hY0 : 0 ≤ Y := by rw [hY]; positivity
  have hkey : Y * ηN ^ ((ℓ : ℝ) - ε - a) ≤ 1 := by
    rcases hY0.eq_or_lt with hYz | hYp
    · rw [← hYz, zero_mul]; norm_num
    · have hUr : ℓ * Y ^ e - ℓ ≤ (U : ℝ) := Nat.le_ceil _
      have hUN : (U : ℝ) ≤ N := by exact_mod_cast le_max_right R U
      have hNe : (ℓ : ℝ) * Y ^ e ≤ N + ℓ := by linarith
      have hηNe : ηN ≤ (Y ^ e)⁻¹ := by
        rw [hηN, eta_nat, div_le_iff₀ (by positivity)]
        have hYe : 0 < Y ^ e := Real.rpow_pos_of_pos hYp e
        rw [inv_mul_eq_div, le_div_iff₀ hYe]
        linarith
      have hpow : ηN ^ ((ℓ : ℝ) - ε - a) ≤ ((Y ^ e)⁻¹) ^ ((ℓ : ℝ) - ε - a) :=
        Real.rpow_le_rpow hηN0.le hηNe hgap.le
      have hinv : ((Y ^ e)⁻¹) ^ ((ℓ : ℝ) - ε - a) = Y⁻¹ := by
        rw [Real.inv_rpow (Real.rpow_nonneg hYp.le e), ← Real.rpow_mul hYp.le, he,
          one_div_mul_cancel hgap.ne', Real.rpow_one]
      rw [hinv] at hpow
      calc Y * ηN ^ ((ℓ : ℝ) - ε - a) ≤ Y * Y⁻¹ := mul_le_mul_of_nonneg_left hpow hY0
        _ = 1 := mul_inv_cancel₀ hYp.ne'
  have hfinal : f (x N) - f xStar ≤ (ηN * ℓ * M / (2 * ε)) ^ a := by
    have e1 : ηN ^ ((ℓ : ℝ) - ε) = ηN ^ ((ℓ : ℝ) - ε - a) * ηN ^ a := by
      rw [← Real.rpow_add hηN0]; ring_nf
    have e2 : (ηN * ℓ * M / (2 * ε)) ^ a = ηN ^ a * X ^ a := by
      rw [← Real.mul_rpow hηN0.le hX0.le, hX]; ring_nf
    rw [e2]
    calc f (x N) - f xStar ≤ Y * ηN ^ ((ℓ : ℝ) - ε) * X ^ a := by rw [← hrewrite]; exact hstep1
      _ = (Y * ηN ^ ((ℓ : ℝ) - ε - a)) * (ηN ^ a * X ^ a) := by rw [e1]; ring
      _ ≤ 1 * (ηN ^ a * X ^ a) := mul_le_mul_of_nonneg_right hkey (by positivity)
      _ = ηN ^ a * X ^ a := one_mul _
  exact absurd (hcon N hRN le_rfl) (not_lt.mpr hfinal)

end Lemmata.FWAffineOpenLoop
