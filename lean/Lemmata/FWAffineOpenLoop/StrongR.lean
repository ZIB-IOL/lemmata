module

public import Lemmata.FWAffineOpenLoop.Strong

@[expose] public section

/-!
# Strong `(M, r)`-growth with `r ∈ [0, 1)`: Theorem 3.4

With the threshold `T_i = (η_i ℓM/(2ε))^{1/(1-r)}`, a step whose Frank–Wolfe gap is at most `T_i`
leaves a best duality gap of at most `T_i`, and every other step contracts it by
`c_i = 1 - (1 - ε/ℓ) η_i`. Hence `pd_t` is at most the starting value of its last stretch of
contracting steps times the product of the `c_i`, which Lemma 3.5 bounds.
-/

namespace Lemmata.FWAffineOpenLoop

open Lemmata.FrankWolfe Lemmata.FWOpenLoop

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `p^a (q/p)^b ≤ q^{min(b, a)}` for `0 < q ≤ p ≤ 1`. -/
theorem rpow_mix_le {p q a b : ℝ} (hq : 0 < q) (hqp : q ≤ p) (hp1 : p ≤ 1) :
    p ^ a * (q / p) ^ b ≤ q ^ min b a := by
  have hp : 0 < p := lt_of_lt_of_le hq hqp
  have e : p ^ a * (q / p) ^ b = p ^ (a - b) * q ^ b := by
    rw [Real.div_rpow hq.le hp.le, Real.rpow_sub hp]; field_simp
  rw [e]
  rcases le_total b a with hba | hab
  · rw [min_eq_left hba]
    have : p ^ (a - b) ≤ 1 := Real.rpow_le_one hp.le hp1 (by linarith)
    calc p ^ (a - b) * q ^ b ≤ 1 * q ^ b := mul_le_mul_of_nonneg_right this (by positivity)
      _ = q ^ b := one_mul _
  · rw [min_eq_right hab]
    have : p ^ (a - b) ≤ q ^ (a - b) := Real.rpow_le_rpow_of_nonpos hq hqp (by linarith)
    calc p ^ (a - b) * q ^ b ≤ q ^ (a - b) * q ^ b :=
          mul_le_mul_of_nonneg_right this (by positivity)
      _ = q ^ a := by rw [← Real.rpow_add hq]; ring_nf

/-- The two kinds of steps of Theorem 3.4. -/
theorem strong_r_step {C : Set E} {f : E → ℝ} {M r ε : ℝ} {ℓ : ℕ} {x v : ℕ → E}
    (hC : Convex ℝ C) (hM : 0 < M) (hℓ : 1 ≤ ℓ) (hr : r ∈ Set.Ico (0 : ℝ) 1)
    (hε : ε ∈ Set.Ioo (0 : ℝ) ℓ) (hg : IsStrongGrowth C f M r)
    (hrun : IsFWRun C (fderiv ℝ f) x v (fun t => eta ℓ t)) (i : ℕ) :
    (fderiv ℝ f (x i) (x i - v i) ≤ (eta ℓ i * ℓ * M / (2 * ε)) ^ (1 / (1 - r)) →
      pdGap f x v (i + 1) ≤ (eta ℓ i * ℓ * M / (2 * ε)) ^ (1 / (1 - r))) ∧
    ((eta ℓ i * ℓ * M / (2 * ε)) ^ (1 / (1 - r)) < fderiv ℝ f (x i) (x i - v i) →
      pdGap f x v (i + 1) ≤
        pdGap f x v i - (1 - ε / ℓ) * (eta ℓ i * fderiv ℝ f (x i) (x i - v i))) := by
  obtain ⟨hr0, hr1⟩ := hr
  obtain ⟨hε0, hεℓ⟩ := hε
  have hmem := Lemmata.FrankWolfe.Proof.fw_run_mem C _ x v _ hC hrun
  have h1 := pd_step hrun i
  obtain ⟨hvC, hvmin, hγ, hx⟩ := hrun.2 i
  have h3 := hg (x i) (hmem i) (v i) hvC hvmin (eta ℓ i) hγ
  rw [← hx] at h3
  have hpg := pd_le_gap f x v i
  have hg0 := gap_nonneg hC hrun i
  set g := fderiv ℝ f (x i) (x i - v i) with hgdef
  set η := eta ℓ i with hη
  have hηpos : 0 < η := by rw [hη, eta_nat]; positivity
  have hη1 : η ≤ 1 := hγ.2
  set a := η * ℓ * M / (2 * ε) with ha
  have hapos : 0 < a := by positivity
  set T := a ^ (1 / (1 - r)) with hT
  have hTpos : 0 < T := Real.rpow_pos_of_pos hapos _
  have h1r : 0 < 1 - r := by linarith
  have hT1r : T ^ (1 - r) = a := by
    rw [hT, ← Real.rpow_mul hapos.le, one_div_mul_cancel h1r.ne', Real.rpow_one]
  have hℓr : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hMη : M * η ^ 2 / 2 = η * (ε / ℓ) * a := by rw [ha]; field_simp
  refine ⟨fun hsmall => ?_, fun hbig => ?_⟩
  · have hgr : g ^ r ≤ T ^ r := Real.rpow_le_rpow hg0 hsmall hr0
    have hsplit : T ^ (1 - r) * T ^ r = T := by
      rw [← Real.rpow_add hTpos, sub_add_cancel, Real.rpow_one]
    have hεℓ' : ε / ℓ ≤ 1 := by rw [div_le_one hℓr]; exact hεℓ.le
    have h5 : M * η ^ 2 / 2 * g ^ r ≤ η * T := by
      rw [hMη]
      calc η * (ε / ℓ) * a * g ^ r ≤ η * 1 * a * T ^ r := by
            apply mul_le_mul _ hgr (Real.rpow_nonneg hg0 _) (by positivity)
            apply mul_le_mul_of_nonneg_right _ hapos.le
            exact mul_le_mul_of_nonneg_left hεℓ' hηpos.le
        _ = η * T := by rw [mul_one, mul_assoc, ← hT1r, hsplit]
    have h6 : (1 - η) * g ≤ (1 - η) * T := mul_le_mul_of_nonneg_left hsmall (by linarith)
    nlinarith
  · have hgpos : 0 < g := lt_trans hTpos hbig
    have hga : a ≤ g ^ (1 - r) := by
      rw [← hT1r]; exact Real.rpow_le_rpow hTpos.le hbig.le h1r.le
    have hsplit : g ^ (1 - r) * g ^ r = g := by
      rw [← Real.rpow_add hgpos, sub_add_cancel, Real.rpow_one]
    have h5 : M * η ^ 2 / 2 * g ^ r ≤ η * (ε / ℓ) * g := by
      rw [hMη]
      calc η * (ε / ℓ) * a * g ^ r ≤ η * (ε / ℓ) * g ^ (1 - r) * g ^ r := by
            apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hg0 _)
            exact mul_le_mul_of_nonneg_left hga (by positivity)
        _ = η * (ε / ℓ) * g := by rw [mul_assoc, hsplit]
    nlinarith

theorem eta_pos_nat (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (t : ℕ) (ht : 1 ≤ t) : 0 < eta ℓ ((t : ℤ) - 1) := by
  rw [eta_pred]
  have : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have : (1 : ℝ) ≤ t := by exact_mod_cast ht
  apply div_pos (by positivity); linarith

theorem eta_pred_le_one (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (t : ℕ) (ht : 1 ≤ t) : eta ℓ ((t : ℤ) - 1) ≤ 1 := by
  have hℓr : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have htr : (1 : ℝ) ≤ t := by exact_mod_cast ht
  rw [eta_pred, div_le_one (by linarith)]
  linarith

theorem eta_pred_anti (ℓ : ℕ) (hℓ : 1 ≤ ℓ) {s t : ℕ} (hs : 1 ≤ s) (hst : s ≤ t) :
    eta ℓ ((t : ℤ) - 1) ≤ eta ℓ ((s : ℤ) - 1) := by
  rw [eta_pred, eta_pred]
  have hℓr : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have : (s : ℝ) ≤ t := by exact_mod_cast hst
  have : (1 : ℝ) ≤ s := by exact_mod_cast hs
  apply div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)

/-- **Theorem 3.4**, the first claim. -/
theorem pd_rate_r_bound {C : Set E} {f : E → ℝ} {M r ε : ℝ} {ℓ : ℕ} {x v : ℕ → E} {xStar : E}
    (hconv : ConvexOn ℝ C f) (hdiff : ∀ y ∈ C, DifferentiableAt ℝ f y)
    (hxs : xStar ∈ minimizers C f) (hM : 0 < M) (hℓ : 1 ≤ ℓ) (hr : r ∈ Set.Ico (0 : ℝ) 1)
    (hε : ε ∈ Set.Ioo (0 : ℝ) ℓ) (hg : IsStrongGrowth C f M r)
    (hrun : IsFWRun C (fderiv ℝ f) x v (fun t => eta ℓ t)) :
    ∀ t : ℕ, 1 ≤ t → pdGap f x v t ≤ Real.exp (ε * ℓ) *
      max (eta ℓ ((t : ℤ) - 1) ^ ((ℓ : ℝ) - ε) * pdGap f x v 1)
        (eta ℓ ((t : ℤ) - 1) ^ (min ((ℓ : ℝ) - ε) (1 / (1 - r))) *
          (ℓ * M / (2 * ε)) ^ (1 / (1 - r))) := by
  obtain ⟨hr0, hr1⟩ := hr
  obtain ⟨hε0, hεℓ⟩ := hε
  have hℓr : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have h1r : 0 < 1 - r := by linarith
  set a : ℝ := 1 / (1 - r) with ha
  set X : ℝ := ℓ * M / (2 * ε) with hX
  have hX0 : 0 ≤ X := by positivity
  set c : ℕ → ℝ := fun i => 1 - (1 - ε / ℓ) * eta ℓ i with hc
  have hcoef0 : 0 ≤ 1 - ε / ℓ := by rw [sub_nonneg, div_le_one (by linarith)]; exact hεℓ.le
  have hc0 : ∀ i, 0 ≤ c i := by
    intro i
    have h0 : 0 ≤ ε / ℓ := by positivity
    have h1 : 1 - ε / ℓ ≤ 1 := by linarith
    have := mul_le_mul h1 (eta_mem ℓ hℓ i).2 (eta_mem ℓ hℓ i).1 zero_le_one
    simp only [hc]; linarith
  set term : ℕ → ℝ := fun R =>
    if R = 1 then pdGap f x v 1 else (eta ℓ ((R - 1 : ℕ) : ℤ) * ℓ * M / (2 * ε)) ^ a with hterm
  have hstep := strong_r_step hconv.1 hM hℓ ⟨hr0, hr1⟩ ⟨hε0, hεℓ⟩ hg hrun
  have hinv : ∀ t, 1 ≤ t → ∃ R, 1 ≤ R ∧ R ≤ t ∧
      pdGap f x v t ≤ term R * ∏ i ∈ Finset.Ico R t, c i := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => exact ⟨1, le_rfl, le_rfl, by simp [hterm]⟩
    | succ t ht ih =>
      obtain ⟨R, hR1, hRt, hR⟩ := ih
      by_cases hsmall : fderiv ℝ f (x t) (x t - v t) ≤ (eta ℓ t * ℓ * M / (2 * ε)) ^ a
      · refine ⟨t + 1, by omega, le_rfl, ?_⟩
        rw [Finset.Ico_self, Finset.prod_empty, mul_one]
        simp only [hterm, show t + 1 ≠ 1 by omega, ↓reduceIte, Nat.add_sub_cancel]
        exact (hstep t).1 hsmall
      · refine ⟨R, hR1, by omega, ?_⟩
        rw [Finset.prod_Ico_succ_top hRt]
        have h := (hstep t).2 (lt_of_not_ge hsmall)
        have hpg := pd_le_gap f x v t
        have hcoef : 0 ≤ (1 - ε / ℓ) * eta ℓ t := mul_nonneg hcoef0 (eta_mem ℓ hℓ t).1
        have h2 : pdGap f x v (t + 1) ≤ c t * pdGap f x v t := by
          simp only [hc]
          have := mul_le_mul_of_nonneg_left hpg hcoef
          nlinarith
        calc pdGap f x v (t + 1) ≤ c t * pdGap f x v t := h2
          _ ≤ c t * (term R * ∏ i ∈ Finset.Ico R t, c i) := mul_le_mul_of_nonneg_left hR (hc0 t)
          _ = term R * ((∏ i ∈ Finset.Ico R t, c i) * c t) := by ring
  intro t ht
  obtain ⟨R, hR1, hRt, hR⟩ := hinv t ht
  set q := eta ℓ ((t : ℤ) - 1) with hq
  have hq0 : 0 < q := eta_pos_nat ℓ hℓ t ht
  have hq1 : q ≤ 1 := eta_pred_le_one ℓ hℓ t ht
  set p := eta ℓ ((R : ℤ) - 1) with hp
  have hp0 : 0 < p := eta_pos_nat ℓ hℓ R hR1
  have hp1 : p ≤ 1 := eta_pred_le_one ℓ hℓ R hR1
  have hqp : q ≤ p := eta_pred_anti ℓ hℓ hR1 hRt
  -- the product over the stretch `[R, t)`
  have hprod : ∏ i ∈ Finset.Ico R t, c i ≤ (q / p) ^ ((ℓ : ℝ) - ε) * Real.exp (ε * ℓ / R) := by
    rcases eq_or_lt_of_le hRt with heq | hlt
    · subst heq
      rw [Finset.Ico_self, Finset.prod_empty, div_self hp0.ne', Real.one_rpow, one_mul]
      exact Real.one_le_exp (by positivity)
    · have hIco : Finset.Ico R t = Finset.Icc R (t - 1) := by
        ext i; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega
      rw [hIco]
      have h := product_bound_eps_closed ℓ R (t - 1) ε hℓ hR1 (by omega) ⟨hε0.le, hεℓ.le⟩
      rwa [← eta_pred_ratio ℓ R t hℓ hR1 (by omega)] at h
  have hexpR : Real.exp (ε * ℓ / R) ≤ Real.exp (ε * ℓ) := by
    apply Real.exp_le_exp.mpr
    have : (1 : ℝ) ≤ R := by exact_mod_cast hR1
    exact div_le_self (by positivity) this
  have hprod' : ∏ i ∈ Finset.Ico R t, c i ≤ (q / p) ^ ((ℓ : ℝ) - ε) * Real.exp (ε * ℓ) :=
    le_trans hprod (mul_le_mul_of_nonneg_left hexpR (by positivity))
  have hpd1 := pd_nonneg hconv hdiff hxs hrun 1
  have hexp0 : 0 < Real.exp (ε * ℓ) := Real.exp_pos _
  by_cases hR1' : R = 1
  · subst hR1'
    simp only [hterm, ↓reduceIte] at hR
    have hp1' : p = 1 := by
      rw [hp]; simp only [eta]; push_cast
      have : (ℓ : ℝ) ≠ 0 := by positivity
      field_simp
      ring
    rw [hp1', div_one] at hprod'
    calc pdGap f x v t ≤ pdGap f x v 1 * ∏ i ∈ Finset.Ico 1 t, c i := hR
      _ ≤ pdGap f x v 1 * (q ^ ((ℓ : ℝ) - ε) * Real.exp (ε * ℓ)) :=
          mul_le_mul_of_nonneg_left hprod' hpd1
      _ = Real.exp (ε * ℓ) * (q ^ ((ℓ : ℝ) - ε) * pdGap f x v 1) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_left _ _) hexp0.le
  · simp only [hterm, hR1', ↓reduceIte] at hR
    have hcast : ((R - 1 : ℕ) : ℤ) = (R : ℤ) - 1 := by omega
    rw [hcast] at hR
    have hterm' : (p * ℓ * M / (2 * ε)) ^ a = p ^ a * X ^ a := by
      rw [← Real.mul_rpow hp0.le hX0]; congr 1; rw [hX]; ring
    rw [hterm'] at hR
    have hmix := rpow_mix_le (a := a) (b := (ℓ : ℝ) - ε) hq0 hqp hp1
    calc pdGap f x v t ≤ p ^ a * X ^ a * ∏ i ∈ Finset.Ico R t, c i := hR
      _ ≤ p ^ a * X ^ a * ((q / p) ^ ((ℓ : ℝ) - ε) * Real.exp (ε * ℓ)) :=
          mul_le_mul_of_nonneg_left hprod' (by positivity)
      _ = Real.exp (ε * ℓ) * ((p ^ a * (q / p) ^ ((ℓ : ℝ) - ε)) * X ^ a) := by ring
      _ ≤ Real.exp (ε * ℓ) * (q ^ (min ((ℓ : ℝ) - ε) a) * X ^ a) := by
          apply mul_le_mul_of_nonneg_left _ hexp0.le
          exact mul_le_mul_of_nonneg_right hmix (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_right _ _) hexp0.le

/-- **Theorem 3.4**, the second claim. -/
theorem gap_rate_r_bound {C : Set E} {f : E → ℝ} {M r ε : ℝ} {ℓ : ℕ} {x v : ℕ → E} {xStar : E}
    (hconv : ConvexOn ℝ C f) (hdiff : ∀ y ∈ C, DifferentiableAt ℝ f y)
    (hxs : xStar ∈ minimizers C f) (hM : 0 < M) (hℓ : 1 ≤ ℓ) (hr : r ∈ Set.Ico (0 : ℝ) 1)
    (hε : ε ∈ Set.Ioo (0 : ℝ) ℓ) (hg : IsStrongGrowth C f M r)
    (hrun : IsFWRun C (fderiv ℝ f) x v (fun t => eta ℓ t)) :
    ∀ t : ℕ, ⌈Real.exp (1 / min ((ℓ : ℝ) - ε) (1 / (1 - r))) * (1 + ℓ) - ℓ⌉₊ ≤ t →
      minGap f x v t ≤ Real.exp (3 + ε * ℓ) *
        eta ℓ ((t : ℤ) - 1) ^ (min ((ℓ : ℝ) - ε) (1 / (1 - r))) *
        max (pdGap f x v 1) ((ℓ * M / (2 * ε)) ^ (1 / (1 - r))) := by
  intro t ht
  obtain ⟨hr0, hr1⟩ := hr
  obtain ⟨hε0, hεℓ⟩ := hε
  have hℓr : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have h1r : 0 < 1 - r := by linarith
  set a : ℝ := 1 / (1 - r) with ha
  have ha0 : 0 < a := by positivity
  set k : ℝ := min ((ℓ : ℝ) - ε) a with hk
  have hk0 : 0 < k := lt_min (by linarith) ha0
  have hkℓ : k ≤ (ℓ : ℝ) - ε := min_le_left _ _
  have hka : k ≤ a := min_le_right _ _
  set X : ℝ := ℓ * M / (2 * ε) with hX
  have hX0 : 0 ≤ X := by positivity
  set c := Real.exp (1 / k) with hc
  have hc1 : 1 ≤ c := Real.one_le_exp (by positivity)
  have hct : c * (((1 : ℕ) : ℝ) + ℓ) ≤ t + ℓ := by
    have h1 := Nat.le_ceil (c * (1 + ℓ) - ℓ)
    have h2 : ((⌈c * (1 + ℓ) - ℓ⌉₊ : ℕ) : ℝ) ≤ t := by exact_mod_cast ht
    push_cast; linarith
  obtain ⟨R, hR1, hRt, hRle, hRlt⟩ := floor_choice ℓ t 1 hc1 hct
  have ht1 : 1 ≤ t := le_trans hR1 hRt
  set q := eta ℓ ((t : ℤ) - 1) with hq
  have hq0 : 0 < q := eta_pos_nat ℓ hℓ t ht1
  set p := eta ℓ ((R : ℤ) - 1) with hp
  have hp0 : 0 < p := eta_pos_nat ℓ hℓ R hR1
  have hp1 : p ≤ 1 := eta_pred_le_one ℓ hℓ R hR1
  have hpd1 := pd_nonneg hconv hdiff hxs hrun 1
  have hexp1 : 1 ≤ Real.exp (ε * ℓ) := Real.one_le_exp (by positivity)
  have hpk : p ^ a ≤ p ^ k := Real.rpow_le_rpow_of_exponent_ge hp0 hp1 hka
  have hstep := strong_r_step hconv.1 hM hℓ ⟨hr0, hr1⟩ ⟨hε0, hεℓ⟩ hg hrun
  set m := minGap f x v t with hm
  -- the bound in terms of `p = η_{R-1}`
  have hmp : m ≤ Real.exp (ε * ℓ) * (p ^ k * max (pdGap f x v 1) (X ^ a)) := by
    by_cases hA : ∃ j ∈ Finset.Icc R t,
        fderiv ℝ f (x j) (x j - v j) ≤ (eta ℓ j * ℓ * M / (2 * ε)) ^ a
    · obtain ⟨j, hj, hjsmall⟩ := hA
      have hmj := minGap_le f x v (Finset.mem_Icc.mp hj).2
      have hηj : eta ℓ j ≤ p := by
        have e : eta ℓ (j : ℤ) = eta ℓ (((j + 1 : ℕ) : ℤ) - 1) := by push_cast; ring_nf
        rw [e]; exact eta_pred_anti ℓ hℓ hR1 (by have := (Finset.mem_Icc.mp hj).1; omega)
      have hthr : (eta ℓ j * ℓ * M / (2 * ε)) ^ a ≤ p ^ a * X ^ a := by
        rw [← Real.mul_rpow hp0.le hX0]
        apply Real.rpow_le_rpow (by have := (eta_mem ℓ hℓ j).1; positivity) _ ha0.le
        rw [hX]
        have : eta ℓ j * ℓ * M / (2 * ε) = eta ℓ j * (ℓ * M / (2 * ε)) := by ring
        rw [this]; exact mul_le_mul_of_nonneg_right hηj hX0
      calc m ≤ p ^ a * X ^ a := le_trans hmj (le_trans hjsmall hthr)
        _ ≤ p ^ k * max (pdGap f x v 1) (X ^ a) :=
            mul_le_mul hpk (le_max_right _ _) (by positivity) (by positivity)
        _ ≤ Real.exp (ε * ℓ) * (p ^ k * max (pdGap f x v 1) (X ^ a)) :=
            le_mul_of_one_le_left (by positivity) hexp1
    · push Not at hA
      have hdec : ∀ j, R ≤ j → j ≤ t → pdGap f x v (j + 1) ≤
          pdGap f x v j - (1 - ε / ℓ) * (eta ℓ j * fderiv ℝ f (x j) (x j - v j)) :=
        fun j h1 h2 => (hstep j).2 (hA j (Finset.mem_Icc.mpr ⟨h1, h2⟩))
      have hsum : ∀ s, R ≤ s → s ≤ t → pdGap f x v (s + 1) ≤ pdGap f x v R -
          (1 - ε / ℓ) * ∑ j ∈ Finset.Icc R s, eta ℓ j * fderiv ℝ f (x j) (x j - v j) := by
        intro s hs
        induction s, hs using Nat.le_induction with
        | base => intro hRt'; rw [Finset.Icc_self, Finset.sum_singleton]; exact hdec R le_rfl hRt'
        | succ s hs ih =>
          intro hst
          rw [Finset.sum_Icc_succ_top (by omega)]
          have h1 := ih (by omega)
          have h2 := hdec (s + 1) (by omega) hst
          nlinarith
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
      have hηsum : (ℓ : ℝ) / k ≤ ∑ j ∈ Finset.Icc R t, eta ℓ j := by
        have := sum_eta_ge ℓ R t hℓ hRt (by positivity) hRle
        rwa [hc, Real.log_exp, mul_one_div] at this
      have hcoef : 1 ≤ (1 - ε / ℓ) * ((ℓ : ℝ) / k) := by
        have e : (1 - ε / ℓ) * ((ℓ : ℝ) / k) = ((ℓ : ℝ) - ε) / k := by field_simp
        rw [e, le_div_iff₀ hk0]; linarith
      have hcoef0 : 0 ≤ 1 - ε / ℓ := by rw [sub_nonneg, div_le_one (by linarith)]; exact hεℓ.le
      have hfin := hsum t hRt le_rfl
      have hpd0 := pd_nonneg hconv hdiff hxs hrun (t + 1)
      have hmR : m ≤ pdGap f x v R := by
        have h1 : m ≤ m * ((1 - ε / ℓ) * ((ℓ : ℝ) / k)) := le_mul_of_one_le_right hm0 hcoef
        have h2 : m * ((1 - ε / ℓ) * ((ℓ : ℝ) / k)) ≤
            (1 - ε / ℓ) * (m * ∑ j ∈ Finset.Icc R t, eta ℓ j) := by
          have := mul_le_mul_of_nonneg_left hηsum (mul_nonneg hm0 hcoef0)
          nlinarith
        have h3 := mul_le_mul_of_nonneg_left hsig hcoef0
        linarith
      have hpdR := pd_rate_r_bound hconv hdiff hxs hM hℓ ⟨hr0, hr1⟩ ⟨hε0, hεℓ⟩ hg hrun R hR1
      have hpk' : p ^ ((ℓ : ℝ) - ε) ≤ p ^ k := Real.rpow_le_rpow_of_exponent_ge hp0 hp1 hkℓ
      calc m ≤ pdGap f x v R := hmR
        _ ≤ Real.exp (ε * ℓ) * max (p ^ ((ℓ : ℝ) - ε) * pdGap f x v 1) (p ^ k * X ^ a) := hpdR
        _ ≤ Real.exp (ε * ℓ) * (p ^ k * max (pdGap f x v 1) (X ^ a)) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            rw [mul_max_of_nonneg _ _ (by positivity)]
            exact max_le_max (mul_le_mul_of_nonneg_right hpk' hpd1) le_rfl
  -- `p^k ≤ e³ q^k`
  have hratio := ratio_le ℓ R t hℓ hR1 ht1 hk0.le (by positivity) hRlt
  have hck : c ^ k = Real.exp 1 := by rw [hc, ← Real.exp_mul, one_div_mul_cancel hk0.ne']
  have h2k : Real.exp (2 * k / ℓ) ≤ Real.exp 2 := by
    apply Real.exp_le_exp.mpr
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hpq : p ^ k ≤ Real.exp 3 * q ^ k := by
    have e : p ^ k = (p / q) ^ k * q ^ k := by
      rw [← Real.mul_rpow (by positivity) hq0.le]; congr 1; field_simp
    rw [e]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    calc (p / q) ^ k ≤ c ^ k * Real.exp (2 * k / ℓ) := hratio
      _ ≤ Real.exp 1 * Real.exp 2 := by
          rw [hck]; exact mul_le_mul_of_nonneg_left h2k (by positivity)
      _ = Real.exp 3 := by rw [← Real.exp_add]; norm_num
  calc m ≤ Real.exp (ε * ℓ) * (p ^ k * max (pdGap f x v 1) (X ^ a)) := hmp
    _ ≤ Real.exp (ε * ℓ) * (Real.exp 3 * q ^ k * max (pdGap f x v 1) (X ^ a)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_right hpq (le_trans hpd1 (le_max_left _ _))
    _ = Real.exp (3 + ε * ℓ) * q ^ k * max (pdGap f x v 1) (X ^ a) := by
        rw [Real.exp_add]; ring

namespace Proof

theorem pd_rate_strong_zero : PDRateStrongZero.{u} := by
  intro E _ _ C f M ℓ x v hC hM hℓ hg hrun t ht
  exact pd_rate_zero_bound hC hM hℓ hg hrun t ht

theorem product_bound : ProductBound := by
  intro ℓ S t hℓ hS hSt
  rw [eta_ratio ℓ S t hℓ hS]
  exact product_bound_closed ℓ S hℓ hS t hSt

theorem product_bound_eps : ProductBoundEps := by
  intro ℓ S t ε hℓ hS hSt hε
  rw [eta_ratio ℓ S t hℓ hS]
  exact product_bound_eps_closed ℓ S t ε hℓ hS hSt hε

theorem pd_rate_strong_one : PDRateStrongOne.{u} := by
  intro E _ _ C f M ℓ x v xStar hconv hdiff hxs hM hℓ hg hrun S
  exact ⟨pd_rate_one_bound hconv hdiff hxs hM hℓ hg hrun S rfl,
    gap_rate_one_bound hconv hdiff hxs hM hℓ hg hrun S rfl⟩

theorem pd_rate_strong : PDRateStrong.{u} := by
  intro E _ _ C f M r ε ℓ x v xStar hconv hdiff hxs hM hℓ hr hε hg hrun k
  exact ⟨pd_rate_r_bound hconv hdiff hxs hM hℓ hr hε hg hrun,
    gap_rate_r_bound hconv hdiff hxs hM hℓ hr hε hg hrun⟩

end Proof

end Lemmata.FWAffineOpenLoop
