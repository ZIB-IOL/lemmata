module

public import Lemmata.FWOpenLoop.SeqGen
public import Lemmata.FWOpenLoop.Interior
public import Lemmata.AwayStepFW.Invariants
public import Lemmata.AwayStepFW.Progress
public import Lemmata.AwayStepFW.Geometry

@[expose] public section

/-!
# Away-step Frank–Wolfe with open-loop step sizes

Lemmas 5.5 and 5.6, Proposition 5.7 and Theorem 5.9. Along a run, the state keeps the invariant
of away-step Frank–Wolfe. Steps of full length `η_{ℓ_t}` and drop steps that pass the test are
progress steps; the others are drop steps that do not increase the primal gap. Since only
Frank–Wolfe steps add vertices to the active set, at most half of the steps are not progress steps.
-/

namespace Lemmata.FWOpenLoop

open Lemmata.FrankWolfe Lemmata.AwayStepFW.Proof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem eta4_pos_nat (k : ℕ) : 0 < eta 4 k := etaL_pos (by norm_num) _ (by omega)

theorem eta4_le_one (k : ℕ) : eta 4 k ≤ 1 := by
  unfold eta
  rw [div_le_one (by positivity)]
  have : (0 : ℝ) ≤ (k : ℤ) := by exact_mod_cast Nat.cast_nonneg k
  linarith

theorem inv_olstep {V : Finset E} {L D : ℝ} {g : StrongDual ℝ E} {x : E} {S : Finset E}
    {lam : E → ℝ} {ℓ : ℕ} (h : Inv V x S lam) {v a : E} (hvV : v ∈ V) (hv : ∀ w ∈ V, g v ≤ g w)
    (ha : a ∈ S) (haS : ∀ w ∈ S, g w ≤ g a) {x' : E} {S' : Finset E} {lam' : E → ℝ} {ℓ' : ℕ}
    (hstep : IsOLAFWStep L D g x S lam ℓ v a x' S' lam' ℓ') : Inv V x' S' lam' := by
  classical
  have hη0 := eta4_pos_nat ℓ
  unfold IsOLAFWStep at hstep
  split_ifs at hstep with hfw
  · dsimp only at hstep
    obtain ⟨hx', hlam', hS', -⟩ := hstep
    set γ := min (eta 4 ℓ) 1 with hγ
    have hγ0 : 0 ≤ γ := le_min hη0.le zero_le_one
    have hγ1 : γ ≤ 1 := min_le_right _ _
    have hsub : S ⊆ insert v S := Finset.subset_insert v S
    have hsumlam : ∑ w ∈ insert v S, lam w = 1 := by
      rw [← h.sum]; symm
      exact Finset.sum_subset hsub (fun w _ hw => h.supp w hw)
    have hsumx : ∑ w ∈ insert v S, lam w • w = x := by
      rw [h.rep]; symm
      exact Finset.sum_subset hsub (fun w _ hw => by rw [h.supp w hw, zero_smul])
    subst hlam'
    rcases eq_or_ne γ 1 with h1 | h1
    · rw [ite_eq_left h1] at hS'
      subst hS'
      refine ⟨by simpa using hvV, fun w => ?_, fun w hw => ?_, ?_, ?_⟩
      · have := h.nonneg w; split_ifs <;> nlinarith
      · rw [Finset.mem_singleton] at hw; simp [hw, h1]
      · simp [h1]
      · rw [hx', h1]; simp
    · rw [ite_eq_right h1] at hS'
      subst hS'
      refine ⟨Finset.insert_subset hvV h.sub, fun w => ?_, fun w hw => ?_, ?_, ?_⟩
      · have := h.nonneg w; split_ifs <;> nlinarith
      · rw [Finset.mem_insert, not_or] at hw
        simp [hw.1, h.supp w hw.2]
      · rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsumlam, Finset.sum_ite_eq']
        simp
      · simp only [add_smul, Finset.sum_add_distrib, mul_smul, ← Finset.smul_sum, hsumx, ite_smul,
          zero_smul, Finset.sum_ite_eq', Finset.mem_insert_self, ite_true]
        rw [hx']
        module
  · dsimp only at hstep
    obtain ⟨hx', hlam', hS', -⟩ := hstep
    have hlt := h.lam_lt_one g hv ha hfw
    set γmax := lam a / (1 - lam a) with hγmax
    set γ := min (eta 4 ℓ) γmax with hγ
    have hmax0 : 0 ≤ γmax := div_nonneg (h.nonneg a) (by linarith)
    have hγ0 : 0 ≤ γ := le_min hη0.le hmax0
    have hγle : γ ≤ γmax := min_le_right _ _
    have hnna : 0 ≤ (1 + γ) * lam a - γ := by
      have : γ * (1 - lam a) ≤ lam a := by
        rw [← le_div_iff₀ (by linarith)]; exact hγle
      nlinarith
    have hsumS : ∑ w ∈ S, ((1 + γ) * lam w - if w = a then γ else 0) = 1 := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, h.sum, Finset.sum_ite_eq', ite_eq_left ha]; ring
    have hrepS : ∑ w ∈ S, ((1 + γ) * lam w - if w = a then γ else 0) • w = x' := by
      simp only [sub_smul, Finset.sum_sub_distrib, mul_smul, ← Finset.smul_sum, ← h.rep, ite_smul,
        zero_smul, Finset.sum_ite_eq', ite_eq_left ha]
      rw [hx']
      module
    subst hlam'
    rcases eq_or_ne γ γmax with hd | hd
    · rw [ite_eq_left hd] at hS'
      subst hS'
      have hza : (1 + γ) * lam a - γ = 0 := by
        rw [hd, hγmax]; field_simp; ring
      refine ⟨(Finset.erase_subset a S).trans h.sub, fun w => ?_, fun w hw => ?_, ?_, ?_⟩
      · by_cases hwa : w = a
        · simp only [hwa, ite_true]; exact hnna
        · simp only [hwa, ite_false, sub_zero]; exact mul_nonneg (by linarith) (h.nonneg w)
      · by_cases hwa : w = a
        · simp only [hwa, ite_true]; exact hza
        · have hwS : w ∉ S := fun hwS => hw (Finset.mem_erase.mpr ⟨hwa, hwS⟩)
          simp [hwa, h.supp w hwS]
      · rw [Finset.sum_erase _ (by simp only [ite_true]; exact hza)]; exact hsumS
      · rw [Finset.sum_erase _ (by simp only [ite_true]; rw [hza, zero_smul])]; exact hrepS.symm
    · rw [ite_eq_right hd] at hS'
      subst hS'
      refine ⟨h.sub, fun w => ?_, fun w hw => ?_, hsumS, hrepS.symm⟩
      · by_cases hwa : w = a
        · simp only [hwa, ite_true]; exact hnna
        · simp only [hwa, ite_false, sub_zero]; exact mul_nonneg (by linarith) (h.nonneg w)
      · have hwa : w ≠ a := fun e => hw (e ▸ ha)
        simp [hwa, h.supp w hw]

theorem olafw_inv {V : Finset E} {f : E → ℝ} {L : ℝ} {x : ℕ → E} {S : ℕ → Finset E}
    {lam : ℕ → E → ℝ} {ℓ : ℕ → ℕ} (h : IsOLAFWRun V f L x S lam ℓ) :
    ∀ t, Inv V (x t) (S t) (lam t) := by
  classical
  obtain ⟨hx0, hS0, hlam0, -, hsteps⟩ := h
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
    exact inv_olstep ih hvV hv ha haS hstep

/-- **Lemma 5.5.** -/
theorem drop_step_bound : DropStep := by
  intro A B η γ hA hB hγ0 hγη
  by_cases h : γ * B ≤ A
  · left; nlinarith
  · right
    replace h := lt_of_not_ge h
    have : 0 ≤ (η - γ) * ((γ + η) * B - A) :=
      mul_nonneg (by linarith) (by nlinarith)
    nlinarith

/-- Steps of full length are progress steps, and the active set grows only in Frank–Wolfe steps:
`|S_{t+1}| + (t + 1) ≤ 1 + 2 ℓ_{t+1}` follows from `|S_t| + t ≤ 1 + 2 ℓ_t`. -/
theorem olafw_card {V : Finset E} {f : E → ℝ} {L : ℝ} {x : ℕ → E} {S : ℕ → Finset E}
    {lam : ℕ → E → ℝ} {ℓ : ℕ → ℕ} (h : IsOLAFWRun V f L x S lam ℓ) :
    ∀ t, (S t).card + t ≤ 1 + 2 * ℓ t := by
  classical
  have hinv := olafw_inv h
  obtain ⟨hx0, hS0, hlam0, hℓ0, hsteps⟩ := h
  intro t
  induction t with
  | zero => rw [hS0, hℓ0]; simp
  | succ t ih =>
    obtain ⟨v, hvV, hv, a, ha, haS, hstep⟩ := hsteps t
    have hη1 := eta4_le_one (ℓ t)
    unfold IsOLAFWStep at hstep
    split_ifs at hstep with hfw
    · dsimp only at hstep
      obtain ⟨-, -, hS', hℓ'⟩ := hstep
      have hγ : min (eta 4 (ℓ t)) 1 = eta 4 (ℓ t) := min_eq_left hη1
      rw [hγ, sub_self, zero_mul, sub_self, zero_mul] at hℓ'
      simp only [le_refl, ↓reduceIte] at hℓ'
      have hcard : (S (t + 1)).card ≤ (S t).card + 1 := by
        rw [hS']
        split_ifs
        · simp
        · exact Finset.card_insert_le _ _
      rw [hℓ']
      omega
    · dsimp only at hstep
      obtain ⟨-, -, hS', hℓ'⟩ := hstep
      set γmax := lam t a / (1 - lam t a)
      by_cases hd : min (eta 4 (ℓ t)) γmax = γmax
      · rw [ite_eq_left hd] at hS'
        have hcard : (S (t + 1)).card + 1 = (S t).card := by
          rw [hS']; exact Finset.card_erase_add_one ha
        have : ℓ t ≤ ℓ (t + 1) := by rw [hℓ']; split_ifs <;> omega
        omega
      · rw [ite_eq_right hd] at hS'
        have hγ : min (eta 4 (ℓ t)) γmax = eta 4 (ℓ t) := by
          rcases min_choice (eta 4 (ℓ t)) γmax with h' | h'
          · exact h'
          · exact absurd h' hd
        rw [hγ, sub_self, zero_mul, sub_self, zero_mul] at hℓ'
        simp only [le_refl, ↓reduceIte] at hℓ'
        rw [hS', hℓ']
        omega

/-- **Lemma 5.6.** -/
theorem progress_steps_bound {V : Finset E} {f : E → ℝ} {L : ℝ} {x : ℕ → E} {S : ℕ → Finset E}
    {lam : ℕ → E → ℝ} {ℓ : ℕ → ℕ} (h : IsOLAFWRun V f L x S lam ℓ) : ∀ t, t ≤ 2 * ℓ t := by
  classical
  intro t
  have hc := olafw_card h t
  have hne : (S t).Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    have := (olafw_inv h t).sum
    rw [hemp, Finset.sum_empty] at this
    exact zero_ne_one this
  have := hne.card_pos
  omega

/-- For `φ(s) = -s c + s² K` with `K ≥ 0` and `0 ≤ γ ≤ η`: if `φ(γ) > φ(η)`, then `φ(γ) ≤ 0`. -/
theorem phi_le_zero {c K γ η : ℝ} (hK : 0 ≤ K) (hγ0 : 0 ≤ γ) (hγη : γ ≤ η)
    (hgt : -η * c + η ^ 2 * K < -γ * c + γ ^ 2 * K) : -γ * c + γ ^ 2 * K ≤ 0 := by
  by_contra hpos
  replace hpos := lt_of_not_ge hpos
  have h1 : η * (-γ * c + γ ^ 2 * K) ≤ γ * (-η * c + η ^ 2 * K) := by
    have : 0 ≤ γ * η * (η - γ) * K :=
      mul_nonneg (mul_nonneg (mul_nonneg hγ0 (le_trans hγ0 hγη)) (by linarith)) hK
    nlinarith
  rcases hγ0.eq_or_lt with h0 | hγpos
  · subst h0; simp at hpos
  · have h2 : γ * (-η * c + η ^ 2 * K) < γ * (-γ * c + γ ^ 2 * K) :=
      mul_lt_mul_of_pos_left hgt hγpos
    have h3 : γ * (-γ * c + γ ^ 2 * K) ≤ η * (-γ * c + γ ^ 2 * K) :=
      mul_le_mul_of_nonneg_right hγη hpos.le
    linarith

/-- One step of away-step Frank–Wolfe with open-loop step sizes. A progress step
(`ℓ_{t+1} = ℓ_t + 1`) satisfies `h_{t+1} ≤ (1 - η) h_t + η² K` and
`h_{t+1} ≤ h_t - η f'(x_t)(a - v)/2 + η² K` with `η = η_{ℓ_t}` and `K = L D²/2`; any other step
does not increase the primal gap. -/
theorem olafw_step {V : Finset E} {f : E → ℝ} {L : ℝ} {x : ℕ → E} {S : ℕ → Finset E}
    {lam : ℕ → E → ℝ} {ℓ : ℕ → ℕ} (hrun : IsOLAFWRun V f L x S lam ℓ)
    (hconv : ConvexOn ℝ (convexHull ℝ (↑V : Set E)) f)
    (hdiff : ∀ y ∈ convexHull ℝ (↑V : Set E), DifferentiableAt ℝ f y)
    (hsm : IsSmoothOn (convexHull ℝ (↑V : Set E)) f L) (hL : 0 ≤ L)
    {xStar : E} (hxs : xStar ∈ minimizers (convexHull ℝ (↑V : Set E)) f) (t : ℕ) :
    ∃ v ∈ V, (∀ w ∈ V, fderiv ℝ f (x t) v ≤ fderiv ℝ f (x t) w) ∧
      ∃ a ∈ S t, (∀ w ∈ S t, fderiv ℝ f (x t) w ≤ fderiv ℝ f (x t) a) ∧
        ((ℓ (t + 1) = ℓ t + 1 ∧
          f (x (t + 1)) - f xStar ≤ (1 - eta 4 (ℓ t)) * (f (x t) - f xStar) +
            eta 4 (ℓ t) ^ 2 * (L * Metric.diam (↑V : Set E) ^ 2 / 2) ∧
          f (x (t + 1)) - f xStar ≤ (f (x t) - f xStar) -
            eta 4 (ℓ t) * (fderiv ℝ f (x t) (a - v) / 2) +
            eta 4 (ℓ t) ^ 2 * (L * Metric.diam (↑V : Set E) ^ 2 / 2)) ∨
         (ℓ (t + 1) = ℓ t ∧ f (x (t + 1)) - f xStar ≤ f (x t) - f xStar)) := by
  classical
  have hinv := olafw_inv hrun
  set P := convexHull ℝ (↑V : Set E) with hPdef
  have hPc : IsCompact P := V.finite_toSet.isCompact_convexHull (𝕜 := ℝ)
  have hmemP : ∀ τ, x τ ∈ P := fun τ =>
    convexHull_mono (by exact_mod_cast (hinv τ).sub) (hinv τ).mem_convexHull
  have hdist : ∀ y ∈ P, ∀ z ∈ P, ‖y - z‖ ≤ Metric.diam (↑V : Set E) := fun y hy z hz => by
    rw [← dist_eq_norm, ← convexHull_diam]; exact Metric.dist_le_diam_of_mem hPc.isBounded hy hz
  obtain ⟨v, hvV, hv, a, ha, haS, hstep⟩ := hrun.2.2.2.2 t
  refine ⟨v, hvV, hv, a, ha, haS, ?_⟩
  have hη0 := eta4_pos_nat (ℓ t)
  have hη1 := eta4_le_one (ℓ t)
  have hvP : v ∈ P := subset_convexHull ℝ _ (Finset.mem_coe.mpr hvV)
  have haP : a ∈ P := subset_convexHull ℝ _ (Finset.mem_coe.mpr ((hinv t).sub ha))
  have hxP := hmemP t
  have hx'P := hmemP (t + 1)
  have hsmooth := hsm (x t) hxP (x (t + 1)) hx'P
  have hhG : f (x t) - f xStar ≤ fderiv ℝ f (x t) (x t - v) := by
    have h1 := convexOn_add_fderiv_le hconv hxP (hdiff _ hxP) hxs.1
    have h2 := le_of_min_vertex (fderiv ℝ f (x t)) hv hxs.1
    have e1 : fderiv ℝ f (x t) (xStar - x t) = fderiv ℝ f (x t) xStar - fderiv ℝ f (x t) (x t) :=
      map_sub _ _ _
    have e2 : fderiv ℝ f (x t) (x t - v) = fderiv ℝ f (x t) (x t) - fderiv ℝ f (x t) v :=
      map_sub _ _ _
    linarith
  have hsplit : fderiv ℝ f (x t) (a - v) =
      fderiv ℝ f (x t) (a - x t) + fderiv ℝ f (x t) (x t - v) := by
    rw [map_sub, map_sub, map_sub]; ring
  unfold IsOLAFWStep at hstep
  split_ifs at hstep with hfw
  · -- a Frank–Wolfe step, of full length
    dsimp only at hstep
    obtain ⟨hx', -, -, hℓ'⟩ := hstep
    have hγ : min (eta 4 (ℓ t)) 1 = eta 4 (ℓ t) := min_eq_left hη1
    rw [hγ] at hx' hℓ'
    rw [sub_self, zero_mul, sub_self, zero_mul] at hℓ'
    simp only [le_refl, ↓reduceIte] at hℓ'
    left
    set g := fderiv ℝ f (x t) with hg
    set η := eta 4 (ℓ t) with hη
    set K := L * Metric.diam (↑V : Set E) ^ 2 / 2 with hK
    have hd : x (t + 1) - x t = η • (v - x t) := by rw [hx']; abel
    rw [hd, map_smul, smul_eq_mul, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at hsmooth
    have hvx : g (v - x t) = -g (x t - v) := by rw [← map_neg, neg_sub]
    rw [hvx] at hsmooth
    have hnorm : ‖v - x t‖ ^ 2 ≤ Metric.diam (↑V : Set E) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hdist v hvP (x t) hxP) 2
    have hq : L / 2 * (η ^ 2 * ‖v - x t‖ ^ 2) ≤ η ^ 2 * K := by
      have := mul_le_mul_of_nonneg_left hnorm (by positivity : (0 : ℝ) ≤ L / 2 * η ^ 2)
      rw [hK]; nlinarith
    have hmain : f (x (t + 1)) - f xStar ≤ (f (x t) - f xStar) - η * g (x t - v) + η ^ 2 * K := by
      linarith
    refine ⟨hℓ', ?_, ?_⟩
    · have := mul_le_mul_of_nonneg_left hhG hη0.le; nlinarith
    · have hle : g (a - v) / 2 ≤ g (x t - v) := by rw [hsplit]; linarith
      have := mul_le_mul_of_nonneg_left hle hη0.le; linarith
  · -- an away step
    dsimp only at hstep
    obtain ⟨hx', -, -, hℓ'⟩ := hstep
    have hlt := (hinv t).lam_lt_one (fderiv ℝ f (x t)) hv ha hfw
    replace hfw := lt_of_not_ge hfw
    set g := fderiv ℝ f (x t) with hg
    set η := eta 4 (ℓ t) with hη
    set K := L * Metric.diam (↑V : Set E) ^ 2 / 2 with hK
    set γmax := lam t a / (1 - lam t a) with hγmax
    set γ := min η γmax with hγ
    have hmax0 : 0 ≤ γmax := div_nonneg ((hinv t).nonneg a) (by linarith)
    have hγ0 : 0 ≤ γ := le_min hη0.le hmax0
    have hγη : γ ≤ η := min_le_left _ _
    have hd : x (t + 1) - x t = γ • (x t - a) := by rw [hx']; abel
    rw [hd, map_smul, smul_eq_mul, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at hsmooth
    have hxa : g (x t - a) = -g (a - x t) := by rw [← map_neg, neg_sub]
    rw [hxa] at hsmooth
    have hnorm : ‖x t - a‖ ^ 2 ≤ Metric.diam (↑V : Set E) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hdist (x t) hxP a haP) 2
    have hq : L / 2 * (γ ^ 2 * ‖x t - a‖ ^ 2) ≤ γ ^ 2 * K := by
      have := mul_le_mul_of_nonneg_left hnorm (by positivity : (0 : ℝ) ≤ L / 2 * γ ^ 2)
      rw [hK]; nlinarith
    have hcA : g (a - v) / 2 ≤ g (a - x t) := by rw [hsplit]; linarith
    have hcG : g (x t - v) ≤ g (a - v) / 2 := by rw [hsplit]; linarith
    have hphi : f (x (t + 1)) - f xStar ≤
        (f (x t) - f xStar) + (-γ * (g (a - v) / 2) + γ ^ 2 * K) := by
      have := mul_le_mul_of_nonneg_left hcA hγ0; linarith
    have hK0 : 0 ≤ K := by positivity
    by_cases htest : (η - γ) * g (a - v) ≤
        (η ^ 2 - γ ^ 2) * (L * Metric.diam (↑V : Set E) ^ 2)
    · rw [ite_eq_left htest] at hℓ'
      left
      have hle : -γ * (g (a - v) / 2) + γ ^ 2 * K ≤ -η * (g (a - v) / 2) + η ^ 2 * K := by
        rw [hK]; nlinarith
      refine ⟨hℓ', ?_, by linarith⟩
      have := mul_le_mul_of_nonneg_left (le_trans hhG hcG) hη0.le
      nlinarith
    · rw [ite_eq_right htest] at hℓ'
      right
      have hgt : -η * (g (a - v) / 2) + η ^ 2 * K < -γ * (g (a - v) / 2) + γ ^ 2 * K := by
        replace htest := lt_of_not_ge htest
        rw [hK]; nlinarith
      have := phi_le_zero hK0 hγ0 hγη hgt
      exact ⟨hℓ', by linarith⟩

/-- The induction step of Proposition 3.1 with `η_k = 4/(k + 4)`. -/
theorem baseline_alg {K h h' : ℝ} (k : ℕ) (hK : 0 ≤ K) (hh : h ≤ 8 * K / (k + 3))
    (hrec : h' ≤ (1 - eta 4 k) * h + eta 4 k ^ 2 * (K / 2)) : h' ≤ 8 * K / (k + 4) := by
  have hη : eta 4 (k : ℤ) = 4 / ((k : ℝ) + 4) := by simp [eta]
  rw [hη] at hrec
  have hk4 : (0 : ℝ) < k + 4 := by positivity
  have hk3 : (0 : ℝ) < k + 3 := by positivity
  have hcoef : 0 ≤ 1 - 4 / ((k : ℝ) + 4) := by
    rw [sub_nonneg, div_le_one hk4]; have : (0 : ℝ) ≤ k := by positivity
    linarith
  have h2 := mul_le_mul_of_nonneg_left hh hcoef
  have key0 : (k : ℝ) / ((k + 4) * (k + 3)) + 1 / (k + 4) ^ 2 ≤ 1 / (k + 4) := by
    rw [div_add_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) hk4]
    have hk0 : (0 : ℝ) ≤ k := by positivity
    nlinarith [mul_nonneg hk0 (sq_nonneg ((k : ℝ) + 4)), sq_nonneg ((k : ℝ) + 4),
      mul_nonneg (mul_nonneg hk0 hk0) hk0]
  have key := mul_le_mul_of_nonneg_left key0 (by positivity : (0 : ℝ) ≤ 8 * K)
  have e1 : (1 - 4 / ((k : ℝ) + 4)) * (8 * K / (k + 3)) =
      8 * K * ((k : ℝ) / ((k + 4) * (k + 3))) := by
    field_simp; ring
  have e2 : (4 / ((k : ℝ) + 4)) ^ 2 * (K / 2) = 8 * K * (1 / (k + 4) ^ 2) := by
    field_simp; ring
  have e3 : 8 * K / ((k : ℝ) + 4) = 8 * K * (1 / (k + 4)) := by ring
  rw [e3]
  nlinarith

/-- The first step is a Frank–Wolfe step of length `1` and a progress step. -/
theorem olafw_first {V : Finset E} {f : E → ℝ} {L : ℝ} {x : ℕ → E} {S : ℕ → Finset E}
    {lam : ℕ → E → ℝ} {ℓ : ℕ → ℕ} (hrun : IsOLAFWRun V f L x S lam ℓ)
    (hconv : ConvexOn ℝ (convexHull ℝ (↑V : Set E)) f)
    (hdiff : ∀ y ∈ convexHull ℝ (↑V : Set E), DifferentiableAt ℝ f y)
    (hsm : IsSmoothOn (convexHull ℝ (↑V : Set E)) f L) (hL : 0 ≤ L)
    {xStar : E} (hxs : xStar ∈ minimizers (convexHull ℝ (↑V : Set E)) f) :
    ℓ 1 = 1 ∧ f (x 1) - f xStar ≤ L * Metric.diam (↑V : Set E) ^ 2 / 2 := by
  have h2 := progress_steps_bound hrun 1
  have hℓ0 := hrun.2.2.2.1
  rcases olafw_step hrun hconv hdiff hsm hL hxs 0 with
    ⟨v, -, -, a, -, -, ⟨hℓ', h1, -⟩ | ⟨hℓ', -⟩⟩
  · rw [hℓ0] at hℓ' h1
    have hη : eta 4 ((0 : ℕ) : ℤ) = 1 := by simp [eta]
    rw [hη] at h1
    refine ⟨hℓ', by nlinarith [sub_nonneg.mpr (hxs.2 _ (subset_convexHull ℝ _ hrun.1))]⟩
  · rw [hℓ', hℓ0] at h2; omega

/-- **Proposition 5.7.** -/
theorem olafw_baseline_bound {V : Finset E} {f : E → ℝ} {L : ℝ} {x : ℕ → E} {S : ℕ → Finset E}
    {lam : ℕ → E → ℝ} {ℓ : ℕ → ℕ} (hconv : ConvexOn ℝ (convexHull ℝ (↑V : Set E)) f)
    (hdiff : ∀ y ∈ convexHull ℝ (↑V : Set E), DifferentiableAt ℝ f y)
    (hsm : IsSmoothOn (convexHull ℝ (↑V : Set E)) f L) (hL : 0 ≤ L)
    (hrun : IsOLAFWRun V f L x S lam ℓ)
    {xStar : E} (hxs : xStar ∈ minimizers (convexHull ℝ (↑V : Set E)) f) :
    ∀ t : ℕ, 1 ≤ t → f (x t) - f xStar ≤ 16 * L * Metric.diam (↑V : Set E) ^ 2 / (t + 6) := by
  set D := Metric.diam (↑V : Set E) with hD
  have hK : 0 ≤ L * D ^ 2 := by positivity
  have key : ∀ t, 1 ≤ t → f (x t) - f xStar ≤ 8 * (L * D ^ 2) / (ℓ t + 3) := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base =>
      obtain ⟨hℓ1, h1⟩ := olafw_first hrun hconv hdiff hsm hL hxs
      rw [hℓ1]; push_cast
      have : L * D ^ 2 / 2 ≤ 8 * (L * D ^ 2) / (1 + 3) := by nlinarith
      linarith
    | succ t ht ih =>
      rcases olafw_step hrun hconv hdiff hsm hL hxs t with
        ⟨v, -, -, a, -, -, ⟨hℓ', h1, -⟩ | ⟨hℓ', hle⟩⟩
      · rw [hℓ']; push_cast
        rw [← hD] at h1
        have := baseline_alg (h' := f (x (t + 1)) - f xStar) (ℓ t) hK ih h1
        rw [show ((ℓ t : ℕ) : ℝ) + 1 + 3 = (ℓ t : ℝ) + 4 by ring]
        exact this
      · rw [hℓ']; exact le_trans hle ih
  intro t ht
  have h2 := progress_steps_bound hrun t
  refine le_trans (key t ht) ?_
  have h2' : (t : ℝ) ≤ 2 * ℓ t := by exact_mod_cast h2
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- Scaling through the pyramidal width (Lemma 5.8) and the Hölderian error bound:
`(ω/μ) h^{1-θ} ≤ f'(x)(a - v)` for an away vertex `a` and a Frank–Wolfe vertex `v`. -/
theorem pyramidal_gap {V : Finset E} {f : E → ℝ} {μ θ : ℝ} {x : E} {S : Finset E} {lam : E → ℝ}
    (hinv : Inv V x S lam) (hconv : ConvexOn ℝ (convexHull ℝ (↑V : Set E)) f)
    (hdiff : ∀ y ∈ convexHull ℝ (↑V : Set E), DifferentiableAt ℝ f y)
    (heb : IsHolderErrorBound (convexHull ℝ (↑V : Set E)) f μ θ) (hμ : 0 < μ) (hθ : θ < 1)
    {xStar : E} (hxs : xStar ∈ minimizers (convexHull ℝ (↑V : Set E)) f)
    {v a : E} (hvV : v ∈ V) (hv : ∀ w ∈ V, fderiv ℝ f x v ≤ fderiv ℝ f x w) (ha : a ∈ S)
    (haS : ∀ w ∈ S, fderiv ℝ f x w ≤ fderiv ℝ f x a) :
    AwayStepFW.pyramidalWidth V / μ * (f x - f xStar) ^ (1 - θ) ≤ fderiv ℝ f x (a - v) := by
  set g := fderiv ℝ f x with hg
  set ω := AwayStepFW.pyramidalWidth V with hω
  have hPc : IsCompact (convexHull ℝ (↑V : Set E)) := V.finite_toSet.isCompact_convexHull (𝕜 := ℝ)
  have hxP : x ∈ convexHull ℝ (↑V : Set E) :=
    convexHull_mono (by exact_mod_cast hinv.sub) hinv.mem_convexHull
  have hgav : 0 ≤ g (a - v) := by
    have h1 := hinv.apply_le g haS
    have h2 := hinv.le_apply g hv
    rw [map_sub]; linarith
  have hω0 : 0 ≤ ω := by
    rw [hω, AwayStepFW.pyramidalWidth]
    apply Real.sSup_nonneg
    intro r hr; exact hr.1
  rcases (sub_nonneg.mpr (hxs.2 x hxP)).eq_or_lt with h0 | hpos
  · rw [← h0, Real.zero_rpow (by linarith : (0 : ℝ) < 1 - θ).ne', mul_zero]; exact hgav
  obtain ⟨y, hyM, hxy, -, hmain, -⟩ := Lemmata.FrankWolfe.Proof.heb_scaling
    (convexHull ℝ (↑V : Set E)) f μ θ hPc hconv hdiff heb xStar hxs x hxP (by linarith)
  have hscale := Lemmata.AwayStepFW.Proof.scaling_via_pyramidal_width V S hinv.sub x
    hinv.mem_convexHull y hyM.1 g a ha haS v hvV hv
  rw [← hω] at hscale
  have hnorm : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have h1 : ω * ((f x - f xStar) ^ (1 - θ) * ‖x - y‖) ≤ ω * (μ * g (x - y)) :=
    mul_le_mul_of_nonneg_left hmain hω0
  have h2 : μ * (ω * g (x - y)) ≤ μ * (g (a - v) * ‖x - y‖) :=
    mul_le_mul_of_nonneg_left hscale hμ.le
  have h3 : (ω / μ * (f x - f xStar) ^ (1 - θ)) * (μ * ‖x - y‖) ≤ g (a - v) * (μ * ‖x - y‖) := by
    have e : (ω / μ * (f x - f xStar) ^ (1 - θ)) * (μ * ‖x - y‖) =
        ω * ((f x - f xStar) ^ (1 - θ) * ‖x - y‖) := by field_simp
    rw [e]; nlinarith
  exact le_of_mul_le_mul_right h3 (by positivity)

theorem eta4_antitone_nat {k₁ k₂ : ℕ} (h : k₁ ≤ k₂) :
    eta 4 ((k₂ : ℤ) - 2) ≤ eta 4 ((k₁ : ℤ) - 2) := by
  unfold eta
  push_cast
  have : (k₁ : ℝ) ≤ k₂ := by exact_mod_cast h
  have h0 : (0 : ℝ) ≤ k₁ := by positivity
  apply div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)

/-- **Theorem 5.9.** -/
theorem olafw_rate_bound {V : Finset E} {f : E → ℝ} {L μ θ : ℝ} {x : ℕ → E} {S : ℕ → Finset E}
    {lam : ℕ → E → ℝ} {ℓ : ℕ → ℕ} (hconv : ConvexOn ℝ (convexHull ℝ (↑V : Set E)) f)
    (hdiff : ∀ y ∈ convexHull ℝ (↑V : Set E), DifferentiableAt ℝ f y)
    (hsm : IsSmoothOn (convexHull ℝ (↑V : Set E)) f L) (hL : 0 < L)
    (hD : 0 < Metric.diam (↑V : Set E)) (hω : 0 < AwayStepFW.pyramidalWidth V)
    (heb : IsHolderErrorBound (convexHull ℝ (↑V : Set E)) f μ θ) (hμ : 0 < μ)
    (hθ : θ ∈ Set.Icc (0 : ℝ) (1 / 2)) (hrun : IsOLAFWRun V f L x S lam ℓ)
    {xStar : E} (hxs : xStar ∈ minimizers (convexHull ℝ (↑V : Set E)) f) :
    ∀ t : ℕ, 1 ≤ t → f (x t) - f xStar ≤
      max (eta 4 ((((t + 1) / 2 : ℕ) : ℤ) - 2) ^ (1 / (1 - θ)) *
          (L * Metric.diam (↑V : Set E) ^ 2 / 2))
        ((eta 4 ((((t + 1) / 2 : ℕ) : ℤ) - 2) *
            (2 * μ * L * Metric.diam (↑V : Set E) ^ 2 / AwayStepFW.pyramidalWidth V)) ^
            (1 / (1 - θ)) +
          eta 4 ((((t + 1) / 2 : ℕ) : ℤ) - 2) ^ 2 * (L * Metric.diam (↑V : Set E) ^ 2 / 2)) := by
  set D := Metric.diam (↑V : Set E) with hDdef
  set ω := AwayStepFW.pyramidalWidth V with hωdef
  set B := L * D ^ 2 / 2 with hB
  have hBpos : 0 < B := by positivity
  set A := ω / (4 * μ) with hA
  have hApos : 0 < A := by positivity
  have hθ1 : θ < 1 := by linarith [hθ.2]
  have hinv := olafw_inv hrun
  have hP : ∀ τ, x τ ∈ convexHull ℝ (↑V : Set E) := fun τ =>
    convexHull_mono (by exact_mod_cast (hinv τ).sub) (hinv τ).mem_convexHull
  have hh0 : ∀ τ, 0 ≤ f (x τ) - f xStar := fun τ => sub_nonneg.mpr (hxs.2 _ (hP τ))
  set e := 1 / (2 * (1 - θ)) with he
  set Q := eta 4 (((1 : ℕ) : ℤ) - 2) * eta 4 (((1 : ℕ) : ℤ) - 1) with hQ
  have hQpos : 0 < Q := mul_pos (etaL_pos (by norm_num) _ (by omega))
    (etaL_pos (by norm_num) _ (by omega))
  have hinvt : ∀ t, 1 ≤ t →
      f (x t) - f xStar ≤ max (seqX 4 e Q B (ℓ t)) (seqY 4 e A B 1 (ℓ t)) := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base =>
      obtain ⟨hℓ1, h1⟩ := olafw_first hrun hconv hdiff hsm hL.le hxs
      rw [hℓ1]
      refine le_max_of_le_left ?_
      simp only [seqX]
      rw [← hQ, div_self hQpos.ne', Real.one_rpow, one_mul]
      exact h1
    | succ t ht ih =>
      rcases olafw_step hrun hconv hdiff hsm hL.le hxs t with
        ⟨v, hvV, hv, a, ha, haS, ⟨hℓ', h1, h2⟩ | ⟨hℓ', hle⟩⟩
      · rw [hℓ']
        rw [← hDdef, ← hB] at h1 h2
        have hgap := pyramidal_gap (hinv t) hconv hdiff heb hμ hθ1 hxs hvV hv ha haS
        rw [← hωdef] at hgap
        have hη0 := eta4_pos_nat (ℓ t)
        have hrec : f (x (t + 1)) - f xStar ≤ (1 - 2 / 4 * eta 4 (ℓ t)) * (f (x t) - f xStar) -
            eta 4 (ℓ t) * A * 1 * (f (x t) - f xStar) ^ (1 - θ) + eta 4 (ℓ t) ^ 2 * B * 1 := by
          have h3 : eta 4 (ℓ t) * (2 * A * (f (x t) - f xStar) ^ (1 - θ)) ≤
              eta 4 (ℓ t) * (fderiv ℝ f (x t) (a - v) / 2) := by
            apply mul_le_mul_of_nonneg_left _ hη0.le
            have e2 : 2 * A = ω / μ / 2 := by rw [hA]; field_simp; ring
            rw [e2]; linarith
          nlinarith
        exact seq_step (ℓ t) (by norm_num) hθ hApos hBpos one_pos hQpos hBpos.le
          ⟨zero_le_one, le_rfl⟩ (hh0 t) hrec ih
      · rw [hℓ']; exact le_trans hle ih
  intro t ht
  have hfin := seq_final (ℓ := 4) (ψ := θ) (A := A) (B := B) (C := 1) (K₀ := B) 1 (ℓ t)
    (by norm_num) hθ hApos hBpos one_pos hBpos.le le_rfl
  have hη1 : eta 4 (((1 : ℕ) : ℤ) - 1) = 1 := by simp [eta]
  have hk : (t + 1) / 2 ≤ ℓ t := by have := progress_steps_bound hrun t; omega
  have hmono := eta4_antitone_nat hk
  have hpos1 : 0 < eta 4 ((ℓ t : ℤ) - 2) := etaL_pos (by norm_num) _ (by omega)
  have hexp : 0 ≤ 1 / (1 - θ) := by apply div_nonneg zero_le_one; linarith
  refine le_trans (hinvt t ht) (le_trans hfin ?_)
  rw [hη1, div_one, mul_one]
  have hBA : ∀ η : ℝ, η * B / A = η * (2 * μ * L * D ^ 2 / ω) := by
    intro η; rw [hA, hB]; field_simp; ring
  rw [hBA]
  apply max_le_max
  · exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hpos1.le hmono hexp) hBpos.le
  · apply add_le_add
    · apply Real.rpow_le_rpow (by positivity) _ hexp
      exact mul_le_mul_of_nonneg_right hmono (by positivity)
    · exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hpos1.le hmono 2) hBpos.le

namespace Proof

universe u

theorem drop_step : DropStep := drop_step_bound

theorem progress_steps : ProgressSteps.{u} := by
  intro E _ _ V f L x S lam ℓ hrun t
  exact progress_steps_bound hrun t

theorem olafw_baseline : OLAFWBaseline.{u} := by
  intro E _ _ V f L x S lam ℓ hconv hdiff hsm hL hrun xStar hxs t ht
  exact olafw_baseline_bound hconv hdiff hsm hL hrun hxs t ht

theorem olafw_rate : OLAFWRate.{u} := by
  intro E _ _ V f L μ θ x S lam ℓ hconv hdiff hsm hL hD hω heb hμ hθ hrun δ ω xStar hxs t ht
  exact olafw_rate_bound hconv hdiff hsm hL hD hω heb hμ hθ hrun hxs t ht

end Proof

end Lemmata.FWOpenLoop
