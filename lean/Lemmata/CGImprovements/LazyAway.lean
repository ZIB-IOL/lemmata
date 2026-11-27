module

public import Lemmata.CGImprovements.Lazy
public import Lemmata.BPCG.Proof

@[expose] public section

/-!
# Lazy away-step Frank–Wolfe (Theorem 3.16)

The active-set invariants are those of away-step Frank–Wolfe. A negative answer certifies
`h_t ≤ φ_t` and, through geometric strong convexity, `μ δ² h_t ≤ 2 φ_t²`; after the halving of `φ`
this gives `μ δ² h_t ≤ 8 φ_t²` for the following steps. Steps that do not drop a vertex gain at
least `φ_t²/(2 K² L D²)`.
-/

namespace Lemmata.CGImprovements

open Lemmata.FrankWolfe

namespace Proof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
theorem inv_away_step {V : Finset E} {x : E} {S : Finset E} {lam : E → ℝ}
    (h : Lemmata.AwayStepFW.Proof.Inv V x S lam) {a : E} (ha : a ∈ S) (hlt : lam a < 1) {γ : ℝ}
    (hγ0 : 0 ≤ γ) (hγ : γ ≤ lam a / (1 - lam a)) :
    Lemmata.AwayStepFW.Proof.Inv V (x - γ • (a - x))
      (if γ = lam a / (1 - lam a) then S.erase a else S)
      (fun u => (1 + γ) * lam u - if u = a then γ else 0) := by
  set lam' : E → ℝ := fun u => (1 + γ) * lam u - if u = a then γ else 0 with hlam'
  have h1a : 0 < 1 - lam a := by linarith
  have hγa : γ * (1 - lam a) ≤ lam a := by rwa [le_div_iff₀ h1a] at hγ
  have hnn : ∀ u, 0 ≤ lam' u := fun u => by
    simp only [hlam']
    have := h.nonneg u
    split_ifs with hua
    · rw [hua]; nlinarith
    · nlinarith
  have hsupp : ∀ u ∉ S, lam' u = 0 := fun u hu => by
    have hua : u ≠ a := fun e => hu (e ▸ ha)
    simp [hlam', hua, h.supp u hu]
  have hsum : ∑ u ∈ S, lam' u = 1 := by
    simp only [hlam', Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_ite_eq', ha, ite_true,
      h.sum]
    ring
  have hrep : ∑ u ∈ S, lam' u • u = x - γ • (a - x) := by
    simp only [hlam', sub_smul, mul_smul, Finset.sum_sub_distrib, ← Finset.smul_sum, ite_smul,
      zero_smul, Finset.sum_ite_eq', ha, ite_true, ← h.rep]
    module
  by_cases hdrop : γ = lam a / (1 - lam a)
  · rw [ite_eq_left hdrop]
    have hza : lam' a = 0 := by
      simp only [hlam', ite_true]
      rw [hdrop]; field_simp; ring
    refine ⟨(Finset.erase_subset a S).trans h.sub, hnn, fun u hu => ?_, ?_, ?_⟩
    · by_cases hua : u = a
      · rw [hua]; exact hza
      · exact hsupp u (fun huS => hu (Finset.mem_erase.mpr ⟨hua, huS⟩))
    · rw [Finset.sum_erase _ hza]; exact hsum
    · rw [Finset.sum_erase _ (by rw [hza, zero_smul])]; exact hrep.symm
  · rw [ite_eq_right hdrop]
    exact ⟨h.sub, hnn, hsupp, hsum, hrep.symm⟩

open Classical in
theorem lazy_afw_run_inv {V : Finset E} {f : E → ℝ} {L K : ℝ} (hL : 0 ≤ L) (hK : 0 < K)
    {x : ℕ → E} {S : ℕ → Finset E} {lam : ℕ → E → ℝ} {φ : ℕ → ℝ}
    (hφ : ∀ t, 0 ≤ φ t) (h : IsLazyAFWRun V f L K x S lam φ) :
    ∀ t, Lemmata.AwayStepFW.Proof.Inv V (x t) (S t) (lam t) := by
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
    rcases hsteps t with ⟨a, ha, hga, γ, hγ, hx', hlam', hS', -⟩ |
        ⟨v, hv, hgv, γ, hγ, hx', hlam', hS', -⟩ | ⟨-, -, hx', hS', hlam', -⟩
    · have hg0 : 0 < fderiv ℝ f (x t) (a - x t) := lt_of_le_of_lt (div_nonneg (hφ t) hK.le) hga
      have hax : a ≠ x t := fun e => by rw [e, sub_self, map_zero] at hg0; exact lt_irrefl _ hg0
      have hlt : lam t a < 1 := by
        have hle : lam t a ≤ 1 := ih.sum ▸ Finset.single_le_sum (fun u _ => ih.nonneg u) ha
        rcases lt_or_eq_of_le hle with h1 | h1
        · exact h1
        · exfalso
          apply hax
          have h0 : ∑ u ∈ (S t).erase a, lam t u = 0 := by
            have hs := ih.sum
            rw [← Finset.add_sum_erase _ _ ha, h1] at hs
            linarith
          have hrest : ∀ u ∈ (S t).erase a, lam t u = 0 := fun u hu =>
            (Finset.sum_eq_zero_iff_of_nonneg (fun u _ => ih.nonneg u)).mp h0 u hu
          have hr := ih.rep
          rw [← Finset.add_sum_erase _ _ ha, h1, one_smul,
            Finset.sum_eq_zero (fun u hu => by rw [hrest u hu, zero_smul]), add_zero] at hr
          exact hr.symm
      have hla := ih.nonneg a
      have hγ0 : 0 ≤ γ := by
        rw [hγ]; exact le_min (div_nonneg hg0.le (by positivity)) (div_nonneg hla (by linarith))
      rw [hx', hlam', hS']
      exact inv_away_step ih ha hlt hγ0 (by rw [hγ]; exact min_le_right _ _)
    · have hg0 : 0 < fderiv ℝ f (x t) (x t - v) := lt_of_le_of_lt (div_nonneg (hφ t) hK.le) hgv
      have hγ01 : γ ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨by rw [hγ]; exact le_min (div_nonneg hg0.le (by positivity)) zero_le_one,
          by rw [hγ]; exact min_le_right _ _⟩
      rw [hx', hlam', hS']
      exact Lemmata.BPCG.Proof.inv_fw_step ih hv hγ01
    · rw [hx', hS', hlam']; exact ih

universe u

theorem lazy_away_rate : LazyAwayRate.{u} := by
  intro E _ _ V f L μ δ K x S lam φ hL hμ hδ hsc hconv hsm hstrong hK hrun xStar hxs hφ0 hφ0' ε hε
    t ht
  classical
  set D := Metric.diam (↑V : Set E) with hD
  set P := convexHull ℝ (↑V : Set E) with hP
  set h : ℕ → ℝ := fun t => f (x t) - f xStar with hh
  have hK0 : 0 < K := by linarith
  have hx0P : x 0 ∈ P := subset_convexHull ℝ _ (by exact_mod_cast hrun.1)
  have hφb : ∀ t, 0 ≤ φ t ∧ φ t ≤ φ 0 := by
    intro t
    induction t with
    | zero => exact ⟨by have := hxs.2 _ hx0P; linarith, le_rfl⟩
    | succ t ih =>
      rcases hrun.2.2.2 t with ⟨-, -, -, -, -, -, -, -, hφ'⟩ | ⟨-, -, -, -, -, -, -, -, hφ'⟩ |
          ⟨-, -, -, -, -, hφ'⟩
      · rw [hφ']; exact ih
      · rw [hφ']; exact ih
      · rw [hφ']; exact ⟨by linarith [ih.1], by linarith [ih.1, ih.2]⟩
  have inv := lazy_afw_run_inv (NNReal.coe_nonneg L) hK0 (fun t => (hφb t).1) hrun
  have hxP : ∀ t, x t ∈ P := fun t =>
    convexHull_mono (by exact_mod_cast (inv t).sub) (inv t).mem_convexHull
  have hh0 : ∀ t, 0 ≤ h t := fun t => by simp only [hh]; linarith [hxs.2 _ (hxP t)]
  have hPc : IsCompact P := V.finite_toSet.isCompact_convexHull (𝕜 := ℝ)
  have hdist : ∀ y ∈ P, ∀ z ∈ P, ‖y - z‖ ≤ D := fun y hy z hz => by
    rw [← dist_eq_norm, hD, ← convexHull_diam]
    exact Metric.dist_le_diam_of_mem hPc.isBounded hy hz
  -- the certificate bounds the primal gap
  have hcertgap : ∀ t, (∀ u ∈ V, fderiv ℝ f (x t) (x t - u) ≤ φ t) → h t ≤ φ t := fun t hc => by
    obtain ⟨w, hwV, hwmin⟩ := V.exists_min_image (fderiv ℝ f (x t)) ⟨x 0, hrun.1⟩
    have h1 := add_fderiv_le_of_convexOn hconv hsm.1 (x t) xStar
    have h2 := Lemmata.CGBasics.Proof.le_on_hull (fderiv ℝ f (x t)) hwmin hxs.1
    have h3 := hc w hwV
    simp only [hh]
    rw [map_sub] at h1 h3
    linarith
  have hγmax0 : ∀ t, ∀ a ∈ S t, 0 ≤ lam t a / (1 - lam t a) := fun t a ha => by
    have hle : lam t a ≤ 1 := (inv t).sum ▸ Finset.single_le_sum (fun u _ => (inv t).nonneg u) ha
    exact div_nonneg ((inv t).nonneg a) (by linarith)
  have hφK : ∀ t, φ t / (2 * K) ≥ φ t ^ 2 / (2 * K ^ 2 * (L * D ^ 2)) ∨ L * D ^ 2 = 0 := by
    intro t
    rcases eq_or_lt_of_le (by positivity : (0 : ℝ) ≤ L * D ^ 2) with h0 | hpos
    · exact Or.inr h0.symm
    · left
      rw [ge_iff_le, div_le_div_iff₀ (by positivity) (by positivity)]
      have hφL : φ t ≤ K * (L * D ^ 2) := by
        have h1 := (hφb t).2
        have h2 : L * D ^ 2 ≤ K * (L * D ^ 2) := le_mul_of_one_le_left hpos.le hK
        linarith
      have h2Kφ : (0 : ℝ) ≤ 2 * K * φ t :=
        mul_nonneg (mul_nonneg (by norm_num) hK0.le) (hφb t).1
      have := mul_le_mul_of_nonneg_left hφL h2Kφ
      linarith
  -- the three outcomes of an iteration
  have hout : ∀ t, ((∀ u ∈ S t, fderiv ℝ f (x t) (u - x t) ≤ φ t) ∧
        (∀ u ∈ V, fderiv ℝ f (x t) (x t - u) ≤ φ t) ∧ h (t + 1) = h t ∧ S (t + 1) = S t ∧
        φ (t + 1) = φ t / 2) ∨
      (h (t + 1) ≤ h t ∧ (S (t + 1)).card + 1 = (S t).card ∧ φ (t + 1) = φ t) ∨
      (h (t + 1) ≤ h t - φ t ^ 2 / (2 * K ^ 2 * (L * D ^ 2)) ∧
        (S (t + 1)).card ≤ (S t).card + 1 ∧ φ (t + 1) = φ t) := by
    intro t
    rcases hrun.2.2.2 t with ⟨a, ha, hga, γ, hγ, hx', -, hS', hφ'⟩ |
        ⟨v, hv, hgv, γ, hγ, hx', -, hS', hφ'⟩ | ⟨hcS, hcV, hx', hS', -, hφ'⟩
    · set G := fderiv ℝ f (x t) (a - x t) with hG
      have hG0 : 0 < G := lt_of_le_of_lt (div_nonneg (hφb t).1 hK0.le) hga
      have hd : 0 < ‖a - x t‖ := norm_pos_iff.mpr (fun e => by
        rw [e, map_zero] at hG; linarith)
      have hdD : ‖a - x t‖ ≤ D := hdist a (subset_convexHull ℝ _ (by exact_mod_cast (inv t).sub ha))
        (x t) (hxP t)
      have hdD2 : (L : ℝ) * ‖a - x t‖ ^ 2 ≤ L * D ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hd.le hdD 2) (NNReal.coe_nonneg L)
      have hq := Lemmata.BPCG.Proof.quad_along hsm (x t) (a - x t) γ
      rw [← hG, ← hx'] at hq
      have hc : 0 < (L : ℝ) * ‖a - x t‖ ^ 2 := by positivity
      have hγs : γ ≤ G / (L * ‖a - x t‖ ^ 2) := by rw [hγ]; exact min_le_left _ _
      have hγ0 : 0 ≤ γ := by
        rw [hγ]; exact le_min (div_nonneg hG0.le hc.le) (hγmax0 t a ha)
      have hγc : γ * (L * ‖a - x t‖ ^ 2) ≤ G := by rwa [le_div_iff₀ hc] at hγs
      by_cases hdrop : γ = lam t a / (1 - lam t a)
      · right; left
        refine ⟨?_, by rw [hS', ite_eq_left hdrop]; exact Finset.card_erase_add_one ha, hφ'⟩
        have h5 := mul_le_mul_of_nonneg_left hγc (by positivity : (0 : ℝ) ≤ γ / 2)
        have h6 := mul_nonneg hγ0 hG0.le
        simp only [hh]
        linarith
      · right; right
        refine ⟨?_, by rw [hS', ite_eq_right hdrop]; omega, hφ'⟩
        have hγv : γ = G / (L * ‖a - x t‖ ^ 2) := by
          rcases min_choice (G / (L * ‖a - x t‖ ^ 2)) (lam t a / (1 - lam t a)) with h1 | h1
          · rw [hγ, h1]
          · exact absurd (by rw [hγ, h1]) hdrop
        have hprog : γ * G - γ ^ 2 * L / 2 * ‖a - x t‖ ^ 2 = G ^ 2 / (2 * (L * ‖a - x t‖ ^ 2)) := by
          rw [hγv]; field_simp; ring
        have hDpos : 0 < (L : ℝ) * D ^ 2 :=
          mul_pos hL (lt_of_lt_of_le (by positivity) (pow_le_pow_left₀ hd.le hdD 2))
        have h1 : G ^ 2 / (2 * (L * D ^ 2)) ≤ G ^ 2 / (2 * (L * ‖a - x t‖ ^ 2)) :=
          div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
            (by linarith [hdD2])
        have h2 : φ t ^ 2 / (2 * K ^ 2 * (L * D ^ 2)) ≤ G ^ 2 / (2 * (L * D ^ 2)) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have hφG : φ t ≤ K * G := by rw [div_lt_iff₀ hK0] at hga; linarith
          have h5 := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hφb t).1 hφG 2)
            (by positivity : (0 : ℝ) ≤ 2 * (L * D ^ 2))
          rw [mul_pow] at h5
          linarith
        simp only [hh]
        linarith
    · set G := fderiv ℝ f (x t) (x t - v) with hG
      have hG0 : 0 < G := lt_of_le_of_lt (div_nonneg (hφb t).1 hK0.le) hgv
      have hd : 0 < ‖x t - v‖ := norm_pos_iff.mpr (fun e => by
        rw [e, map_zero] at hG; linarith)
      have hdD : ‖x t - v‖ ≤ D :=
        hdist (x t) (hxP t) v (subset_convexHull ℝ _ (by exact_mod_cast hv))
      have hdD2 : (L : ℝ) * ‖x t - v‖ ^ 2 ≤ L * D ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hd.le hdD 2) (NNReal.coe_nonneg L)
      have hq := Lemmata.BPCG.Proof.quad_along hsm (x t) (x t - v) γ
      rw [← hG, ← hx'] at hq
      have hc : 0 < (L : ℝ) * ‖x t - v‖ ^ 2 := by positivity
      have hDpos : 0 < (L : ℝ) * D ^ 2 :=
        mul_pos hL (lt_of_lt_of_le (by positivity) (pow_le_pow_left₀ hd.le hdD 2))
      have hφG : φ t ≤ K * G := by rw [div_lt_iff₀ hK0] at hgv; linarith
      right; right
      refine ⟨?_, ?_, hφ'⟩
      · simp only [hh]
        rcases le_total (G / (L * ‖x t - v‖ ^ 2)) 1 with hle | hle
        · rw [hγ, min_eq_left hle] at hq
          have hprog : G / (L * ‖x t - v‖ ^ 2) * G -
              (G / (L * ‖x t - v‖ ^ 2)) ^ 2 * L / 2 * ‖x t - v‖ ^ 2 =
              G ^ 2 / (2 * (L * ‖x t - v‖ ^ 2)) := by field_simp; ring
          have h1 : G ^ 2 / (2 * (L * D ^ 2)) ≤ G ^ 2 / (2 * (L * ‖x t - v‖ ^ 2)) :=
            div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
              (by linarith [hdD2])
          have h2 : φ t ^ 2 / (2 * K ^ 2 * (L * D ^ 2)) ≤ G ^ 2 / (2 * (L * D ^ 2)) := by
            rw [div_le_div_iff₀ (by positivity) (by positivity)]
            have h5 := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hφb t).1 hφG 2)
              (by positivity : (0 : ℝ) ≤ 2 * (L * D ^ 2))
            rw [mul_pow] at h5
            linarith
          linarith
        · rw [hγ, min_eq_right hle] at hq
          have hcG : (L : ℝ) * ‖x t - v‖ ^ 2 ≤ G := by rwa [le_div_iff₀ hc, one_mul] at hle
          have h3 : φ t / (2 * K) ≤ G / 2 := by
            rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
          rcases hφK t with h4 | h4
          · simp only [one_pow, one_mul] at hq
            linarith
          · linarith
      · rw [hS']
        split_ifs
        · simp
        · exact Finset.card_insert_le v (S t)
    · left
      exact ⟨hcS, hcV, by simp only [hh, hx'], hS', hφ'⟩
  have hmono : ∀ t, h (t + 1) ≤ h t := fun t => by
    rcases hout t with ⟨-, -, h1, -, -⟩ | ⟨h1, -, -⟩ | ⟨h1, -, -⟩
    · rw [h1]
    · exact h1
    · have : 0 ≤ φ t ^ 2 / (2 * K ^ 2 * (L * D ^ 2)) := by positivity
      linarith
  have hanti : Antitone h := antitone_nat_of_succ_le hmono
  rcases eq_or_lt_of_le (by positivity : (0 : ℝ) ≤ L * D ^ 2) with hK00 | hKpos
  · have h1 : h 0 ≤ 0 := by simp only [hh]; rw [← hK00] at hφ0'; linarith
    have h2 := hanti (Nat.zero_le t)
    have h3 : h t ≤ ε := by linarith
    simpa [hh] using h3
  set c := μ * δ ^ 2 / (16 * K ^ 2 * (L * D ^ 2)) with hc
  set q₀ := φ 0 ^ 2 / (2 * K ^ 2 * (L * D ^ 2)) with hq₀
  set n₀ := ⌈Real.logb 2 (φ 0 / ε)⌉₊ with hn₀
  have hc0 : 0 ≤ c := by positivity
  have hφε : φ 0 / 2 ^ n₀ ≤ ε := by
    rcases le_or_gt (φ 0) 0 with hφ | hφ
    · have : φ 0 / 2 ^ n₀ ≤ 0 := div_nonpos_of_nonpos_of_nonneg hφ (by positivity)
      linarith
    · rw [div_le_iff₀ (by positivity)]
      have h1 : Real.logb 2 (φ 0 / ε) ≤ n₀ := Nat.le_ceil _
      have h2 : φ 0 / ε ≤ (2 : ℝ) ^ (n₀ : ℝ) := by
        rw [← Real.logb_le_logb (b := 2) (by norm_num) (div_pos hφ hε) (by positivity),
          Real.logb_rpow (by norm_num) (by norm_num)]
        exact h1
      rw [Real.rpow_natCast, div_le_iff₀ hε] at h2
      linarith
  have hneg : ∀ t, (∀ u ∈ S t, fderiv ℝ f (x t) (u - x t) ≤ φ t) →
      (∀ u ∈ V, fderiv ℝ f (x t) (x t - u) ≤ φ t) → μ * δ ^ 2 * h t ≤ 2 * φ t ^ 2 := by
    intro t hcS hcV
    have hSne : (S t).Nonempty := by
      rcases (S t).eq_empty_or_nonempty with h0 | h0
      · have := (inv t).sum; rw [h0, Finset.sum_empty] at this; norm_num at this
      · exact h0
    obtain ⟨a, ha, haS⟩ := (S t).exists_max_image (fderiv ℝ f (x t)) hSne
    obtain ⟨w, hw, hwV⟩ := V.exists_min_image (fderiv ℝ f (x t)) ⟨x 0, hrun.1⟩
    have hgeo := Lemmata.AwayStepFW.Proof.geometric_strong_convexity V f μ δ hμ hδ hsc hstrong xStar
      hxs (S t) (inv t).sub (x t) (inv t).mem_convexHull a ha haS w hw hwV
    have h1 := hcS a ha
    have h2 := hcV w hw
    have h3 := (inv t).apply_le (fderiv ℝ f (x t)) haS
    have h4 := Lemmata.CGBasics.Proof.le_on_hull (fderiv ℝ f (x t)) hwV (hxP t)
    have hgaw : fderiv ℝ f (x t) (a - w) ≤ 2 * φ t := by rw [map_sub] at h1 h2 ⊢; linarith
    have hgaw0 : 0 ≤ fderiv ℝ f (x t) (a - w) := by rw [map_sub]; linarith
    have h5 := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * μ * δ ^ 2)).mp hgeo
    have h6 := pow_le_pow_left₀ hgaw0 hgaw 2
    have h7 : (2 * φ t) ^ 2 = 4 * φ t ^ 2 := by ring
    simp only [hh] at h5 ⊢
    linarith
  have hstate : ∀ t, ∃ n dr gpre gpost : ℕ, n + dr + gpre + gpost = t ∧
      (S t).card + dr ≤ 1 + gpre + gpost ∧ φ t = φ 0 / 2 ^ n ∧ (n₀ + 1 ≤ n → h t ≤ ε) ∧
      (n = 0 → gpost = 0 ∧ (gpre : ℝ) * q₀ ≤ h 0 - h t) ∧ (gpre : ℝ) * q₀ ≤ h 0 ∧
      (1 ≤ n → μ * δ ^ 2 * h t ≤ 8 * φ t ^ 2) ∧ h t ≤ Real.exp (-(c * gpost)) * h 0 := by
    intro t
    induction t with
    | zero =>
      refine ⟨0, 0, 0, 0, rfl, by rw [hrun.2.1]; simp, by simp, fun h => absurd h (by omega),
        fun _ => ⟨rfl, by simp⟩, by simp [hh0 0], fun h => absurd h (by omega), by simp⟩
    | succ t ih =>
      obtain ⟨n, dr, gpre, gpost, hsum, hcard, hφn, hε', hpre, hpre', hlin, hexp⟩ := ih
      rcases hout t with ⟨hcS, hcV, he, hS', hφ'⟩ | ⟨hle, hc', hφ'⟩ | ⟨hle, hc', hφ'⟩
      · refine ⟨n + 1, dr, gpre, gpost, by omega, by rw [hS']; omega,
          by rw [hφ', hφn, pow_succ]; field_simp, fun hN => ?_, fun h => absurd h (by omega),
          hpre', fun _ => ?_, by rw [he]; exact hexp⟩
        · rw [he]
          rcases Nat.lt_or_ge n (n₀ + 1) with hlt | hge
          · have hN0 : n = n₀ := by omega
            calc h t ≤ φ t := hcertgap t hcV
              _ = φ 0 / 2 ^ n := hφn
              _ = φ 0 / 2 ^ n₀ := by rw [hN0]
              _ ≤ ε := hφε
          · exact hε' hge
        · rw [he, hφ']
          have := hneg t hcS hcV
          nlinarith
      · refine ⟨n, dr + 1, gpre, gpost, by omega, by omega, by rw [hφ', hφn],
          fun hN => hle.trans (hε' hN), fun h0 => ⟨(hpre h0).1, by linarith [(hpre h0).2]⟩,
          hpre', fun h1 => ?_, hle.trans hexp⟩
        rw [hφ']
        have := hlin h1
        have := mul_le_mul_of_nonneg_left hle (by positivity : (0 : ℝ) ≤ μ * δ ^ 2)
        linarith
      · rcases Nat.eq_zero_or_pos n with hn0 | hn1
        · -- before the first negative answer: `φ_t = φ₀`
          have hφt : φ t = φ 0 := by rw [hφn, hn0, pow_zero, div_one]
          have hq : h (t + 1) ≤ h t - q₀ := by rw [hq₀, ← hφt]; exact hle
          obtain ⟨hgp, hpre0⟩ := hpre hn0
          refine ⟨n, dr, gpre + 1, gpost, by omega, by omega, by rw [hφ', hφn],
            fun hN => absurd hN (by omega), fun _ => ⟨hgp, ?_⟩, ?_, fun h => absurd h (by omega),
            ?_⟩
          · push_cast; linarith
          · push_cast; linarith [hh0 (t + 1)]
          · rw [hgp]; simp only [Nat.cast_zero, mul_zero, neg_zero, Real.exp_zero, one_mul]
            linarith [hanti (Nat.zero_le (t + 1))]
        · have hl := hlin hn1
          have hprog : c * h t ≤ φ t ^ 2 / (2 * K ^ 2 * (L * D ^ 2)) := by
            rw [hc, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
            have := mul_le_mul_of_nonneg_right hl
              (by positivity : (0 : ℝ) ≤ 2 * K ^ 2 * (L * D ^ 2))
            linarith
          have hstep : h (t + 1) ≤ Real.exp (-c) * h t := by
            have := Real.add_one_le_exp (-c)
            have := mul_le_mul_of_nonneg_right this (hh0 t)
            linarith
          refine ⟨n, dr, gpre, gpost + 1, by omega, by omega, by rw [hφ', hφn],
            fun hN => (hmono t).trans (hε' hN), fun h => absurd h (by omega),
            hpre', fun _ => ?_, ?_⟩
          · rw [hφ']
            have := mul_le_mul_of_nonneg_left (hmono t) (by positivity : (0 : ℝ) ≤ μ * δ ^ 2)
            linarith
          · calc h (t + 1) ≤ Real.exp (-c) * h t := hstep
              _ ≤ Real.exp (-c) * (Real.exp (-(c * gpost)) * h 0) :=
                mul_le_mul_of_nonneg_left hexp (Real.exp_pos _).le
              _ = Real.exp (-(c * ((gpost + 1 : ℕ) : ℝ))) * h 0 := by
                rw [← mul_assoc, ← Real.exp_add]; push_cast; ring_nf
  obtain ⟨n, dr, gpre, gpost, hsum, hcard, -, hε', -, hpre', -, hexp⟩ := hstate t
  by_cases hsmall : h 0 ≤ ε
  · have := hanti (Nat.zero_le t)
    have : h t ≤ ε := by linarith
    simpa [hh] using this
  push Not at hsmall
  have hh0pos : 0 < h 0 := lt_trans hε hsmall
  have hφ0pos : 0 < φ 0 := by
    have : 0 < f (x 0) - f xStar := hh0pos
    linarith
  set A := ⌈4 * K ^ 2 * L * D ^ 2 / φ 0⌉₊ with hA
  set B := ⌈16 * K ^ 2 * L * D ^ 2 / (μ * δ ^ 2) * Real.log ((f (x 0) - f xStar) / ε)⌉₊ with hB
  rcases Nat.lt_or_ge n (n₀ + 1) with hn | hn
  swap
  · simpa [hh] using hε' hn
  rcases Nat.lt_or_ge gpost B with hgp | hgp
  swap
  · have hcinv : c * (16 * K ^ 2 * L * D ^ 2 / (μ * δ ^ 2)) = 1 := by
      have hpos' : 0 < 16 * K ^ 2 * (L * D ^ 2) * (μ * δ ^ 2) :=
        mul_pos (mul_pos (mul_pos (by norm_num) (pow_pos hK0 2)) hKpos) (mul_pos hμ (pow_pos hδ 2))
      rw [hc, div_mul_div_comm,
        show μ * δ ^ 2 * (16 * K ^ 2 * L * D ^ 2) = 16 * K ^ 2 * (L * D ^ 2) * (μ * δ ^ 2) by ring]
      exact div_self hpos'.ne'
    have h1 : 16 * K ^ 2 * L * D ^ 2 / (μ * δ ^ 2) * Real.log ((f (x 0) - f xStar) / ε) ≤ B :=
      Nat.le_ceil _
    have h2 : (B : ℝ) ≤ gpost := by exact_mod_cast hgp
    have hcB : Real.log ((f (x 0) - f xStar) / ε) ≤ c * gpost := by
      calc Real.log ((f (x 0) - f xStar) / ε) =
            c * (16 * K ^ 2 * L * D ^ 2 / (μ * δ ^ 2) * Real.log ((f (x 0) - f xStar) / ε)) := by
            rw [← mul_assoc, hcinv, one_mul]
        _ ≤ c * B := mul_le_mul_of_nonneg_left h1 hc0
        _ ≤ c * gpost := mul_le_mul_of_nonneg_left h2 hc0
    have h3 : Real.exp (-(c * gpost)) ≤ Real.exp (-Real.log ((f (x 0) - f xStar) / ε)) :=
      Real.exp_le_exp.mpr (by linarith)
    have hpos : 0 < (f (x 0) - f xStar) / ε := div_pos hh0pos hε
    rw [show Real.exp (-Real.log ((f (x 0) - f xStar) / ε)) = ((f (x 0) - f xStar) / ε)⁻¹ by
      rw [Real.exp_neg, Real.exp_log hpos]] at h3
    have h4 : Real.exp (-(c * gpost)) * h 0 ≤ ε := by
      calc Real.exp (-(c * gpost)) * h 0 ≤ ((f (x 0) - f xStar) / ε)⁻¹ * h 0 :=
            mul_le_mul_of_nonneg_right h3 hh0pos.le
        _ = ε := by
            have : h 0 = f (x 0) - f xStar := rfl
            rw [this, inv_div]
            exact div_mul_cancel₀ ε hh0pos.ne'
    simpa [hh] using hexp.trans h4
  exfalso
  have hgpre : gpre ≤ A := by
    have h1 : (gpre : ℝ) * q₀ ≤ 2 * φ 0 := by
      have : h 0 ≤ 2 * φ 0 := by simp only [hh]; linarith
      linarith
    have hq : (gpre : ℝ) * φ 0 ^ 2 ≤ 2 * φ 0 * (2 * K ^ 2 * (L * D ^ 2)) := by
      rw [hq₀, mul_div_assoc', div_le_iff₀ (by positivity)] at h1
      exact h1
    have h2 : (gpre : ℝ) * φ 0 ≤ 4 * K ^ 2 * L * D ^ 2 := by
      have h3 : (gpre : ℝ) * φ 0 * φ 0 ≤ (4 * K ^ 2 * L * D ^ 2) * φ 0 := by
        have e1 : (gpre : ℝ) * φ 0 * φ 0 = (gpre : ℝ) * φ 0 ^ 2 := by ring
        have e2 : (4 * K ^ 2 * L * D ^ 2) * φ 0 = 2 * φ 0 * (2 * K ^ 2 * (L * D ^ 2)) := by ring
        rw [e1, e2]; exact hq
      exact le_of_mul_le_mul_right h3 hφ0pos
    have h4 : (gpre : ℝ) ≤ A := by
      have : (gpre : ℝ) ≤ 4 * K ^ 2 * L * D ^ 2 / φ 0 := by rw [le_div_iff₀ hφ0pos]; exact h2
      exact this.trans (Nat.le_ceil _)
    exact_mod_cast h4
  have hS1 : 1 ≤ (S t).card := by
    rcases Nat.eq_zero_or_pos (S t).card with h0 | h0
    · have := (inv t).sum
      rw [Finset.card_eq_zero.mp h0, Finset.sum_empty] at this
      norm_num at this
    · exact h0
  omega

end Proof

end Lemmata.CGImprovements
