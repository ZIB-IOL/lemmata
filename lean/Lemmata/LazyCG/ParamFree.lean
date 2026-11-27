module

public import Lemmata.LazyCG.Proof

@[expose] public section

/-!
# The parameter-free lazy conditional gradient algorithm (Theorem 4.2, Corollary 4.3)

Negative answers halve `Φ` and keep `h_{t+1} ≤ 2 Φ_t`. A positive answer gains at least
`q(Φ) = min {Φ/(2K), Φ²/(2 C K²)}`, so while `Φ` stays fixed there are at most `2Φ/q(Φ)` positive
answers. Summing over the halvings gives `4K` per value `Φ > K C` and a geometric series below
`16 K² C/ε` for the values `ε/2 < Φ ≤ K C`.
-/

namespace Lemmata.LazyCG

open Lemmata.FrankWolfe

universe u

namespace Proof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
/-- The number of iterations among `1, …, t` that change `Φ`. -/
noncomputable def negCount (Φ : ℕ → ℝ) (t : ℕ) : ℕ :=
  ((Finset.Icc 1 t).filter (fun s => Φ s ≠ Φ (s - 1))).card

theorem negCount_zero (Φ : ℕ → ℝ) : negCount Φ 0 = 0 := by
  simp [negCount]

theorem negCount_succ (Φ : ℕ → ℝ) (t : ℕ) :
    negCount Φ (t + 1) = negCount Φ t + if Φ (t + 1) ≠ Φ t then 1 else 0 := by
  classical
  unfold negCount
  rw [show Finset.Icc 1 (t + 1) = insert (t + 1) (Finset.Icc 1 t) by
    ext s
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega]
  rw [Finset.filter_insert]
  simp only [Nat.add_sub_cancel]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · simp

/-- The basic invariants of Algorithm 7: the primal gap is at most `2 Φ_t`, and `Φ_t` is `Φ₀`
halved once per iteration that changes it. -/
theorem pf_invariants {P : Set E} {f : E → ℝ} {K : ℝ} {x : ℕ → E} {Φ : ℕ → ℝ}
    (hconv : ConvexOn ℝ Set.univ f) (hdiff : Differentiable ℝ f)
    (hrun : IsParamFreeLCGRun P f K x Φ) {xStar : E} (hxs : xStar ∈ minimizers P f)
    (h1 : f (x 1) - f xStar ≤ 2 * Φ 0) :
    ∀ t, f (x (t + 1)) - f xStar ≤ 2 * Φ t ∧ Φ t = Φ 0 / 2 ^ negCount Φ t := by
  intro t
  induction t with
  | zero => exact ⟨h1, by simp [negCount_zero]⟩
  | succ t ih =>
    obtain ⟨hinv, hΦ⟩ := ih
    rcases hrun.2 (t + 1) (by omega) with ⟨v, -, -, γ, -, -, hls, hΦ'⟩ | ⟨hle, hx', hΦ'⟩
    · simp only [Nat.add_sub_cancel] at hls hΦ'
      have h0 := hls 0 ⟨le_rfl, zero_le_one⟩
      simp only [zero_smul, add_zero] at h0
      refine ⟨by rw [hΦ']; linarith, ?_⟩
      rw [negCount_succ]
      simp only [hΦ', ne_eq, not_true_eq_false, ↓reduceIte, add_zero]
      exact hΦ
    · simp only [Nat.add_sub_cancel] at hle hΦ'
      have h2 := add_fderiv_le_of_convexOn hconv hdiff (x (t + 1)) xStar
      have h3 := hle xStar hxs.1
      have h4 : fderiv ℝ f (x (t + 1)) (xStar - x (t + 1)) =
          -fderiv ℝ f (x (t + 1)) (x (t + 1) - xStar) := by rw [← map_neg, neg_sub]
      refine ⟨by rw [hx', hΦ']; linarith, ?_⟩
      rw [negCount_succ]
      by_cases hz : Φ t = 0
      · have h5 : Φ (t + 1) = Φ t := by rw [hΦ', hz]; simp
        simp only [h5, ne_eq, not_true_eq_false, ↓reduceIte, add_zero]
        exact hΦ
      · have h5 : Φ (t + 1) ≠ Φ t := by rw [hΦ']; intro h; apply hz; linarith
        simp only [h5, ne_eq, not_false_eq_true, ↓reduceIte]
        rw [hΦ', hΦ, pow_succ]
        field_simp

/-- If the gap is still above `ε`, at most `⌈log₂ (Φ₀/ε)⌉₊` halvings have happened. -/
theorem negCount_le {Φ₀ ε : ℝ} (hε : 0 < ε) {n : ℕ} (h : ε < 2 * (Φ₀ / 2 ^ n)) :
    n ≤ ⌈Real.logb 2 (Φ₀ / ε)⌉₊ := by
  have h2n : (2 : ℝ) ^ n * ε < 2 * Φ₀ := by
    have hp : (0 : ℝ) < 2 ^ n := by positivity
    rw [mul_div_assoc', lt_div_iff₀ hp] at h
    linarith
  have hΦ₀ : 0 < Φ₀ := by
    have : 0 < (2 : ℝ) ^ n * ε := by positivity
    linarith
  have hlt : (n : ℝ) < Real.logb 2 (2 * Φ₀ / ε) := by
    rw [Real.lt_logb_iff_rpow_lt (by norm_num) (by positivity), Real.rpow_natCast,
      lt_div_iff₀ hε]
    exact h2n
  rw [show 2 * Φ₀ / ε = 2 * (Φ₀ / ε) by ring, Real.logb_mul (by norm_num) (by positivity),
    Real.logb_self_eq_one (by norm_num)] at hlt
  have hc := Nat.le_ceil (Real.logb 2 (Φ₀ / ε))
  have : (n : ℝ) < 1 + ⌈Real.logb 2 (Φ₀ / ε)⌉₊ := by linarith
  have : n < 1 + ⌈Real.logb 2 (Φ₀ / ε)⌉₊ := by exact_mod_cast this
  omega

theorem param_free_negatives : ParamFreeNegatives.{u} := by
  intro E _ _ P f K x Φ hconv hdiff hrun xStar hxs h1 ε hε N hN
  obtain ⟨hinv, hΦ⟩ := pf_invariants hconv hdiff hrun hxs h1 N
  show negCount Φ N ≤ _
  apply negCount_le hε
  rw [← hΦ]
  linarith

/-- The guaranteed progress of a positive answer. -/
noncomputable def pfq (K C φ : ℝ) : ℝ := min (φ / (2 * K)) (φ ^ 2 / (2 * C * K ^ 2))

theorem pf_progress {P : Set E} {f : E → ℝ} {C K : ℝ} (hcurv : HasCurvature P f C) (hC : 0 < C)
    (hK : 1 ≤ K) {x v : E} (hx : x ∈ P) (hv : v ∈ P) {φ : ℝ} (hφ : 0 ≤ φ)
    (hgt : φ / K < fderiv ℝ f x (x - v)) {x' : E}
    (hls : ∀ s ∈ Set.Icc (0 : ℝ) 1, f x' ≤ f (x + s • (v - x))) :
    f x' ≤ f x - pfq K C φ := by
  have hK0 : 0 < K := by linarith
  have key : ∀ s ∈ Set.Icc (0 : ℝ) 1, f x' ≤ f x - s * (φ / K) + C / 2 * s ^ 2 := by
    intro s hs
    have h1 := hls s hs
    have h2 := hcurv x hx v hv s hs
    have h3 : fderiv ℝ f x (v - x) = -fderiv ℝ f x (x - v) := by rw [← map_neg, neg_sub]
    rw [h3] at h2
    have h4 : s * (φ / K) ≤ s * fderiv ℝ f x (x - v) := mul_le_mul_of_nonneg_left hgt.le hs.1
    nlinarith
  by_cases hbig : K * C ≤ φ
  · have h1 := key 1 ⟨zero_le_one, le_rfl⟩
    have h2 : pfq K C φ ≤ φ / (2 * K) := min_le_left _ _
    have h3 : C / 2 ≤ φ / (2 * K) := by
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]
      nlinarith
    have h4 : φ / K = 2 * (φ / (2 * K)) := by field_simp
    linarith
  · push Not at hbig
    set s := φ / (K * C) with hs
    have hs0 : 0 ≤ s := by positivity
    have hs1 : s ≤ 1 := by
      rw [hs, div_le_one (by positivity)]
      exact hbig.le
    have h1 := key s ⟨hs0, hs1⟩
    have h2 : pfq K C φ ≤ φ ^ 2 / (2 * C * K ^ 2) := min_le_right _ _
    have h3 : s * (φ / K) - C / 2 * s ^ 2 = φ ^ 2 / (2 * C * K ^ 2) := by
      rw [hs]
      field_simp
      ring
    linarith

set_option maxHeartbeats 1000000 in
theorem param_free_rate : ParamFreeRate.{u} := by
  intro E _ _ P f C K x Φ hP hconv hdiff hcurv hC hK hrun xStar hxs h1 ε hε N hN
  classical
  have hK0 : 0 < K := by linarith
  have hinvs := pf_invariants hconv hdiff hrun hxs h1
  by_contra hgap
  push Not at hgap
  obtain ⟨hinvN, hΦN⟩ := hinvs N
  have hn := negCount_le hε (show ε < 2 * (Φ 0 / 2 ^ negCount Φ N) by rw [← hΦN]; linarith)
  have hΦ0 : 0 < Φ 0 := by
    have h2 : 0 < 2 * (Φ 0 / 2 ^ negCount Φ N) := by rw [← hΦN]; linarith
    have hp : (0 : ℝ) < 2 ^ negCount Φ N := by positivity
    by_contra h
    push Not at h
    have : Φ 0 / 2 ^ negCount Φ N ≤ 0 := div_nonpos_of_nonpos_of_nonneg h hp.le
    linarith
  have hΦpos : ∀ t, 0 < Φ t := fun t => by rw [(hinvs t).2]; positivity
  have hxP : ∀ t, 1 ≤ t → x t ∈ P := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => exact hrun.1
    | succ t ht ih =>
      rcases hrun.2 t ht with ⟨v, hv, -, γ, hγ, hx', -, -⟩ | ⟨-, hx', -⟩
      · rw [hx']
        exact hP.add_smul_sub_mem ih hv hγ
      · rw [hx']
        exact ih
  have hh0 : ∀ t, 1 ≤ t → 0 ≤ f (x t) - f xStar := fun t ht => by
    linarith [hxs.2 _ (hxP t ht)]
  have hqpos : ∀ φ, 0 < φ → 0 < pfq K C φ := fun φ hφ => by
    simp only [pfq]
    exact lt_min (by positivity) (by positivity)
  set w : ℝ → ℝ := fun φ => 2 * φ / pfq K C φ with hw
  set W : ℕ → ℝ := fun n => ∑ j ∈ Finset.range n, w (Φ 0 / 2 ^ j) with hW
  have hamort : ∀ t : ℕ, (t : ℝ) - negCount Φ t ≤
      W (negCount Φ t) + (2 * Φ t - (f (x (t + 1)) - f xStar)) / pfq K C (Φ t) := by
    intro t
    induction t with
    | zero =>
      simp only [negCount_zero, Nat.cast_zero, sub_zero, hW, Finset.range_zero,
        Finset.sum_empty, zero_add]
      exact div_nonneg (by linarith [(hinvs 0).1]) (hqpos _ (hΦpos 0)).le
    | succ t ih =>
      have hqt := hqpos _ (hΦpos t)
      rcases hrun.2 (t + 1) (by omega) with ⟨v, hv, hgt, γ, -, -, hls, hΦ'⟩ | ⟨-, hx', hΦ'⟩
      · simp only [Nat.add_sub_cancel] at hgt hls hΦ'
        have hprog := pf_progress hcurv hC hK (hxP (t + 1) (by omega)) hv (hΦpos t).le hgt hls
        have hnc : negCount Φ (t + 1) = negCount Φ t := by
          rw [negCount_succ]
          simp [hΦ']
        rw [hnc, hΦ']
        have h2 : (2 * Φ t - (f (x (t + 1)) - f xStar)) / pfq K C (Φ t) + 1 ≤
            (2 * Φ t - (f (x (t + 1 + 1)) - f xStar)) / pfq K C (Φ t) := by
          rw [div_add_one hqt.ne', div_le_div_iff_of_pos_right hqt]
          linarith
        push_cast
        linarith
      · simp only [Nat.add_sub_cancel] at hΦ'
        have hne : Φ (t + 1) ≠ Φ t := by
          rw [hΦ']
          intro h
          linarith [hΦpos t]
        have hnc : negCount Φ (t + 1) = negCount Φ t + 1 := by
          rw [negCount_succ]
          simp only [hne, ne_eq, not_false_eq_true, ↓reduceIte]
        rw [hnc]
        have hWs : W (negCount Φ t + 1) = W (negCount Φ t) + w (Φ t) := by
          simp only [hW]
          rw [Finset.sum_range_succ, ← (hinvs t).2]
        have h1' : (2 * Φ t - (f (x (t + 1)) - f xStar)) / pfq K C (Φ t) ≤ w (Φ t) := by
          simp only [hw]
          apply div_le_div_of_nonneg_right _ hqt.le
          linarith [hh0 (t + 1) (by omega)]
        have h2' : 0 ≤ (2 * Φ (t + 1) - (f (x (t + 1 + 1)) - f xStar)) / pfq K C (Φ (t + 1)) :=
          div_nonneg (by linarith [(hinvs (t + 1)).1]) (hqpos _ (hΦpos _)).le
        push_cast
        linarith
  set n := negCount Φ N with hndef
  have hNb : (N : ℝ) - n ≤ W (n + 1) := by
    have h1' := hamort N
    have h2 : (2 * Φ N - (f (x (N + 1)) - f xStar)) / pfq K C (Φ N) ≤ w (Φ N) := by
      simp only [hw]
      apply div_le_div_of_nonneg_right _ (hqpos _ (hΦpos N)).le
      linarith [hh0 (N + 1) (by omega)]
    have hWs : W (n + 1) = W n + w (Φ N) := by
      simp only [hW]
      rw [Finset.sum_range_succ, ← hΦN]
    linarith
  have hwle : ∀ φ, 0 < φ → w φ ≤ (if K * C < φ then 4 * K else 0) + 4 * C * K ^ 2 / φ := by
    intro φ hφ
    simp only [hw, pfq]
    split_ifs with hbig
    · have hh := mul_lt_mul_of_pos_left hbig (by positivity : (0 : ℝ) < 2 * K * φ)
      have e1 : min (φ / (2 * K)) (φ ^ 2 / (2 * C * K ^ 2)) = φ / (2 * K) :=
        min_eq_left (by rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith [hh])
      rw [e1]
      have e2 : 2 * φ / (φ / (2 * K)) = 4 * K := by field_simp; ring
      rw [e2]
      have : 0 ≤ 4 * C * K ^ 2 / φ := by positivity
      linarith
    · push Not at hbig
      have hh := mul_le_mul_of_nonneg_left hbig (by positivity : (0 : ℝ) ≤ 2 * K * φ)
      have e1 : min (φ / (2 * K)) (φ ^ 2 / (2 * C * K ^ 2)) = φ ^ 2 / (2 * C * K ^ 2) :=
        min_eq_right (by rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith [hh])
      rw [e1]
      have e2 : 2 * φ / (φ ^ 2 / (2 * C * K ^ 2)) = 4 * C * K ^ 2 / φ := by field_simp; ring
      rw [e2]
      simp
  have hsum1 : ∑ j ∈ Finset.range (n + 1), (if K * C < Φ 0 / 2 ^ j then 4 * K else 0) ≤
      4 * K * ⌈Real.logb 2 (Φ 0 / (K * C))⌉₊ := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hcard : ((Finset.range (n + 1)).filter (fun j => K * C < Φ 0 / 2 ^ j)).card ≤
        ⌈Real.logb 2 (Φ 0 / (K * C))⌉₊ := by
      calc _ ≤ (Finset.range ⌈Real.logb 2 (Φ 0 / (K * C))⌉₊).card := by
            apply Finset.card_le_card
            intro j hj
            simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
            have hp : (0 : ℝ) < 2 ^ j := by positivity
            have h1' : (2 : ℝ) ^ j < Φ 0 / (K * C) := by
              rw [lt_div_iff₀ (by positivity)]
              rw [lt_div_iff₀ hp] at hj
              linarith
            have h2 : (j : ℝ) < Real.logb 2 (Φ 0 / (K * C)) := by
              rw [Real.lt_logb_iff_rpow_lt (by norm_num) (by positivity), Real.rpow_natCast]
              exact h1'
            have h3 := Nat.le_ceil (Real.logb 2 (Φ 0 / (K * C)))
            exact_mod_cast (lt_of_lt_of_le h2 h3)
        _ = _ := Finset.card_range _
    have h4 : (((Finset.range (n + 1)).filter (fun j => K * C < Φ 0 / 2 ^ j)).card : ℝ) ≤
        ⌈Real.logb 2 (Φ 0 / (K * C))⌉₊ := by exact_mod_cast hcard
    nlinarith
  have hsum2 : ∑ j ∈ Finset.range (n + 1), 4 * C * K ^ 2 / (Φ 0 / 2 ^ j) ≤
      8 * C * K ^ 2 / Φ N := by
    have e : ∀ j : ℕ, 4 * C * K ^ 2 / (Φ 0 / 2 ^ j) = (4 * C * K ^ 2 / Φ 0) * 2 ^ j :=
      fun j => by field_simp
    simp only [e, ← Finset.mul_sum]
    have hg : ∑ j ∈ Finset.range (n + 1), (2 : ℝ) ^ j = 2 ^ (n + 1) - 1 := by
      rw [geom_sum_eq (by norm_num)]
      norm_num
    rw [hg, hΦN, show 8 * C * K ^ 2 / (Φ 0 / 2 ^ n) = (4 * C * K ^ 2 / Φ 0) * (2 * 2 ^ n) by
      field_simp
      ring]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [pow_succ]
    linarith
  have hWb : W (n + 1) ≤ 4 * K * ⌈Real.logb 2 (Φ 0 / (K * C))⌉₊ + 8 * C * K ^ 2 / Φ N := by
    calc W (n + 1) = ∑ j ∈ Finset.range (n + 1), w (Φ 0 / 2 ^ j) := rfl
      _ ≤ ∑ j ∈ Finset.range (n + 1),
            ((if K * C < Φ 0 / 2 ^ j then 4 * K else 0) + 4 * C * K ^ 2 / (Φ 0 / 2 ^ j)) :=
          Finset.sum_le_sum (fun j _ => hwle _ (by positivity))
      _ = _ := Finset.sum_add_distrib
      _ ≤ _ := add_le_add hsum1 hsum2
  have hΦNε : ε / 2 < Φ N := by linarith
  have h8 : 8 * C * K ^ 2 / Φ N < 16 * K ^ 2 * C / ε := by
    rw [div_lt_div_iff₀ (hΦpos N) hε]
    have hh := mul_lt_mul_of_pos_left hΦNε (by positivity : (0 : ℝ) < 16 * K ^ 2 * C)
    nlinarith [hh]
  have hn' : (n : ℝ) ≤ ⌈Real.logb 2 (Φ 0 / ε)⌉₊ := by exact_mod_cast hn
  linarith

end Proof

end Lemmata.LazyCG
