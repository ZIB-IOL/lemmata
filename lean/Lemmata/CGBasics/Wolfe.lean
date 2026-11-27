module

public import Lemmata.CGBasics.LowerBound
public import Lemmata.CGBasics.Vanilla
public import Lemmata.FrankWolfe.Polytope.Faces
public import Mathlib.Analysis.PSeries

@[expose] public section

/-!
# Wolfe's lower bound (Lemma 2.10 and Theorem 2.8)

On the dyadic block `[2^k, 2^{k+1})`, Cauchy–Schwarz and the tail bound at `t = 2^k` give
`(∑ γ_i)² ≤ C/(k log 2)^{2+δ}`, so the block sums are at most a constant times `k^{-(1+δ/2)}`,
which is summable.
-/

namespace Lemmata.CGBasics

open Lemmata.FrankWolfe

namespace Proof

theorem square_tail_summable : SquareTailSummable := by
  intro γ C δ t₀ hγ hδ hsq htail
  set k₀ := t₀ + 2 with hk₀
  set c' := Real.sqrt (max C 0) / Real.log 2 ^ (1 + δ / 2) with hc'
  set b : ℕ → ℝ := fun k => c' * (k : ℝ) ^ (-(1 + δ / 2)) with hb
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc'0 : 0 ≤ c' := by positivity
  have hbsum : Summable b := (Real.summable_nat_rpow.mpr (by linarith)).mul_left c'
  have hb0 : ∀ k, 0 ≤ b k := fun k => by positivity
  have hblock : ∀ k, k₀ ≤ k → ∑ i ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), γ i ≤ b k := by
    intro k hk
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
    have h2k : t₀ ≤ 2 ^ k := le_trans (by omega : t₀ ≤ k) (Nat.lt_two_pow_self).le
    have hcard : (Finset.Ico (2 ^ k) (2 ^ (k + 1))).card = 2 ^ k := by
      rw [Nat.card_Ico, pow_succ]; omega
    have hsq_le : ∑ i ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), γ i ^ 2 ≤ ∑' j, γ (2 ^ k + j) ^ 2 := by
      have hs' : Summable (fun j => γ (2 ^ k + j) ^ 2) :=
        ((summable_nat_add_iff (2 ^ k)).mpr hsq).congr (fun j => by rw [add_comm])
      rw [Finset.sum_Ico_eq_sum_range]
      exact hs'.sum_le_tsum _ (fun j _ => sq_nonneg _)
    have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.Ico (2 ^ k) (2 ^ (k + 1))) (f := γ)
    rw [hcard] at hcs
    have ht := htail (2 ^ k) h2k
    have hlogk : Real.log ((2 ^ k : ℕ) : ℝ) = k * Real.log 2 := by
      push_cast; rw [Real.log_pow]
    have hpos2k : (0 : ℝ) < ((2 ^ k : ℕ) : ℝ) := by positivity
    have hkl : 0 < (k : ℝ) * Real.log 2 := by positivity
    -- `(∑ γ)² ≤ C / (k log 2)^{2+δ} ≤ (b k)²`
    have hsq_block : (∑ i ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), γ i) ^ 2 ≤
        max C 0 / ((k : ℝ) * Real.log 2) ^ (2 + δ) := by
      have h1 : (∑ i ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), γ i) ^ 2 ≤
          ((2 ^ k : ℕ) : ℝ) * (C / (((2 ^ k : ℕ) : ℝ) * Real.log ((2 ^ k : ℕ) : ℝ) ^ (2 + δ))) := by
        calc _ ≤ ((2 ^ k : ℕ) : ℝ) * ∑ i ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), γ i ^ 2 := by
              exact_mod_cast hcs
          _ ≤ _ := mul_le_mul_of_nonneg_left (hsq_le.trans ht) hpos2k.le
      rw [hlogk] at h1
      have h3 : ((2 ^ k : ℕ) : ℝ) * (C / (((2 ^ k : ℕ) : ℝ) * ((k : ℝ) * Real.log 2) ^ (2 + δ))) =
          C / ((k : ℝ) * Real.log 2) ^ (2 + δ) := by
        field_simp
      rw [h3] at h1
      exact h1.trans (div_le_div_of_nonneg_right (le_max_left _ _) (by positivity))
    have hbk : b k ^ 2 = max C 0 / ((k : ℝ) * Real.log 2) ^ (2 + δ) := by
      have hk0 : (0 : ℝ) < k := by linarith
      rw [hb, hc']
      simp only
      rw [mul_pow, div_pow, Real.sq_sqrt (le_max_right _ _), ← Real.rpow_natCast,
        ← Real.rpow_natCast, ← Real.rpow_mul hlog2.le, ← Real.rpow_mul hk0.le,
        Real.mul_rpow hk0.le hlog2.le]
      push_cast
      rw [show (1 + δ / 2) * 2 = 2 + δ by ring, show -(1 + δ / 2) * 2 = -(2 + δ) by ring,
        Real.rpow_neg hk0.le]
      field_simp
    have hS0 : 0 ≤ ∑ i ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), γ i :=
      Finset.sum_nonneg (fun i _ => hγ i)
    exact (pow_le_pow_iff_left₀ hS0 (hb0 k) two_ne_zero).mp (hbk ▸ hsq_block)
  set A := ∑ i ∈ Finset.range (2 ^ k₀), γ i with hA
  have hpartial : ∀ K, k₀ ≤ K →
      ∑ i ∈ Finset.range (2 ^ K), γ i ≤ A + ∑ k ∈ Finset.Ico k₀ K, b k := by
    intro K hK
    induction K, hK using Nat.le_induction with
    | base => simp [hA]
    | succ K hK ih =>
      rw [← Finset.sum_range_add_sum_Ico _ (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ K)),
        Finset.sum_Ico_succ_top hK]
      have := hblock K hK
      linarith
  refine summable_of_sum_range_le hγ (c := A + ∑' k, b k) (fun N => ?_)
  have hN : N ≤ 2 ^ (N + k₀) := (Nat.lt_two_pow_self).le.trans
    (Nat.pow_le_pow_right (by norm_num) (by omega))
  calc ∑ i ∈ Finset.range N, γ i ≤ ∑ i ∈ Finset.range (2 ^ (N + k₀)), γ i :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hN) (fun i _ _ => hγ i)
    _ ≤ A + ∑ k ∈ Finset.Ico k₀ (N + k₀), b k := hpartial _ (by omega)
    _ ≤ A + ∑' k, b k := by
        have := hbsum.sum_le_tsum (Finset.Ico k₀ (N + k₀)) (fun k _ => hb0 k)
        linarith

/-- On a compact set of non-minimizers a continuous function stays above the minimum by a margin. -/
theorem gap_on_compact {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {K : Set E}
    {f : E → ℝ} (hf : Continuous f) (hK : IsCompact K) {fStar : ℝ}
    (hdisj : ∀ y ∈ K, fStar < f y) : ∃ η > 0, ∀ y ∈ K, fStar + η ≤ f y := by
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · exact ⟨1, one_pos, by simp [hKe]⟩
  obtain ⟨y0, hy0, hmin⟩ := hK.exists_isMinOn hKne hf.continuousOn
  exact ⟨f y0 - fStar, by linarith [hdisj y0 hy0], fun y hy => by
    linarith [isMinOn_iff.mp hmin y hy]⟩

/-- A linear functional minimized over `V` at `v` is minimized over `conv V` at `v`. -/
theorem le_on_hull {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {V : Finset E}
    (g : StrongDual ℝ E) {v : E} (hv : ∀ w ∈ V, g v ≤ g w) {y : E}
    (hy : y ∈ convexHull ℝ (↑V : Set E)) : g v ≤ g y :=
  convexHull_min (fun w hw => hv w hw) (convex_halfSpace_ge g.toLinearMap.isLinear (g v)) hy

theorem wolfe_lower_bound : WolfeLowerBound.{u} := by
  intro E _ _ V ψ f L ν x v γ t₀ hL hconv hsm hΩ hx0 hrun hxt₀ hval xStar hxs δ hδ
  classical
  set P := convexHull ℝ (↑V : Set E) with hP
  set D := Metric.diam (↑V : Set E) with hD
  set F := exposedFace V ψ with hF
  have hPc : IsCompact P := V.finite_toSet.isCompact_convexHull (𝕜 := ℝ)
  have hfc : Continuous f := hsm.1.continuous
  have hxP : ∀ t, x t ∈ P := iterates_mem (convex_convexHull ℝ _) hx0 (fun t =>
    ⟨subset_convexHull ℝ _ (by exact_mod_cast (hrun t).1), (hrun t).2.2.1, (hrun t).2.2.2.1⟩)
  have hvP : ∀ t, v t ∈ P := fun t => subset_convexHull ℝ _ (by exact_mod_cast (hrun t).1)
  have hfP : ∀ y ∈ P, f xStar ≤ f y := fun y hy => hxs.2 y hy
  have hg0 : ∀ t, 0 ≤ fderiv ℝ f (x t) (x t - v t) := fun t => by
    rw [map_sub]; linarith [le_on_hull (fderiv ℝ f (x t)) (hrun t).2.1 (hxP t)]
  have hgh : ∀ t, f (x t) - f xStar ≤ fderiv ℝ f (x t) (x t - v t) := fun t => by
    have h1 := add_fderiv_le_of_convexOn hconv hsm.1 (x t) xStar
    have h2 := le_on_hull (fderiv ℝ f (x t)) (hrun t).2.1 hxs.1
    rw [map_sub] at h1 ⊢
    linarith
  have hdist : ∀ t, ‖x t - v t‖ ≤ D := fun t => by
    rw [← dist_eq_norm, hD, ← convexHull_diam]
    exact Metric.dist_le_diam_of_mem hPc.isBounded (hxP t) (hvP t)
  have hprog := fun t => (hrun t).2.2.2.2.2
  have hmono : ∀ t, f (x (t + 1)) ≤ f (x t) := fun t => by
    have := hprog t
    have : 0 ≤ fderiv ℝ f (x t) (x t - v t) ^ 2 / (2 * L * ‖x t - v t‖ ^ 2) := by positivity
    linarith
  have hanti : Antitone (fun t => f (x t)) := antitone_nat_of_succ_le hmono
  -- the functional `ℓ = M - ψ` vanishes exactly on the face
  obtain ⟨w0, hw0⟩ : F.Nonempty := by
    obtain ⟨w, hw, hmax⟩ := V.exists_max_image ψ
      (by
        by_contra h
        rw [Finset.not_nonempty_iff_eq_empty] at h
        have h0 := hxP 0
        rw [hP, h] at h0
        simp at h0)
    exact ⟨w, Finset.mem_filter.mpr ⟨hw, hmax⟩⟩
  have hw0V : w0 ∈ V := (Finset.mem_filter.mp hw0).1
  set M := ψ w0 with hM
  have hMmax : ∀ u ∈ V, ψ u ≤ M := (Finset.mem_filter.mp hw0).2
  set ℓ : E → ℝ := fun y => M - ψ y with hℓ
  have hℓP : ∀ y ∈ P, 0 ≤ ℓ y := fun y hy => by
    have : y ∈ {z | ψ z ≤ M} :=
      convexHull_min (fun u hu => hMmax u hu) (convex_halfSpace_le ψ.toLinearMap.isLinear M) hy
    simp only [hℓ]; simp only [Set.mem_ofPred_eq] at this; linarith
  have hℓF : ∀ y ∈ P, ℓ y = 0 → y ∈ convexHull ℝ (↑F : Set E) := fun y hy h0 => by
    rw [hF, mem_convexHull_exposedFace_iff ψ hy]
    intro u hu
    have := hMmax u hu
    simp only [hℓ] at h0
    linarith
  have hℓstep : ∀ t, ℓ (x (t + 1)) = (1 - γ t) * ℓ (x t) + γ t * ℓ (v t) := fun t => by
    simp only [hℓ, (hrun t).2.2.2.1, map_add, map_smul, map_sub, smul_eq_mul]
    ring
  have hℓv : ∀ t, 0 ≤ ℓ (v t) := fun t => hℓP _ (hvP t)
  -- (1) the iterates stay off the face
  have hℓpos : ∀ t, t₀ ≤ t → 0 < ℓ (x t) := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base =>
      rcases lt_or_eq_of_le (hℓP _ (hxP t₀)) with h | h
      · exact h
      · exact absurd (hℓF _ (hxP t₀) h.symm) hxt₀
    | succ t ht ih =>
      rw [hℓstep]
      have hγ := (hrun t).2.2.1
      rcases lt_or_eq_of_le hγ.2 with hγ1 | hγ1
      · have : 0 < (1 - γ t) * ℓ (x t) := mul_pos (by linarith) ih
        nlinarith [hℓv t, hγ.1]
      · rw [hγ1, sub_self, zero_mul, one_mul, zero_add]
        rcases lt_or_eq_of_le (hℓv t) with hpos | hzero
        · exact hpos
        · exfalso
          have hvF : v t ∈ F := Finset.mem_filter.mpr ⟨(hrun t).1, fun u hu => by
            have := hMmax u hu; simp only [hℓ] at hzero; linarith⟩
          have hx1 : x (t + 1) = v t := by rw [(hrun t).2.2.2.1, hγ1, one_smul]; abel
          have h1 := hval (v t) hvF
          have h2 := hanti (show t₀ ≤ t + 1 by omega)
          simp only at h2
          rw [hx1] at h2
          linarith
  -- (2) the primal gap tends to `0`
  have hh0 : ∀ ε > 0, ∃ T, ∀ t ≥ T, f (x t) - f xStar < ε := by
    intro ε hε
    by_contra hcon
    push Not at hcon
    have hall : ∀ t, ε ≤ f (x t) - f xStar := fun t => by
      obtain ⟨s, hs, hle⟩ := hcon t
      have := hanti hs; simp only at this; linarith
    have hd : ∀ t, 0 < ‖x t - v t‖ := fun t => by
      rcases eq_or_lt_of_le (norm_nonneg (x t - v t)) with h | h
      · have : x t - v t = 0 := norm_eq_zero.mp h.symm
        have := hgh t; rw [‹x t - v t = 0›, map_zero] at this; linarith [hall t]
      · exact h
    have hDpos : 0 < D := lt_of_lt_of_le (hd 0) (hdist 0)
    set c := ε ^ 2 / (2 * L * D ^ 2) with hc
    have hcpos : 0 < c := by positivity
    have hdec : ∀ t, c ≤ f (x t) - f (x (t + 1)) := fun t => by
      have hg := (hall t).trans (hgh t)
      calc c ≤ fderiv ℝ f (x t) (x t - v t) ^ 2 / (2 * L * D ^ 2) :=
            div_le_div_of_nonneg_right (pow_le_pow_left₀ hε.le hg 2) (by positivity)
        _ ≤ fderiv ℝ f (x t) (x t - v t) ^ 2 / (2 * L * ‖x t - v t‖ ^ 2) := by
            apply div_le_div_of_nonneg_left (sq_nonneg _) (by have := hd t; positivity)
            have := pow_le_pow_left₀ (norm_nonneg _) (hdist t) 2
            nlinarith
        _ ≤ _ := hprog t
    have htel : ∀ n : ℕ, (n : ℝ) * c ≤ f (x 0) - f (x n) := fun n => by
      induction n with
      | zero => simp
      | succ n ih => push_cast; linarith [hdec n]
    obtain ⟨n, hn⟩ := exists_nat_gt ((f (x 0) - f xStar) / c)
    have h1 := htel n
    have h2 := hfP _ (hxP n)
    rw [div_lt_iff₀ hcpos] at hn
    linarith
  -- (3) the iterates approach the face
  have hℓ0 : ∀ ε > 0, ∃ T, ∀ t ≥ T, ℓ (x t) < ε := by
    intro ε hε
    have hK : IsCompact (P ∩ {y | ε ≤ ℓ y}) := hPc.inter_right
      (isClosed_le continuous_const (continuous_const.sub ψ.continuous))
    obtain ⟨η, hη, hηK⟩ := gap_on_compact hfc hK (fStar := f xStar) (fun y hy => by
      rcases lt_or_eq_of_le (hfP y hy.1) with h | h
      · exact h
      · exfalso
        have hymin : y ∈ minimizers P f := ⟨hy.1, fun z hz => h ▸ hfP z hz⟩
        have hyF := hΩ hymin
        have : ℓ y = 0 := by
          have h3 := (mem_convexHull_exposedFace_iff ψ hy.1).mp hyF w0 hw0V
          have h4 := hℓP y hy.1
          simp only [hℓ] at h4 ⊢; linarith
        have := hy.2; simp only [Set.mem_ofPred_eq] at this; linarith)
    obtain ⟨T, hT⟩ := hh0 η hη
    refine ⟨T, fun t ht => ?_⟩
    by_contra hc
    push Not at hc
    have := hηK (x t) ⟨hxP t, hc⟩
    have := hT t ht
    linarith
  -- (4) the iterates stay away from the vertices
  have hwgap : ∀ w ∈ V, f xStar < f w := fun w hw => by
    by_cases hwF : w ∈ F
    · have h1 := hval w hwF
      have h2 := hfP _ (hxP t₀)
      linarith
    · rcases lt_or_eq_of_le (hfP w (subset_convexHull ℝ _ (by exact_mod_cast hw))) with h | h
      · exact h
      · exfalso
        have hwmin : w ∈ minimizers P f :=
          ⟨subset_convexHull ℝ _ (by exact_mod_cast hw), fun z hz => h ▸ hfP z hz⟩
        have := (mem_convexHull_exposedFace_iff ψ hwmin.1).mp (hΩ hwmin)
        exact hwF (Finset.mem_filter.mpr ⟨hw, this⟩)
  obtain ⟨wm, hwm, hwmmin⟩ := V.exists_min_image (fun w => f w - f xStar) ⟨w0, hw0V⟩
  set η := (f wm - f xStar) / 2 with hη
  have hηpos : 0 < η := by have := hwgap wm hwm; rw [hη]; linarith
  have hball : ∀ w ∈ V, ∃ r > 0, ∀ y, ‖y - w‖ < r → f w - η < f y := fun w _ => by
    obtain ⟨r, hr, hr'⟩ := Metric.continuous_iff.mp hfc w η hηpos
    exact ⟨r, hr, fun y hy => by
      have := hr' y (by rwa [dist_eq_norm]); rw [Real.dist_eq, abs_lt] at this; linarith⟩
  choose! rad hrad0 hrad using hball
  obtain ⟨wr, hwr, hwrmin⟩ := V.exists_min_image rad ⟨w0, hw0V⟩
  set r := rad wr with hr
  have hr0 : 0 < r := hrad0 wr hwr
  obtain ⟨Tr, hTr⟩ := hh0 η hηpos
  have hfar : ∀ t ≥ Tr, ∀ w ∈ V, r ≤ ‖x t - w‖ := fun t ht w hw => by
    by_contra hc
    push Not at hc
    have h1 := hrad w hw (x t) (lt_of_lt_of_le hc (hwrmin w hw))
    have h2 : f wm - f xStar ≤ f w - f xStar := hwmmin w hw
    linarith [hTr t ht]
  -- (5) if the bound failed from some point on, the step sizes would be summable
  rw [Filter.frequently_atTop]
  intro N
  by_contra hcon
  push Not at hcon
  set T1 := max (max N t₀) (max Tr 2) with hT1
  set c := 2 * L * ν ^ 2 / r ^ 2 with hc
  have hc0 : 0 ≤ c := by positivity
  have hγ0 : ∀ i, 0 ≤ γ i := fun i => (hrun i).2.2.1.1
  have hγsq : ∀ t, T1 ≤ t → γ t ^ 2 ≤ c * (f (x t) - f (x (t + 1))) := by
    intro t ht
    have hd := hfar t (by omega) (v t) (hrun t).1
    have hdpos : 0 < ‖x t - v t‖ := lt_of_lt_of_le hr0 hd
    set g := fderiv ℝ f (x t) (x t - v t) with hg
    have h1 : γ t ^ 2 ≤ (ν * g / ‖x t - v t‖ ^ 2) ^ 2 :=
      pow_le_pow_left₀ (hγ0 t) (hrun t).2.2.2.2.1 2
    have h2 : (ν * g / ‖x t - v t‖ ^ 2) ^ 2 ≤ c * (g ^ 2 / (2 * L * ‖x t - v t‖ ^ 2)) := by
      have hr2 : r ^ 2 ≤ ‖x t - v t‖ ^ 2 := pow_le_pow_left₀ hr0.le hd 2
      have e1 : (ν * g / ‖x t - v t‖ ^ 2) ^ 2 =
          ν ^ 2 * g ^ 2 / (‖x t - v t‖ ^ 2 * ‖x t - v t‖ ^ 2) := by ring
      have e2 : c * (g ^ 2 / (2 * L * ‖x t - v t‖ ^ 2)) =
          ν ^ 2 * g ^ 2 / (r ^ 2 * ‖x t - v t‖ ^ 2) := by
        rw [hc]; field_simp
      rw [e1, e2]
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_right hr2 (by positivity)
    have h3 := mul_le_mul_of_nonneg_left (hprog t) hc0
    linarith
  have htel : ∀ t, T1 ≤ t → ∀ n,
      ∑ i ∈ Finset.range n, γ (t + i) ^ 2 ≤ c * (f (x t) - f xStar) := by
    intro t ht n
    have key : ∑ i ∈ Finset.range n, γ (t + i) ^ 2 ≤ c * (f (x t) - f (x (t + n))) := by
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Finset.sum_range_succ]
        have h1 := hγsq (t + n) (by omega)
        have e : c * (f (x t) - f (x (t + (n + 1)))) =
            c * (f (x t) - f (x (t + n))) + c * (f (x (t + n)) - f (x (t + n + 1))) := by
          rw [show t + (n + 1) = t + n + 1 by ring]; ring
        rw [e]
        linarith
    have hlow := hfP _ (hxP (t + n))
    have := mul_le_mul_of_nonneg_left
      (show f (x t) - f (x (t + n)) ≤ f (x t) - f xStar by linarith) hc0
    linarith
  have hsumsq : Summable (fun i => γ i ^ 2) := by
    have hs : Summable (fun i => γ (T1 + i) ^ 2) :=
      summable_of_sum_range_le (fun i => sq_nonneg _) (htel T1 le_rfl)
    exact (summable_nat_add_iff T1).mp (hs.congr (fun i => by rw [add_comm]))
  have htail : ∀ t : ℕ, T1 ≤ t →
      ∑' i, γ (t + i) ^ 2 ≤ c * (L * D ^ 2) / (t * Real.log t ^ (2 + δ)) := by
    intro t ht
    have h1 : ∑' i, γ (t + i) ^ 2 ≤ c * (f (x t) - f xStar) :=
      Real.tsum_le_of_sum_range_le (fun i => sq_nonneg _) (htel t ht)
    have h2 := hcon t (by omega)
    have h3 := mul_le_mul_of_nonneg_left h2.le hc0
    rw [mul_div_assoc]
    linarith
  have hsum := square_tail_summable γ (c * (L * D ^ 2)) δ T1 hγ0 hδ hsumsq htail
  obtain ⟨T2, hT21, hT2⟩ : ∃ T2, T1 ≤ T2 ∧ ∑' i, γ (i + T2) ≤ 1 / 2 := by
    obtain ⟨T, hT⟩ := ((tendsto_sum_nat_add γ).eventually
      (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).exists_forall_of_atTop
    exact ⟨max T T1, le_max_right _ _, (hT _ (le_max_left _ _)).le⟩
  have hpos2 := hℓpos T2 (by omega)
  have hshift : Summable (fun i => γ (i + T2)) := (summable_nat_add_iff T2).mpr hsum
  have hpart : ∀ n, ∑ i ∈ Finset.range n, γ (T2 + i) ≤ 1 / 2 := fun n => by
    have := hshift.sum_le_tsum (Finset.range n) (fun i _ => hγ0 _)
    rw [Finset.sum_congr rfl (fun i _ => by rw [add_comm T2 i])]
    linarith
  have hweight : ∀ n, (1 - ∑ i ∈ Finset.range n, γ (T2 + i)) * ℓ (x T2) ≤ ℓ (x (T2 + n)) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [show T2 + (n + 1) = T2 + n + 1 by ring, hℓstep, Finset.sum_range_succ]
      have hγn := (hrun (T2 + n)).2.2.1
      have hS : 0 ≤ ∑ i ∈ Finset.range n, γ (T2 + i) := Finset.sum_nonneg (fun i _ => hγ0 _)
      have ha := mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr hγn.2)
      have hb := mul_nonneg (mul_nonneg hγn.1 hS) hpos2.le
      have hc' := mul_nonneg hγn.1 (hℓv (T2 + n))
      nlinarith
  obtain ⟨T, hT⟩ := hℓ0 (ℓ (x T2) / 2) (by linarith)
  have h1 := hweight (max T T2 - T2)
  have h2 := hpart (max T T2 - T2)
  have h3 := hT (T2 + (max T T2 - T2)) (by omega)
  nlinarith

end Proof

end Lemmata.CGBasics
