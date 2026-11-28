module

public import Lemmata.FWCaratheodory.Hadamard
public import Lemmata.CGBasics.Main
public import Lemmata.FWOpenLoop.Interior

@[expose] public section

/-!
# Cardinality bounds (Corollaries 5.1, 5.3 and 7.1)

Every iteration adds at most one atom, so `x_t` is a convex combination of at most `t + 1` points.
The rates of the shared entries then bound the number of iterations: the vanilla rate of the basics
entry (Corollary 5.1), a linear rate for a target in the relative interior, from the interior gap
bound of the open-loop entry and the error bound of Lemma 3.1 (Corollary 5.3), and the linear rate
over strongly convex sets of the basics entry with `c = dist(x⋆, C)` (Corollary 7.1).
-/

namespace Lemmata.FWCaratheodory

open Lemmata.FrankWolfe Lemmata.CGBasics Lemmata.FWOpenLoop

universe u

/-- Sparse iterates. -/
theorem run_sparsity_bound {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] {C V : Set E}
    {f' : E → StrongDual ℝ E} {x v : ℕ → E} {γ : ℕ → ℝ} (hrun : IsFWRun C f' x v γ)
    (hx0 : x 0 ∈ V) (hv : ∀ t, v t ∈ V) :
    ∀ t : ℕ, ∃ S : Finset E, ↑S ⊆ V ∧ S.card ≤ t + 1 ∧ x t ∈ convexHull ℝ (↑S : Set E) := by
  classical
  intro t
  induction t with
  | zero =>
    refine ⟨{x 0}, by simpa using hx0, by simp, ?_⟩
    exact subset_convexHull ℝ _ (by simp)
  | succ t ih =>
    obtain ⟨S, hSV, hScard, hxS⟩ := ih
    obtain ⟨-, -, hγ, hx⟩ := hrun.2 t
    refine ⟨insert (v t) S, ?_, ?_, ?_⟩
    · intro y hy
      rw [Finset.coe_insert, Set.mem_insert_iff] at hy
      rcases hy with rfl | hy
      exacts [hv t, hSV hy]
    · exact (Finset.card_insert_le _ _).trans (by omega)
    · rw [hx]
      have h1 : x t ∈ convexHull ℝ (↑(insert (v t) S) : Set E) :=
        convexHull_mono (by rw [Finset.coe_insert]; exact Set.subset_insert _ _) hxS
      have h2 : v t ∈ convexHull ℝ (↑(insert (v t) S) : Set E) := subset_convexHull ℝ _ (by simp)
      exact (convex_convexHull ℝ _).add_smul_sub_mem h1 h2 hγ

/-- A short-step run is a Frank–Wolfe run. -/
theorem shortStep_isFWRun {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] {C : Set E}
    {f : E → ℝ} {L : NNReal} {x v : ℕ → E} {γ : ℕ → ℝ} (h : IsShortStepRun C f L x v γ) :
    IsFWRun C (fderiv ℝ f) x v γ :=
  ⟨h.1, fun t => ⟨(h.2 t).1, (h.2 t).2.1, (h.2 t).2.2.1, (h.2 t).2.2.2.1⟩⟩

/-- From a linear rate to an iteration count. -/
theorem linear_threshold {K A ε h : ℝ} {t : ℕ} (hK : 1 ≤ K) (hA : 0 ≤ A) (hε : 0 < ε)
    (ht1 : 1 ≤ t) (hh : h ≤ (1 - 1 / K) ^ (t - 1) * (A / 2))
    (ht : 1 + K * Real.log (A / ε ^ 2) ≤ t) : 2 * h ≤ ε ^ 2 := by
  rcases hA.eq_or_lt with hA0 | hApos
  · rw [← hA0, zero_div, mul_zero] at hh
    nlinarith [sq_nonneg ε]
  have hK0 : 0 < K := by linarith
  have hq0 : 0 ≤ 1 - 1 / K := by rw [sub_nonneg, div_le_one hK0]; exact hK
  have hexp : (1 - 1 / K) ^ (t - 1) ≤ Real.exp (-(((t - 1 : ℕ) : ℝ) / K)) := by
    have h1 : 1 - 1 / K ≤ Real.exp (-(1 / K)) := by
      have := Real.add_one_le_exp (-(1 / K)); linarith
    calc (1 - 1 / K) ^ (t - 1) ≤ Real.exp (-(1 / K)) ^ (t - 1) := pow_le_pow_left₀ hq0 h1 _
      _ = Real.exp (-(((t - 1 : ℕ) : ℝ) / K)) := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hlog : Real.log (A / ε ^ 2) ≤ ((t - 1 : ℕ) : ℝ) / K := by
    rw [Nat.cast_sub ht1, le_div_iff₀ hK0]; push_cast; linarith
  have h2 : Real.exp (-(((t - 1 : ℕ) : ℝ) / K)) ≤ ε ^ 2 / A := by
    have e : ε ^ 2 / A = Real.exp (-Real.log (A / ε ^ 2)) := by
      rw [Real.exp_neg, Real.exp_log (by positivity)]; field_simp
    rw [e]
    exact Real.exp_le_exp.mpr (by linarith)
  have h3 : h ≤ ε ^ 2 / A * (A / 2) :=
    le_trans hh (mul_le_mul_of_nonneg_right (le_trans hexp h2) (by positivity))
  have e : ε ^ 2 / A * (A / 2) = ε ^ 2 / 2 := by field_simp
  linarith

variable {n : ℕ} {p : ENNReal}

theorem lpObjective_self (xStar : PiLp p (fun _ : Fin n => ℝ)) [Fact (1 ≤ p)] :
    lpObjective xStar xStar = 0 := by
  simp [lpObjective]

theorem lpObjective_nonneg [Fact (1 ≤ p)] (xStar z : PiLp p (fun _ : Fin n => ℝ)) :
    0 ≤ lpObjective xStar z := by
  simp only [lpObjective]; positivity

theorem minimizers_lpObjective [Fact (1 ≤ p)] {C : Set (PiLp p (fun _ : Fin n => ℝ))}
    {xStar : PiLp p (fun _ : Fin n => ℝ)} (hxs : xStar ∈ C) :
    xStar ∈ minimizers C (lpObjective xStar) ∧
      ∀ y ∈ minimizers C (lpObjective xStar), y = xStar := by
  refine ⟨⟨hxs, fun z _ => by rw [lpObjective_self]; exact lpObjective_nonneg xStar z⟩, ?_⟩
  intro y hy
  have h1 := hy.2 xStar hxs
  rw [lpObjective_self] at h1
  simp only [lpObjective] at h1
  have : ‖y - xStar‖ ^ 2 = 0 := le_antisymm (by linarith) (sq_nonneg _)
  rw [sq_eq_zero_iff, norm_eq_zero, sub_eq_zero] at this
  exact this

theorem norm_le_of_obj [Fact (1 ≤ p)] {xStar z : PiLp p (fun _ : Fin n => ℝ)} {ε : ℝ}
    (hε : 0 < ε) (h : 2 * lpObjective xStar z ≤ ε ^ 2) : ‖z - xStar‖ ≤ ε := by
  simp only [lpObjective] at h
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hε.le (by norm_num : (2 : ℕ) ≠ 0)).mp (by linarith)

namespace Proof

theorem run_sparsity : RunSparsity.{u} := by
  intro E _ _ C V f' x v γ hrun hx0 hv t
  exact run_sparsity_bound hrun hx0 hv t

theorem short_step_cardinality : ShortStepCardinality := by
  intro n p _ hp2 hpt V xStar x v γ hVfin hxs hx0 hv hrun ε hε t ht1 htε
  have hr2 : 2 ≤ p.toReal := by simpa using ENNReal.toReal_mono hpt hp2
  obtain ⟨hdiff, hconv, -, hlip, -, -⟩ := lpObjective_props hp2 hpt xStar
  set C := convexHull ℝ V with hC
  have hCc : IsCompact C := Set.Finite.isCompact_convexHull (𝕜 := ℝ) hVfin
  have hxsmin := (minimizers_lpObjective (C := C) hxs).1
  have hrate := (vanilla_rate C (lpObjective xStar) (Real.toNNReal (p.toReal - 1)) x v γ hCc
    (convex_convexHull ℝ V) hconv ⟨hdiff, hlip⟩ hrun.1 hrun.2 xStar hxsmin t ht1).1
  rw [hC, convexHull_diam, lpObjective_self, sub_zero,
    Real.coe_toNNReal _ (by linarith : (0 : ℝ) ≤ p.toReal - 1)] at hrate
  refine ⟨norm_le_of_obj hε ?_, run_sparsity_bound (shortStep_isFWRun hrun) hx0 hv t⟩
  have ht3 : (0 : ℝ) < (t : ℝ) + 3 := by positivity
  have h1 : 4 * (p.toReal - 1) * Metric.diam V ^ 2 ≤ ε ^ 2 * ((t : ℝ) + 3) := by
    rw [div_le_iff₀ (by positivity)] at htε; linarith
  have h2 : 2 * (2 * (p.toReal - 1) * Metric.diam V ^ 2 / ((t : ℝ) + 3)) ≤ ε ^ 2 := by
    rw [← mul_div_assoc, div_le_iff₀ ht3]; linarith
  linarith

theorem interior_cardinality : InteriorCardinality := by
  intro n p _ hp2 hpt V xStar r x v γ hVfin hxs hr hball hx0 hv hrun ε hε t ht1 htε
  have hr2 : 2 ≤ p.toReal := by simpa using ENNReal.toReal_mono hpt hp2
  obtain ⟨hdiff, hconv, -, -, -, hsharp⟩ := lpObjective_props hp2 hpt xStar
  set f := lpObjective xStar with hf
  have hfx : f xStar = 0 := lpObjective_self xStar
  set C := convexHull ℝ V with hC
  set L := p.toReal - 1 with hL
  have hL1 : 1 ≤ L := by linarith
  set D := Metric.diam V with hD
  have hCc : IsCompact C := Set.Finite.isCompact_convexHull (𝕜 := ℝ) hVfin
  have hCconv : Convex ℝ C := convex_convexHull ℝ V
  have hconvC : ConvexOn ℝ C f := hconv.subset (Set.subset_univ C) hCconv
  have hmin := minimizers_lpObjective (C := C) hxs
  have hball' : ∀ y ∈ minimizers C f, ∀ z ∈ affineSpan ℝ C, ‖z - y‖ ≤ r → z ∈ C := by
    intro y hy z hz hzy
    rw [hmin.2 y hy] at hzy
    exact hball z hz hzy
  have hmem : ∀ t, x t ∈ C :=
    Lemmata.FrankWolfe.Proof.fw_run_mem C _ x v γ hCconv (shortStep_isFWRun hrun)
  have hbdd : Bornology.IsBounded C := hCc.isBounded
  have hdiam : ∀ y ∈ C, ∀ z ∈ C, ‖y - z‖ ≤ D := by
    intro y hy z hz
    rw [← dist_eq_norm, hD, ← convexHull_diam]; exact Metric.dist_le_diam_of_mem hbdd hy hz
  set K := max 2 (4 * L * D ^ 2 / r ^ 2) with hK
  have hK2 : 2 ≤ K := le_max_left _ _
  have hKr : 4 * L * D ^ 2 / r ^ 2 ≤ K := le_max_right _ _
  have hcoe : ((Real.toNNReal L : NNReal) : ℝ) = L := Real.coe_toNNReal _ (by linarith)
  -- one step
  have hstep : ∀ s, f (x (s + 1)) ≤ (1 - 1 / K) * f (x s) := by
    intro s
    obtain ⟨hvC, hvmin, -, -, hss⟩ := hrun.2 s
    have hgap := interior_gap hCc hconvC (fun y _ => hdiff y) (hsharp C hxs)
      (Real.sqrt_pos.mpr (by norm_num)) (by norm_num) hr hball' hmin.1 (hmem s) hvmin
    rw [hfx, sub_zero, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] at hgap
    set g := fderiv ℝ f (x s) (x s - v s) with hg
    set h := f (x s) with hh
    have hh0 : 0 ≤ h := lpObjective_nonneg xStar _
    have hg0 : 0 ≤ g := by have := hvmin (x s) (hmem s); rw [hg, map_sub]; linarith
    have hhg : h ≤ g := by
      have h1 := convexOn_add_fderiv_le hconvC (hmem s) (hdiff _) hxs
      have h2 := hvmin xStar hxs
      rw [hfx] at h1
      rw [hg, map_sub]; rw [map_sub] at h1; simp only [hh]; linarith
    -- `r²/2 h ≤ g²`
    have hsq : r ^ 2 / 2 * h ≤ g ^ 2 := by
      have hlhs : 0 ≤ r / Real.sqrt 2 * h ^ (1 / 2 : ℝ) := by positivity
      have := pow_le_pow_left₀ hlhs hgap 2
      have key : (h ^ (1 / 2 : ℝ)) ^ 2 = h := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hh0]; norm_num
      rw [mul_pow, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), key] at this
      linarith
    set d := ‖v s - x s‖ with hd
    have hdD : d ≤ D := by rw [hd, norm_sub_rev]; exact hdiam _ (hmem s) _ hvC
    have hK1 : 1 / K ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
    rcases le_or_gt (L * d ^ 2) g with hbig | hsmall
    · have h1 := hss 1 ⟨zero_le_one, le_rfl⟩
      rw [hcoe] at h1
      have : f (x (s + 1)) ≤ h / 2 := by nlinarith
      nlinarith
    · have hd0 : 0 < d := by
        by_contra hd0
        have : d = 0 := le_antisymm (not_lt.mp hd0) (norm_nonneg _)
        rw [this] at hsmall; nlinarith
      have hD0 : 0 < D := lt_of_lt_of_le hd0 hdD
      have hs : g / (L * d ^ 2) ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨by positivity, by rw [div_le_one (by positivity)]; exact hsmall.le⟩
      have h1 := hss _ hs
      rw [hcoe] at h1
      have e : f (x s) - g / (L * d ^ 2) * g + (g / (L * d ^ 2)) ^ 2 * L / 2 * d ^ 2 =
          h - g ^ 2 / (2 * L * d ^ 2) := by field_simp; ring
      rw [e] at h1
      have h2 : g ^ 2 / (2 * L * D ^ 2) ≤ g ^ 2 / (2 * L * d ^ 2) := by
        apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
        have := pow_le_pow_left₀ hd0.le hdD 2
        nlinarith
      have h3 : r ^ 2 / (4 * L * D ^ 2) * h ≤ g ^ 2 / (2 * L * D ^ 2) := by
        calc r ^ 2 / (4 * L * D ^ 2) * h = r ^ 2 / 2 * h / (2 * L * D ^ 2) := by
              field_simp; ring
          _ ≤ g ^ 2 / (2 * L * D ^ 2) := div_le_div_of_nonneg_right hsq (by positivity)
      have h4 : 1 / K ≤ r ^ 2 / (4 * L * D ^ 2) := by
        rw [div_le_div_iff₀ (by linarith) (by positivity)]
        rw [div_le_iff₀ (by positivity)] at hKr
        linarith
      have h5 : 1 / K * h ≤ r ^ 2 / (4 * L * D ^ 2) * h := mul_le_mul_of_nonneg_right h4 hh0
      linarith
  -- the rate
  have hf1 : f (x 1) ≤ L * D ^ 2 / 2 := by
    obtain ⟨hvC, hvmin, -, -, hss⟩ := hrun.2 0
    have h1 := hss 1 ⟨zero_le_one, le_rfl⟩
    rw [hcoe] at h1
    have hhg : f (x 0) ≤ fderiv ℝ f (x 0) (x 0 - v 0) := by
      have h1 := convexOn_add_fderiv_le hconvC (hmem 0) (hdiff _) hxs
      have h2 := hvmin xStar hxs
      rw [hfx] at h1
      rw [map_sub]; rw [map_sub] at h1; linarith
    have hdD : ‖v 0 - x 0‖ ≤ D := by rw [norm_sub_rev]; exact hdiam _ (hmem 0) _ hvC
    have := pow_le_pow_left₀ (norm_nonneg _) hdD 2
    nlinarith
  have hrate : ∀ s, 1 ≤ s → f (x s) ≤ (1 - 1 / K) ^ (s - 1) * (L * D ^ 2 / 2) := by
    intro s hs
    induction s, hs using Nat.le_induction with
    | base => simpa using hf1
    | succ s hs ih =>
      have hq : 0 ≤ 1 - 1 / K := by
        rw [sub_nonneg, div_le_one (by linarith)]; linarith
      calc f (x (s + 1)) ≤ (1 - 1 / K) * f (x s) := hstep s
        _ ≤ (1 - 1 / K) * ((1 - 1 / K) ^ (s - 1) * (L * D ^ 2 / 2)) :=
            mul_le_mul_of_nonneg_left ih hq
        _ = (1 - 1 / K) ^ (s + 1 - 1) * (L * D ^ 2 / 2) := by
            rw [show s + 1 - 1 = s - 1 + 1 by omega, pow_succ]; ring
  have h2 := linear_threshold (by linarith) (by positivity) hε ht1 (hrate t ht1) htε
  exact ⟨norm_le_of_obj hε h2, run_sparsity_bound (shortStep_isFWRun hrun) hx0 hv t⟩

theorem projection_cardinality : ProjectionCardinality := by
  intro n p _ hp2 hpt C V α xStar x v γ hCc hCconv hUC hα hVC hxs hx0 hv hrun ε hε t ht1 htε
  have hr2 : 2 ≤ p.toReal := by simpa using ENNReal.toReal_mono hpt hp2
  obtain ⟨hdiff, hconv, -, hlip, hnorm, -⟩ := lpObjective_props hp2 hpt xStar
  set f := lpObjective xStar with hf
  set L := p.toReal - 1 with hL
  have hL1 : 1 ≤ L := by linarith
  have hCne : C.Nonempty := ⟨x 0, hVC hx0⟩
  set c := Metric.infDist xStar C with hc
  have hc0 : 0 < c := (hCc.isClosed.notMem_iff_infDist_pos hCne).mp hxs
  have hgrad : ∀ y ∈ C, c ≤ ‖fderiv ℝ f y‖ := by
    intro y hy
    rw [hnorm, ← dist_eq_norm, dist_comm]
    exact Metric.infDist_le_dist_of_mem hy
  obtain ⟨y0, hy0, hy0d⟩ := hCc.exists_infDist_eq_dist hCne xStar
  have hfy0 : f y0 = c ^ 2 / 2 := by
    simp only [hf, lpObjective]; rw [hc, hy0d, dist_comm, dist_eq_norm]
  have hy0min : y0 ∈ minimizers C f := by
    refine ⟨hy0, fun z hz => ?_⟩
    rw [hfy0]
    simp only [hf, lpObjective]
    have : c ≤ ‖z - xStar‖ := by
      rw [← dist_eq_norm, dist_comm]; exact Metric.infDist_le_dist_of_mem hz
    have := pow_le_pow_left₀ hc0.le this 2
    linarith
  have hcoe : ((Real.toNNReal L : NNReal) : ℝ) = L := Real.coe_toNNReal _ (by linarith)
  have hrate := uniformly_convex_linear C f (Real.toNNReal L) α c x v γ hCc hCconv hUC hα hc0
    (by rw [hcoe]; linarith) hconv ⟨hdiff, hlip⟩ hgrad hrun y0 hy0min t ht1
  rw [hcoe] at hrate
  set K := max 2 (2 * L / (α * c)) with hK
  have hq : max (1 / 2) (1 - α * c / (2 * L)) = 1 - 1 / K := by
    have hac : 0 < α * c := mul_pos hα hc0
    rcases le_total 2 (2 * L / (α * c)) with h2 | h2
    · rw [hK, max_eq_right h2]
      have : α * c / (2 * L) ≤ 1 / 2 := by
        rw [le_div_iff₀ hac] at h2
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
      rw [max_eq_right (by linarith)]
      field_simp
    · rw [hK, max_eq_left h2]
      have : 1 / 2 ≤ α * c / (2 * L) := by
        rw [div_le_iff₀ hac] at h2
        rw [div_le_div_iff₀ (by norm_num) (by positivity)]; linarith
      rw [max_eq_left (by linarith)]
      norm_num
  rw [hq, hfy0] at hrate
  have h2 := linear_threshold (le_trans (by norm_num) (le_max_left _ _)) (by positivity) hε ht1
    hrate htε
  refine ⟨?_, run_sparsity_bound (shortStep_isFWRun hrun) hx0 hv t⟩
  simp only [hf, lpObjective] at h2
  linarith

end Proof

end Lemmata.FWCaratheodory
