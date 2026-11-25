module

public import Lemmata.FrankWolfeLDS.Statement
public import Lemmata.FrankWolfeLDS.Proof.LocalGapGeometry
public import Lemmata.FrankWolfeLDS.Proof.Smoothness

@[expose] public section

/-!
# From the development to the statements

The development (`Proof/*`) works with an oracle structure `Oracle C`, an abstract gradient map
`f'`, a line-search structure `LineSearch`, and one theorem per step-size rule. This file
connects it to the statements of `Statement.lean`:

* the standing assumptions give the oracle, the line-search rule and the two inequalities the
  development uses (`StandingAssumptions.oracle`, `.lineSearch`, `.smooth`, `.firstOrder`), and
  the development's iterates are the iterates of `fwIterates` (`openLoop_eq`, `shortStep_eq`,
  `lineSearch_eq`);
* three hypotheses of the development that the paper does not make are removed: positivity of
  the gap in Theorem 3.5 (once the gap vanishes, it stays zero), the bound on the initial gap in
  Theorem 3.6 (it holds after the first step), and the split of Theorem 4.2 for the open loop
  into `q = 2` and `q > 2`;
* Corollary 3.8 is proved here: either some point of `C` has zero gradient, and Theorem 3.6
  applies, or the gradient is bounded away from zero on the compact set `C`, and the
  `o(1/t)` case of Proposition 3.7 applies.
-/

namespace Lemmata.FrankWolfeLDS

open Filter Topology
open scoped Gradient InnerProductSpace NNReal

universe u

/-- The minimizer set is the level set of the optimal value. -/
theorem minimizers_eq {E : Type*} {C : Set E} {f : E → ℝ} {xStar : E} (hx : xStar ∈ minimizers C f) :
    minimizers C f = C ∩ {y | f y = f xStar} := by
  ext y
  constructor
  · rintro ⟨hyC, hymin⟩
    exact ⟨hyC, le_antisymm (hymin _ hx.1) (hx.2 _ hyC)⟩
  · rintro ⟨hyC, hyv⟩
    refine ⟨hyC, fun z hz => ?_⟩
    rw [show f y = f xStar from hyv]
    exact hx.2 z hz

section Bridge

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {C : Set E} {lmo : E → E} {f : E → ℝ} {L : ℝ≥0}

namespace StandingAssumptions

variable (h : StandingAssumptions C lmo f L)

theorem isCompact (h : StandingAssumptions C lmo f L) : IsCompact C := h.1
theorem convex (h : StandingAssumptions C lmo f L) : Convex ℝ C := h.2.1
theorem isLMO (h : StandingAssumptions C lmo f L) : IsLinearMinimizationOracle C lmo := h.2.2.1
theorem differentiable (h : StandingAssumptions C lmo f L) : Differentiable ℝ f := h.2.2.2.1
theorem convexOn (h : StandingAssumptions C lmo f L) : ConvexOn ℝ Set.univ f := h.2.2.2.2.1
theorem lipschitz_gradient (h : StandingAssumptions C lmo f L) : LipschitzWith L (∇ f) := h.2.2.2.2.2.1
theorem L_pos (h : StandingAssumptions C lmo f L) : 0 < L := h.2.2.2.2.2.2

/-- The oracle of the development. -/
def oracle : Oracle C := ⟨lmo, h.isLMO, h.isCompact⟩

theorem nonempty (h : StandingAssumptions C lmo f L) : C.Nonempty := h.oracle.nonempty

theorem smooth (h : StandingAssumptions C lmo f L) : IsLipschitzSmoothUpperBound f L (∇ f) :=
  isLipschitzSmoothUpperBound_of_lipschitzWith h.differentiable h.lipschitz_gradient

theorem firstOrder (h : StandingAssumptions C lmo f L) : IsFirstOrderConvex f (∇ f) :=
  isFirstOrderConvex_of_convexOn h.differentiable h.convexOn

/-- The line-search rule of the development. -/
def lineSearch {σ : E → ℝ} (hσ : IsExactLineSearch lmo f σ) : LineSearch h.oracle f (∇ f) where
  step := σ
  step_mem x := (hσ x).1
  step_opt x η hη := (hσ x).2 η hη

theorem openLoop_eq (x₀ : E) :
    frankWolfeSequence h.oracle (∇ f) x₀ = fwIterates lmo f openLoopStep x₀ := by
  funext t
  induction t with
  | zero => rfl
  | succ t ih =>
    change frankWolfeStep h.oracle (∇ f) (frankWolfeSequence h.oracle (∇ f) x₀ t)
        (openLoopStepSize 2 t) = fwStep lmo f (fwIterates lmo f openLoopStep x₀ t)
        (openLoopStep t (fwIterates lmo f openLoopStep x₀ t))
    rw [ih]
    simp [frankWolfeStep, fwStep, LMO, oracle, openLoopStepSize, openLoopStep]

theorem shortStep_eq (x₀ : E) :
    globalShortStepSequence h.oracle (∇ f) L x₀ = fwIterates lmo f (shortStep lmo f L) x₀ := by
  funext t
  induction t with
  | zero => rfl
  | succ t ih =>
    change globalShortStep h.oracle (∇ f) L (globalShortStepSequence h.oracle (∇ f) L x₀ t) =
      fwStep lmo f (fwIterates lmo f (shortStep lmo f L) x₀ t)
        (shortStep lmo f L t (fwIterates lmo f (shortStep lmo f L) x₀ t))
    rw [ih]
    rfl

theorem lineSearch_eq {σ : E → ℝ} (hσ : IsExactLineSearch lmo f σ) (x₀ : E) :
    exactLineSearchSequence h.oracle f (∇ f) (h.lineSearch hσ) x₀ =
      fwIterates lmo f (fun _ => σ) x₀ := by
  funext t
  induction t with
  | zero => rfl
  | succ t ih =>
    change exactLineSearch h.oracle f (∇ f) (h.lineSearch hσ)
        (exactLineSearchSequence h.oracle f (∇ f) (h.lineSearch hσ) x₀ t) =
      fwStep lmo f (fwIterates lmo f (fun _ => σ) x₀ t) (σ (fwIterates lmo f (fun _ => σ) x₀ t))
    rw [ih]
    rfl

end StandingAssumptions

/-- A point with zero gradient minimizes a differentiable convex function. -/
theorem le_of_gradient_eq_zero (h : StandingAssumptions C lmo f L) {y : E} (hy : ∇ f y = 0)
    (z : E) : f y ≤ f z := by
  have := h.firstOrder y z
  simp only [hy, inner_zero_left, add_zero] at this
  exact this

end Bridge

section Helpers

/-- A rate from some index `T` on, in the development's form, in the form of the statements. -/
theorem reindex_rate {F : ℕ → ℝ} {e : ℝ}
    (h : ∃ T : ℕ, ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, F (T + n) ≤ K / ((n : ℝ) + 1) ^ e) :
    ∃ t₀ : ℕ, ∃ K > 0, ∀ t ≥ t₀, F t ≤ K / ((t - t₀ + 1 : ℕ) : ℝ) ^ e := by
  obtain ⟨T, K, hK, hb⟩ := h
  refine ⟨T, K, hK, fun t ht => ?_⟩
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le ht
  have : ((T + n - T + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast [Nat.add_sub_cancel_left]; ring
  rw [this]
  exact hb n

/-- If `(t + 2) a (t + 1) → 0` along the shifted sequence, then `(t + 2) a t → 0`. -/
theorem tendsto_of_tendsto_shift {a : ℕ → ℝ}
    (h : Tendsto (fun t : ℕ => ((t : ℝ) + 2) * a (t + 1)) atTop (𝓝 0)) :
    Tendsto (fun t : ℕ => ((t : ℝ) + 2) * a t) atTop (𝓝 0) := by
  rw [← tendsto_add_atTop_iff_nat 1]
  have hfrac : Tendsto (fun t : ℕ => ((t : ℝ) + 3) / ((t : ℝ) + 2)) atTop (𝓝 1) := by
    have h1 : Tendsto (fun t : ℕ => 1 / ((t : ℝ) + 2)) atTop (𝓝 0) :=
      tendsto_const_div_add_atTop_nhds_zero_nat 1 2 |>.congr fun t => by push_cast; ring
    have := h1.const_add 1
    simp only [add_zero] at this
    refine this.congr fun t => ?_
    field_simp
    ring
  have := h.mul hfrac
  simp only [zero_mul] at this
  refine this.congr fun t => ?_
  push_cast
  field_simp
  ring

/-- Running a rule that does not depend on the time for `t + 1` steps from `x₀` is running it
for `t` steps from `x₁`. -/
theorem fwIterates_succ_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (lmo : E → E) (f : E → ℝ) (step : ℕ → E → ℝ)
    (hstep : ∀ t, step t = step 0) (x₀ : E) (t : ℕ) :
    fwIterates lmo f step x₀ (t + 1) = fwIterates lmo f step (fwIterates lmo f step x₀ 1) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change fwStep lmo f (fwIterates lmo f step x₀ (t + 1))
        (step (t + 1) (fwIterates lmo f step x₀ (t + 1))) =
      fwStep lmo f (fwIterates lmo f step (fwIterates lmo f step x₀ 1) t)
        (step t (fwIterates lmo f step (fwIterates lmo f step x₀ 1) t))
    rw [ih, hstep (t + 1), hstep t]

end Helpers

section Monotone

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {C : Set E} (O : Oracle C)

/-- The quantity `½ min (g, g² / (L D²))` of the descent lemmas is nonnegative at points of
`C`, because the Frank-Wolfe gap `g` is. -/
theorem descent_nonneg (f' : E → E) (L : NNReal) {x : E} (hx : x ∈ C) :
    0 ≤ (1 / 2 : ℝ) * min (inner ℝ (f' x) (x - LMO O (f' x)))
      ((inner ℝ (f' x) (x - LMO O (f' x))) ^ 2 / ((L : ℝ) * ‖LMO O (f' x) - x‖ ^ 2)) := by
  have hg : 0 ≤ inner ℝ (f' x) (x - LMO O (f' x)) := by
    rw [inner_sub_right]
    linarith [LMO_le O (f' x) hx]
  have : 0 ≤ (inner ℝ (f' x) (x - LMO O (f' x))) ^ 2 / ((L : ℝ) * ‖LMO O (f' x) - x‖ ^ 2) := by
    positivity
  positivity

theorem globalShortStepSequence_antitone (hC_convex : Convex ℝ C) (f : E → ℝ) (f' : E → E)
    (L : NNReal) (hSmooth : IsLipschitzSmoothUpperBound f L f') {x0 : E} (hx0 : x0 ∈ C)
    (t : ℕ) :
    f (globalShortStepSequence O f' L x0 (t + 1)) ≤ f (globalShortStepSequence O f' L x0 t) := by
  have hx := globalShortStepSequence_mem O hC_convex f' L hx0 t
  have h1 := globalShortStep_decrease O f f' L hSmooth hx
  have h2 := descent_nonneg O f' L hx
  change f (globalShortStep O f' L (globalShortStepSequence O f' L x0 t)) ≤ _
  linarith

theorem exactLineSearchSequence_antitone (hC_convex : Convex ℝ C) (f : E → ℝ) (f' : E → E)
    (hLS : LineSearch O f f') (L : NNReal) (hSmooth : IsLipschitzSmoothUpperBound f L f')
    {x0 : E} (hx0 : x0 ∈ C) (t : ℕ) :
    f (exactLineSearchSequence O f f' hLS x0 (t + 1)) ≤
      f (exactLineSearchSequence O f f' hLS x0 t) := by
  have hx := exactLineSearchSequence_mem O hC_convex f f' hLS hx0 t
  have h1 := exactLineSearch_decrease O f f' L hLS hSmooth hx
  have h2 := descent_nonneg O f' L hx
  change f (exactLineSearch O f f' hLS (exactLineSearchSequence O f f' hLS x0 t)) ≤ _
  linarith

end Monotone

/-- Once a nonnegative, nonincreasing gap vanishes, `(t + 2) F_t → 0`; otherwise the gap is
positive. -/
theorem tendsto_or_gap_pos {F : ℕ → ℝ} (hnonneg : ∀ t, 0 ≤ F t) (hmono : ∀ t, F (t + 1) ≤ F t)
    (h : (∀ t, 0 < F t) → Tendsto (fun t : ℕ => ((t : ℝ) + 2) * F t) atTop (𝓝 0)) :
    Tendsto (fun t : ℕ => ((t : ℝ) + 2) * F t) atTop (𝓝 0) := by
  by_cases hpos : ∀ t, 0 < F t
  · exact h hpos
  push Not at hpos
  obtain ⟨t₀, ht₀⟩ := hpos
  have hzero : ∀ t ≥ t₀, F t = 0 := by
    intro t ht
    have : F t ≤ F t₀ := by
      induction t, ht using Nat.le_induction with
      | base => exact le_rfl
      | succ n _ ih => exact (hmono n).trans ih
    linarith [hnonneg t]
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop t₀] with t ht
  rw [hzero t ht, mul_zero]

section Results

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem standardRate_of {C : Set E} {lmo : E → E} {f : E → ℝ} {L : ℝ≥0}
    (h : StandingAssumptions C lmo f L) {σ : E → ℝ} (hσ : IsExactLineSearch lmo f σ)
    {xStar : E} (hxStar : xStar ∈ minimizers C f) {x₀ : E} (hx₀ : x₀ ∈ C) {t : ℕ} (ht : 1 ≤ t) :
    f (fwIterates lmo f openLoopStep x₀ t) - f xStar ≤ 2 * L * Metric.diam C ^ 2 / (t + 2) ∧
    f (fwIterates lmo f (shortStep lmo f L) x₀ t) - f xStar ≤
      2 * L * Metric.diam C ^ 2 / (t + 2) ∧
    f (fwIterates lmo f (fun _ => σ) x₀ t) - f xStar ≤ 2 * L * Metric.diam C ^ 2 / (t + 2) := by
  refine ⟨?_, ?_, ?_⟩
  · have := frank_wolfe_convergence_after_first_step h.oracle h.convex f (∇ f) L h.smooth
      h.firstOrder hxStar.1 hx₀ t ht
    rwa [h.openLoop_eq] at this
  · have := global_short_step_convergence_after_first_step h.oracle h.convex f (∇ f) L h.L_pos
      h.smooth h.firstOrder hxStar.1 hx₀ t ht
    rwa [h.shortStep_eq] at this
  · have := exact_line_search_convergence_after_first_step h.oracle h.convex f (∇ f)
      (h.lineSearch hσ) L h.smooth h.firstOrder hxStar.1 hx₀ t ht
    rwa [h.lineSearch_eq hσ] at this

namespace Proof

theorem standard_rate : StandardRate.{u} := by
  intro E _ _ _ C lmo f L h σ hσ xStar hxStar x₀ hx₀ t ht
  exact standardRate_of h hσ hxStar hx₀ ht

theorem uniformly_convex_lds : UniformlyConvexImpliesLDS.{u} := by
  intro E _ _ C lmo α q hC hlmo _ _ hUC M _ _
  exact hasLocalLMOGapPowerOn_of_uniformlyConvex (⟨lmo, hlmo, hC⟩ : Oracle C) hUC

theorem conditional_short_step_line_search : ConditionalShortStepLineSearch.{u} := by
  intro E _ _ _ C lmo f L h σ hσ M A q hMC _ hA hq hLDS xStar p hxStar hpM hpval hpgrad x₀ hx₀
    x hx hδ
  have hnonneg : ∀ t, 0 ≤ f (x t) - f xStar := by
    intro t
    have := le_of_gradient_eq_zero h (hpgrad 0) (x t)
    rw [hpval 0] at this
    linarith
  have hLocal : HasLocalLMOGapPowerOn h.oracle M A q := hLDS
  rcases hx with rfl | rfl
  · refine tendsto_or_gap_pos hnonneg (fun t => ?_) (fun hpos => ?_)
    · have := globalShortStepSequence_antitone h.oracle h.convex f (∇ f) L h.smooth hx₀ t
      rw [h.shortStep_eq] at this
      linarith
    · have := globalShortStep_localGap_boosted_convergence_of_minimizerSequence_tendsto_zero
        h.oracle h.convex hq hA f (∇ f) L h.L_pos h.firstOrder h.smooth xStar hLocal p
        (fun t => hMC (hpM t)) hpM hpval hpgrad hx₀ (by rw [h.shortStep_eq]; exact hpos)
        (by rw [h.shortStep_eq]; exact hδ)
      rwa [h.shortStep_eq] at this
  · refine tendsto_or_gap_pos hnonneg (fun t => ?_) (fun hpos => ?_)
    · have := exactLineSearchSequence_antitone h.oracle h.convex f (∇ f) (h.lineSearch hσ) L
        h.smooth hx₀ t
      rw [h.lineSearch_eq hσ] at this
      linarith
    · have := exactLineSearch_localGap_boosted_convergence_of_minimizerSequence_tendsto_zero
        h.oracle h.convex hq hA f (∇ f) L h.L_pos h.firstOrder h.smooth xStar hLocal p
        (fun t => hMC (hpM t)) hpM hpval hpgrad (h.lineSearch hσ) hx₀
        (by rw [h.lineSearch_eq hσ]; exact hpos) (by rw [h.lineSearch_eq hσ]; exact hδ)
      rwa [h.lineSearch_eq hσ] at this

theorem zero_gradient_minimizer : ZeroGradientMinimizer.{u} := by
  intro E _ _ _ C lmo f L h σ hσ A q hA hq hLDS xStar hxStar hgrad x₀ hx₀ x hx
  have hLocal : HasLocalLMOGapPowerOn h.oracle (C ∩ {y | f y = f xStar}) A q := by
    rw [← minimizers_eq hxStar]; exact hLDS
  -- after one step, the gap is at most `2 L D² / 3 ≤ L D²`
  have hthird : ∀ y : E, f y - f xStar ≤ 2 * L * Metric.diam C ^ 2 / ((1 : ℕ) + 2) →
      f y - f xStar ≤ L * Metric.diam C ^ 2 := by
    intro y hy
    have : 0 ≤ (L : ℝ) * Metric.diam C ^ 2 := by positivity
    push_cast at hy
    linarith
  have hrate := fun t (ht : 1 ≤ t) => standardRate_of h hσ hxStar hx₀ ht
  rcases hx with rfl | rfl
  · have hx₁ : fwIterates lmo f (shortStep lmo f L) x₀ 1 ∈ C := by
      rw [← h.shortStep_eq]; exact globalShortStepSequence_mem h.oracle h.convex _ L hx₀ 1
    have := globalShortStep_localGap_boosted_convergence_of_zeroGradient_minimizer h.oracle
      h.convex hq hA f (∇ f) L h.L_pos h.firstOrder h.smooth hxStar.1 hgrad hLocal hx₁
      (hthird _ (hrate 1 le_rfl).2.1)
    rw [h.shortStep_eq] at this
    refine tendsto_of_tendsto_shift (this.congr fun t => ?_)
    rw [fwIterates_succ_eq lmo f _ (fun _ => rfl) x₀ t]
  · have hx₁ : fwIterates lmo f (fun _ => σ) x₀ 1 ∈ C := by
      rw [← h.lineSearch_eq hσ]
      exact exactLineSearchSequence_mem h.oracle h.convex f _ (h.lineSearch hσ) hx₀ 1
    have := exactLineSearch_localGap_boosted_convergence_of_zeroGradient_minimizer h.oracle
      h.convex hq hA f (∇ f) L h.L_pos h.firstOrder h.smooth hxStar.1 hgrad hLocal
      (h.lineSearch hσ) hx₁ (hthird _ (hrate 1 le_rfl).2.2)
    rw [h.lineSearch_eq hσ] at this
    refine tendsto_of_tendsto_shift (this.congr fun t => ?_)
    rw [fwIterates_succ_eq lmo f _ (fun _ => rfl) x₀ t]

theorem gradient_bounded_below : GradientBoundedBelow.{u} := by
  intro E _ _ _ C lmo f L h σ hσ A q G hA hq hLDS hG hlb xStar hxStar x₀ hx₀ x hx
  have hLocal : HasLocalLMOGapPowerOn h.oracle (C ∩ {y | f y = f xStar}) A q := by
    rw [← minimizers_eq hxStar]; exact hLDS
  have hκ : (1 - min 1 (A * G / L) / 2 : ℝ) = 1 - 1 / 2 * min 1 (A * G / L) := by ring
  refine ⟨fun hq2 => ?_, fun hq2 => ?_⟩
  · subst hq2
    rcases hx with rfl | rfl
    · obtain ⟨T, hT⟩ := globalShortStep_localGap_polyak_linear_rate h.oracle h.convex hA f (∇ f)
        L h.L_pos h.firstOrder h.smooth xStar hxStar.1 hLocal G hG hlb hxStar.2 x₀ hx₀
      refine ⟨T, fun t ht => ?_⟩
      obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le ht
      have := hT n
      rw [h.shortStep_eq] at this
      rwa [hκ, Nat.add_sub_cancel_left]
    · obtain ⟨T, hT⟩ := exactLineSearch_localGap_polyak_linear_rate h.oracle h.convex hA f (∇ f)
        L h.L_pos h.firstOrder h.smooth xStar hxStar.1 hLocal G hG hlb hxStar.2
        (h.lineSearch hσ) x₀ hx₀
      refine ⟨T, fun t ht => ?_⟩
      obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le ht
      have := hT n
      rw [h.lineSearch_eq hσ] at this
      rwa [hκ, Nat.add_sub_cancel_left]
  · refine reindex_rate (F := fun t => f (x t) - f xStar) ?_
    rcases hx with rfl | rfl
    · obtain ⟨T, K, hK, hb⟩ := globalShortStep_localGap_polyak_power_rate h.oracle h.convex hq2 hA
        f (∇ f) L h.L_pos h.firstOrder h.smooth xStar hxStar.1 hLocal G hG hlb hxStar.2 x₀ hx₀
      refine ⟨T, K, hK, fun n => ?_⟩
      have := hb n
      rwa [h.shortStep_eq] at this
    · obtain ⟨T, K, hK, hb⟩ := exactLineSearch_localGap_polyak_power_rate h.oracle h.convex hq2 hA
        f (∇ f) L h.L_pos h.firstOrder h.smooth xStar hxStar.1 hLocal G hG hlb hxStar.2
        (h.lineSearch hσ) x₀ hx₀
      refine ⟨T, K, hK, fun n => ?_⟩
      have := hb n
      rwa [h.lineSearch_eq hσ] at this

theorem beyond_one_over_t : BeyondOneOverT.{u} := by
  intro E _ _ _ C lmo f L h σ hσ A q hA hq hLDS xStar hxStar x₀ hx₀ x hx
  by_cases hz : ∃ y ∈ C, ∇ f y = 0
  · -- a point of `C` with zero gradient is a minimizer: Theorem 3.6
    obtain ⟨y, hyC, hy0⟩ := hz
    have hymin : y ∈ minimizers C f := ⟨hyC, fun z _ => le_of_gradient_eq_zero h hy0 z⟩
    have hval : f y = f xStar := le_antisymm (hymin.2 _ hxStar.1) (hxStar.2 _ hyC)
    have := zero_gradient_minimizer C lmo f L h σ hσ A q hA hq hLDS y hymin hy0 x₀ hx₀ x hx
    simpa only [hval] using this
  · -- otherwise `‖∇ f‖` has a positive minimum on the compact set `C`: Proposition 3.7
    push Not at hz
    obtain ⟨y₀, hy₀C, hy₀⟩ := h.isCompact.exists_isMinOn h.nonempty
      h.lipschitz_gradient.continuous.norm.continuousOn
    have hG : 0 < ‖∇ f y₀‖ := norm_pos_iff.mpr (hz y₀ hy₀C)
    have hlb : ∀ y ∈ C, ‖∇ f y₀‖ ≤ ‖∇ f y‖ := fun y hy => isMinOn_iff.mp hy₀ y hy
    have hLocal : HasLocalLMOGapPowerOn h.oracle (C ∩ {y | f y = f xStar}) A q := by
      rw [← minimizers_eq hxStar]; exact hLDS
    rcases hx with rfl | rfl
    · have := globalShortStep_localGap_polyak_convergence h.oracle h.convex hq hA f (∇ f) L
        h.L_pos h.firstOrder h.smooth hxStar.1 hLocal _ hG hlb hxStar.2 hx₀
      rwa [h.shortStep_eq] at this
    · have := exactLineSearch_localGap_polyak_convergence h.oracle h.convex hq hA f (∇ f) L
        h.L_pos h.firstOrder h.smooth hxStar.1 hLocal _ hG hlb hxStar.2 (h.lineSearch hσ) hx₀
      rwa [h.lineSearch_eq hσ] at this

theorem conditional_open_loop : ConditionalOpenLoop.{u} := by
  intro E _ _ _ C lmo f L h M A q hMC _ hA hq hLDS xStar hxStar p hpM hpval x₀ hx₀ hδ
  have hq' : q = 2 ∨ 2 < q := (eq_or_lt_of_le hq).imp Eq.symm id
  have := frankWolfe_localGap_boosted_convergence_of_minimizerSequence_tendsto_zero h.oracle
    h.convex hq' hA f (∇ f) L h.L_pos h.firstOrder h.smooth xStar (Mset := M) hLDS p
    (fun t => hMC (hpM t)) hpM hpval (fun t y hy => by rw [hpval t]; exact hxStar.2 y hy) hx₀
    (by rw [h.openLoop_eq]; exact hδ)
  rwa [h.openLoop_eq] at this

theorem open_loop_rate : OpenLoopRate.{u} := by
  intro E _ _ _ C lmo f L h A q hA hq hLDS xStar hxStar x₀ hx₀
  have hq' : q = 2 ∨ 2 < q := (eq_or_lt_of_le hq).imp Eq.symm id
  have hLocal : HasLocalLMOGapPowerOn h.oracle (C ∩ {y | f y = f xStar}) A q := by
    rw [← minimizers_eq hxStar]; exact hLDS
  have := frankWolfe_localGap_boosted_convergence_of_minimizer h.oracle h.convex hq' hA f (∇ f)
    L h.L_pos h.firstOrder h.smooth hxStar.1 hLocal hxStar.2 hx₀
  rwa [h.openLoop_eq] at this

theorem holder_error_bound_rate : HolderErrorBoundRate.{u} := by
  intro E _ _ _ C lmo f L h σ hσ A q B r hA hq hB hr hLDS xStar hxStar hHEB x₀ hx₀ x hx
  have hLocal : HasLocalLMOGapPowerOn h.oracle (C ∩ {y | f y = f xStar}) A q := by
    rw [← minimizers_eq hxStar]; exact hLDS
  have hHEB' : HasLocalHolderErrorBoundOn (C := C) (C ∩ {y | f y = f xStar}) f (f xStar) B r := by
    rw [← minimizers_eq hxStar]; exact hHEB
  refine reindex_rate (F := fun t => f (x t) - f xStar) ?_
  rcases hx with rfl | rfl | rfl
  · rcases eq_or_lt_of_le hq with hq2 | hq2
    · subst hq2
      obtain ⟨T, K, hK, hb⟩ := frankWolfe_localGap_two_heb_power_rate h.oracle h.convex hr hA hB
        f (∇ f) L h.L_pos h.firstOrder h.smooth xStar hxStar.1 hLocal hHEB' hxStar.2 x₀ hx₀
      refine ⟨T, K, hK, fun n => ?_⟩
      have e : r * 2 / (r * 2 - 2) = r / (r - 1) := by
        have : r - 1 ≠ 0 := by linarith
        have : r * 2 - 2 ≠ 0 := by linarith
        field_simp
      have := hb n
      rw [h.openLoop_eq] at this
      simpa only [e] using this
    · obtain ⟨T, K, hK, hb⟩ := frankWolfe_localGap_heb_power_rate h.oracle h.convex hq2 hr hA hB
        f (∇ f) L h.L_pos h.firstOrder h.smooth xStar hxStar.1 hLocal hHEB' hxStar.2 x₀ hx₀
      refine ⟨T, K, hK, fun n => ?_⟩
      have := hb n
      rwa [h.openLoop_eq] at this
  · obtain ⟨T, K, hK, hb⟩ := globalShortStep_localGap_heb_power_rate h.oracle h.convex hq hr hA hB
      f (∇ f) L h.L_pos h.firstOrder h.smooth xStar hxStar.1 hLocal hHEB' hxStar.2 x₀ hx₀
    refine ⟨T, K, hK, fun n => ?_⟩
    have := hb n
    rwa [h.shortStep_eq] at this
  · obtain ⟨T, K, hK, hb⟩ := exactLineSearch_localGap_heb_power_rate h.oracle h.convex hq hr hA hB
      f (∇ f) L h.L_pos h.firstOrder h.smooth xStar hxStar.1 hLocal hHEB' hxStar.2
      (h.lineSearch hσ) x₀ hx₀
    refine ⟨T, K, hK, fun n => ?_⟩
    have := hb n
    rwa [h.lineSearch_eq hσ] at this

theorem uniformly_convex_gap : UniformlyConvexGap.{u} := by
  intro E _ _ C α q _ _ hUC g x s hx hs hmin
  exact uniformlyConvex_support_lower_bound hUC hs hx fun y hy => by
    rw [inner_sub_right]
    linarith [hmin y hy]

theorem patch_criterion : PatchCriterion.{u} := by
  intro E _ _ C lmo hC hlmo M K α q ρ β _ _ hq hUC hρ hβ hcond
  exact hasLocalLMOGapPowerOn_of_uniformlyConvexPatchOrResidual (⟨lmo, hlmo, hC⟩ : Oracle C)
    (by linarith) hUC hρ (fun x hx hd => (hcond x hx hd).1) (fun x hx hd g => (hcond x hx hd).2 g)
    hβ.le

end Proof

end Results

end Lemmata.FrankWolfeLDS
