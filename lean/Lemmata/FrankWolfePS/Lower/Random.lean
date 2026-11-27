module

public import Lemmata.FrankWolfePS.Lower.LowerBound
public import Mathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public section

namespace Lemmata.FrankWolfePS
open Finset MeasureTheory
open scoped BigOperators ENNReal
variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]

/-- Finite averaging against an arbitrary independent tape law. Only measurability
of the finitely many failure events is needed. -/
theorem seed_average {A : Type*} (H : Finset A) (hne : H.Nonempty)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (e : A → Set Ω)
    (meas : ∀ i ∈ H, MeasurableSet (e i))
    (bound : ∀ ω, (H.card : ℝ) / 4 ≤ ∑ i ∈ H, flag (ω ∈ e i)) :
    (H.card : ℝ) / 4 ≤ ∑ i ∈ H, μ.real (e i) ∧ ∃ i ∈ H, 1 / 4 ≤ μ.real (e i) := by
  classical
  let b (i : A) : Ω → ℝ := (e i).indicator (fun _ => 1)
  have hb (i) (hi : i ∈ H) : Integrable (b i) μ :=
    (integrable_const _).indicator (meas i hi)
  have hbi (i) (hi : i ∈ H) : (∫ ω, b i ω ∂μ) = μ.real (e i) :=
    integral_indicator_one (meas i hi)
  have hu (ω : Ω) : (H.card : ℝ) / 4 ≤ ∑ i ∈ H, b i ω := by
    simpa [b, Set.indicator, flag] using bound ω
  have hi := integral_mono (μ := μ) (integrable_const ((H.card : ℝ) / 4))
    (integrable_finsetSum _ hb) hu
  rw [integral_const, smul_eq_mul, probReal_univ, one_mul,
      integral_finsetSum _ hb, sum_congr rfl hbi] at hi
  refine ⟨hi, ?_⟩
  by_contra! no
  have lt := sum_lt_sum_of_nonempty hne no
  simp only [sum_const, nsmul_eq_mul] at lt
  linarith

/-- Averaging over an independent tape selects a fixed instance. -/
theorem select_tape {A : Type*} (H : Finset A) (nonempty : H.Nonempty) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (p : ℝ) (e : A → Set Ω) (meas : ∀ i ∈ H, MeasurableSet (e i))
    (fixed : ∀ ω, (H.card : ℝ) * p ≤ ∑ i ∈ H, flag (ω ∈ e i)) : ∃ i ∈ H, p ≤ μ.real (e i) := by
  classical
  let ind := fun i => (e i).indicator (fun _ => (1 : ℝ))
  have mg (i) (hi : i ∈ H) : Integrable (ind i) μ := (integrable_const 1).indicator (meas i hi)
  have pt (ω : Ω) : (H.card : ℝ) * p ≤ ∑ i ∈ H, ind i ω := by
    simpa [ind, flag, Set.indicator] using fixed ω
  have val (i) (hi : i ∈ H) : (∫ ω, ind i ω ∂μ) = μ.real (e i) := integral_indicator_one (meas i hi)
  have h := integral_mono (μ := μ) (integrable_const ((H.card : ℝ) * p))
    (integrable_finsetSum H mg) pt
  rw [integral_const, smul_eq_mul, probReal_univ, one_mul, integral_finsetSum H mg,
    sum_congr rfl val] at h
  by_contra! no
  have bad := sum_lt_sum_of_nonempty nonempty no
  simp only [sum_const, nsmul_eq_mul] at bad; linarith

/-- Markov's inequality for a nonnegative integrable gap: if `b ≤ g` with probability at least
`p`, the mean of `g` is at least `p b`. -/
theorem fraction_mul_le_integral (μ : Measure Ω) [IsProbabilityMeasure μ] {g : Ω → ℝ}
    (hg : Integrable g μ) (h0 : ∀ ω, 0 ≤ g ω) {p b : ℝ} (hb : 0 ≤ b)
    (hm : MeasurableSet {ω | b ≤ g ω}) (hp : p ≤ μ.real {ω | b ≤ g ω}) :
    p * b ≤ ∫ ω, g ω ∂μ := by
  have major (ω : Ω) : {ω | b ≤ g ω}.indicator (fun _ => b) ω ≤ g ω := by
    by_cases h : ω ∈ {ω | b ≤ g ω}
    · rw [Set.indicator_of_mem h]; exact h
    · rw [Set.indicator_of_notMem h]; exact h0 ω
  have H := integral_mono ((integrable_const b).indicator hm) hg major
  rw [integral_indicator_const b hm, smul_eq_mul] at H
  exact (mul_le_mul_of_nonneg_right hp hb).trans H

/-- A continuous function of a measurable point that stays in a compact set is integrable. -/
theorem integrable_comp_of_mem_compact {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    [OpensMeasurableSpace E] (μ : Measure Ω) [IsFiniteMeasure μ] {K : Set E} (hK : IsCompact K)
    {F : E → ℝ} (hF : Continuous F) {z : Ω → E} (hz : Measurable z) (mem : ∀ ω, z ω ∈ K) :
    Integrable (fun ω => F (z ω)) μ := by
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hF.continuousOn
  exact (integrable_const M).mono' (hF.measurable.comp hz).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => hM _ (mem ω))

def badSeeds (R : ℝ) (T : ℕ) (strat : Ω → Orders ι (Pt ι) T)
    (I : Finset ι) : Set Ω :=
  {ω | failure R (T + 1) I ((strat ω).run I)}

theorem randomized_lower_bound (T : ℕ) (anchor : ι) (hN : Fintype.card ι = 256 * (T + 1))
    (R : ℝ) (hR : 0 < R) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (strat : Ω → Orders ι (Pt ι) T)
    (meas : ∀ S ∈ shells T anchor, MeasurableSet (badSeeds R T strat (insert anchor S))) :
    (↑(shells T anchor).card : ℝ) / 4 ≤
        ∑ S ∈ shells T anchor, μ.real (badSeeds R T strat (insert anchor S)) ∧
      ∃ S ∈ shells T anchor, 1 / 4 ≤ μ.real (badSeeds R T strat (insert anchor S)) := by
  have ne : (shells T anchor).Nonempty := by
    apply powersetCard_nonempty.mpr
    simp [hN]
    omega
  exact seed_average _ ne μ _ meas (fun ω => fixed_tape_lower_bound T anchor hN R hR (strat ω))

end Lemmata.FrankWolfePS
