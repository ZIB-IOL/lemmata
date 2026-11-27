module

public import Lemmata.FanoDiffusion.Statement
public import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
public import Mathlib.Probability.Kernel.Composition.Lemmas

@[expose] public section

/-!
# The information diffusion Fano inequality for the relative entropy (Proposition 2.1, `α = 1`)

The relative entropy splits over an event `R` and its complement, and on each part it is at least
`p log (p/q) + q - p`, with `p` and `q` the masses of the part. Summing gives the data processing
bound `d(P(R) ‖ Q(R)) ≤ D(P ‖ Q)`, and `d(p ‖ q) + H(p) = p log (1/q) + (1 - p) log (1/(1 - q))`.
-/

namespace Lemmata.FanoDiffusion

open MeasureTheory ProbabilityTheory InformationTheory Real
open scoped ENNReal

universe u

namespace Proof

section KL

variable {Ω : Type*} [MeasurableSpace Ω]

theorem rnDeriv_restrict_restrict (μ ν : Measure Ω) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hac : μ ≪ ν) {R : Set Ω} (hR : MeasurableSet R) :
    (μ.restrict R).rnDeriv (ν.restrict R) =ᵐ[ν.restrict R] μ.rnDeriv ν := by
  have h1 : μ.restrict R = (ν.restrict R).withDensity (μ.rnDeriv ν) := by
    conv_lhs => rw [← Measure.withDensity_rnDeriv_eq μ ν hac]
    exact restrict_withDensity hR _
  rw [h1]
  exact Measure.rnDeriv_withDensity _ (Measure.measurable_rnDeriv μ ν)

/-- The relative entropy splits over an event and its complement. -/
theorem klDiv_split (μ ν : Measure Ω) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hac : μ ≪ ν)
    {R : Set Ω} (hR : MeasurableSet R) :
    klDiv (μ.restrict R) (ν.restrict R) + klDiv (μ.restrict Rᶜ) (ν.restrict Rᶜ) = klDiv μ ν := by
  rw [klDiv_eq_lintegral_klFun_of_ac (hac.restrict R),
    klDiv_eq_lintegral_klFun_of_ac (hac.restrict Rᶜ), klDiv_eq_lintegral_klFun_of_ac hac]
  have h1 : (fun x => ENNReal.ofReal (klFun ((μ.restrict R).rnDeriv (ν.restrict R) x).toReal))
      =ᵐ[ν.restrict R] fun x => ENNReal.ofReal (klFun (μ.rnDeriv ν x).toReal) :=
    (rnDeriv_restrict_restrict μ ν hac hR).mono fun x hx => by simp only [hx]
  have h2 : (fun x => ENNReal.ofReal (klFun ((μ.restrict Rᶜ).rnDeriv (ν.restrict Rᶜ) x).toReal))
      =ᵐ[ν.restrict Rᶜ] fun x => ENNReal.ofReal (klFun (μ.rnDeriv ν x).toReal) :=
    (rnDeriv_restrict_restrict μ ν hac hR.compl).mono fun x hx => by simp only [hx]
  rw [lintegral_congr_ae h1, lintegral_congr_ae h2]
  exact lintegral_add_compl _ hR

/-- Data processing for an event: `d(P(R) ‖ Q(R)) ≤ D(P ‖ Q)`. -/
theorem binary_kl_le (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {R : Set Ω} (hR : MeasurableSet R) (hfin : klDiv P Q ≠ ∞) :
    P.real R * log (P.real R / Q.real R) +
        (1 - P.real R) * log ((1 - P.real R) / (1 - Q.real R)) ≤ (klDiv P Q).toReal := by
  have hac : P ≪ Q := (klDiv_ne_top_iff.mp hfin).1
  have h1 := mul_log_le_klDiv (P.restrict R) (Q.restrict R)
  have h2 := mul_log_le_klDiv (P.restrict Rᶜ) (Q.restrict Rᶜ)
  have eP : (P.restrict R).real Set.univ = P.real R := by
    simp [Measure.real]
  have eQ : (Q.restrict R).real Set.univ = Q.real R := by
    simp [Measure.real]
  have eP' : (P.restrict Rᶜ).real Set.univ = 1 - P.real R := by
    have : (P.restrict Rᶜ).real Set.univ = P.real Rᶜ := by
      simp [Measure.real]
    rw [this, measureReal_compl hR, probReal_univ]
  have eQ' : (Q.restrict Rᶜ).real Set.univ = 1 - Q.real R := by
    have : (Q.restrict Rᶜ).real Set.univ = Q.real Rᶜ := by
      simp [Measure.real]
    rw [this, measureReal_compl hR, probReal_univ]
  rw [eP, eQ] at h1
  rw [eP', eQ'] at h2
  have hsum := add_le_add h1 h2
  rw [klDiv_split P Q hac hR] at hsum
  have h3 := ENNReal.ofReal_add_le.trans hsum
  have h4 := ENNReal.toReal_mono hfin h3
  rw [ENNReal.toReal_ofReal'] at h4
  have h5 := le_max_left (P.real R * log (P.real R / Q.real R) + Q.real R - P.real R +
    ((1 - P.real R) * log ((1 - P.real R) / (1 - Q.real R)) + (1 - Q.real R) - (1 - P.real R))) 0
  linarith

/-- The information diffusion inequality before dividing:
`P(R) log ((1 - p_min)/p_max) ≤ D(P ‖ Q) + H(P(R)) + log (1 - p_min)`. -/
theorem fano_kl_core (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {R : Set Ω} (hR : MeasurableSet R) (hfin : klDiv P Q ≠ ∞) {pmin pmax : ℝ}
    (hpmin1 : pmin < 1) (hpmax : 0 < pmax) (hlo : pmin ≤ Q.real R) (hhi : Q.real R ≤ pmax) :
    P.real R * log ((1 - pmin) / pmax) ≤
      (klDiv P Q).toReal + binEntropy (P.real R) + log (1 - pmin) := by
  have hac : P ≪ Q := (klDiv_ne_top_iff.mp hfin).1
  have hb := binary_kl_le P Q hR hfin
  set p := P.real R with hp
  set q := Q.real R with hq
  have hp0 : 0 ≤ p := measureReal_nonneg
  have hp1 : p ≤ 1 := by rw [hp]; exact measureReal_le_one
  have hq0 : 0 ≤ q := measureReal_nonneg
  have hq1 : q ≤ 1 := by rw [hq]; exact measureReal_le_one
  have hqpos : 0 < p → 0 < q := fun hpos => by
    rcases eq_or_lt_of_le hq0 with h | h
    · exfalso
      have hQ0 : Q R = 0 := (measureReal_eq_zero_iff (measure_ne_top Q R)).mp h.symm
      have hP0 : P R = 0 := hac hQ0
      have : p = 0 := (measureReal_eq_zero_iff (measure_ne_top P R)).mpr hP0
      linarith
    · exact h
  have hq1lt : p < 1 → q < 1 := fun hlt => by
    rcases eq_or_lt_of_le hq1 with h | h
    · exfalso
      have hQc : Q.real Rᶜ = 0 := by rw [measureReal_compl hR, probReal_univ, ← hq, h]; ring
      have hQ0 : Q Rᶜ = 0 := (measureReal_eq_zero_iff (measure_ne_top Q _)).mp hQc
      have hP0 : P Rᶜ = 0 := hac hQ0
      have hPc : P.real Rᶜ = 0 := (measureReal_eq_zero_iff (measure_ne_top P _)).mpr hP0
      rw [measureReal_compl hR, probReal_univ, ← hp] at hPc
      linarith
    · exact h
  have hH : binEntropy p = -p * log p - (1 - p) * log (1 - p) := by
    rw [binEntropy_eq_negMulLog_add_negMulLog_one_sub, negMulLog_def]
    ring
  have hkey : p * log (p / q) + (1 - p) * log ((1 - p) / (1 - q)) + binEntropy p =
      -p * log q - (1 - p) * log (1 - q) := by
    rw [hH]
    rcases eq_or_lt_of_le hp0 with h0 | hpos
    · rw [← h0]
      norm_num [log_inv]
    · rcases eq_or_lt_of_le hp1 with h1 | hlt
      · rw [h1]
        norm_num [log_inv]
      · have hq' := hqpos hpos
        have hq1' := hq1lt hlt
        rw [log_div hpos.ne' hq'.ne', log_div (by linarith) (by linarith)]
        ring
  have h3 : -p * log pmax ≤ -p * log q := by
    rcases eq_or_lt_of_le hp0 with h0 | hpos
    · rw [← h0]; simp
    · have := log_le_log (hqpos hpos) hhi
      nlinarith
  have h4 : -(1 - p) * log (1 - pmin) ≤ -(1 - p) * log (1 - q) := by
    rcases eq_or_lt_of_le hp1 with h1 | hlt
    · rw [h1]; simp
    · have := log_le_log (by linarith [hq1lt hlt]) (by linarith : 1 - q ≤ 1 - pmin)
      nlinarith
  have h5 : log ((1 - pmin) / pmax) = log (1 - pmin) - log pmax :=
    log_div (by linarith) hpmax.ne'
  rw [h5]
  nlinarith

theorem info_diffusion_fano_kl : InfoDiffusionFanoKL.{u} := by
  intro Ω _ P Q _ _ R pmin pmax hR hpmin hpmax hsum hlo hhi hfin
  have hcore := fano_kl_core P Q hR hfin (by linarith) hpmax hlo hhi
  have hL : 0 < log ((1 - pmin) / pmax) := by
    apply Real.log_pos
    rw [one_lt_div hpmax]
    linarith
  rw [le_div_iff₀ hL]
  exact hcore

end KL

section Chain

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

instance isProbabilityMeasure_chainLaw (μ : Measure (α × β)) [IsProbabilityMeasure μ]
    (κ : Kernel β γ) [IsMarkovKernel κ] : IsProbabilityMeasure (chainLaw μ κ) := by
  unfold chainLaw
  infer_instance

theorem chainLaw_fst (μ : Measure (α × β)) [IsProbabilityMeasure μ] (κ : Kernel β γ)
    [IsMarkovKernel κ] : (chainLaw μ κ).fst = μ.fst := by
  ext s hs
  rw [Measure.fst_apply hs, Measure.fst_apply hs, chainLaw,
    Measure.bind_apply (measurable_fst hs) (Kernel.aemeasurable _)]
  have h1 : ∀ p : α × β, ((Kernel.id : Kernel α α) ∥ₖ κ) p (Prod.fst ⁻¹' s) =
      (Prod.fst ⁻¹' s).indicator 1 p := by
    intro p
    rw [show (Prod.fst ⁻¹' s : Set (α × γ)) = s ×ˢ (Set.univ : Set γ) from Set.prod_univ.symm,
      Kernel.parallelComp_apply_prod, Kernel.id_apply, measure_univ, mul_one,
      Measure.dirac_apply' _ hs]
    by_cases h : p.1 ∈ s
    · have h' : p ∈ Prod.fst ⁻¹' s := h
      rw [Set.indicator_of_mem h, Set.indicator_of_mem h', Pi.one_apply, Pi.one_apply]
    · have h' : p ∉ Prod.fst ⁻¹' s := h
      rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h']
  simp_rw [h1]
  rw [lintegral_indicator_one (measurable_fst hs)]

theorem chainLaw_snd (μ : Measure (α × β)) [IsProbabilityMeasure μ] (κ : Kernel β γ)
    [IsMarkovKernel κ] : (chainLaw μ κ).snd = κ ∘ₘ μ.snd := by
  ext t ht
  rw [Measure.snd_apply ht, chainLaw,
    Measure.bind_apply (measurable_snd ht) (Kernel.aemeasurable _),
    Measure.bind_apply ht (Kernel.aemeasurable _), Measure.snd,
    lintegral_map (Kernel.measurable_coe κ ht) measurable_snd]
  congr 1
  ext p
  rw [show (Prod.snd ⁻¹' t : Set (α × γ)) = (Set.univ : Set α) ×ˢ t from Set.univ_prod.symm,
    Kernel.parallelComp_apply_prod, Kernel.id_apply, measure_univ, one_mul]

/-- Data processing for mutual information along a Markov chain: `I(X; X̂) ≤ I(X; Y)`. -/
theorem mutualInfo_chainLaw_le (μ : Measure (α × β)) [IsProbabilityMeasure μ] (κ : Kernel β γ)
    [IsMarkovKernel κ] : mutualInfo (chainLaw μ κ) ≤ mutualInfo μ := by
  unfold mutualInfo
  rw [chainLaw_fst, chainLaw_snd, Measure.prod_comp_right]
  exact klDiv_comp_right_le _ _ _

end Chain

theorem fano_arbitrary_relation : FanoArbitraryRelation.{u} := by
  intro α β γ _ _ _ μ _ κ _ R pmin pmax hR hpmin hpmax hsum hbd hfin
  have hdpi := mutualInfo_chainLaw_le μ κ
  have hfinν : mutualInfo (chainLaw μ κ) ≠ ∞ := ne_top_of_le_ne_top hfin hdpi
  set ν := chainLaw μ κ with hν
  have hQR : pmin ≤ (ν.fst.prod ν.snd).real R ∧ (ν.fst.prod ν.snd).real R ≤ pmax := by
    rw [hν, chainLaw_fst]
    have happ := Measure.prod_apply_symm (μ := μ.fst) (ν := (chainLaw μ κ).snd) hR
    have hlo : ∀ z, ENNReal.ofReal pmin ≤ μ.fst ((fun x => (x, z)) ⁻¹' R) := fun z => by
      have h := (hbd z).1
      exact ENNReal.ofReal_le_of_le_toReal h
    have hhi : ∀ z, μ.fst ((fun x => (x, z)) ⁻¹' R) ≤ ENNReal.ofReal pmax := fun z => by
      have h := (hbd z).2
      exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hpmax.le).mpr h
    have hI1 : ENNReal.ofReal pmin ≤ (μ.fst.prod (chainLaw μ κ).snd) R := by
      rw [happ]
      calc ENNReal.ofReal pmin = ∫⁻ _, ENNReal.ofReal pmin ∂(chainLaw μ κ).snd := by
            simp [measure_univ]
        _ ≤ _ := lintegral_mono hlo
    have hI2 : (μ.fst.prod (chainLaw μ κ).snd) R ≤ ENNReal.ofReal pmax := by
      rw [happ]
      calc _ ≤ ∫⁻ _, ENNReal.ofReal pmax ∂(chainLaw μ κ).snd := lintegral_mono hhi
        _ = ENNReal.ofReal pmax := by simp [measure_univ]
    constructor
    · exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mp hI1
    · exact ENNReal.toReal_le_of_le_ofReal hpmax.le hI2
  have h1 := info_diffusion_fano_kl ν (ν.fst.prod ν.snd) R pmin pmax hR hpmin hpmax hsum hQR.1
    hQR.2 hfinν
  refine ⟨h1, ?_⟩
  have hL : 0 < log ((1 - pmin) / pmax) := by
    apply Real.log_pos
    rw [one_lt_div hpmax]
    linarith
  apply div_le_div_of_nonneg_right _ hL.le
  have := ENNReal.toReal_mono hfin hdpi
  linarith

end Proof

end Lemmata.FanoDiffusion
