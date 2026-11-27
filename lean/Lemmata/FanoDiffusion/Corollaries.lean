module

public import Lemmata.FanoDiffusion.Proof

@[expose] public section

/-!
# Distance-based and continuous Fano inequalities (Corollaries 2.6 and 2.7)

Both follow from Proposition 2.2 with the relation `ρ(x, x̂) ≤ t`, `p_min = 0`, and `p_max` the
largest probability of a ball under the uniform law of `X`.
-/

namespace Lemmata.FanoDiffusion

open MeasureTheory ProbabilityTheory InformationTheory Real
open scoped ENNReal

universe u

namespace Proof

theorem distance_fano : DistanceFano.{u} := by
  intro α β _ _ _ _ μ _ κ _ ρ t N hunif hN0 hNlt hcount hfin
  classical
  set n := Fintype.card α with hn
  have hn0 : (0 : ℝ) < n := by
    have : 0 < n := lt_trans hN0 hNlt
    exact_mod_cast this
  have hN0' : (0 : ℝ) < N := by exact_mod_cast hN0
  have hNn : (N : ℝ) < n := by exact_mod_cast hNlt
  set R : Set (α × α) := {p | ρ p.1 p.2 ≤ t} with hRdef
  have hRm : MeasurableSet R := (Set.toFinite R).measurableSet
  have hsec : ∀ z, μ.fst.real {x | (x, z) ∈ R} =
      ((Finset.univ.filter fun x => ρ x z ≤ t).card : ℝ) / n := by
    intro z
    have e : {x | (x, z) ∈ R} = ↑(Finset.univ.filter fun x => ρ x z ≤ t) := by
      ext x
      simp [hRdef]
    rw [e, Measure.real, ← sum_measure_singleton]
    simp only [hunif, Finset.sum_const, nsmul_eq_mul]
    rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      div_eq_mul_inv]
  have hfano := fano_arbitrary_relation μ κ R 0 (N / n) hRm le_rfl (by positivity)
    (by rw [zero_add, div_lt_one hn0]; exact hNn)
    (fun z => ⟨measureReal_nonneg, by
      rw [hsec z]
      apply div_le_div_of_nonneg_right _ hn0.le
      exact_mod_cast hcount z⟩) hfin
  have hcompl : (chainLaw μ κ).real {p | t < ρ p.1 p.2} = 1 - (chainLaw μ κ).real R := by
    have : {p : α × α | t < ρ p.1 p.2} = Rᶜ := by
      ext p
      simp [hRdef, not_le]
    rw [this, measureReal_compl hRm, probReal_univ]
  set Pt := (chainLaw μ κ).real {p | t < ρ p.1 p.2} with hPt
  have hνR : (chainLaw μ κ).real R = 1 - Pt := by rw [hcompl]; ring
  have hH : binEntropy ((chainLaw μ κ).real R) = binEntropy Pt := by
    rw [hνR, binEntropy_one_sub]
  have hL : log ((1 - 0) / (N / n)) = log (n / N) := by
    rw [sub_zero, one_div_div]
  obtain ⟨h1, h2⟩ := hfano
  rw [hH, hL] at h1 h2
  simp only [sub_zero, Real.log_one, add_zero] at h1 h2
  rw [hνR] at h1
  linarith

theorem continuous_fano : ContinuousFano.{u} := by
  intro α β _ _ μ _ κ _ S ρ t V hS hSfin hunif hρ hV0 hVS hball hfin
  set R : Set (α × α) := {p | ρ p.1 p.2 ≤ t} with hRdef
  have hRm : MeasurableSet R := measurableSet_le hρ measurable_const
  have hvS : 0 < volume.real S := lt_trans hV0 hVS
  have hsec : ∀ z, μ.fst.real {x | (x, z) ∈ R} =
      volume.real ({x | ρ x z ≤ t} ∩ S) / volume.real S := by
    intro z
    have hmz : MeasurableSet {x | ρ x z ≤ t} :=
      measurableSet_le (hρ.comp (measurable_id.prodMk measurable_const)) measurable_const
    have e : {x | (x, z) ∈ R} = {x | ρ x z ≤ t} := by
      ext x
      simp [hRdef]
    rw [e, hunif]
    simp only [Measure.real, Measure.smul_apply, Measure.restrict_apply hmz, smul_eq_mul]
    rw [ENNReal.toReal_mul, ENNReal.toReal_inv, div_eq_inv_mul]
  have hfano := fano_arbitrary_relation μ κ R 0 (V / volume.real S) hRm le_rfl (div_pos hV0 hvS)
    (by rw [zero_add, div_lt_one hvS]; exact hVS)
    (fun z => ⟨measureReal_nonneg, by
      rw [hsec z]
      exact div_le_div_of_nonneg_right (hball z) hvS.le⟩) hfin
  have hcompl : (chainLaw μ κ).real {p | t < ρ p.1 p.2} = 1 - (chainLaw μ κ).real R := by
    have : {p : α × α | t < ρ p.1 p.2} = Rᶜ := by
      ext p
      simp [hRdef, not_le]
    rw [this, measureReal_compl hRm, probReal_univ]
  set Pt := (chainLaw μ κ).real {p | t < ρ p.1 p.2} with hPt
  have hνR : (chainLaw μ κ).real R = 1 - Pt := by rw [hcompl]; ring
  have hL : log ((1 - 0) / (V / volume.real S)) = log (volume.real S / V) := by
    rw [sub_zero, one_div_div]
  have hLpos : 0 < log (volume.real S / V) := by
    apply Real.log_pos
    rw [one_lt_div hV0]
    exact hVS
  have hHle : binEntropy ((chainLaw μ κ).real R) ≤ log 2 := binEntropy_le_log_two
  obtain ⟨h1, h2⟩ := hfano
  rw [hL] at h1 h2
  simp only [sub_zero, Real.log_one, add_zero] at h1 h2
  have h3 : ((mutualInfo μ).toReal + binEntropy ((chainLaw μ κ).real R)) /
      log (volume.real S / V) ≤ ((mutualInfo μ).toReal + log 2) / log (volume.real S / V) :=
    div_le_div_of_nonneg_right (by linarith) hLpos.le
  linarith [hνR]

end Proof

end Lemmata.FanoDiffusion
