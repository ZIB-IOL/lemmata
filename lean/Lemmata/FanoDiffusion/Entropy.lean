module

public import Lemmata.FanoDiffusion.Proof

@[expose] public section

/-!
# Entropy of finite random variables

On a finite set with all singletons measurable, the Radon–Nikodym derivative at a point of positive
mass is the ratio of the masses, so the relative entropy is the finite sum
`Σ P(b) log (P(b)/Q(b))`. For a joint law of `(X, X̂)` and the product of its marginals this gives
`I(X; X̂) = H(X) + H(X̂) - H(X, X̂) = H(X) - H(X | X̂)`.
-/

namespace Lemmata.FanoDiffusion

open MeasureTheory ProbabilityTheory InformationTheory Real
open scoped ENNReal

universe u

namespace Proof

section Finite

variable {β : Type*} [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]

theorem ac_of_singleton {μ ν : Measure β} (h : ∀ b, ν {b} = 0 → μ {b} = 0) : μ ≪ ν := by
  classical
  intro s hs
  have e : μ s = ∑ b ∈ s.toFinset, μ {b} := by rw [sum_measure_singleton, Set.coe_toFinset]
  rw [e]
  exact Finset.sum_eq_zero fun b hb =>
    h b (measure_mono_null (Set.singleton_subset_iff.mpr (Set.mem_toFinset.mp hb)) hs)

theorem rnDeriv_singleton {μ ν : Measure β} [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hac : μ ≪ ν)
    (b : β) (hb : ν {b} ≠ 0) : μ.rnDeriv ν b = μ {b} / ν {b} := by
  have h := Measure.setLIntegral_rnDeriv hac {b}
  rw [lintegral_singleton] at h
  rw [← h, ENNReal.mul_div_cancel_right hb (measure_ne_top ν _)]

/-- The relative entropy on a finite set. -/
theorem klDiv_fintype (μ ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hac : μ ≪ ν) :
    klDiv μ ν ≠ ∞ ∧ (klDiv μ ν).toReal = ∑ b, μ.real {b} * log (μ.real {b} / ν.real {b}) := by
  have hsum := klDiv_eq_lintegral_klFun_of_ac hac
  rw [lintegral_fintype] at hsum
  have hfin : ∀ b, ENNReal.ofReal (klFun (μ.rnDeriv ν b).toReal) * ν {b} ≠ ∞ := fun b =>
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top ν _)
  have hne : klDiv μ ν ≠ ∞ := by
    rw [hsum]
    exact ENNReal.sum_ne_top.mpr fun b _ => hfin b
  refine ⟨hne, ?_⟩
  rw [hsum, ENNReal.toReal_sum fun b _ => hfin b]
  have hterm : ∀ b, (ENNReal.ofReal (klFun (μ.rnDeriv ν b).toReal) * ν {b}).toReal =
      μ.real {b} * log (μ.real {b} / ν.real {b}) + ν.real {b} - μ.real {b} := by
    intro b
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (klFun_nonneg ENNReal.toReal_nonneg)]
    by_cases hb : ν {b} = 0
    · have hμb : μ {b} = 0 := hac hb
      simp [Measure.real, hb, hμb]
    · rw [rnDeriv_singleton hac b hb, ENNReal.toReal_div]
      change klFun (μ.real {b} / ν.real {b}) * ν.real {b} = _
      have hpos : 0 < ν.real {b} := ENNReal.toReal_pos hb (measure_ne_top ν _)
      rw [klFun_apply]
      field_simp
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have h1 : ∑ b, ν.real {b} = 1 := by
    rw [sum_measureReal_singleton, Finset.coe_univ, probReal_univ]
  have h2 : ∑ b, μ.real {b} = 1 := by
    rw [sum_measureReal_singleton, Finset.coe_univ, probReal_univ]
  rw [h1, h2]
  ring

end Finite

section Joint

variable {α γ : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] [Fintype γ]
  [MeasurableSpace γ] [MeasurableSingletonClass γ]

omit [Fintype α] in
theorem fst_real_singleton (ν : Measure (α × γ)) [IsFiniteMeasure ν] (a : α) :
    ν.fst.real {a} = ∑ c, ν.real {(a, c)} := by
  classical
  have e : (Prod.fst ⁻¹' {a} : Set (α × γ)) = ⋃ c ∈ (Finset.univ : Finset γ), {(a, c)} := by
    ext ⟨x, c⟩
    simp [eq_comm]
  rw [Measure.real, Measure.fst_apply (measurableSet_singleton a), e,
    measure_biUnion_finset (fun c _ c' _ hcc' => Set.disjoint_singleton.mpr (by simpa using hcc'))
      (fun c _ => measurableSet_singleton _),
    ENNReal.toReal_sum (fun c _ => measure_ne_top ν _)]
  rfl

omit [Fintype γ] in
theorem snd_real_singleton (ν : Measure (α × γ)) [IsFiniteMeasure ν] (c : γ) :
    ν.snd.real {c} = ∑ a, ν.real {(a, c)} := by
  classical
  have e : (Prod.snd ⁻¹' {c} : Set (α × γ)) = ⋃ a ∈ (Finset.univ : Finset α), {(a, c)} := by
    ext ⟨a, x⟩
    simp [eq_comm]
  rw [Measure.real, Measure.snd_apply (measurableSet_singleton c), e,
    measure_biUnion_finset (fun a _ a' _ haa' => Set.disjoint_singleton.mpr (by simpa using haa'))
      (fun a _ => measurableSet_singleton _),
    ENNReal.toReal_sum (fun a _ => measure_ne_top ν _)]
  rfl

omit [Fintype α] [MeasurableSingletonClass α] [Fintype γ] [MeasurableSingletonClass γ] in
theorem prod_real_singleton (ν : Measure (α × γ)) [IsFiniteMeasure ν] (a : α) (c : γ) :
    (ν.fst.prod ν.snd).real {(a, c)} = ν.fst.real {a} * ν.snd.real {c} := by
  rw [← Set.singleton_prod_singleton, Measure.real, Measure.prod_prod, ENNReal.toReal_mul]
  rfl

theorem mutual_info_entropy : MutualInfoEntropy.{u} := by
  intro α γ _ _ _ _ _ _ ν _
  have hle_fst : ∀ a c, ν.real {(a, c)} ≤ ν.fst.real {a} := fun a c => by
    rw [fst_real_singleton]
    exact Finset.single_le_sum (f := fun c => ν.real {(a, c)})
      (fun _ _ => measureReal_nonneg) (Finset.mem_univ c)
  have hle_snd : ∀ a c, ν.real {(a, c)} ≤ ν.snd.real {c} := fun a c => by
    rw [snd_real_singleton]
    exact Finset.single_le_sum (f := fun a => ν.real {(a, c)})
      (fun _ _ => measureReal_nonneg) (Finset.mem_univ a)
  have hac : ν ≪ ν.fst.prod ν.snd := ac_of_singleton fun ⟨a, c⟩ h => by
    have h1 : (ν.fst.prod ν.snd).real {(a, c)} = 0 := by rw [Measure.real, h]; rfl
    rw [prod_real_singleton] at h1
    have h2 : ν.real {(a, c)} = 0 := by
      rcases mul_eq_zero.mp h1 with h3 | h3
      · exact le_antisymm (h3 ▸ hle_fst a c) measureReal_nonneg
      · exact le_antisymm (h3 ▸ hle_snd a c) measureReal_nonneg
    exact (measureReal_eq_zero_iff (measure_ne_top ν _)).mp h2
  obtain ⟨hne, heq⟩ := klDiv_fintype ν (ν.fst.prod ν.snd) hac
  refine ⟨hne, ?_⟩
  unfold mutualInfo condEntropy entropy
  rw [heq]
  have hterm : ∀ x : α × γ, ν.real {x} * log (ν.real {x} / (ν.fst.prod ν.snd).real {x}) =
      ν.real {x} * log (ν.real {x}) - ν.real {x} * log (ν.fst.real {x.1}) -
        ν.real {x} * log (ν.snd.real {x.2}) := by
    rintro ⟨a, c⟩
    rw [prod_real_singleton]
    rcases eq_or_lt_of_le (measureReal_nonneg : 0 ≤ ν.real {(a, c)}) with h | h
    · rw [← h]
      ring
    · have ha := lt_of_lt_of_le h (hle_fst a c)
      have hc := lt_of_lt_of_le h (hle_snd a c)
      rw [log_div h.ne' (mul_pos ha hc).ne', log_mul ha.ne' hc.ne']
      ring
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  have hA : ∑ x : α × γ, ν.real {x} * log (ν.fst.real {x.1}) =
      ∑ a, ν.fst.real {a} * log (ν.fst.real {a}) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    show ∑ c, ν.real {(a, c)} * log (ν.fst.real {a}) = ν.fst.real {a} * log (ν.fst.real {a})
    rw [← Finset.sum_mul, ← fst_real_singleton]
  have hC : ∑ x : α × γ, ν.real {x} * log (ν.snd.real {x.2}) =
      ∑ c, ν.snd.real {c} * log (ν.snd.real {c}) := by
    rw [Fintype.sum_prod_type_right]
    refine Finset.sum_congr rfl fun c _ => ?_
    show ∑ a, ν.real {(a, c)} * log (ν.snd.real {c}) = ν.snd.real {c} * log (ν.snd.real {c})
    rw [← Finset.sum_mul, ← snd_real_singleton]
  rw [hA, hC]
  simp only [negMulLog_def, neg_mul, Finset.sum_neg_distrib]
  ring

theorem entropy_uniform : EntropyUniform.{u} := by
  intro α _ _ ν hunif
  unfold entropy
  have h1 : ∀ a, ν.real {a} = (Fintype.card α : ℝ)⁻¹ := fun a => by
    rw [Measure.real, hunif a, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  simp only [h1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, negMulLog_def]
  rcases (Fintype.card α).eq_zero_or_pos with h | h
  · simp [h]
  · have hc : (0 : ℝ) < Fintype.card α := by exact_mod_cast h
    rw [log_inv]
    field_simp

theorem entropy_fano : EntropyFano.{u} := by
  intro α γ _ _ _ _ _ _ ν _ R pmin pmax hpmin hpmin1 hpmax hbd
  have hRm : MeasurableSet R := (Set.toFinite R).measurableSet
  obtain ⟨hne, hI⟩ := mutual_info_entropy ν
  have hQR : pmin ≤ (ν.fst.prod ν.snd).real R ∧ (ν.fst.prod ν.snd).real R ≤ pmax := by
    have happ := Measure.prod_apply_symm (μ := ν.fst) (ν := ν.snd) hRm
    have hlo : ∀ z, ENNReal.ofReal pmin ≤ ν.fst ((fun x => (x, z)) ⁻¹' R) := fun z =>
      ENNReal.ofReal_le_of_le_toReal (hbd z).1
    have hhi : ∀ z, ν.fst ((fun x => (x, z)) ⁻¹' R) ≤ ENNReal.ofReal pmax := fun z =>
      (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hpmax.le).mpr (hbd z).2
    have hI1 : ENNReal.ofReal pmin ≤ (ν.fst.prod ν.snd) R := by
      rw [happ]
      calc ENNReal.ofReal pmin = ∫⁻ _, ENNReal.ofReal pmin ∂ν.snd := by simp [measure_univ]
        _ ≤ _ := lintegral_mono hlo
    have hI2 : (ν.fst.prod ν.snd) R ≤ ENNReal.ofReal pmax := by
      rw [happ]
      calc _ ≤ ∫⁻ _, ENNReal.ofReal pmax ∂ν.snd := lintegral_mono hhi
        _ = ENNReal.ofReal pmax := by simp [measure_univ]
    exact ⟨(ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mp hI1,
      ENNReal.toReal_le_of_le_ofReal hpmax.le hI2⟩
  have hcore := fano_kl_core ν (ν.fst.prod ν.snd) hRm hne hpmin1 hpmax hQR.1 hQR.2
  change ν.real R * log ((1 - pmin) / pmax) ≤
    (mutualInfo ν).toReal + binEntropy (ν.real R) + log (1 - pmin) at hcore
  rw [hI] at hcore
  have hRc : ν.real Rᶜ = 1 - ν.real R := by rw [measureReal_compl hRm, probReal_univ]
  have hH : binEntropy (ν.real Rᶜ) = binEntropy (ν.real R) := by rw [hRc, binEntropy_one_sub]
  have hlog : log ((1 - pmin) / pmax) = log (1 - pmin) - log pmax :=
    log_div (by linarith) hpmax.ne'
  rw [hH, hRc]
  nlinarith [hcore, hlog]

theorem distance_fano_entropy : DistanceFanoEntropy.{u} := by
  intro α _ _ _ ν _ ρ t Nmin Nmax hunif hNmax hNmin hcount
  classical
  set n := Fintype.card α with hn
  have hn0 : (0 : ℝ) < n := by
    have : 0 < n := lt_of_le_of_lt (Nat.zero_le _) hNmin
    exact_mod_cast this
  have hNmax' : (0 : ℝ) < Nmax := by exact_mod_cast hNmax
  have hNminn : (Nmin : ℝ) < n := by exact_mod_cast hNmin
  set R : Set (α × α) := {p | ρ p.1 p.2 ≤ t} with hRdef
  have hsec : ∀ z, ν.fst.real {x | (x, z) ∈ R} =
      ((Finset.univ.filter fun x => ρ x z ≤ t).card : ℝ) / n := by
    intro z
    have e : {x | (x, z) ∈ R} = ↑(Finset.univ.filter fun x => ρ x z ≤ t) := by
      ext x
      simp [hRdef]
    rw [e, Measure.real, ← sum_measure_singleton]
    simp only [hunif, Finset.sum_const, nsmul_eq_mul]
    rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      div_eq_mul_inv]
  have h := entropy_fano ν R (Nmin / n) (Nmax / n) (by positivity)
    (by rw [div_lt_one hn0]; exact hNminn) (by positivity)
    (fun z => ⟨by
      rw [hsec z]
      exact div_le_div_of_nonneg_right (by exact_mod_cast (hcount z).1) hn0.le, by
      rw [hsec z]
      exact div_le_div_of_nonneg_right (by exact_mod_cast (hcount z).2) hn0.le⟩)
  have hHX : entropy ν.fst = log n := entropy_uniform ν.fst hunif
  have hRc : Rᶜ = {p : α × α | t < ρ p.1 p.2} := by
    ext p
    simp [hRdef, not_le]
  rw [hHX, hRc] at h
  have e1 : log n + log (Nmax / n) = log Nmax := by
    rw [log_div hNmax'.ne' hn0.ne']
    ring
  have e2 : ((1 : ℝ) - Nmin / n) / (Nmax / n) = ((n : ℝ) - Nmin) / Nmax := by
    rw [one_sub_div hn0.ne', div_div_div_cancel_right₀ hn0.ne']
  rw [e2] at h
  linarith

end Joint

end Proof

end Lemmata.FanoDiffusion
