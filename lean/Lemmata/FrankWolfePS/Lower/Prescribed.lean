module

public import Lemmata.FrankWolfePS.Lower.Feasible
public import Lemmata.FrankWolfePS.Lower.Transcript
public import Lemmata.FrankWolfePS.Lower.Faces
public import Lemmata.FrankWolfePS.Lower.Posterior
public import Lemmata.FrankWolfePS.Upper.Complexity
public import Lemmata.FrankWolfePS.Unique.Lower
public import Lemmata.FrankWolfePS.Joint.Complexity
@[expose] public section

namespace Lemmata.FrankWolfePS
open Finset MeasureTheory
open scoped RealInnerProductSpace

/-- The paper's fixed-parameter theorem. One legal physical body is selected
for a given method and number of oracle calls, independently of the realized tape. -/
theorem fixed_smoothness_lower_bound {ι Ω : Type*} [Fintype ι] [LinearOrder ι]
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : ℕ) (anchor : ι) (hN : Fintype.card ι = 256 * (T + 1))
    {L β D : ℝ} (hL : 0 < L) (hβ : 0 < β) (hD : 2 < β * D)
    (s : Ω → Method (Ambient ι) T) :
    let r := 1 / β
    let a := (D - 2 / β) / Real.sqrt 2
    let run := fun I ω => (s ω).physicalRun a r anchor I
    (∀ S ∈ instanceSets T anchor, Measurable (run (insert anchor S))) →
    ∃ I : Finset ι, I.card = 8 * (T + 1) ∧ anchor ∈ I ∧
      IsCompact (physicalBody a r I) ∧ Convex ℝ (physicalBody a r I) ∧
      Metric.diam (physicalBody a r I) = D ∧
      (∀ z ∈ physicalBody a r I, ∀ w ∈ physicalBody a r I, ∀ n m : Ambient ι,
        ‖n‖ = 1 → ‖m‖ = 1 → Supports (physicalBody a r I) z n →
        Supports (physicalBody a r I) w m → ‖n - m‖ ≤ β * ‖z - w‖) ∧
      1 / 4 ≤ μ.real {ω | embed (run I ω) ∉ physicalBody a r I ∨
        L * (D - 2 / β) ^ 2 / (32 * ((T + 1 : ℕ) : ℝ)) ≤
            L * obj r (run I ω) - physicalOpt L a r I} := by
  dsimp only
  let r := 1 / β
  let a := (D - 2 / β) / Real.sqrt 2
  obtain ⟨hr, ha, hinv, hdiam, hcut, _⟩ := prescribed_parameters (L := L) hβ hD (T + 1)
  change 0 < r at hr
  change 0 < a at ha
  change 1 / r = β at hinv
  change 2 * r + Real.sqrt 2 * a = D at hdiam
  change L * a ^ 2 / (16 * ((T + 1 : ℕ) : ℝ)) = _ at hcut
  intro meas
  obtain ⟨S, hS, hp⟩ := (scaled_randomized_lower_bound T anchor hN hL ha hr μ s
    (fun S hs => bad_measurable ha hr _ _ _ (meas S hs))).2
  have hs := mem_powersetCard.mp hS
  have hn : anchor ∉ S := fun hi => (notMem_erase anchor univ) (hs.1 hi)
  have hc : (insert anchor S).card = 8 * (T + 1) := by rw [card_insert_of_notMem hn, hs.2]; omega
  have par := physical_parameters ha hr (insert anchor S) (by omega)
  have cp := physical_body_compact_convex (a := a) (r := r) (insert anchor S)
  refine ⟨_, hc, mem_insert_self .., cp.1, cp.2, par.1.trans hdiam, ?_, ?_⟩
  · simpa only [hinv] using par.2
  · simpa only [physicalFailure, hcut] using hp

/-- For an always-feasible method both bounds, at the prescribed geometric parameters, hold on a
single instance: the gap is at least `L (D - 2/β)² / (32 (T + 1))` with probability at least
`3/4`, and the expected gap is at least `3 L (D - 2/β)² / (128 (T + 1))`. -/
theorem fixed_smoothness_expected_lower_bound {ι Ω : Type*} [Fintype ι] [LinearOrder ι]
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : ℕ) (anchor : ι) (hN : Fintype.card ι = 256 * (T + 1))
    {L β D : ℝ} (hL : 0 < L) (hβ : 0 < β) (hD : 2 < β * D)
    (s : Ω → Method (Ambient ι) T) :
    let r := 1 / β
    let a := (D - 2 / β) / Real.sqrt 2
    let run := fun I ω => (s ω).physicalRun a r anchor I
    (∀ S ∈ instanceSets T anchor, Measurable (run (insert anchor S))) →
    (∀ S ∈ instanceSets T anchor, ∀ ω, embed (run (insert anchor S) ω) ∈
        physicalBody a r (insert anchor S)) →
    ∃ S ∈ instanceSets T anchor, let I := insert anchor S
      Metric.diam (physicalBody a r I) = D ∧
      (3 / 4 ≤ μ.real {ω | L * (D - 2 / β) ^ 2 / (32 * ((T + 1 : ℕ) : ℝ)) ≤
        L * obj r (run I ω) - physicalOpt L a r I}) ∧
      3 * L * (D - 2 / β) ^ 2 / (128 * ((T + 1 : ℕ) : ℝ)) ≤
        ∫ ω, L * obj r (run I ω) - physicalOpt L a r I ∂μ := by
  dsimp only
  let r := 1 / β
  let a := (D - 2 / β) / Real.sqrt 2
  obtain ⟨hr, ha, _, hdiam, hcut, -⟩ := prescribed_parameters (L := L) hβ hD (T + 1)
  change 0 < r at hr
  change 0 < a at ha
  change 2 * r + Real.sqrt 2 * a = D at hdiam
  change L * a ^ 2 / (16 * ((T + 1 : ℕ) : ℝ)) = _ at hcut
  intro meas feas
  obtain ⟨S, hS, hp, he⟩ := feasible_lower_bound T anchor hN hL ha hr μ s meas feas
  have hs := mem_powersetCard.mp hS
  have hn : anchor ∉ S := fun hi => (notMem_erase anchor univ) (hs.1 hi)
  have hc : (insert anchor S).card = 8 * (T + 1) := by rw [card_insert_of_notMem hn, hs.2]; omega
  refine ⟨S, hS,
      (physical_parameters ha hr _ (by omega : 1 < (insert anchor S).card)).1.trans hdiam, ?_, ?_⟩
  · have same : {ω | physicalFailure L a r (T + 1) (insert anchor S)
          ((s ω).physicalRun a r anchor (insert anchor S))} =
        {ω | L * (D - 2 / β) ^ 2 / (32 * ((T + 1 : ℕ) : ℝ)) ≤
          L * obj r ((s ω).physicalRun a r anchor (insert anchor S)) -
            physicalOpt L a r (insert anchor S)} := by
      ext ω
      simp only [Set.mem_ofPred_eq, physicalFailure, hcut]
      exact or_iff_right (not_not.mpr (feas S hS ω))
    rw [same] at hp
    exact hp
  · rw [hcut] at he
    calc 3 * L * (D - 2 / β) ^ 2 / (128 * ((T + 1 : ℕ) : ℝ))
        = 3 / 4 * (L * (D - 2 / β) ^ 2 / (32 * ((T + 1 : ℕ) : ℝ))) := by ring
      _ ≤ _ := he

end Lemmata.FrankWolfePS
