module

public import Lemmata.Centroid.Proof.MinimalBorderRank
public import Lemmata.Centroid.Proof.SymmetricMax
public import Lemmata.Centroid.Proof.Asymptotics
public import Mathlib.Order.ConditionallyCompletePartialOrder.Basic

@[expose] public section

open scoped BigOperators

namespace Lemmata.Centroid

open Tensor (Concise centroid rationalBorderRank)

private theorem generalBoundAt_three_cases (q s : ℕ) :
    generalBoundAt q s = q ^ 3 + 1 +
      if s ≤ 1 then s else if s ≤ q then s * (s - 1)
      else q * s + ((s - q - 1) ^ 2 - q) := by
  by_cases hs₀ : s = 0
  · subst s
    simp [generalBoundAt]
  by_cases hs₁ : s = 1
  · subst s
    simp [generalBoundAt, Nat.add_assoc]
  have hs₂ : ¬ s ≤ 1 := by omega
  by_cases hs : s ≤ q <;>
    simp [generalBoundAt, hs₀, hs₁, hs₂, hs, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm]

-- DOCS_BEGIN_MAIN
theorem generalCentroidBound (F : Type*) [Field F] (N q s : ℕ)
    (hN : 2 ≤ N) (hqs : q * (q + 1) + s = N) (hs : s ≤ 2 * q + 1) :
    (let bound := q ^ 3 + 1 +
       if s ≤ 1 then s else if s ≤ q then s * (s - 1)
       else q * s + ((s - q - 1) ^ 2 - q)
     (∀ T : Cubic F (Fin N), Concise T →
       Module.finrank F (centroid T) ≤ bound ∧ N ≤ rationalBorderRank T) ∧
     (∃ T : Cubic F (Fin N), Concise T ∧ rationalBorderRank T = N ∧
       Module.finrank F (centroid T) = bound)) := by
  dsimp only
  have hb := (generalBound_eq hN hs hqs.symm).trans (generalBoundAt_three_cases q s)
  constructor
  · intro T hT
    constructor
    · simpa only [hb] using Tensor.centroid_upper_bound hT N (by simp)
    · simpa only [Fintype.card_fin] using hT.le_rationalBorderRank (0 : Fin 3)
  · obtain ⟨T, hT, hrank, hdim⟩ := Tensor.exists_minimal_general_maximizer (F := F) N
    exact ⟨T, hT, hrank, hdim.trans hb⟩

theorem symmetricCentroidBound (F : Type*) [Field F] (N q s : ℕ)
    (hN : 2 ≤ N) (hqs : q * (q + 3) / 2 + s = N) (hs : s ≤ q + 1) :
    (let bound := (q + 2).choose 3 + 1 + max s (s.choose 2)
     (∀ T : Cubic F (Fin N), Concise T → Cubic.IsSymmetric T →
       Module.finrank F (centroid T) ≤ bound) ∧
     (∃ T : Cubic F (Fin N), Concise T ∧ Cubic.IsSymmetric T ∧
       Module.finrank F (centroid T) = bound)) := by
  dsimp only
  have hb : symmetricBound N = (q + 2).choose 3 + 1 + max s (s.choose 2) :=
    symmetricBound_eq hN hs (by simpa only [symmetricBase] using hqs.symm)
  constructor
  · intro T hT hsym
    simpa only [Fintype.card_fin, hb] using symmetric_centroid_upper_bound hT hsym
  · obtain ⟨T, hT, hsym, hdim⟩ := exists_symmetric_maximizer (F := F) N
    exact ⟨T, hT, hsym, hdim.trans hb⟩

theorem centroidAsymptotics (F : Type*) [Field F] :
    Filter.Tendsto
      (fun N : ℕ => ((sSup (Tensor.cubicCentroidDimensions F N) : ℕ) : ℝ) /
        (N : ℝ) ^ ((3 : ℝ) / 2)) Filter.atTop (nhds 1) ∧
    Filter.Tendsto
      (fun N : ℕ => ((sSup (symmetricCentroidDimensions F N) : ℕ) : ℝ) /
        (N : ℝ) ^ ((3 : ℝ) / 2)) Filter.atTop (nhds (Real.sqrt 2 / 3)) := by
  have hg (N : ℕ) : sSup (Tensor.cubicCentroidDimensions F N) = generalBound N :=
    (Tensor.general_maximum (F := F) N).csSup_eq
  have hs (N : ℕ) : sSup (symmetricCentroidDimensions F N) = symmetricBound N :=
    (symmetric_maximum (F := F) N).csSup_eq
  constructor
  · simpa only [hg] using generalBound_asymptotic
  · simpa only [hs] using symmetricBound_asymptotic
-- DOCS_END_MAIN

end Lemmata.Centroid
