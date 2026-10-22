module

public import Lemmata.DistributionalLowerBounds.Core.Distributional.YoungOld

@[expose] public section

/-!
# Linear one-query drift from shifted rank thresholds

The old record proxy can be of order `m^(3/2)`. Split certified cells at
`rank a + 1`: at most one boundary cell per row remains. For a deep cell,
swapping its lower rank into the row makes that row the unique minimizer of
its occupied shifted threshold. This gives an injective counting map.

The endpoint `oneQuery_expected_deficit_drop_linear` is unconditional for the
explicit `WaterQuery` interface, including known-coordinate contributions.
The raw transcript-to-`WaterQuery` and adaptive strategy certificates have the
same formalization boundary as the existing distributional theorem.
-/

namespace Lemmata.DistributionalLowerBounds.Core.Distributional
namespace QueryRanks

/-- A downward cell more than one unit below its row's water threshold. -/
def DeepEdge {m : ℕ} {D : FerrersData m} (Q : QueryRanks D) :=
  {e : DownEdge D // (Q.rank e.lowerValue : ℝ) + 1 < Q.tau e.source * Q.q e.row}

/-- A downward cell in the half-open, unit-width boundary interval. -/
def BoundaryEdge {m : ℕ} {D : FerrersData m} (Q : QueryRanks D) :=
  {e : DownEdge D // (Q.rank e.lowerValue : ℝ) < Q.tau e.source * Q.q e.row ∧
    Q.tau e.source * Q.q e.row ≤ (Q.rank e.lowerValue : ℝ) + 1}

noncomputable instance {m : ℕ} {D : FerrersData m} (Q : QueryRanks D) :
    Fintype (DeepEdge Q) :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

noncomputable instance {m : ℕ} {D : FerrersData m} (Q : QueryRanks D) :
    Fintype (BoundaryEdge Q) :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

lemma deep_q_pos {m : ℕ} {D : FerrersData m} (Q : QueryRanks D)
    (e : DeepEdge Q) : 0 < Q.q e.1.row := by
  by_contra hn
  have hz : Q.q e.1.row = 0 := le_antisymm (le_of_not_gt hn) (Q.q_nonneg _)
  have h := e.2
  rw [hz, mul_zero] at h
  have hr : (0 : ℝ) ≤ Q.rank e.1.lowerValue := by positivity
  linarith

/-- Away from the lowered row, the swap only raises rank values. -/
lemma target_rank_ge_of_ne {m : ℕ} {D : FerrersData m} (Q : QueryRanks D)
    (e : DownEdge D) (k : Fin m) (hk : k ≠ e.row) :
    Q.rank (e.source.1 k) ≤ Q.rank (e.target.1 k) := by
  by_cases ha : e.source.1 k = e.lowerValue
  · have hnew : e.target.1 k = e.source.1 e.row := by
      simp [DownEdge.target, ha]
    rw [hnew, ha]
    exact (Q.rank_strict e.lower_lt).le
  · have hs : e.source.1 k ≠ e.source.1 e.row :=
      fun h => hk (e.source.1.injective h)
    have hnew : e.target.1 k = e.source.1 k := by
      simp [DownEdge.target, Equiv.swap_apply_of_ne_of_ne ha hs]
    rw [hnew]

/-- The lowered row uniquely minimizes the target's shifted threshold.
The cross-multiplied formulation also handles zero query components. -/
lemma deep_unique_minimum {m : ℕ} {D : FerrersData m} (Q : QueryRanks D)
    (e : DeepEdge Q) (k : Fin m) (hk : k ≠ e.1.row) :
    ((Q.rank (e.1.target.1 e.1.row) : ℝ) + 1) * Q.q k <
      ((Q.rank (e.1.target.1 k) : ℝ) + 1) * Q.q e.1.row := by
  have hqi := deep_q_pos Q e
  let t : ℝ := ((Q.rank e.1.lowerValue : ℝ) + 1) / Q.q e.1.row
  have ht : t < Q.tau e.1.source := (div_lt_iff₀ hqi).2 e.2
  have hterm := Q.below_term e.1.source t k ht
  have hraw : t * Q.q k < (Q.rank (e.1.source.1 k) : ℝ) + 1 := by linarith
  have hcross := (mul_lt_mul_iff_left₀ hqi).2 hraw
  have hcancel : (t * Q.q k) * Q.q e.1.row =
      ((Q.rank e.1.lowerValue : ℝ) + 1) * Q.q k := by
    dsimp [t]
    field_simp
  rw [hcancel] at hcross
  have hr : (Q.rank (e.1.source.1 k) : ℝ) ≤ Q.rank (e.1.target.1 k) :=
    Nat.cast_le.mpr (target_rank_ge_of_ne Q e.1 k hk)
  have hraise := mul_le_mul_of_nonneg_left (add_le_add_right hr 1) hqi.le
  have hrow : e.1.target.1 e.1.row = e.1.lowerValue := by
    simp [DownEdge.target]
  rw [hrow]
  nlinarith

noncomputable def deepSwitch {m : ℕ} {D : FerrersData m}
    (Q : QueryRanks D) (e : DeepEdge Q) : FerrersPerm D × Fin m :=
  (e.1.target, e.1.source.1 e.1.row)

/-- Deep cells are recoverable from the target and the original larger rank. -/
theorem deepSwitch_injective {m : ℕ} {D : FerrersData m}
    (Q : QueryRanks D) : Function.Injective Q.deepSwitch := by
  intro e f hef
  have ht : e.1.target = f.1.target := congrArg Prod.fst hef
  have hs : e.1.source.1 e.1.row = f.1.source.1 f.1.row := congrArg Prod.snd hef
  have hr : e.1.row = f.1.row := by
    by_contra hn
    have he := deep_unique_minimum Q e f.1.row (Ne.symm hn)
    have hf := deep_unique_minimum Q f e.1.row hn
    rw [ht] at he
    linarith
  have ha : e.1.lowerValue = f.1.lowerValue := by
    have hv := DFunLike.congr_fun (congrArg Subtype.val ht) e.1.row
    simp only [DownEdge.target, swapValues_apply, Equiv.swap_apply_right] at hv
    simpa [hr] using hv
  have hsource : e.1.source = f.1.source := by
    apply Subtype.ext
    calc
      e.1.source.1 = swapValues e.1.target.1 e.1.lowerValue
          (e.1.source.1 e.1.row) := (DownEdge.swap_target_back e.1).symm
      _ = swapValues f.1.target.1 f.1.lowerValue
          (f.1.source.1 f.1.row) := by rw [ht, ha, hs]
      _ = f.1.source.1 := DownEdge.swap_target_back f.1
  apply Subtype.ext
  cases e with
  | mk ee he =>
    cases f with
    | mk ff hf =>
      cases ee
      cases ff
      simp_all

theorem card_deepEdge_le {m : ℕ} {D : FerrersData m} (Q : QueryRanks D) :
    Fintype.card (DeepEdge Q) ≤ m * Fintype.card (FerrersPerm D) := by
  have h := Fintype.card_le_of_injective Q.deepSwitch (deepSwitch_injective Q)
  simpa [Fintype.card_prod, Nat.mul_comm] using h

noncomputable def boundaryMap {m : ℕ} {D : FerrersData m}
    (Q : QueryRanks D) (e : BoundaryEdge Q) : FerrersPerm D × Fin m :=
  (e.1.source, e.1.row)

/-- Distinct integer ranks cannot share one half-open unit-width interval. -/
theorem boundaryMap_injective {m : ℕ} {D : FerrersData m}
    (Q : QueryRanks D) : Function.Injective Q.boundaryMap := by
  intro e f hef
  have hs : e.1.source = f.1.source := congrArg Prod.fst hef
  have hr : e.1.row = f.1.row := congrArg Prod.snd hef
  have he := e.2
  have hf := f.2
  rw [hs, hr] at he
  have h1 : (Q.rank e.1.lowerValue : ℝ) < (Q.rank f.1.lowerValue : ℝ) + 1 := by
    linarith
  have h2 : (Q.rank f.1.lowerValue : ℝ) < (Q.rank e.1.lowerValue : ℝ) + 1 := by
    linarith
  have h1n : Q.rank e.1.lowerValue < Q.rank f.1.lowerValue + 1 := by
    exact_mod_cast h1
  have h2n : Q.rank f.1.lowerValue < Q.rank e.1.lowerValue + 1 := by
    exact_mod_cast h2
  have ha : e.1.lowerValue = f.1.lowerValue :=
    Q.rank_strict.injective (by omega)
  apply Subtype.ext
  cases e with
  | mk ee he =>
    cases f with
    | mk ff hf =>
      cases ee
      cases ff
      simp_all

theorem card_boundaryEdge_le {m : ℕ} {D : FerrersData m} (Q : QueryRanks D) :
    Fintype.card (BoundaryEdge Q) ≤ m * Fintype.card (FerrersPerm D) := by
  have h := Fintype.card_le_of_injective Q.boundaryMap (boundaryMap_injective Q)
  simpa [Fintype.card_prod, Nat.mul_comm] using h

noncomputable def splitCertified {m : ℕ} {D : FerrersData m}
    (Q : QueryRanks D) (e : CertifiedCell Q) : DeepEdge Q ⊕ BoundaryEdge Q := by
  classical
  by_cases h : (Q.rank e.1.lowerValue : ℝ) + 1 < Q.tau e.1.source * Q.q e.1.row
  · exact Sum.inl ⟨e.1, h⟩
  · exact Sum.inr ⟨e.1, e.2.2, le_of_not_gt h⟩

noncomputable def unsplitCertified {m : ℕ} {D : FerrersData m}
    (Q : QueryRanks D) : DeepEdge Q ⊕ BoundaryEdge Q → DownEdge D
  | Sum.inl e => e.1
  | Sum.inr e => e.1

lemma unsplit_splitCertified {m : ℕ} {D : FerrersData m}
    (Q : QueryRanks D) (e : CertifiedCell Q) :
    Q.unsplitCertified (Q.splitCertified e) = e.1 := by
  classical
  unfold splitCertified
  split_ifs <;> rfl

lemma splitCertified_injective {m : ℕ} {D : FerrersData m}
    (Q : QueryRanks D) : Function.Injective Q.splitCertified := by
  intro e f h
  apply Subtype.ext
  have hd := congrArg Q.unsplitCertified h
  simpa only [unsplit_splitCertified] using hd

/-- The quantitative linear certified-cell bound, without the record proxy. -/
theorem card_certifiedCell_linear {m : ℕ} {D : FerrersData m} (Q : QueryRanks D) :
    Fintype.card (CertifiedCell Q) ≤ 2 * m * Fintype.card (FerrersPerm D) := by
  have h := Fintype.card_le_of_injective Q.splitCertified (splitCertified_injective Q)
  rw [Fintype.card_sum] at h
  have hd := card_deepEdge_le Q
  have hb := card_boundaryEdge_le Q
  simp only [Nat.mul_assoc]
  omega

/-- Six-linear cut-edge bound for an exact water query. -/
theorem card_waterCutEdge_linear {m : ℕ} {D : FerrersData m} (W : WaterQuery D) :
    Fintype.card (WaterCutEdge W) ≤ 6 * m * Fintype.card (FerrersPerm D) := by
  have h := Fintype.card_le_of_injective (chargeCutEdge W) (chargeCutEdge_injective W)
  simp only [EdgeCharge, Fintype.card_sum] at h
  have ha := card_activeEdge_le W.toQueryRanks
  have hc := card_certifiedCell_linear W.toQueryRanks
  simp only [Nat.mul_assoc] at hc ⊢
  omega

end QueryRanks

/-- Linear expected deficit drift on every certified water-query posterior. -/
theorem oneQuery_expected_deficit_drop_linear {m : ℕ} {D : FerrersData m}
    (W : QueryRanks.WaterQuery D) :
    uniformAverage (fun sigma =>
      (DownEdge.natDeficit D : ℝ) - DownEdge.internalOutdegree W.answer sigma) ≤
      6 * (m : ℝ) := by
  rw [DownEdge.edge_boundary_identity]
  have hcard := card_waterCutEdge_eq_sum W
  have hcardR : (Fintype.card (QueryRanks.WaterCutEdge W) : ℝ) =
      ∑ sigma, (DownEdge.cutOutdegree W.answer sigma : ℝ) := by exact_mod_cast hcard
  rw [← hcardR]
  have hbound : (Fintype.card (QueryRanks.WaterCutEdge W) : ℝ) ≤
      6 * (m : ℝ) * Fintype.card (FerrersPerm D) := by
    exact_mod_cast QueryRanks.card_waterCutEdge_linear W
  by_cases hN : Fintype.card (FerrersPerm D) = 0
  · simp [hN]
  · have hpos : (0 : ℝ) < Fintype.card (FerrersPerm D) := by
      exact_mod_cast Nat.pos_of_ne_zero hN
    exact (div_le_iff₀ hpos).2 hbound

end Lemmata.DistributionalLowerBounds.Core.Distributional
