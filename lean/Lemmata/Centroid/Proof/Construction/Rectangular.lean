module

public import Lemmata.Centroid.Proof.Construction.RectangularRank
public import Lemmata.Centroid.Proof.Construction.RectangularSpans
public import Lemmata.Centroid.Proof.Construction.RectangularSplit
public import Lemmata.Centroid.Proof.Construction.RectangularConcise
public import Lemmata.Centroid.Proof.Construction.LowerBound
public import Lemmata.Centroid.Proof.Construction.Relabel

@[expose] public section

namespace Lemmata.Centroid.Construction.Rectangular

noncomputable section

variable {F : Type*} [Field F]

theorem rationalBorderRankAtMost (n t : ℕ) (hn : 0 < n) (ht : t ≤ n) :
    Tensor.RationalBorderRankAtMost (tensor (F := F) n t hn ht) ((n + 1) ^ 2 + t) := by
  have hr := Realization.rational_second_order_realization_core (pairs (F := F) n t hn ht)
    (tau n t) (polynomialPoint n t ht) (basePoint n t ht)
    (polynomialPoint_coeff_zero n t ht) (basePoint_rankAtMost n t ht)
    (frameSpans n t hn ht) (polynomialPoint_coeff_one n t ht) (polynomialPoint_coeff_two n t ht)
  have hc : Fintype.card (PointIndex n t) + n = (n + 1) ^ 2 + t := by
    simp only [PointIndex, Fintype.card_sum, Fintype.card_prod, Fintype.card_option, Fintype.card_fin]
    ring
  rwa [hc] at hr

def coordinateEquiv (n t : ℕ) (i : Fin 3) :
    Coordinates n t i ≃ Fin ((n + 1) ^ 2 + t) :=
  Fintype.equivFinOfCardEq (coordinate_card n t i)

def witness (n t : ℕ) (hn : 0 < n) (ht : t ≤ n) :
    Tensor F (Fin 3) (fun _ => Fin ((n + 1) ^ 2 + t)) :=
  Tensor.relabel (coordinateEquiv n t) (tensor n t hn ht)

theorem witness_concise (n t : ℕ) (hn : 0 < n) (ht : t ≤ n) :
    Tensor.Concise (witness (F := F) n t hn ht) :=
  (concise n t hn ht).relabel (coordinateEquiv n t)

theorem witness_rationalBorderRank (n t : ℕ) (hn : 0 < n) (ht : t ≤ n) :
    Tensor.rationalBorderRank (witness (F := F) n t hn ht) = (n + 1) ^ 2 + t := by
  apply le_antisymm
  · exact (Tensor.rationalBorderRank_le_iff _ _).mpr
      ((rationalBorderRankAtMost n t hn ht).relabel (coordinateEquiv n t))
  · simpa only [Fintype.card_fin] using (witness_concise (F := F) n t hn ht).le_rationalBorderRank 0

theorem witness_centroid_lower_bound (n t : ℕ) (hn : 0 < n) (ht : t ≤ n) :
    n ^ 3 + n * (n + 1 + t) + 1 ≤
      Module.finrank F (Tensor.centroid (witness (F := F) n t hn ht)) :=
  (centroid_lower_bound n t hn ht).trans (Tensor.finrank_centroid_le_relabel (coordinateEquiv n t) _)

theorem exists_minimal (n t : ℕ) (hn : 0 < n) (ht : t ≤ n) (hsmall : t ^ 2 ≤ n) :
    ∃ T : Tensor F (Fin 3) (fun _ => Fin ((n + 1) ^ 2 + t)),
      Tensor.Concise T ∧ Tensor.rationalBorderRank T = (n + 1) ^ 2 + t ∧
        generalBoundAt n (n + 1 + t) ≤ Module.finrank F (Tensor.centroid T) := by
  refine ⟨witness n t hn ht, witness_concise n t hn ht, witness_rationalBorderRank n t hn ht, ?_⟩
  rw [generalBoundAt_second hn t, Nat.sub_eq_zero_of_le hsmall, Nat.add_zero]
  exact witness_centroid_lower_bound n t hn ht

end

end Lemmata.Centroid.Construction.Rectangular
