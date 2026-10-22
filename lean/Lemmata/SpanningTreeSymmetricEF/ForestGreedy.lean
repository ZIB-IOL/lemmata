module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Max
public import Mathlib.Tactic

@[expose] public section


/-!
Finite weighted dominance from an extension/cardinality property. This is the
weight-induction part of the forest argument, independent of graph encoding.
-/
namespace Lemmata.SpanningTreeSymmetricEF.ForestPolytope

open scoped BigOperators

/-- Subtract the smallest weight and extend the recursively selected set.
The hypothesis is an unweighted extension property, not weighted dominance. -/
theorem weighted_dominance_of_extension {E : Type*} [DecidableEq E]
    (I : Finset E → Prop) (x : E → ℝ) (h_empty : I ∅)
    (h_extend : ∀ s t : Finset E, I t → t ⊆ s →
      ∃ u : Finset E, I u ∧ t ⊆ u ∧ u ⊆ s ∧ (∑ e ∈ s, x e) ≤ (u.card : ℝ))
    (s : Finset E) (c : E → ℝ) (hc : ∀ e ∈ s, 0 ≤ c e) :
    ∃ t : Finset E, I t ∧ t ⊆ s ∧ (∑ e ∈ s, c e * x e) ≤ ∑ e ∈ t, c e := by
  classical
  induction s using Finset.strongInductionOn generalizing c with
  | _ s ih =>
    by_cases hs : s.Nonempty
    · obtain ⟨a, ha, hmin⟩ := s.exists_min_image c hs
      let d : E → ℝ := fun e => c e - c a
      have hd : ∀ e ∈ s, 0 ≤ d e := fun e he => sub_nonneg.mpr (hmin e he)
      obtain ⟨t, ht, hts, hweight⟩ := ih (s.erase a) (Finset.erase_ssubset ha) d
        (fun e he => hd e (Finset.mem_of_mem_erase he))
      obtain ⟨u, hu, htu, hus, hcard⟩ := h_extend s t ht
        (hts.trans (Finset.erase_subset a s))
      refine ⟨u, hu, hus, ?_⟩
      have hrec : (∑ e ∈ s, d e * x e) ≤ ∑ e ∈ u, d e := by
        calc
          _ = ∑ e ∈ s.erase a, d e * x e := by
            rw [← Finset.sum_erase_add _ _ ha]
            simp [d]
          _ ≤ ∑ e ∈ t, d e := hweight
          _ ≤ ∑ e ∈ u, d e :=
            Finset.sum_le_sum_of_subset_of_nonneg htu (fun e he _ => hd e (hus he))
      have hmul := mul_le_mul_of_nonneg_left hcard (hc a ha)
      have hid : (∑ e ∈ s, c e * x e) =
          (∑ e ∈ s, d e * x e) + c a * ∑ e ∈ s, x e := by
        simp only [d, sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
        ring
      have huid : (∑ e ∈ u, c e) = (∑ e ∈ u, d e) + c a * (u.card : ℝ) := by
        simp [d, Finset.sum_sub_distrib]
        ring
      rw [hid, huid]
      exact add_le_add hrec hmul
    · have hs0 : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      subst s
      exact ⟨∅, h_empty, Finset.Subset.refl _, by simp⟩

end Lemmata.SpanningTreeSymmetricEF.ForestPolytope
