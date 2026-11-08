module

public import Lemmata.RM59.Proof.BinaryQuadGeometry

@[expose] public section

namespace Lemmata.RM59.BinaryQuadGeometry

open scoped BigOperators

def EvenCoefficientCases (c : Point 4) : Prop :=
  c = 0 ∨ (∃ i j : Fin 4, i ≠ j ∧ c = Pi.single i 1 + Pi.single j 1) ∨ c = (fun _ => 1)

instance (c : Point 4) : Decidable (EvenCoefficientCases c) := by
  unfold EvenCoefficientCases
  infer_instance

theorem even_coefficient_cases : ∀ c : Point 4, (∑ i, c i) = 0 → EvenCoefficientCases c := by
  decide

theorem sumFour_eq_sum {m : Nat} (p : Fin 4 → Point m) : sumFour p = ∑ i, p i := by
  simp [sumFour, Fin.sum_univ_succ, add_assoc]

theorem affineIndependent_of_injective_sum {m : Nat} (p : Fin 4 → Point m)
    (hp : Function.Injective p) (hs : sumFour p ≠ 0) : AffineIndependent Field p := by
  apply (affineIndependent_iff_of_fintype Field p).2
  intro c hc hv
  have hlin : (∑ i, c i • p i) = 0 := by
    simpa only [Finset.weightedVSub_eq_linear_combination Finset.univ hc] using hv
  rcases even_coefficient_cases c hc with he | ⟨i, j, hij, he⟩ | he
  · subst c
    intro i
    rfl
  · have hlc : Fintype.linearCombination Field p c = 0 := by
      rw [Fintype.linearCombination_apply]
      exact hlin
    rw [he, map_add, Fintype.linearCombination_apply_single,
      Fintype.linearCombination_apply_single, one_smul, one_smul] at hlc
    have hh := congrArg (fun x => x + p j) hlc
    rw [add_assoc, point_add_self, add_zero, zero_add] at hh
    exact (hij (hp hh)).elim
  · apply False.elim
    apply hs
    rw [sumFour_eq_sum]
    simpa only [he, one_smul] using hlin

end Lemmata.RM59.BinaryQuadGeometry
