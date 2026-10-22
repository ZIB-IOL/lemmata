module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.Index
public import Mathlib.Data.Nat.Choose.Basic

@[expose] public section


namespace Lemmata.SpanningTreeSymmetricEF
open Equiv

/-- The subgroup of even permutations fixing every element of `W` pointwise.
This is the Lean version of `A([n] \ W) ≤ S_n`. -/
def alternatingPointwiseStabilizer {α : Type} [Fintype α] [DecidableEq α]
    (W : Finset α) : Subgroup (Equiv.Perm α) where
  carrier := {g | g ∈ alternatingGroup α ∧ ∀ x, x ∈ W → g x = x}
  one_mem' := by
    constructor
    · exact Subgroup.one_mem (alternatingGroup α)
    · intro x _hx
      rfl
  mul_mem' := by
    intro a b ha hb
    constructor
    · exact Subgroup.mul_mem (alternatingGroup α) ha.1 hb.1
    · intro x hx
      rw [Equiv.Perm.mul_apply, hb.2 x hx]
      exact ha.2 x hx
  inv_mem' := by
    intro a ha
    constructor
    · exact Subgroup.inv_mem (alternatingGroup α) ha.1
    · intro x hx
      calc
        a⁻¹ x = a⁻¹ (a x) := by rw [ha.2 x hx]
        _ = x := by simp

/-- External small-index theorem needed by the paper, specialized to the safe
`k = 3`, `n ≥ 13` regime.  Mathematically this is the Dixon--Mortimer/KPT input:
if a subgroup of `S_n` has index strictly smaller than `choose n 3`, it contains
`A([n] \ W)` for some `|W| ≤ 2`.

This structure records the endpoint we assume; it is not proved here. -/
structure SmallIndexK3Criterion where
  exists_alternating_pointwise_stabilizer :
    ∀ {n : Nat}, 13 ≤ n →
    ∀ G : Subgroup (Equiv.Perm (Fin n)),
      G.index < Nat.choose n 3 →
      ∃ W : Finset (Fin n), W.card ≤ 2 ∧ alternatingPointwiseStabilizer W ≤ G


end Lemmata.SpanningTreeSymmetricEF
