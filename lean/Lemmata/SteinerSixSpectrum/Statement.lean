module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Int.Basic

@[expose] public section

namespace Lemmata.SteinerSixSpectrum

/-- A family of six-element blocks covering the specified pairs exactly once. -/
structure PairDesign (X : Type*) (eligible : X → X → Prop) where
  blocks : Set (Finset X)
  six : ∀ B ∈ blocks, B.card = 6
  eligible_of_mem : ∀ B ∈ blocks, ∀ x ∈ B, ∀ y ∈ B, x ≠ y → eligible x y
  cover : ∀ x y, x ≠ y → eligible x y →
    ∃! B, B ∈ blocks ∧ x ∈ B ∧ y ∈ B

/-- A Steiner system in which each pair of distinct points lies in exactly one hexad. -/
abbrev SteinerSystem (X : Type*) := PairDesign X (fun _ _ => True)

end Lemmata.SteinerSixSpectrum
