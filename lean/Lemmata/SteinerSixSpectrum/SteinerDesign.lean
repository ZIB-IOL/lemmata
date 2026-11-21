module

public import Lemmata.SteinerSixSpectrum.Statement

public section

namespace Lemmata.SteinerSixSpectrum

/-- A Steiner system on `v` points with blocks of size `k`, in which every
`t`-element set of points lies in exactly one block. -/
structure SteinerDesign (t k v : ℕ) where
  blocks : Set (Finset (Fin v))
  block_card : ∀ B ∈ blocks, B.card = k
  cover : ∀ T : Finset (Fin v), T.card = t → ∃! B, B ∈ blocks ∧ T ⊆ B

@[inherit_doc] scoped notation "S(" t ", " k ", " v ")" => SteinerDesign t k v

def SteinerSystem.toSteinerDesign {v : ℕ} (d : SteinerSystem (Fin v)) : S(2, 6, v) where
  blocks := d.blocks
  block_card := d.six
  cover := by
    intro T hT
    obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hT
    simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using
      d.cover x y hxy trivial

end Lemmata.SteinerSixSpectrum
