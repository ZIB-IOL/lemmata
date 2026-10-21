module

public import Lemmata.TensorRank.Def.WeightedGraph

@[expose] public section

set_option autoImplicit false

namespace Lemmata.TensorRank

def starDimensions {k : ℕ} (c : Fin k) (n : ℕ) (e : Edge k) : ℕ :=
  if c ∈ e.val then n else 1

end Lemmata.TensorRank
