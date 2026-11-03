module

/-
Copyright (c) 2026 Kirill Khoruzhii. Licensed under Apache-2.0.
Modified for the arbitrary-field tensor-rank formalization; namespace and imports
adapted for Lemmata. See docs/tensor-rank/NOTICE.txt for upstream attribution
and modification notices, and docs/tensor-rank/LICENSE.txt for the license.
-/

public import Lemmata.TensorRank.Def.WeightedGraph

@[expose] public section

set_option autoImplicit false

namespace Lemmata.TensorRank

def starDimensions {k : ℕ} (c : Fin k) (n : ℕ) (e : Edge k) : ℕ :=
  if c ∈ e.val then n else 1

end Lemmata.TensorRank
