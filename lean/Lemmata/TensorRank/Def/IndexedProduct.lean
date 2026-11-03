module

/-
Copyright (c) 2026 Kirill Khoruzhii. Licensed under Apache-2.0.
Modified for the arbitrary-field tensor-rank formalization; namespace and imports
adapted for Lemmata. See docs/tensor-rank/NOTICE.txt for upstream attribution
and modification notices, and docs/tensor-rank/LICENSE.txt for the license.
-/

public import Lemmata.TensorRank.Def.Tensor

@[expose] public section

set_option autoImplicit false

open scoped BigOperators

namespace Lemmata.TensorRank.Tensor

def indexedProduct {R I J : Type*} [CommMonoid R] [Fintype J]
    {V : J → I → Type*} (T : ∀ j, Tensor R I (V j)) :
    Tensor R I (fun i => ∀ j, V j i) :=
  fun x => ∏ j, T j (fun i => x i j)

end Lemmata.TensorRank.Tensor
