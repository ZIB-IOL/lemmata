module

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
