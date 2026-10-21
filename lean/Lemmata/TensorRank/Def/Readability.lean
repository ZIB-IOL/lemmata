module

public import Lemmata.TensorRank.Def.Tensor

@[expose] public section

set_option autoImplicit false

namespace Lemmata.TensorRank.Tensor

variable {R I L : Type*} {V : I → Type*}

def Reads [Zero R] (Z : L → Tensor R I V) (reader : I) (label : V reader → L) : Prop :=
  ∀ q x, Z q x ≠ 0 → label (x reader) = q

end Lemmata.TensorRank.Tensor
