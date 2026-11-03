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

namespace Lemmata.TensorRank.Tensor

variable {R I L : Type*} {V : I → Type*}

def Reads [Zero R] (Z : L → Tensor R I V) (reader : I) (label : V reader → L) : Prop :=
  ∀ q x, Z q x ≠ 0 → label (x reader) = q

end Lemmata.TensorRank.Tensor
