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

universe u v w

variable {R : Type u} {I : Type v} {V : I → Type w}

noncomputable def diagonal [Zero R] [One R] (l : ℕ) : Tensor R I (fun _ => Fin l) := by
  classical
  exact fun x => if ∃ a : Fin l, ∀ i, x i = a then 1 else 0

noncomputable def copies [MulZeroOneClass R] (l : ℕ) (T : Tensor R I V) :
    Tensor R I (fun i => Fin l × V i) :=
  product (diagonal l) T

end Lemmata.TensorRank.Tensor
