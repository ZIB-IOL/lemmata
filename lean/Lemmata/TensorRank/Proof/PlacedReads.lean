module

/-
Copyright (c) 2026 Kirill Khoruzhii. Licensed under Apache-2.0.
Modified for the arbitrary-field tensor-rank formalization; namespace and imports
adapted for Lemmata. See docs/tensor-rank/NOTICE.txt for upstream attribution
and modification notices, and docs/tensor-rank/LICENSE.txt for the license.
-/

public import Lemmata.TensorRank.Proof.ReaderTransport

@[expose] public section

set_option autoImplicit false

namespace Lemmata.TensorRank.Tensor

variable {R : Type*} {I J : Type} {C : Type*} [Zero R] {V : I → Type*}

def placedLabel (e : J ≃ I) (reader : I) (label : V reader → C) :
    V (e (e.symm reader)) → C :=
  fun x => label (cast (congrArg V (e.apply_symm_apply reader)) x)

theorem Reads.relabel_at (e : J ≃ I) {reader : I} {Z : C → Tensor R I V}
    {label : V reader → C} (h : Reads Z reader label) :
    Reads (fun q => Lemmata.TensorRank.Tensor.relabel e (Z q)) (e.symm reader) (placedLabel e reader label) := by
  intro q x hx
  have hh := h q (Equiv.piCongrLeft V e x) hx
  change label (cast (congrArg V (e.apply_symm_apply reader)) (x (e.symm reader))) = q
  rw [Equiv.piCongrLeft_apply_eq_cast] at hh
  exact hh

theorem Reads.reindexLabels {D : Type*} (f : D ≃ C) {reader : I}
    {Z : C → Tensor R I V} {label : V reader → C} (h : Reads Z reader label) :
    Reads (fun q => Z (f q)) reader (fun x => f.symm (label x)) := by
  intro q x hx
  change f.symm (label (x reader)) = q
  rw [h (f q) x hx, f.symm_apply_apply]

end Lemmata.TensorRank.Tensor
