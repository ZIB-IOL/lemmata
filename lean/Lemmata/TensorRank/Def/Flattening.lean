module

public import Lemmata.TensorRank.Def.Rank
public import Mathlib.LinearAlgebra.Matrix.Rank

@[expose] public section

set_option autoImplicit false

namespace Lemmata.TensorRank.Tensor

universe u v w

variable {F : Type u} {I : Type v} {V : I → Type w}

abbrev CutRow (V : I → Type w) (S : Finset I) := ∀ i : {i // i ∈ S}, V i.val

abbrev CutColumn (V : I → Type w) (S : Finset I) := ∀ i : {i // i ∉ S}, V i.val

noncomputable def joinCut (S : Finset I) (a : CutRow V S) (b : CutColumn V S) : ∀ i, V i := by
  classical
  exact fun i => if h : i ∈ S then a ⟨i, h⟩ else b ⟨i, h⟩

noncomputable def flatten (T : Tensor F I V) (S : Finset I) :
    Matrix (CutRow V S) (CutColumn V S) F :=
  fun a b => T (joinCut S a b)

noncomputable def flatRank [Field F] [Fintype I] [∀ i, Fintype (V i)]
    (T : Tensor F I V) (S : Finset I) : ℕ := by
  classical
  exact (flatten T S).rank

end Lemmata.TensorRank.Tensor
