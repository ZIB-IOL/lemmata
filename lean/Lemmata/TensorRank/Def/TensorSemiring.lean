module

public import Lemmata.TensorRank.Def.Maps
public import Lemmata.TensorRank.Def.DirectSum
public import Lemmata.TensorRank.Def.Spectrum
public import Mathlib.Basic.Complex.Basic

@[expose] public section

set_option autoImplicit false

open Classical

noncomputable section

namespace Lemmata.TensorRank

structure Format (I : Type) where
  Coordinate : I → Type
  finite : ∀ i, Fintype (Coordinate i)

attribute [instance] Format.finite

namespace Format

abbrev Tensor {I : Type} (F : Format I) := Lemmata.TensorRank.Tensor ℂ I F.Coordinate

def product {I : Type} (F G : Format I) : Format I :=
  ⟨fun i => F.Coordinate i × G.Coordinate i, fun _ => inferInstance⟩

end Format

end Lemmata.TensorRank

namespace Lemmata.TensorRank.Tensor

variable {R I : Type*} [CommSemiring R] [Fintype I]
variable {V W : I → Type*} [∀ i, Fintype (V i)] [∀ i, Fintype (W i)]

def embed (e : ∀ i, V i ↪ W i) (T : Tensor R I V) : Tensor R I W :=
  localMap (fun i y x => if e i x = y then 1 else 0) T

def directSum (S : Tensor R I V) (T : Tensor R I W) :
    Tensor R I (fun i => V i ⊕ W i) :=
  embed (fun _ => Function.Embedding.inl) S + embed (fun _ => Function.Embedding.inr) T

end Lemmata.TensorRank.Tensor

namespace Lemmata.TensorRank.TensorSemiring

structure Object (k : ℕ) where
  format : Format (Fin k)
  tensor : format.Tensor

namespace Object

variable {k : ℕ}

def Rel (A B : Object k) : Prop := Tensor.Restricts A.tensor B.tensor

def Equivalent (A B : Object k) : Prop := Rel A B ∧ Rel B A

def zero (k : ℕ) : Object k := ⟨⟨fun _ => Empty, fun _ => inferInstance⟩, 0⟩

def one (k : ℕ) : Object k := ⟨⟨fun _ => PUnit, fun _ => inferInstance⟩, fun _ => 1⟩

def nat (k m : ℕ) : Object k :=
  ⟨⟨fun _ => Fin m, fun _ => inferInstance⟩, Tensor.diagonal m⟩

def add (A B : Object k) : Object k :=
  ⟨⟨fun i => A.format.Coordinate i ⊕ B.format.Coordinate i, fun _ => inferInstance⟩,
    Tensor.directSum A.tensor B.tensor⟩

def mul (A B : Object k) : Object k :=
  ⟨A.format.product B.format, Tensor.product A.tensor B.tensor⟩

def relabel (σ : Equiv.Perm (Fin k)) (A : Object k) : Object k :=
  ⟨⟨fun i => A.format.Coordinate (σ i), fun _ => inferInstance⟩,
    fun x => A.tensor (Equiv.piCongrLeft A.format.Coordinate σ x)⟩

def power (A : Object k) (n : ℕ) : Object k :=
  ⟨⟨fun i => Fin n → A.format.Coordinate i, fun _ => inferInstance⟩, Tensor.power A.tensor n⟩

end Object

abbrev Value (k : ℕ) := Quot (Object.Equivalent (k := k))

abbrev ofObject {k : ℕ} (A : Object k) : Value k := Quot.mk _ A

abbrev ofTensor {k : ℕ} {V : Fin k → Type} [∀ i, Fintype (V i)]
    (T : Tensor ℂ (Fin k) V) : Value k :=
  ofObject ⟨⟨V, fun _ => inferInstance⟩, T⟩

end Lemmata.TensorRank.TensorSemiring
