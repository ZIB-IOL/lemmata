module

public import Lemmata.TensorRank.Def.Tensor

@[expose] public section

set_option autoImplicit false

open scoped BigOperators
open Classical

namespace Lemmata.TensorRank.Tensor

universe u v w z

variable {R : Type u} {I : Type v} {V : I → Type w} {W : I → Type z}

noncomputable def localMap [CommSemiring R] [Fintype I] [∀ i, Fintype (V i)]
    (A : ∀ i, W i → V i → R) (T : Tensor R I V) : Tensor R I W :=
  fun y => ∑ x : ∀ i, V i, (∏ i, A i (y i) (x i)) * T x

def powerKernel [CommMonoid R] (A : ∀ i, W i → V i → R) (n : ℕ) :
    ∀ i, (Fin n → W i) → (Fin n → V i) → R :=
  fun i y x => ∏ j, A i (y j) (x j)

def productKernel [Mul R] {U Z : I → Type*}
    (A : ∀ i, W i → V i → R) (B : ∀ i, Z i → U i → R) :
    ∀ i, (W i × Z i) → (V i × U i) → R :=
  fun i y x => A i y.1 x.1 * B i y.2 x.2

/-- Independent linear maps at the original parties send `T` to `S`. -/
def Restricts [CommSemiring R] [Fintype I] [∀ i, Fintype (V i)]
    (S : Tensor R I W) (T : Tensor R I V) : Prop :=
  ∃ A : ∀ i, W i → V i → R, S = localMap A T

end Lemmata.TensorRank.Tensor
