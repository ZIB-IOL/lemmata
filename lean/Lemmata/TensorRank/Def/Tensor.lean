module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.Pi

@[expose] public section

set_option autoImplicit false

open scoped BigOperators

namespace Lemmata.TensorRank

universe u v w z

abbrev Tensor (R : Type u) (I : Type v) (V : I → Type w) := (∀ i, V i) → R

namespace Tensor

variable {R : Type u} {I : Type v} {V : I → Type w} {W : I → Type z}

def pure [CommMonoid R] [Fintype I] (v : ∀ i, V i → R) : Tensor R I V :=
  fun x => ∏ i, v i (x i)

def product [Mul R] (T : Tensor R I V) (S : Tensor R I W) :
    Tensor R I (fun i => V i × W i) :=
  fun x => T (fun i => (x i).1) * S (fun i => (x i).2)

def power [CommMonoid R] (T : Tensor R I V) (n : ℕ) :
    Tensor R I (fun i => Fin n → V i) :=
  fun x => ∏ j, T (fun i => x i j)

def reindex (e : ∀ i, W i → V i) (T : Tensor R I V) : Tensor R I W :=
  fun x => T (fun i => e i (x i))

@[simp] theorem pure_apply [CommMonoid R] [Fintype I]
    (v : ∀ i, V i → R) (x : ∀ i, V i) : pure v x = ∏ i, v i (x i) := rfl

@[simp] theorem power_apply [CommMonoid R] (T : Tensor R I V) (n : ℕ)
    (x : ∀ i, Fin n → V i) : power T n x = ∏ j, T (fun i => x i j) := rfl

end Tensor
end Lemmata.TensorRank
