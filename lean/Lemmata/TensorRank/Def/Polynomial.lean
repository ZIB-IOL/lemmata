module

public import Lemmata.TensorRank.Def.Tensor
public import Lemmata.TensorRank.Def.Maps
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Degree.Defs

@[expose] public section

set_option autoImplicit false

namespace Lemmata.TensorRank.Tensor

universe u v w

variable {R : Type u} {I : Type v} {V : I → Type w}

section Semiring

variable [Semiring R]

def coefficient (P : Tensor (Polynomial R) I V) (e : ℕ) : Tensor R I V :=
  fun x => (P x).coeff e

def evaluate (P : Tensor (Polynomial R) I V) (t : R) : Tensor R I V :=
  fun x => Polynomial.eval t (P x)

def DegreeLE (P : Tensor (Polynomial R) I V) (D : ℕ) : Prop :=
  ∀ x, (P x).natDegree ≤ D

/-- The first possibly nonzero coefficient is the target tensor. -/
def Leading (P : Tensor (Polynomial R) I V) (e : ℕ) (T : Tensor R I V) : Prop :=
  coefficient P e = T ∧ ∀ j < e, coefficient P j = 0

end Semiring

variable [CommSemiring R] [Fintype I] [∀ i, Fintype (V i)] {W : I → Type*}

noncomputable def polynomialMap (A : ∀ i, W i → V i → Polynomial R)
    (T : Tensor R I V) : Tensor (Polynomial R) I W :=
  localMap A (fun x => Polynomial.C (T x))

/-- Independent polynomial local maps have the target as their first coefficient. -/
def Degenerates (S : Tensor R I W) (T : Tensor R I V) : Prop :=
  ∃ (A : ∀ i, W i → V i → Polynomial R) (e : ℕ), Leading (polynomialMap A T) e S

end Lemmata.TensorRank.Tensor
