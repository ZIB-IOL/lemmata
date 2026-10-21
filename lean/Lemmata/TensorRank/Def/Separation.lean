module

public import Lemmata.TensorRank.Def.Polynomial
public import Lemmata.TensorRank.Def.DirectSum
public import Mathlib.Analysis.Complex.Basic

@[expose] public section

set_option autoImplicit false

open scoped BigOperators
open Classical

noncomputable section

namespace Lemmata.TensorRank.Separation

universe u

abbrev Party (r : ℕ) := Bool ⊕ Fin r

abbrev SharedCoordinate {r : ℕ} (V : Party r → Type u) (M : ℕ) : Party r → Type u
  | .inl b => Fin M × V (.inl b)
  | .inr i => V (.inr i)

abbrev SeparatedTag {r : ℕ} (M : ℕ) : Party r → Type
  | .inl _ => Fin M × Fin M
  | .inr _ => Fin M

abbrev SeparatedCoordinate {r : ℕ} (V : Party r → Type u) (M : ℕ) (p : Party r) :=
  SeparatedTag M p × V p

instance {r M : ℕ} {V : Party r → Type u} [∀ p, Fintype (V p)] (p : Party r) :
    Fintype (SharedCoordinate V M p) := by cases p <;> infer_instance

instance {r M : ℕ} {V : Party r → Type u} [∀ p, Fintype (V p)] (p : Party r) :
    Fintype (SeparatedCoordinate V M p) := by cases p <;> infer_instance

def period (r M : ℕ) : ℕ := (r + 1) * M

def shift (r M : ℕ) : ℕ := (r + 2) * (M - 1) ^ 2

def frequency {r M : ℕ} (g : Fin r → Fin M) (h u v : Fin M) : ℤ :=
  (∑ i, (g i : ℤ)) - (r : ℤ) * h + u - v

def totalDegree {r M : ℕ} (g : Fin r → Fin M) (h u v : Fin M) : ℕ :=
  (∑ i, (g i).val ^ 2) + r * ((M - 1) ^ 2 - h.val ^ 2) +
    2 * h.val * u.val + 2 * ((M - 1) ^ 2 - h.val * v.val)

variable {r M : ℕ} {V : Party r → Type u}

def sharedBase (x : ∀ p, SharedCoordinate V M p) : ∀ p, V p
  | .inl b => (x (.inl b)).2
  | .inr i => x (.inr i)

def label (p : Party r) (x : SeparatedCoordinate V M p) : Fin M :=
  match p with
  | .inl _ => x.1.1
  | .inr _ => x.1

def input (p : Party r) (x : SeparatedCoordinate V M p) : SharedCoordinate V M p :=
  match p with
  | .inl _ => (x.1.1, x.2)
  | .inr _ => x.2

def sharedSum (Z : Fin M → Tensor ℂ (Party r) V) :
    Tensor ℂ (Party r) (SharedCoordinate V M) :=
  fun x => if (x (.inl false)).1 = (x (.inl true)).1 then
    Z (x (.inl false)).1 (sharedBase x) else 0

def separatedSum (Z : Fin M → Tensor ℂ (Party r) V) :
    Tensor ℂ (Party r) (SeparatedCoordinate V M) :=
  fun x => if (∀ p, label p (x p) = (x (.inl false)).1.1) ∧
      (x (.inl false)).1.2 = (x (.inl true)).1.2 then
    Z (x (.inl false)).1.1 (fun p => (x p).2) else 0

def amplitude (ζ : ℂ) (p : Party r) (t : Fin (period r M))
    (x : SeparatedCoordinate V M p) : ℂ :=
  match p with
  | .inl false => ζ ^ ((t : ℤ) * ((x.1.2 : ℤ) - (r : ℤ) * x.1.1))
  | .inl true => (period r M : ℂ)⁻¹ * ζ ^ (-((t : ℤ) * x.1.2))
  | .inr _ => ζ ^ ((t : ℤ) * x.1)

def weight (p : Party r) (x : SeparatedCoordinate V M p) : ℕ :=
  match p with
  | .inl false => r * ((M - 1) ^ 2 - x.1.1.val ^ 2) + 2 * x.1.1.val * x.1.2.val
  | .inl true => 2 * ((M - 1) ^ 2 - x.1.1.val * x.1.2.val)
  | .inr _ => x.1.val ^ 2

def kernel (ζ : ℂ) (p : Party r) (x : SeparatedCoordinate V M p)
    (a : Fin (period r M) × SharedCoordinate V M p) : Polynomial ℂ :=
  Polynomial.C (amplitude ζ p a.1 x) * Polynomial.X ^ weight p x *
    if a.2 = input p x then 1 else 0

def family [∀ p, Fintype (V p)] (ζ : ℂ) (Z : Fin M → Tensor ℂ (Party r) V) :
    Tensor (Polynomial ℂ) (Party r) (SeparatedCoordinate V M) :=
  Tensor.polynomialMap (kernel ζ) (Tensor.copies (period r M) (sharedSum Z))

end Lemmata.TensorRank.Separation
