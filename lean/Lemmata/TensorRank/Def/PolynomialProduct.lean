module

public import Lemmata.TensorRank.Def.Tensor
public import Mathlib.Basic.Complex.Basic

@[expose] public section

set_option autoImplicit false

open scoped BigOperators
open Classical

namespace Lemmata.TensorRank.PolynomialProduct

variable {J : Type*} [Fintype J]

def degree (a : J → ℕ) : ℕ := ∑ j, (a j - 1)

abbrev Coordinate (a : J → ℕ) : Option J → Type _
  | none => Fin (degree a + 1)
  | some j => Fin (a j)

instance coordinateFintype (a : J → ℕ) (p : Option J) : Fintype (Coordinate a p) := by
  cases p <;> unfold Coordinate <;> infer_instance

def tensor (a : J → ℕ) : Tensor ℂ (Option J) (Coordinate a) :=
  fun x => if (∑ j, (x (some j)).val) = (x none).val then 1 else 0

abbrev SelectedCoordinate (a : J → ℕ) (b : ℕ) : Bool ⊕ J → Type _
  | .inl false => Fin b
  | .inl true => Fin (b + degree a)
  | .inr j => Fin (a j)

instance selectedCoordinateFintype (a : J → ℕ) (b : ℕ) (p : Bool ⊕ J) :
    Fintype (SelectedCoordinate a b p) := by
  rcases p with ⟨⟨⟩⟩ | j <;> unfold SelectedCoordinate <;> infer_instance

def selected (a : J → ℕ) (b : ℕ) : Tensor ℂ (Bool ⊕ J) (SelectedCoordinate a b) :=
  fun x => if (x (.inl false)).val + (∑ j, (x (.inr j)).val) = (x (.inl true)).val
    then 1 else 0

def inputLabel (a : J → ℕ) (b : ℕ) (y : Fin (3 * b + degree a)) : Fin 3 :=
  if y.val < b then 0 else if y.val < 2 * b + degree a then 1 else 2

def outputLabel (a : J → ℕ) (b : ℕ) (z : Fin ((3 * b + degree a) + degree a)) : Fin 3 :=
  if z.val < b + degree a then 0 else if z.val < 2 * b + degree a then 1 else 2

def tripleSector (a : J → ℕ) (b : ℕ) (q : Fin 3) :
    Tensor ℂ (Bool ⊕ J) (SelectedCoordinate a (3 * b + degree a)) :=
  fun x => if inputLabel a b (x (.inl false)) = q ∧ outputLabel a b (x (.inl true)) = q
    then selected a (3 * b + degree a) x else 0

abbrev BitCoordinate : Bool ⊕ J → Type
  | .inl _ => Fin 2
  | .inr _ => PUnit

instance bitCoordinateFintype (p : Bool ⊕ J) : Fintype (BitCoordinate p) := by
  rcases p with q | j <;> unfold BitCoordinate <;> infer_instance

def pairing : Tensor ℂ (Bool ⊕ J) BitCoordinate :=
  fun x => if x (.inl false) = x (.inl true) then 1 else 0

def amplified (a : J → ℕ) (b : ℕ) := Tensor.product (selected a b) pairing

abbrev ConcaveCoordinate (a : J → ℕ) (b : ℕ) : Bool ⊕ J → Type _
  | .inl false => Fin (b + 1) ⊕ Fin (b - 1)
  | .inl true => Fin (b + degree a + 1) ⊕ Fin ((b - 1) + degree a)
  | .inr j => Fin (a j)

instance concaveCoordinateFintype (a : J → ℕ) (b : ℕ) (p : Bool ⊕ J) :
    Fintype (ConcaveCoordinate a b p) := by
  rcases p with ⟨⟨⟩⟩ | j <;> unfold ConcaveCoordinate <;> infer_instance

def concaveSector (a : J → ℕ) (b : ℕ) (q : Bool) :
    Tensor ℂ (Bool ⊕ J) (ConcaveCoordinate a b) :=
  fun x => match q, x (.inl false), x (.inl true) with
    | false, .inl y, .inl z => if y.val + (∑ j, (x (.inr j)).val) = z.val then 1 else 0
    | true, .inr y, .inr z => if y.val + (∑ j, (x (.inr j)).val) = z.val then 1 else 0
    | _, _, _ => 0

def concave (a : J → ℕ) (b : ℕ) : Tensor ℂ (Bool ⊕ J) (ConcaveCoordinate a b) :=
  ∑ q : Bool, concaveSector a b q

end Lemmata.TensorRank.PolynomialProduct
