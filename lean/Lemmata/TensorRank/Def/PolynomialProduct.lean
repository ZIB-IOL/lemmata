module

/-
Copyright (c) 2026 Kirill Khoruzhii. Licensed under Apache-2.0.
Modified for the arbitrary-field tensor-rank formalization; namespace and imports
adapted for Lemmata. See docs/tensor-rank/NOTICE.txt for upstream attribution
and modification notices, and docs/tensor-rank/LICENSE.txt for the license.
-/

public import Lemmata.TensorRank.Def.Tensor
public import Mathlib.Algebra.Field.Basic

@[expose] public section

set_option autoImplicit false

open scoped BigOperators
open Classical

namespace Lemmata.TensorRank.PolynomialProduct

variable {𝕜 : Type*} [Field 𝕜]

variable {J : Type*} [Fintype J]

def degree (a : J → ℕ) : ℕ := ∑ j, (a j - 1)

abbrev Coordinate (a : J → ℕ) : Option J → Type _
  | none => Fin (degree a + 1)
  | some j => Fin (a j)

instance coordinateFintype (a : J → ℕ) (p : Option J) : Fintype (Coordinate a p) := by
  cases p <;> unfold Coordinate <;> infer_instance

def tensor (a : J → ℕ) : Tensor 𝕜 (Option J) (Coordinate a) :=
  fun x => if (∑ j, (x (some j)).val) = (x none).val then 1 else 0

abbrev SelectedCoordinate (a : J → ℕ) (b : ℕ) : Bool ⊕ J → Type _
  | .inl false => Fin b
  | .inl true => Fin (b + degree a)
  | .inr j => Fin (a j)

instance selectedCoordinateFintype (a : J → ℕ) (b : ℕ) (p : Bool ⊕ J) :
    Fintype (SelectedCoordinate a b p) := by
  rcases p with ⟨⟨⟩⟩ | j <;> unfold SelectedCoordinate <;> infer_instance

def selected (a : J → ℕ) (b : ℕ) : Tensor 𝕜 (Bool ⊕ J) (SelectedCoordinate a b) :=
  fun x => if (x (.inl false)).val + (∑ j, (x (.inr j)).val) = (x (.inl true)).val
    then 1 else 0

end Lemmata.TensorRank.PolynomialProduct
