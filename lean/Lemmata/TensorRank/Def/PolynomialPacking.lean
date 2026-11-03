module

/-
Copyright (c) 2026 Kirill Khoruzhii. Licensed under Apache-2.0.
Modified for the arbitrary-field tensor-rank formalization; namespace and imports
adapted for Lemmata. See docs/tensor-rank/NOTICE.txt for upstream attribution
and modification notices, and docs/tensor-rank/LICENSE.txt for the license.
-/

public import Lemmata.TensorRank.Def.PolynomialProduct
public import Lemmata.TensorRank.Def.Polynomial
public import Lemmata.TensorRank.Def.Readability
public import Lean.Elab.Tactic.Omega

@[expose] public section

set_option autoImplicit false

open scoped BigOperators
open Classical

noncomputable section

namespace Lemmata.TensorRank.PolynomialProduct.Packing

variable {𝕜 : Type*} [Field 𝕜] {J : Type*} [Fintype J]

def count (a : J → ℕ) (b : ℕ) : ℕ := degree a + 2 * b

def length (a : J → ℕ) (b : ℕ) : ℕ := degree a + b

abbrev ReaderInput (a : J → ℕ) (b c : ℕ) :=
  (Fin (c + 1) × Fin b) ⊕ Fin (length a b)

abbrev ReaderOutput (a : J → ℕ) (b c : ℕ) :=
  (Fin (c + 1) × Fin (length a b)) ⊕ Fin b

abbrev Coordinate (a : J → ℕ) (b c : ℕ) : Bool ⊕ J → Type _
  | .inl false => ReaderInput a b c
  | .inl true => ReaderOutput a b c
  | .inr j => Fin (a j)

instance coordinateFintype (a : J → ℕ) (b c : ℕ) (p : Bool ⊕ J) :
    Fintype (Coordinate a b c p) := by
  rcases p with ⟨⟨⟩⟩ | j <;> unfold Coordinate <;> infer_instance

abbrev PairCoordinate (c : ℕ) : Bool ⊕ J → Type
  | .inl _ => Fin c
  | .inr _ => PUnit

instance pairCoordinateFintype (c : ℕ) (p : Bool ⊕ J) : Fintype (PairCoordinate c p) := by
  cases p <;> unfold PairCoordinate <;> infer_instance

def readerPairing (c : ℕ) : Tensor 𝕜 (Bool ⊕ J) (PairCoordinate c) :=
  fun x => if x (.inl false) = x (.inl true) then 1 else 0

def source (a : J → ℕ) (b c : ℕ) :=
  Tensor.product (selected (𝕜 := 𝕜) a (b + 1)) (readerPairing (𝕜 := 𝕜) (J := J) c)

def inputLabel (a : J → ℕ) (b c : ℕ) : ReaderInput a b c → Option (Fin (c + 1))
  | .inl u => some u.1
  | .inr _ => none

def outputLabel (a : J → ℕ) (b c : ℕ) : ReaderOutput a b c → Option (Fin (c + 1))
  | .inl v => some v.1
  | .inr _ => none

def target (a : J → ℕ) (b c : ℕ) : Tensor 𝕜 (Bool ⊕ J) (Coordinate a b c) :=
  fun x => match x (.inl false), x (.inl true) with
  | .inl u, .inl v =>
      if u.1 = v.1 ∧ u.2.val + (∑ j, (x (.inr j)).val) = v.2.val then 1 else 0
  | .inr u, .inr v =>
      if u.val + (∑ j, (x (.inr j)).val) = degree a + v.val then 1 else 0
  | _, _ => 0

def sector (a : J → ℕ) (b c : ℕ) (q : Option (Fin (c + 1))) :
    Tensor 𝕜 (Bool ⊕ J) (Coordinate a b c) :=
  fun x => if inputLabel a b c (x (.inl false)) = q ∧ outputLabel a b c (x (.inl true)) = q
    then target (𝕜 := 𝕜) a b c x else 0

def positiveSource (a : J → ℕ) (b c : ℕ) (l : Fin (c + 1)) (u : Fin b)
    (hl : l.val < c) : Fin (b + 1) × Fin c :=
  (⟨u.val, by have := u.isLt; omega⟩, ⟨l.val, hl⟩)

def negativeSource (a : J → ℕ) (b c : ℕ) (l : Fin (c + 1)) (u : Fin b)
    (hl : 0 < l.val) : Fin (b + 1) × Fin c :=
  (⟨u.val + 1, by have := u.isLt; omega⟩, ⟨l.val - 1, by have := l.isLt; omega⟩)

def middleSource (a : J → ℕ) (b c : ℕ) (u : Fin (length a b)) (hc : count a b ≤ c) :
    Fin (b + 1) × Fin c :=
  (⟨b, by omega⟩, ⟨u.val, by have := u.isLt; dsimp [length, count] at *; omega⟩)

def encode (a : J → ℕ) (b c : ℕ) (hc : count a b ≤ c) :
    ReaderInput a b c → (Fin (b + 1) × Fin c) → Polynomial 𝕜
  | .inl y, u =>
      (if h : y.1.val < c then if u = positiveSource a b c y.1 y.2 h then 1 else 0 else 0) -
      (if h : 0 < y.1.val then if u = negativeSource a b c y.1 y.2 h then 1 else 0 else 0)
  | .inr y, u => Polynomial.X * if u = middleSource a b c y hc then 1 else 0

def fullWeight (a : J → ℕ) (b c : ℕ) (y : Fin (c + 1) × Fin (length a b))
    (v : Fin (b + 1 + degree a) × Fin c) : 𝕜 :=
  if y.1.val + y.2.val < length a b then
    if y.1.val ≤ v.2.val ∧ v.2.val + v.1.val = y.1.val + y.2.val then 1 else 0
  else -(if v.2.val < y.1.val ∧ v.2.val + v.1.val = y.1.val + y.2.val then 1 else 0)

def decode (a : J → ℕ) (b c : ℕ) :
    ReaderOutput a b c → (Fin (b + 1 + degree a) × Fin c) → Polynomial 𝕜
  | .inl y, v => Polynomial.X * Polynomial.C (fullWeight (𝕜 := 𝕜) a b c y v)
  | .inr y, v => if v.2.val + v.1.val = length a b + y.val then 1 else 0

def kernel (a : J → ℕ) (b c : ℕ) (hc : count a b ≤ c) :
    ∀ p, Coordinate a b c p → SelectedCoordinate a (b + 1) p × PairCoordinate c p →
      Polynomial 𝕜
  | .inl false => encode a b c hc
  | .inl true => decode a b c
  | .inr _ => fun y v => if v = (y, PUnit.unit) then 1 else 0

end Lemmata.TensorRank.PolynomialProduct.Packing
