module

/-
Copyright (c) 2026 Kirill Khoruzhii. Licensed under Apache-2.0.
Modified for the arbitrary-field tensor-rank formalization; namespace and imports
adapted for Lemmata. See docs/tensor-rank/NOTICE.txt for upstream attribution
and modification notices, and docs/tensor-rank/LICENSE.txt for the license.
-/

public import Lemmata.TensorRank.Def.Polynomial
public import Lemmata.TensorRank.Def.DirectSum
public import Mathlib.Algebra.Field.Basic

@[expose] public section

set_option autoImplicit false

open scoped BigOperators
open Classical

noncomputable section

namespace Lemmata.TensorRank.Separation

variable {𝕜 : Type*} [Field 𝕜]

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

def sourceCopies (r M : ℕ) : ℕ := r * (M - 1) + M

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

def sharedSum (Z : Fin M → Tensor 𝕜 (Party r) V) :
    Tensor 𝕜 (Party r) (SharedCoordinate V M) :=
  fun x => if (x (.inl false)).1 = (x (.inl true)).1 then
    Z (x (.inl false)).1 (sharedBase x) else 0

def separatedSum (Z : Fin M → Tensor 𝕜 (Party r) V) :
    Tensor 𝕜 (Party r) (SeparatedCoordinate V M) :=
  fun x => if (∀ p, label p (x p) = (x (.inl false)).1.1) ∧
      (x (.inl false)).1.2 = (x (.inl true)).1.2 then
    Z (x (.inl false)).1.1 (fun p => (x p).2) else 0

def weight (p : Party r) (x : SeparatedCoordinate V M p) : ℕ :=
  match p with
  | .inl false => r * ((M - 1) ^ 2 - x.1.1.val ^ 2) + 2 * x.1.1.val * x.1.2.val
  | .inl true => 2 * ((M - 1) ^ 2 - x.1.1.val * x.1.2.val)
  | .inr _ => x.1.val ^ 2

end Lemmata.TensorRank.Separation
