module

/-
Copyright (c) 2026 Kirill Khoruzhii. Licensed under Apache-2.0.
Modified for the arbitrary-field tensor-rank formalization; namespace and imports
adapted for Lemmata. See docs/tensor-rank/NOTICE.txt for upstream attribution
and modification notices, and docs/tensor-rank/LICENSE.txt for the license.
-/

public import Lemmata.TensorRank.Proof.PolynomialProduct

@[expose] public section

set_option autoImplicit false

open scoped BigOperators
open Classical

noncomputable section

namespace Lemmata.TensorRank.PolynomialProduct

variable {𝕜 : Type*} [Field 𝕜]


variable {J : Type*} [Fintype J]

def assemble {V : Bool ⊕ J → Type*} (u : V (.inl false)) (v : V (.inl true))
    (x : ∀ j, V (.inr j)) : ∀ p, V p
  | .inl false => u
  | .inl true => v
  | .inr j => x j

def assignmentEquiv (V : Bool ⊕ J → Type*) :
    (∀ p, V p) ≃ V (.inl false) × V (.inl true) × (∀ j, V (.inr j)) where
  toFun x := (x (.inl false), x (.inl true), fun j => x (.inr j))
  invFun x := assemble x.1 x.2.1 x.2.2
  left_inv x := by funext p; rcases p with ⟨⟨⟩⟩ | j <;> rfl
  right_inv _ := rfl

omit [Fintype J] in
theorem assignmentEquiv_apply (V : Bool ⊕ J → Type*) (x : ∀ p, V p) :
    assignmentEquiv V x = (x (.inl false), x (.inl true), fun j => x (.inr j)) := rfl

def twoReaderKernel {R : Type*} [Zero R] [One R] {V W : Bool ⊕ J → Type*}
    (A : W (.inl false) → V (.inl false) → R)
    (B : W (.inl true) → V (.inl true) → R) (e : ∀ j, W (.inr j) → V (.inr j)) :
    ∀ p, W p → V p → R
  | .inl false => A
  | .inl true => B
  | .inr j => fun y v => if v = e j y then 1 else 0

theorem localMap_twoReaders {R : Type*} [CommSemiring R] {V W : Bool ⊕ J → Type*}
    [∀ p, Fintype (V p)] (A : W (.inl false) → V (.inl false) → R)
    (B : W (.inl true) → V (.inl true) → R) (e : ∀ j, W (.inr j) → V (.inr j))
    (T : Tensor R (Bool ⊕ J) V) (x : ∀ p, W p) :
    Tensor.localMap (twoReaderKernel A B e) T x =
      ∑ u, ∑ v, A (x (.inl false)) u * B (x (.inl true)) v *
        T (assemble u v (fun j => e j (x (.inr j)))) := by
  let : DecidableEq (Bool ⊕ J) := Classical.decEq _
  have h := Fintype.sum_equiv (assignmentEquiv V)
    (fun z => (∏ p, twoReaderKernel A B e p (x p) (z p)) * T z)
    (fun z => A (x (.inl false)) z.1 * B (x (.inl true)) z.2.1 *
      ((∏ j, if z.2.2 j = e j (x (.inr j)) then 1 else 0) *
        T (assemble z.1 z.2.1 z.2.2)))
    (fun z => by
      have hz : assemble (z (.inl false)) (z (.inl true)) (fun j => z (.inr j)) = z := by
        funext p
        rcases p with ⟨⟨⟩⟩ | j <;> rfl
      simp only [Fintype.prod_sum_type, Fintype.prod_bool, twoReaderKernel, assignmentEquiv_apply]
      rw [hz]
      simp only [mul_assoc, mul_comm, mul_left_comm]
      congr 3)
  refine h.trans ?_
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro u _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro v _
  dsimp only
  rw [← Finset.mul_sum]
  congr 1
  simp only [Fintype.prod_boole, ← funext_iff]
  simp

end Lemmata.TensorRank.PolynomialProduct
