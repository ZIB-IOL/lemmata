module

/-
Copyright (c) 2026 Kirill Khoruzhii. Licensed under Apache-2.0.
Modified for the arbitrary-field tensor-rank formalization; namespace and imports
adapted for Lemmata. See docs/tensor-rank/NOTICE.txt for upstream attribution
and modification notices, and docs/tensor-rank/LICENSE.txt for the license.
-/

public import Lemmata.TensorRank.Proof.ContextTransport

@[expose] public section

set_option autoImplicit false

open scoped BigOperators
open Classical

namespace Lemmata.TensorRank.Tensor

variable {𝕜 : Type*} [Field 𝕜] {I : Type} [Fintype I]

theorem ContextLE.of_reindex_reverse
    {V W : I → Type} [∀ i, Fintype (V i)] [∀ i, Fintype (W i)]
    {S : Tensor 𝕜 I V} {T : Tensor 𝕜 I W}
    (e : ∀ i, W i ≃ V i) (he : Lemmata.TensorRank.Tensor.reindex (fun i => e i) S = T) : ContextLE 1 T S := by
  rw [← he]
  exact (reindex_restricts (fun i => e i) S).contextLE

theorem indexedProduct_reindex_indices {C D : Type} [Fintype C] [Fintype D]
    {V : D → I → Type} (e : C ≃ D) (S : ∀ d, Tensor 𝕜 I (V d)) :
    reindex (fun i => Equiv.piCongrLeft (fun d => V d i) e) (indexedProduct S) =
      indexedProduct (fun c => S (e c)) := by
  funext x
  exact (Fintype.prod_equiv e _ _ (fun c => by
    simp [reindex, indexedProduct])).symm

theorem ContextLE.indexedProduct {C : Type} [Fintype C]
    {V W : C → I → Type} [∀ c i, Fintype (V c i)] [∀ c i, Fintype (W c i)]
    {S : ∀ c, Tensor 𝕜 I (V c)} {T : ∀ c, Tensor 𝕜 I (W c)} {r : C → ℝ}
    (h : ∀ c, ContextLE (r c) (S c) (T c)) (hr : ∀ c, 0 ≤ r c) :
    ContextLE (∏ c, r c) (Lemmata.TensorRank.Tensor.indexedProduct S) (Lemmata.TensorRank.Tensor.indexedProduct T) := by
  let e : Fin (Fintype.card C) ≃ C := (Fintype.equivFin C).symm
  have ht := ContextLE.indexedProduct_fin (fun c => h (e c)) (fun c => hr (e c))
  have hcost : (∏ c : Fin (Fintype.card C), r (e c)) = ∏ c, r c := e.prod_comp r
  rw [hcost] at ht
  apply (contextLE_reindex_iff _ _
    (fun i => Equiv.piCongrLeft (fun c => V c i) e)
    (fun i => Equiv.piCongrLeft (fun c => W c i) e)).mp
  rwa [indexedProduct_reindex_indices, indexedProduct_reindex_indices]

def pairIndexCoordinate {C : Type} (V : C × Bool → I → Type) (i : I) :
    (∀ c, V (c, false) i × V (c, true) i) ≃ (∀ t, V t i) where
  toFun f t := match t with
    | (c, false) => (f c).1
    | (c, true) => (f c).2
  invFun f c := (f (c, false), f (c, true))
  left_inv f := rfl
  right_inv f := by funext t; rcases t with ⟨c, b⟩; cases b <;> rfl

theorem indexedProduct_pairs_reindex {C : Type} [Fintype C]
    {V : C × Bool → I → Type} (S : ∀ t, Tensor 𝕜 I (V t)) :
    reindex (fun i => pairIndexCoordinate V i) (indexedProduct S) =
      indexedProduct (fun c => Lemmata.TensorRank.Tensor.product (S (c, false)) (S (c, true))) := by
  funext x
  simp only [reindex, indexedProduct, Lemmata.TensorRank.Tensor.product,
    Fintype.prod_prod_type, Fintype.prod_bool, pairIndexCoordinate, Equiv.coe_fn_mk]
  apply Finset.prod_congr rfl
  intro c _
  exact mul_comm _ _

theorem indexedProduct_ne_zero {C : Type} [Fintype C]
    {V : C → I → Type} (S : ∀ c, Tensor 𝕜 I (V c)) (hS : ∀ c, S c ≠ 0) :
    indexedProduct S ≠ 0 := by
  have hex (c : C) : ∃ x, S c x ≠ 0 := by
    by_contra h
    push Not at h
    exact hS c (funext h)
  choose x hx using hex
  intro hz
  have he := congrFun hz (fun i c => x c i)
  change (∏ c, S c (x c)) = 0 at he
  exact (Finset.prod_ne_zero_iff.mpr (fun c _ => hx c)) he

theorem ContextLE.unit_left_of_ne_zero [Nonempty I]
    {V W : I → Type} [∀ i, Fintype (V i)] [∀ i, Fintype (W i)]
    (S : Tensor 𝕜 I V) (hS : S ≠ 0) (T : Tensor 𝕜 I W) :
    ContextLE 1 T (Lemmata.TensorRank.Tensor.product S T) := by
  let e (i : I) : W i ≃ (Fin 1 × W i) :=
    { toFun := fun x => (0, x)
      invFun := fun x => x.2
      left_inv := fun _ => rfl
      right_inv := fun x => Prod.ext (Subsingleton.elim _ _) rfl }
  have he : Lemmata.TensorRank.Tensor.reindex (fun i => e i)
      (Lemmata.TensorRank.Tensor.product (diagonal (R := 𝕜) (I := I) 1) T) = T := by
    funext x
    simp [Lemmata.TensorRank.Tensor.reindex, Lemmata.TensorRank.Tensor.product, diagonal_one, e]
  have hu := ContextLE.of_reindex_reverse (fun i => e i) he
  have hs := (diagonal_one_restricts hS).contextLE.rightTensor T
  simpa only [one_mul] using hu.trans hs zero_le_one

end Lemmata.TensorRank.Tensor
