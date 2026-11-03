module

/-
Copyright (c) 2026 Kirill Khoruzhii. Licensed under Apache-2.0.
Modified for the arbitrary-field tensor-rank formalization; namespace and imports
adapted for Lemmata. See docs/tensor-rank/NOTICE.txt for upstream attribution
and modification notices, and docs/tensor-rank/LICENSE.txt for the license.
-/

public import Lemmata.TensorRank.Proof.Context
public import Lemmata.TensorRank.Proof.ReaderTransport
public import Lemmata.TensorRank.Proof.Parties

@[expose] public section

set_option autoImplicit false

open scoped BigOperators
open Classical

namespace Lemmata.TensorRank.Tensor

variable {𝕜 : Type*} [Field 𝕜] {I : Type} [Fintype I]
variable {V W U Z : I → Type}
variable [∀ i, Fintype (V i)] [∀ i, Fintype (W i)]
variable [∀ i, Fintype (U i)] [∀ i, Fintype (Z i)]

theorem ContextLE.reindex {c : ℝ} {S : Tensor 𝕜 I V} {T : Tensor 𝕜 I W}
    (h : ContextLE c S T) (e : ∀ i, U i ≃ V i) (f : ∀ i, Z i ≃ W i) :
    ContextLE c (Lemmata.TensorRank.Tensor.reindex (fun i => e i) S) (Lemmata.TensorRank.Tensor.reindex (fun i => f i) T) :=
  (contextLE_reindex_iff S T e f).mpr h

theorem ContextLE.relabel {J : Type} [Fintype J] (e : J ≃ I)
    {c : ℝ} {S : Tensor 𝕜 I V} {T : Tensor 𝕜 I W} (h : ContextLE c S T) :
    ContextLE c (Lemmata.TensorRank.Tensor.relabel e S) (Lemmata.TensorRank.Tensor.relabel e T) := by
  intro X _ H
  have he (Y : I → Type) [∀ i, Fintype (Y i)] (A : Tensor 𝕜 I Y) :
      asymptoticRank (Lemmata.TensorRank.Tensor.product A (Lemmata.TensorRank.Tensor.relabel e.symm H)) =
        asymptoticRank (Lemmata.TensorRank.Tensor.product (Lemmata.TensorRank.Tensor.relabel e A) H) := by
    calc
      _ = asymptoticRank (Lemmata.TensorRank.Tensor.product (Lemmata.TensorRank.Tensor.relabel e.symm H) A) :=
        asymptoticRank_product_comm _ _
      _ = asymptoticRank (Lemmata.TensorRank.Tensor.product H (Lemmata.TensorRank.Tensor.relabel e A)) :=
        asymptoticRank_relabel_context e H A
      _ = _ := asymptoticRank_product_comm _ _
  simpa only [he] using h (fun i => X (e.symm i)) (Lemmata.TensorRank.Tensor.relabel e.symm H)

theorem ContextLE.power {c : ℝ} {S : Tensor 𝕜 I V} {T : Tensor 𝕜 I W}
    (h : ContextLE c S T) (n : ℕ) (hc : 0 ≤ c) :
    ContextLE (c ^ n) (Lemmata.TensorRank.Tensor.power S n) (Lemmata.TensorRank.Tensor.power T n) := by
  have hp := ContextLE.indexedProduct_fin
    (V := fun _ : Fin n => V) (W := fun _ : Fin n => W)
    (S := fun _ : Fin n => S) (T := fun _ : Fin n => T) (c := fun _ => c)
    (fun _ => h) (fun _ => hc)
  have hs : Lemmata.TensorRank.Tensor.indexedProduct (fun _ : Fin n => S) = Lemmata.TensorRank.Tensor.power S n := by
    funext x
    rfl
  have ht : Lemmata.TensorRank.Tensor.indexedProduct (fun _ : Fin n => T) = Lemmata.TensorRank.Tensor.power T n := by
    funext x
    rfl
  rw [hs, ht] at hp
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using hp

omit [Fintype I] [∀ i, Fintype (V i)] [∀ i, Fintype (W i)] [∀ i, Fintype (U i)] in
theorem product_assoc_reindex (S : Tensor 𝕜 I V) (T : Tensor 𝕜 I W)
    (H : Tensor 𝕜 I U) :
    Lemmata.TensorRank.Tensor.reindex (fun i => Equiv.prodAssoc (V i) (W i) (U i))
      (Lemmata.TensorRank.Tensor.product S (Lemmata.TensorRank.Tensor.product T H)) = Lemmata.TensorRank.Tensor.product (Lemmata.TensorRank.Tensor.product S T) H := by
  funext x
  exact (mul_assoc _ _ _).symm

omit [Fintype I] [∀ i, Fintype (V i)] [∀ i, Fintype (W i)] in
theorem product_comm_reindex (S : Tensor 𝕜 I V) (T : Tensor 𝕜 I W) :
    Lemmata.TensorRank.Tensor.reindex (fun i => Equiv.prodComm (V i) (W i)) (Lemmata.TensorRank.Tensor.product T S) = Lemmata.TensorRank.Tensor.product S T := by
  funext x
  exact mul_comm _ _

omit [Fintype I] [∀ i, Fintype (V i)] [∀ i, Fintype (W i)]
  [∀ i, Fintype (U i)] [∀ i, Fintype (Z i)] in
theorem product_middle_reindex (S : Tensor 𝕜 I V) (T : Tensor 𝕜 I W)
    (P : Tensor 𝕜 I U) (Q : Tensor 𝕜 I Z) :
    Lemmata.TensorRank.Tensor.reindex (fun i => Equiv.prodProdProdComm (V i) (W i) (U i) (Z i))
      (Lemmata.TensorRank.Tensor.product (Lemmata.TensorRank.Tensor.product S P) (Lemmata.TensorRank.Tensor.product T Q)) = Lemmata.TensorRank.Tensor.product (Lemmata.TensorRank.Tensor.product S T) (Lemmata.TensorRank.Tensor.product P Q) := by
  funext x
  exact mul_mul_mul_comm _ _ _ _

theorem ContextLE.power_product (S : Tensor 𝕜 I V) (T : Tensor 𝕜 I W) (n : ℕ) :
    ContextLE 1 (Lemmata.TensorRank.Tensor.product (Lemmata.TensorRank.Tensor.power S n) (Lemmata.TensorRank.Tensor.power T n))
      (Lemmata.TensorRank.Tensor.power (Lemmata.TensorRank.Tensor.product S T) n) :=
  ContextLE.of_reindex
    (fun i => Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => V i) (fun _ => W i))
    (power_product_reindex S T n)

theorem ContextLE.flatten_power (S : Tensor 𝕜 I V) (m n : ℕ) :
    ContextLE 1 (Lemmata.TensorRank.Tensor.power S (n * m))
      (Lemmata.TensorRank.Tensor.power (Lemmata.TensorRank.Tensor.power S m) n) :=
  ContextLE.of_reindex (fun i => wordFlatten (V i) m n) (power_mul_reindex S m n)

omit [Field 𝕜] [Fintype I] [∀ i, Fintype (V i)] in
theorem relabel_comp_indices {J K : Type} (e : J ≃ I) (f : K ≃ J) (T : Tensor 𝕜 I V) :
    Lemmata.TensorRank.Tensor.relabel f (Lemmata.TensorRank.Tensor.relabel e T) =
      Lemmata.TensorRank.Tensor.relabel (f.trans e) T := by
  funext x
  unfold Lemmata.TensorRank.Tensor.relabel
  congr 1
  funext i
  obtain ⟨j, rfl⟩ := e.surjective i
  obtain ⟨a, rfl⟩ := f.surjective j
  simp only [Equiv.piCongrLeft_apply_apply]
  exact (Equiv.piCongrLeft_apply_apply V (f.trans e) x a).symm

omit [Field 𝕜] [Fintype I] [∀ i, Fintype (V i)] [∀ i, Fintype (W i)] in
theorem relabel_reindex_indices {J : Type} (e : J ≃ I)
    (coords : ∀ i, W i → V i) (T : Tensor 𝕜 I V) :
    Lemmata.TensorRank.Tensor.relabel e (Lemmata.TensorRank.Tensor.reindex coords T) =
      Lemmata.TensorRank.Tensor.reindex (fun j => coords (e j)) (Lemmata.TensorRank.Tensor.relabel e T) := by
  funext x
  unfold Lemmata.TensorRank.Tensor.relabel Lemmata.TensorRank.Tensor.reindex
  congr 1
  funext i
  obtain ⟨j, rfl⟩ := e.surjective i
  simp

end Lemmata.TensorRank.Tensor
