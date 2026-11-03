module

/-
Copyright (c) 2026 Kirill Khoruzhii. Licensed under Apache-2.0.
Modified for the arbitrary-field tensor-rank formalization; namespace and imports
adapted for Lemmata. See docs/tensor-rank/NOTICE.txt for upstream attribution
and modification notices, and docs/tensor-rank/LICENSE.txt for the license.
-/

public import Lemmata.TensorRank.Proof.WeightedGraph
public import Lemmata.TensorRank.Proof.ContextIndexed

@[expose] public section

set_option autoImplicit false

open scoped BigOperators
open Classical

namespace Lemmata.TensorRank.Tensor

variable {𝕜 : Type*} [Field 𝕜] {k : ℕ}
variable {V W U : Fin k → Type}
variable [∀ i, Fintype (V i)] [∀ i, Fintype (W i)] [∀ i, Fintype (U i)]

theorem ContextLE.weighted_split (T : Tensor 𝕜 (Fin k) V) (a b : Edge k → ℕ) :
    ContextLE 1 (Lemmata.TensorRank.Tensor.product T (weightedComplete (𝕜 := 𝕜) (fun e => a e * b e)))
      (Lemmata.TensorRank.Tensor.product (Lemmata.TensorRank.Tensor.product T (weightedComplete a)) (weightedComplete b)) := by
  have hg := (ContextLE.of_reindex (weightedProductCoordinate a b)
    (weighted_product_reindex (𝕜 := 𝕜) a b)).leftTensor T
  have ha := ContextLE.of_reindex
    (fun i => Equiv.prodAssoc (V i) (WeightedCoordinate a i) (WeightedCoordinate b i))
    (product_assoc_reindex T (weightedComplete a) (weightedComplete b))
  simpa only [one_mul] using hg.trans ha zero_le_one

theorem ContextLE.weighted_merge (T : Tensor 𝕜 (Fin k) V) (a b : Edge k → ℕ) :
    ContextLE 1
      (Lemmata.TensorRank.Tensor.product (Lemmata.TensorRank.Tensor.product T (weightedComplete (𝕜 := 𝕜) a)) (weightedComplete b))
      (Lemmata.TensorRank.Tensor.product T (weightedComplete (𝕜 := 𝕜) (fun e => a e * b e))) := by
  have ha := ContextLE.of_reindex_reverse
    (fun i => Equiv.prodAssoc (V i) (WeightedCoordinate a i) (WeightedCoordinate b i))
    (product_assoc_reindex T (weightedComplete a) (weightedComplete b))
  have hg := (ContextLE.of_reindex_reverse (weightedProductCoordinate a b)
    (weighted_product_reindex (𝕜 := 𝕜) a b)).leftTensor T
  simpa only [one_mul] using ha.trans hg zero_le_one

private def swapRightCoordinate (A B C : Type) : ((A × B) × C) ≃ ((A × C) × B) where
  toFun x := ((x.1.1, x.2), x.1.2)
  invFun x := ((x.1.1, x.2), x.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

theorem ContextLE.swap_right (S : Tensor 𝕜 (Fin k) V)
    (T : Tensor 𝕜 (Fin k) W) (H : Tensor 𝕜 (Fin k) U) :
    ContextLE 1 (Lemmata.TensorRank.Tensor.product (Lemmata.TensorRank.Tensor.product S T) H)
      (Lemmata.TensorRank.Tensor.product (Lemmata.TensorRank.Tensor.product S H) T) := by
  apply ContextLE.of_reindex (fun i => swapRightCoordinate (V i) (U i) (W i))
  funext x
  change (S (fun i => (x i).1.1) * T (fun i => (x i).2)) * H (fun i => (x i).1.2) = _
  exact mul_right_comm _ _ _

theorem ContextLE.weighted_comp
    (S : Tensor 𝕜 (Fin k) V) (T : Tensor 𝕜 (Fin k) W) (H : Tensor 𝕜 (Fin k) U)
    (a b c d : Edge k → ℕ)
    (h : ContextLE 1 (Lemmata.TensorRank.Tensor.product S (weightedComplete (𝕜 := 𝕜) b))
      (Lemmata.TensorRank.Tensor.product T (weightedComplete a)))
    (g : ContextLE 1 (Lemmata.TensorRank.Tensor.product T (weightedComplete (𝕜 := 𝕜) d))
      (Lemmata.TensorRank.Tensor.product H (weightedComplete c))) :
    ContextLE 1
      (Lemmata.TensorRank.Tensor.product S (weightedComplete (𝕜 := 𝕜) (fun e => b e * d e)))
      (Lemmata.TensorRank.Tensor.product H (weightedComplete (𝕜 := 𝕜) (fun e => c e * a e))) := by
  have h₁ := (ContextLE.weighted_split S b d).trans (h.rightTensor (weightedComplete d)) zero_le_one
  have h₂ := h₁.trans (ContextLE.swap_right T (weightedComplete a) (weightedComplete d)) (by norm_num)
  have h₃ := h₂.trans (g.rightTensor (weightedComplete a)) (by norm_num)
  simpa only [one_mul] using h₃.trans (ContextLE.weighted_merge H c a) (by norm_num)

theorem ContextLE.weighted_chain {X : ℕ → Fin k → Type} [∀ n i, Fintype (X n i)]
    (T : ∀ n, Tensor 𝕜 (Fin k) (X n)) (a b : ℕ → Edge k → ℕ) (N : ℕ)
    (h : ∀ n, n < N → ContextLE 1
      (Lemmata.TensorRank.Tensor.product (T (n + 1)) (weightedComplete (𝕜 := 𝕜) (b n)))
      (Lemmata.TensorRank.Tensor.product (T n) (weightedComplete (a n)))) :
    ContextLE 1
      (Lemmata.TensorRank.Tensor.product (T N) (weightedComplete (𝕜 := 𝕜) (fun e => ∏ n ∈ Finset.range N, b n e)))
      (Lemmata.TensorRank.Tensor.product (T 0) (weightedComplete (𝕜 := 𝕜) (fun e => ∏ n ∈ Finset.range N, a n e))) := by
  induction N with
  | zero => exact ContextLE.refl _
  | succ N ih =>
    have hg := ih (fun n hn => h n (by omega))
    have hc := ContextLE.weighted_comp (T (N + 1)) (T N) (T 0) (a N) (b N)
      (fun e => ∏ n ∈ Finset.range N, a n e) (fun e => ∏ n ∈ Finset.range N, b n e)
      (h N (by omega)) hg
    have he : (fun e => b N e * ∏ n ∈ Finset.range N, b n e) =
        (fun e => ∏ n ∈ Finset.range (N + 1), b n e) := by
      funext e
      rw [Finset.prod_range_succ, Nat.mul_comm]
    rw [he] at hc
    have ha : (fun e => (∏ n ∈ Finset.range N, a n e) * a N e) =
        (fun e => ∏ n ∈ Finset.range (N + 1), a n e) := by
      funext e
      exact (Finset.prod_range_succ _ _).symm
    rw [ha] at hc
    exact hc

theorem ContextLE.weighted_reverse_chain {X : ℕ → Fin k → Type} [∀ n i, Fintype (X n i)]
    (T : ∀ n, Tensor 𝕜 (Fin k) (X n)) (a b : ℕ → Edge k → ℕ) (N : ℕ)
    (h : ∀ n, n < N → ContextLE 1
      (Lemmata.TensorRank.Tensor.product (T n) (weightedComplete (𝕜 := 𝕜) (b n)))
      (Lemmata.TensorRank.Tensor.product (T (n + 1)) (weightedComplete (a n)))) :
    ContextLE 1
      (Lemmata.TensorRank.Tensor.product (T 0) (weightedComplete (𝕜 := 𝕜) (fun e => ∏ n ∈ Finset.range N, b n e)))
      (Lemmata.TensorRank.Tensor.product (T N) (weightedComplete (𝕜 := 𝕜) (fun e => ∏ n ∈ Finset.range N, a n e))) := by
  induction N with
  | zero => exact ContextLE.refl _
  | succ N ih =>
    have hg := ih (fun n hn => h n (by omega))
    have hc := ContextLE.weighted_comp (T 0) (T N) (T (N + 1))
      (fun e => ∏ n ∈ Finset.range N, a n e) (fun e => ∏ n ∈ Finset.range N, b n e)
      (a N) (b N) hg (h N (by omega))
    have he : (fun e => a N e * ∏ n ∈ Finset.range N, a n e) =
        (fun e => ∏ n ∈ Finset.range (N + 1), a n e) := by
      funext e
      rw [Finset.prod_range_succ, Nat.mul_comm]
    rw [he] at hc
    have hb : (fun e => (∏ n ∈ Finset.range N, b n e) * b N e) =
        (fun e => ∏ n ∈ Finset.range (N + 1), b n e) := by
      funext e
      exact (Finset.prod_range_succ _ _).symm
    rw [hb] at hc
    exact hc

end Lemmata.TensorRank.Tensor
