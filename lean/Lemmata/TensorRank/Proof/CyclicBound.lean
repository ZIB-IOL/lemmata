module

/-
Copyright (c) 2026 Kirill Khoruzhii. Licensed under Apache-2.0.
Modified for the arbitrary-field tensor-rank formalization; namespace and imports
adapted for Lemmata. See docs/tensor-rank/NOTICE.txt for upstream attribution
and modification notices, and docs/tensor-rank/LICENSE.txt for the license.
-/

public import Lemmata.TensorRank.Proof.CyclicRound
public import Lemmata.TensorRank.Proof.CyclicExponent
public import Lemmata.TensorRank.Proof.Refinement
public import Lemmata.TensorRank.Proof.Formats

@[expose] public section

set_option autoImplicit false

open scoped BigOperators
open Classical

noncomputable section

namespace Lemmata.TensorRank.CyclicPolynomial

variable {𝕜 : Type*} [Field 𝕜] {k : ℕ} [NeZero k]

theorem full_asymptoticRank_le (e : Fin k ≃ ZMod k) (n : ℕ) :
    Tensor.asymptoticRank (stageTensor (𝕜 := 𝕜) e n (k - 1)) ≤
      ((1 + (k - 1) * (n - 1) : ℕ) : ℝ) ^ (2 * k) := by
  calc
    _ ≤ ∏ t : CyclicSchedule.Token k,
        Tensor.asymptoticRank (stageFactor (𝕜 := 𝕜) e n (k - 1) t) :=
      Tensor.asymptoticRank_indexedProduct_le (stageFactor (𝕜 := 𝕜) e n (k - 1))
    _ ≤ ∏ _t : CyclicSchedule.Token k, ((1 + (k - 1) * (n - 1) : ℕ) : ℝ) :=
      Finset.prod_le_prod₀ (fun t _ => Tensor.asymptoticRank_nonneg _)
        (fun t _ => stageFactor_full_asymptoticRank_le e n t)
    _ = _ := by simp only [Finset.prod_const, Finset.card_univ, CyclicSchedule.token_card]

theorem full_one_ne_zero (e : Fin k ≃ ZMod k) : stageTensor (𝕜 := 𝕜) e 1 (k - 1) ≠ 0 := by
  change Tensor.indexedProduct (stageFactor (𝕜 := 𝕜) e 1 (k - 1)) ≠ 0
  apply Tensor.indexedProduct_ne_zero (stageFactor (𝕜 := 𝕜) e 1 (k - 1))
  intro t hz
  have hr := stageFactor_full_one_rank (𝕜 := 𝕜) e t
  rw [hz, Tensor.rank_zero] at hr
  omega

theorem round_full_weighted_context (e : Fin k ≃ ZMod k) (b : ℕ) (hb : 0 < b) :
    Tensor.ContextLE 1
      (Tensor.product (stageTensor (𝕜 := 𝕜) e b (k - 1))
        (weightedComplete (𝕜 := 𝕜) (fun _ : Edge k => (k * b + 2) ^ 4)))
      (Tensor.product (stageTensor (𝕜 := 𝕜) e (b + 1) (k - 1))
        (weightedComplete (𝕜 := 𝕜) (fun _ : Edge k => (k * b) ^ 4))) := by
  have ho := (Tensor.ContextLE.of_reindex _
    (weighted_constant_reindex (𝕜 := 𝕜) k ((k * b + 2) ^ 4))).leftTensor
      (stageTensor (𝕜 := 𝕜) e b (k - 1))
  have hi := (Tensor.ContextLE.of_reindex_reverse _
    (weighted_constant_reindex (𝕜 := 𝕜) k ((k * b) ^ 4))).leftTensor
      (stageTensor (𝕜 := 𝕜) e (b + 1) (k - 1))
  simpa only [one_mul] using ((ho.trans (round_full_context e b hb) zero_le_one).trans hi (by norm_num))

theorem graph_comparison (e : Fin k ≃ ZMod k) (n : ℕ) (hn : 2 ≤ n) :
    Tensor.asymptoticRank (completeGraph (𝕜 := 𝕜) k (CyclicExponent.outputProduct k n)) ≤
      ((1 + (k - 1) * (n - 1) : ℕ) : ℝ) ^ (2 * k) *
        Tensor.asymptoticRank (completeGraph (𝕜 := 𝕜) k (CyclicExponent.inputProduct k n)) := by
  cases n with
  | zero => omega
  | succ N =>
    let : Nonempty (Fin k) := ⟨⟨0, NeZero.pos k⟩⟩
    have hc := Tensor.ContextLE.weighted_reverse_chain
      (fun b => stageTensor (𝕜 := 𝕜) e (b + 1) (k - 1))
      (fun b _ => (k * (b + 1)) ^ 4) (fun b _ => (k * (b + 1) + 2) ^ 4) N
      (fun b _ => round_full_weighted_context e (b + 1) (by omega))
    have ha : (fun _ : Edge k => ∏ b ∈ Finset.range N, (k * (b + 1)) ^ 4) =
        (fun _ : Edge k => CyclicExponent.inputProduct k (N + 1)) := by
      funext f
      simp only [CyclicExponent.inputProduct, Finset.prod_Ico_eq_prod_range,
        Nat.add_sub_cancel, Nat.add_comm]
    have hb : (fun _ : Edge k => ∏ b ∈ Finset.range N, (k * (b + 1) + 2) ^ 4) =
        (fun _ : Edge k => CyclicExponent.outputProduct k (N + 1)) := by
      funext f
      simp only [CyclicExponent.outputProduct, Finset.prod_Ico_eq_prod_range,
        Nat.add_sub_cancel, Nat.add_comm]
    rw [ha, hb] at hc
    have hu := Tensor.ContextLE.unit_left_of_ne_zero
      (stageTensor (𝕜 := 𝕜) e 1 (k - 1)) (full_one_ne_zero e)
      (weightedComplete (𝕜 := 𝕜) (fun _ : Edge k => CyclicExponent.outputProduct k (N + 1)))
    have h := (hu.trans hc zero_le_one).asymptoticRank_le
    simp only [one_mul] at h
    have hupper := h.trans (Tensor.asymptoticRank_product_le _ _)
    have hfinal := hupper.trans (mul_le_mul_of_nonneg_right (full_asymptoticRank_le e (N + 1))
      (Tensor.asymptoticRank_nonneg _))
    simpa only [asymptoticRank_weighted_constant, Nat.add_sub_cancel] using hfinal

end Lemmata.TensorRank.CyclicPolynomial

namespace Lemmata.TensorRank

variable {𝕜 : Type*} [Field 𝕜]

theorem graphExponent_le_quarter_square (k : ℕ) (hk : 2 ≤ k) :
    graphExponent (𝕜 := 𝕜) k ≤ (k : ℝ) ^ 2 / 4 := by
  let : NeZero k := ⟨by omega⟩
  let e : Fin k ≃ ZMod k := (ZMod.finEquiv k).toEquiv
  exact CyclicExponent.graphExponent_le_quarter_square_of_comparisons hk
    (fun n hn => CyclicPolynomial.graph_comparison e n hn)

end Lemmata.TensorRank
