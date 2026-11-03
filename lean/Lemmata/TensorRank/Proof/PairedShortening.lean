module

/-
Copyright (c) 2026 Kirill Khoruzhii. Licensed under Apache-2.0.
Modified for the arbitrary-field tensor-rank formalization; namespace and imports
adapted for Lemmata. See docs/tensor-rank/NOTICE.txt for upstream attribution
and modification notices, and docs/tensor-rank/LICENSE.txt for the license.
-/

public import Lemmata.TensorRank.Proof.PairedPacking
public import Lemmata.TensorRank.Proof.ReaderPairing
public import Lemmata.TensorRank.Proof.ContextLimit

@[expose] public section

set_option autoImplicit false

open scoped BigOperators
open Classical

noncomputable section

namespace Lemmata.TensorRank.PolynomialProduct.Packing.Paired

variable {𝕜 : Type*} [Field 𝕜] {J : Type} [Fintype J]

theorem product_pairing_context (d : ℕ) :
    Tensor.ContextLE 1
      (Tensor.product (readerPairing (𝕜 := 𝕜) (J := J) d)
        (Tensor.relabel swapReaders (readerPairing (𝕜 := 𝕜) (J := J) d)))
      (readerPairing (𝕜 := 𝕜) (J := J) (d * d)) := by
  have hs := (swapped_pairing_context (𝕜 := 𝕜) (J := J) d).leftTensor
    (readerPairing (𝕜 := 𝕜) (J := J) d)
  have hp := (Tensor.reindex_restricts (fun p => Pairing.productCoordinate (J := J) d d p)
    (readerPairing (𝕜 := 𝕜) (J := J) (d * d))).contextLE
  rw [Pairing.product_reindex] at hp
  simpa only [one_mul] using hs.trans hp zero_le_one

theorem pairing_product_context (d : ℕ) :
    Tensor.ContextLE 1 (readerPairing (𝕜 := 𝕜) (J := J) (d * d))
      (Tensor.product (readerPairing (𝕜 := 𝕜) (J := J) d)
        (Tensor.relabel swapReaders (readerPairing (𝕜 := 𝕜) (J := J) d))) := by
  have hp := Tensor.ContextLE.of_reindex (fun p => Pairing.productCoordinate (J := J) d d p)
    (Pairing.product_reindex (𝕜 := 𝕜) (J := J) d d)
  have hs := (pairing_context_swap (𝕜 := 𝕜) (J := J) d).leftTensor
    (readerPairing (𝕜 := 𝕜) (J := J) d)
  simpa only [one_mul] using hp.trans hs zero_le_one

def sourceTensor (a : J → ℕ) (b c : ℕ) :=
  Tensor.product (short (𝕜 := 𝕜) a (b + 1))
    (readerPairing (𝕜 := 𝕜) (J := J) (c * c))

def targetTensor (a : J → ℕ) (b c : ℕ) :=
  Tensor.product (short (𝕜 := 𝕜) a b)
    (readerPairing (𝕜 := 𝕜) (J := J) ((c + 2) * (c + 2)))

theorem input_context_source (a : J → ℕ) (b c : ℕ) :
    Tensor.ContextLE 1 (input (𝕜 := 𝕜) a b c) (sourceTensor (𝕜 := 𝕜) a b c) := by
  let C := selected (𝕜 := 𝕜) a (b + 1)
  let E := readerPairing (𝕜 := 𝕜) (J := J) c
  have hi : input (𝕜 := 𝕜) a b c =
      Tensor.product (Tensor.product C E)
        (Tensor.product (Tensor.relabel swapReaders C) (Tensor.relabel swapReaders E)) := by
    unfold input source
    rw [Tensor.relabel_product]
  have he := Tensor.product_middle_reindex C (Tensor.relabel swapReaders C)
    E (Tensor.relabel swapReaders E)
  have hs := Tensor.ContextLE.of_reindex _ he
  have hp := (product_pairing_context (𝕜 := 𝕜) (J := J) c).leftTensor
    (short (𝕜 := 𝕜) a (b + 1))
  rw [hi]
  simpa only [short, sourceTensor, one_mul] using hs.trans hp zero_le_one

theorem shortening_polynomial (a : J → ℕ) (b c N : ℕ) (hc : count a b ≤ c) :
    Tensor.ContextLE
      ((((Fintype.card J + 2 : ℕ) : ℝ) ^ 2) * ((N : ℝ) + 1) ^ (2 * (c + 2)))
      (Tensor.power (targetTensor (𝕜 := 𝕜) a b c) N)
      (Tensor.power (sourceTensor (𝕜 := 𝕜) a b c) N) := by
  let h := c + 2
  obtain ⟨w, _, hsize⟩ := Types.exists_large_word h N (by omega)
  let M := Fintype.card (Types.Words (Types.histogram w))
  let A := (N + 1) ^ (2 * h)
  let S := short (𝕜 := 𝕜) a b
  let E := readerPairing (𝕜 := 𝕜) (J := J) (h * h)
  have hdim : (h * h) ^ N ≤ A * (M * M) := by
    have hbound : h ^ N ≤ (N + 1) ^ h * M := by exact_mod_cast hsize
    calc
      _ = h ^ N * h ^ N := mul_pow _ _ _
      _ ≤ ((N + 1) ^ h * M) * ((N + 1) ^ h * M) := Nat.mul_le_mul hbound hbound
      _ = _ := by
        dsimp [A]
        rw [show 2 * h = h * 2 by omega, pow_mul, pow_two]
        ring
  have hsplit : Tensor.ContextLE 1 (Tensor.power (targetTensor (𝕜 := 𝕜) a b c) N)
      (Tensor.product (Tensor.power S N) (Tensor.power E N)) := by
    have he := Tensor.power_product_reindex S E N
    have hr := (Tensor.reindex_restricts
      (fun p => Equiv.arrowProdEquivProdArrow (Fin N)
        (fun _ => SelectedCoordinate a b p × SelectedCoordinate a b (swapReaders p))
        (fun _ => PairCoordinate (h * h) p))
      (Tensor.product (Tensor.power S N) (Tensor.power E N))).contextLE
    rw [he] at hr
    exact hr
  have hpower := (Tensor.reindex_restricts (fun p => Pairing.powerCoordinate (J := J) (h * h) N p)
    (readerPairing (𝕜 := 𝕜) (J := J) ((h * h) ^ N))).contextLE
  rw [Pairing.power_reindex] at hpower
  have hpower' := hpower.leftTensor (Tensor.power S N)
  have hcomm := Tensor.ContextLE.of_reindex _
    (Tensor.product_comm_reindex
      (readerPairing (𝕜 := 𝕜) (J := J) ((h * h) ^ N)) (Tensor.power S N))
  have hamp := (Pairing.context_amplify (𝕜 := 𝕜) (J := J) hdim).rightTensor (Tensor.power S N)
  have hp := (pairing_product_context (𝕜 := 𝕜) (J := J) M).rightTensor (Tensor.power S N)
  have hpaired := hp.trans (paired_type_context_raw (𝕜 := 𝕜) a b c hc w) zero_le_one
  have h₁ := hsplit.trans hpower' zero_le_one
  have h₂ := h₁.trans hcomm (by norm_num)
  have h₃ := h₂.trans hamp (by norm_num)
  have h₄ := h₃.trans hpaired (by positivity)
  have h₅ := h₄.trans ((input_context_source (𝕜 := 𝕜) a b c).power N zero_le_one) (by positivity)
  simpa only [A, h, one_mul, mul_one, one_pow, Nat.cast_pow, Nat.cast_add, Nat.cast_one,
    mul_comm] using h₅

private theorem context_pairing_dimensions
    {V W : Bool ⊕ J → Type} [∀ p, Fintype (V p)] [∀ p, Fintype (W p)]
    (P : Tensor 𝕜 (Bool ⊕ J) V) (Q : Tensor 𝕜 (Bool ⊕ J) W)
    {d d' e e' : ℕ} (hd : d = d') (he : e = e')
    (h : Tensor.ContextLE 1 (Tensor.product P (readerPairing (𝕜 := 𝕜) d))
      (Tensor.product Q (readerPairing e))) :
    Tensor.ContextLE 1 (Tensor.product P (readerPairing (𝕜 := 𝕜) d'))
      (Tensor.product Q (readerPairing e')) := by
  cases hd
  cases he
  exact h

theorem shortening (a : J → ℕ) (b c : ℕ) (hc : count a b ≤ c) :
    Tensor.ContextLE 1
      (Tensor.product (short (𝕜 := 𝕜) a b)
        (readerPairing (𝕜 := 𝕜) (J := J) ((c + 2) ^ 2)))
      (Tensor.product (short (𝕜 := 𝕜) a (b + 1))
        (readerPairing (𝕜 := 𝕜) (J := J) (c ^ 2))) := by
  have h : Tensor.ContextLE 1 (targetTensor (𝕜 := 𝕜) a b c) (sourceTensor (𝕜 := 𝕜) a b c) := by
    apply Tensor.ContextLE.of_polynomial_powers
      (((Fintype.card J + 2 : ℕ) : ℝ) ^ 2) (by positivity) (2 * (c + 2))
    intro N _
    exact shortening_polynomial a b c N hc
  exact context_pairing_dimensions _ _ (pow_two (c + 2)).symm (pow_two c).symm h

end Lemmata.TensorRank.PolynomialProduct.Packing.Paired
