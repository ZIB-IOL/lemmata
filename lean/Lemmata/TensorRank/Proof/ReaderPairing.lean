module

/-
Copyright (c) 2026 Kirill Khoruzhii. Licensed under Apache-2.0.
Modified for the arbitrary-field tensor-rank formalization; namespace and imports
adapted for Lemmata. See docs/tensor-rank/NOTICE.txt for upstream attribution
and modification notices, and docs/tensor-rank/LICENSE.txt for the license.
-/

public import Lemmata.TensorRank.Def.PolynomialPacking
public import Lemmata.TensorRank.Proof.ContextTransport
public import Lemmata.TensorRank.Proof.GraphRank

@[expose] public section

set_option autoImplicit false

open scoped BigOperators
open Classical

noncomputable section

namespace Lemmata.TensorRank.PolynomialProduct.Packing.Pairing

variable {𝕜 : Type*} [Field 𝕜] {J : Type} [Fintype J]

def productCoordinate (a b : ℕ) (p : Bool ⊕ J) :
    (PairCoordinate a p × PairCoordinate b p) ≃ PairCoordinate (a * b) p :=
  match p with
  | .inl _ => finProdFinEquiv
  | .inr _ =>
    { toFun := fun _ => PUnit.unit
      invFun := fun _ => (PUnit.unit, PUnit.unit)
      left_inv := by rintro ⟨⟨⟩, ⟨⟩⟩; rfl
      right_inv := by rintro ⟨⟩; rfl }

theorem product_reindex (a b : ℕ) :
    Tensor.reindex (fun p => productCoordinate (J := J) a b p)
      (readerPairing (𝕜 := 𝕜) (a * b)) =
        Tensor.product (readerPairing (𝕜 := 𝕜) (J := J) a) (readerPairing b) := by
  funext x
  simp only [Tensor.reindex, readerPairing, productCoordinate,
    finProdFinEquiv.injective.eq_iff, Prod.ext_iff, Tensor.product]
  rw [ite_and]
  split_ifs <;> simp_all

def powerCoordinate (d n : ℕ) (p : Bool ⊕ J) :
    (Fin n → PairCoordinate d p) ≃ PairCoordinate (d ^ n) p :=
  match p with
  | .inl _ => wordIndex d n
  | .inr _ => Equiv.ofUnique (Fin n → PUnit) PUnit

theorem power_reindex (d n : ℕ) :
    Tensor.reindex (fun p => powerCoordinate (J := J) d n p)
      (readerPairing (𝕜 := 𝕜) (d ^ n)) =
        Tensor.power (readerPairing (𝕜 := 𝕜) (J := J) d) n := by
  funext x
  have he : wordIndex d n (fun t => x (.inl false) t) =
      wordIndex d n (fun t => x (.inl true) t) ↔
      ∀ t, x (.inl false) t = x (.inl true) t := by
    rw [(wordIndex d n).injective.eq_iff, funext_iff]
  change (if wordIndex d n (fun t => x (.inl false) t) =
      wordIndex d n (fun t => x (.inl true) t) then (1 : 𝕜) else 0) = _
  simp only [he, Tensor.power, readerPairing, Fintype.prod_boole]
  split_ifs <;> rfl

def paddingCoordinate {a b : ℕ} (hab : a ≤ b) (p : Bool ⊕ J) :
    PairCoordinate a p → PairCoordinate b p :=
  match p with
  | .inl _ => Fin.castLE hab
  | .inr _ => id

theorem padding_reindex {a b : ℕ} (hab : a ≤ b) :
    Tensor.reindex (fun p => paddingCoordinate (J := J) hab p)
      (readerPairing (𝕜 := 𝕜) b) = readerPairing (𝕜 := 𝕜) (J := J) a := by
  funext x
  simp only [Tensor.reindex, readerPairing, paddingCoordinate, Fin.castLE_inj]

theorem context_mono {a b : ℕ} (hab : a ≤ b) :
    Tensor.ContextLE 1 (readerPairing (𝕜 := 𝕜) (J := J) a) (readerPairing b) := by
  have ht := (Tensor.reindex_restricts (fun p => paddingCoordinate (J := J) hab p)
    (readerPairing (𝕜 := 𝕜) b)).contextLE
  rwa [padding_reindex] at ht

theorem rank_le (a : ℕ) : Tensor.rank (readerPairing (𝕜 := 𝕜) (J := J) a) ≤ a := by
  apply (Tensor.rank_le_iff _ _).mpr
  let v (t : Fin a) (p : Bool ⊕ J) : PairCoordinate a p → 𝕜 :=
    match p with
    | .inl _ => fun u => if u = t then 1 else 0
    | .inr _ => fun _ => 1
  refine ⟨fun _ => 1, v, ?_⟩
  funext x
  simp [Tensor.pure, v, readerPairing, Fintype.prod_sum_type, Fintype.prod_bool,
    ite_mul, mul_ite, eq_comm]

theorem context_amplify {A M D : ℕ} (hD : D ≤ A * M) :
    Tensor.ContextLE (A : ℝ) (readerPairing (𝕜 := 𝕜) (J := J) D) (readerPairing M) := by
  have hp := Tensor.ContextLE.of_reindex (fun p => productCoordinate (J := J) A M p)
    (product_reindex (𝕜 := 𝕜) (J := J) A M)
  have hc : Tensor.ContextLE (A : ℝ)
      (Tensor.product (readerPairing (𝕜 := 𝕜) (J := J) A) (readerPairing M))
      (readerPairing M) := by
    intro U _ H
    rw [Tensor.asymptoticRank_product_assoc]
    apply (Tensor.asymptoticRank_product_le _ _).trans
    apply mul_le_mul_of_nonneg_right _ (Tensor.asymptoticRank_nonneg _)
    exact (Tensor.asymptoticRank_le_rank _).trans (by exact_mod_cast rank_le (𝕜 := 𝕜) (J := J) A)
  simpa only [one_mul] using
    ((context_mono (𝕜 := 𝕜) (J := J) hD).trans hp zero_le_one).trans hc (by norm_num)

end Lemmata.TensorRank.PolynomialProduct.Packing.Pairing
