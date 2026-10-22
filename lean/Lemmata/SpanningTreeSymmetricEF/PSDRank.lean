module

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.LinearAlgebra.Matrix.Rank

@[expose] public section


/-!
# Identity submatrices force PSD order

The results here concern concrete real PSD matrix factorizations. They do not
assume a PSD-rank lower bound. A trace-factorization application would require
constructing geometric PSD factors. PrimalPSDBound.lean and NonnegativeOuter.lean
instead prove the relevant geometric size bound directly, without conic duality.
-/

namespace Lemmata.SpanningTreeSymmetricEF.PSDRank

open Matrix
open scoped MatrixOrder

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Gram factors have zero trace pairing exactly when their cross product vanishes. -/
theorem trace_gram_mul_gram_eq_zero_iff (U V : Matrix κ κ ℝ) :
    ((Uᴴ * U) * (Vᴴ * V)).trace = 0 ↔ U * Vᴴ = 0 := by
  have h : ((Uᴴ * U) * (Vᴴ * V)).trace =
      ((U * Vᴴ)ᴴ * (U * Vᴴ)).trace := by
    rw [conjTranspose_mul, conjTranspose_conjTranspose]
    calc
      _ = ((Uᴴ * U) * Vᴴ * V).trace := by simp only [Matrix.mul_assoc]
      _ = (V * (Uᴴ * U) * Vᴴ).trace := trace_mul_cycle _ _ _
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [h, trace_conjTranspose_mul_self_eq_zero_iff]

/-- Every real PSD matrix has a Gram factor of the same order. -/
theorem exists_gram_factor {A : Matrix κ κ ℝ} (hA : A.PosSemidef) :
    ∃ U : Matrix κ κ ℝ, A = Uᴴ * U := by
  classical
  simpa only [star_eq_conjTranspose] using
    CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg

/-- Pairwise zero cross products and nonzero diagonal cross products yield an
ordinary identity factorization through the common coordinate space. -/
theorem card_le_of_cross_products
    (U V : ι → Matrix κ κ ℝ)
    (hoff : ∀ i j, i ≠ j → U i * V j = 0)
    (hdiag : ∀ i, U i * V i ≠ 0) :
    Fintype.card ι ≤ Fintype.card κ := by
  classical
  have hentry : ∀ i, ∃ r c, (U i * V i) r c ≠ 0 := by
    intro i
    by_contra h
    push Not at h
    exact hdiag i (by ext r c; exact h r c)
  choose r c hrc using hentry
  let d : ι → ℝ := fun i => (U i * V i) (r i) (c i)
  let X : Matrix ι κ ℝ := fun i t => U i (r i) t / d i
  let Y : Matrix κ ι ℝ := fun t j => V j t (c j)
  have hXY : X * Y = 1 := by
    ext i j
    have hentry' : (X * Y) i j = (U i * V j) (r i) (c j) / d i := by
      change (∑ t, (U i (r i) t / d i) * V j t (c j)) =
        (∑ t, U i (r i) t * V j t (c j)) / d i
      simp only [div_mul_eq_mul_div, Finset.sum_div]
    rw [hentry']
    by_cases hij : i = j
    · subst j
      simp [d, hrc]
    · simp [hoff i j hij, hij]
  calc
    Fintype.card ι = (1 : Matrix ι ι ℝ).rank := Matrix.rank_one.symm
    _ = (X * Y).rank := congrArg Matrix.rank hXY.symm
    _ ≤ X.rank := Matrix.rank_mul_le_left X Y
    _ ≤ Fintype.card κ := Matrix.rank_le_card_width X

/-- A real PSD factorization of an identity matrix has order at least the
identity's order. The matrix order and identity index set are arbitrary finite
types, including empty types. No PSD-rank conclusion is assumed. -/
theorem card_le_of_identity_factorization [DecidableEq ι]
    (A B : ι → Matrix κ κ ℝ)
    (hA : ∀ i, (A i).PosSemidef)
    (hB : ∀ i, (B i).PosSemidef)
    (htrace : ∀ i j, (A i * B j).trace = if i = j then 1 else 0) :
    Fintype.card ι ≤ Fintype.card κ := by
  classical
  choose U hU using fun i => exists_gram_factor (hA i)
  choose V hV using fun i => exists_gram_factor (hB i)
  apply card_le_of_cross_products U (fun j => (V j)ᴴ)
  · intro i j hij
    apply (trace_gram_mul_gram_eq_zero_iff (U i) (V j)).mp
    rw [← hU i, ← hV j, htrace]
    simp [hij]
  · intro i hzero
    have ht := (trace_gram_mul_gram_eq_zero_iff (U i) (V i)).mpr hzero
    rw [← hU i, ← hV i, htrace] at ht
    simp at ht

/-- Block-diagonal embedding preserves positive semidefiniteness, allowing
blocks of different (and possibly zero) orders. -/
theorem posSemidef_blockDiagonal
    {β : Type*} [Fintype β] [DecidableEq β]
    {κ : β → Type*} [∀ b, Fintype (κ b)]
    (A : ∀ b, Matrix (κ b) (κ b) ℝ)
    (hA : ∀ b, (A b).PosSemidef) :
    (Matrix.blockDiagonal' A).PosSemidef := by
  classical
  choose U hU using fun b => exists_gram_factor (hA b)
  have h : Matrix.blockDiagonal' A =
      (Matrix.blockDiagonal' U)ᴴ * Matrix.blockDiagonal' U := by
    rw [Matrix.blockDiagonal'_conjTranspose, ← Matrix.blockDiagonal'_mul]
    exact congrArg Matrix.blockDiagonal' (funext hU)
  rw [h]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- For a product of real PSD cones the identity order is bounded by the
sum of the block orders, not their sum of squares. -/
theorem card_le_sum_of_identity_block_factorization [DecidableEq ι]
    {β : Type*} [Fintype β]
    {κ : β → Type*} [∀ b, Fintype (κ b)]
    (A B : ι → ∀ b, Matrix (κ b) (κ b) ℝ)
    (hA : ∀ i b, (A i b).PosSemidef)
    (hB : ∀ i b, (B i b).PosSemidef)
    (htrace : ∀ i j, (∑ b, (A i b * B j b).trace) = if i = j then 1 else 0) :
    Fintype.card ι ≤ ∑ b, Fintype.card (κ b) := by
  classical
  have h := card_le_of_identity_factorization
    (fun i => Matrix.blockDiagonal' (A i))
    (fun j => Matrix.blockDiagonal' (B j))
    (fun i => posSemidef_blockDiagonal (A i) (hA i))
    (fun j => posSemidef_blockDiagonal (B j) (hB j))
    (fun i j => by
      rw [← Matrix.blockDiagonal'_mul, Matrix.trace_blockDiagonal']
      exact htrace i j)
  simpa only [Fintype.card_sigma] using h

end Lemmata.SpanningTreeSymmetricEF.PSDRank
