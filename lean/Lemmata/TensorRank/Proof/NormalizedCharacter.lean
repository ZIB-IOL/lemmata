module

public import Lemmata.TensorRank.Proof.CharacterEdges
public import Lemmata.TensorRank.Proof.SymmetricCharacter

@[expose] public section

set_option autoImplicit false

open scoped BigOperators
open Classical

noncomputable section

namespace Lemmata.TensorRank.TensorSemiring

variable {k : ℕ}

def meanExponent (f : Character k) : ℝ := (∑ e, f.pairExponent e) / (k.choose 2 : ℝ)

def normalizedValue (f : Character k) (a : Value k) : ℝ := symmetricValue f (meanExponent f) a

def normalizedEval (f : Character k) {V : Fin k → Type} [∀ i, Fintype (V i)]
    (T : Tensor ℂ (Fin k) V) : ℝ := normalizedValue f (ofTensor T)

variable [Nonempty (Fin k)] (f : Character k)

theorem meanExponent_pos (hk : 2 ≤ k) : 0 < meanExponent f :=
  div_pos f.sum_pairExponent_pos (by exact_mod_cast Nat.choose_pos hk)

omit [Nonempty (Fin k)] in
theorem permutationCount_mul_meanExponent (hk : 2 ≤ k) :
    (Fintype.card (Equiv.Perm (Fin k)) : ℝ) * meanExponent f =
      ((2 * (k - 2).factorial : ℕ) : ℝ) * ∑ e, f.pairExponent e := by
  have hc : (k.choose 2 : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hk).ne'
  have hm : (k.choose 2 : ℝ) * ((2 * (k - 2).factorial : ℕ) : ℝ) = (k.factorial : ℝ) := by
    exact_mod_cast edge_multiplicity_factorial hk
  rw [meanExponent, Fintype.card_perm, Fintype.card_fin, ← hm]
  field_simp

theorem normalizedEval_singleEdge (hk : 2 ≤ k) (e : Edge k) {n : ℕ} (hn : 1 ≤ n) :
    normalizedEval f (weightedComplete (singleEdgeDimensions e n)) = n := by
  have h := f.prod_eval_relabel_pair hk e hn
  change symmetricProduct f (ofTensor (weightedComplete (singleEdgeDimensions e n))) = _ at h
  have hr : (0 : ℝ) < ((2 * (k - 2).factorial : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (by decide : 0 < 2) (Nat.factorial_pos _)
  rw [normalizedEval, normalizedValue, symmetricValue, h,
    ← Real.rpow_mul (Nat.cast_nonneg n), permutationCount_mul_meanExponent f hk,
    mul_one_div_cancel (mul_pos hr f.sum_pairExponent_pos).ne', Real.rpow_one]

theorem normalizedEval_nonneg {V : Fin k → Type} [∀ i, Fintype (V i)]
    (T : Tensor ℂ (Fin k) V) : 0 ≤ normalizedEval f T :=
  symmetricValue_nonneg f (meanExponent f) (ofTensor T)

theorem one_le_normalizedEval (hk : 2 ≤ k) {V : Fin k → Type} [∀ i, Fintype (V i)]
    {T : Tensor ℂ (Fin k) V} (hT : T ≠ 0) : 1 ≤ normalizedEval f T := by
  have h := symmetricEval_mono f (meanExponent f) (meanExponent_pos f hk)
    (Tensor.diagonal_one_restricts hT)
  simpa only [normalizedEval, normalizedValue, symmetricEval, ofTensor_diagonal,
    Nat.cast_one, symmetricValue_one]
    using h

theorem normalizedEval_le_rank (hk : 2 ≤ k) {V : Fin k → Type} [∀ i, Fintype (V i)]
    (T : Tensor ℂ (Fin k) V) :
    normalizedEval f T ≤ (Tensor.rank T : ℝ) ^ (1 / meanExponent f) :=
  symmetricEval_le_rank f (meanExponent f) (meanExponent_pos f hk) T

end Lemmata.TensorRank.TensorSemiring
