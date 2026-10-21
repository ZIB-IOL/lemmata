module

public import Lemmata.TensorRank.Proof.CharacterSeparation
public import Lemmata.TensorRank.Proof.SymmetricCharacter
public import Lemmata.TensorRank.Proof.NormalizedCharacter
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

@[expose] public section

set_option autoImplicit false

open scoped BigOperators
open Classical

noncomputable section

namespace Lemmata.TensorRank.TensorSemiring

variable {k : ℕ} [Nonempty (Fin k)] (f : Character k)
variable {C : Type} [Fintype C] {N : ℕ} {V : Fin k → Type} [∀ i, Fintype (V i)]

omit [Nonempty (Fin k)] in
theorem symmetricProduct_wordTensor (Z : C → Tensor ℂ (Fin k) V) (w : Fin N → C) :
    symmetricProduct f (ofTensor (Tensor.wordTensor Z w)) =
      ∏ c, symmetricProduct f (ofTensor (Z c)) ^ (Types.histogram w c).val := by
  change (∏ σ : Equiv.Perm (Fin k), (f.permute σ).eval (Tensor.wordTensor Z w)) = _
  simp_rw [Character.eval_wordTensor]
  rw [Finset.prod_comm]
  simp_rw [Finset.prod_pow]
  rfl

theorem symmetricEval_wordTensor (p : ℝ) (Z : C → Tensor ℂ (Fin k) V) (w : Fin N → C) :
    symmetricEval f p (Tensor.wordTensor Z w) =
      ∏ c, symmetricEval f p (Z c) ^ (Types.histogram w c).val := by
  simp only [symmetricEval, symmetricValue, symmetricProduct_wordTensor]
  rw [← Real.finsetProd_rpow _ _ (fun c _ => pow_nonneg (symmetricProduct_nonneg f _) _)]
  apply Finset.prod_congr rfl
  intro c _
  exact (Real.rpow_pow_comm (symmetricProduct_nonneg f _) _ _).symm

theorem symmetricProduct_fixed_type_bound (hk : 2 ≤ k) (a b : Fin k) (hab : a ≠ b)
    (Z : C → Tensor ℂ (Fin k) V) {left : V a → C} {right : V b → C}
    (hl : Tensor.Reads Z a left) (hr : Tensor.Reads Z b right)
    {h : C → Fin (N + 1)} (base : Types.Words h) :
    symmetricProduct f (ofTensor (weightedComplete (singleEdgeDimensions
      (edgeBetween a b hab.symm) (Fintype.card (Types.Words h))))) *
        (∏ c, symmetricProduct f (ofTensor (Z c)) ^ (h c).val) ≤
      ((k - 1 : ℕ) : ℝ) ^ Fintype.card (Equiv.Perm (Fin k)) *
        symmetricProduct f (ofTensor (∑ c, Z c)) ^ N := by
  let G := weightedComplete (singleEdgeDimensions (edgeBetween a b hab.symm)
    (Fintype.card (Types.Words h)))
  have hp := Finset.prod_le_prod₀
    (fun (σ : Equiv.Perm (Fin k)) (_ : σ ∈ Finset.univ) =>
      mul_nonneg ((f.permute σ).eval_nonneg G) (Finset.prod_nonneg
        (fun c _ => pow_nonneg ((f.permute σ).eval_nonneg (Z c)) (h c).val)))
    (fun σ _ => Separation.character_fixed_type_edge_bound (f.permute σ) hk a b hab Z hl hr base)
  simp only [Finset.prod_mul_distrib] at hp
  rw [Finset.prod_comm] at hp
  simp_rw [Finset.prod_pow] at hp
  simp only [Finset.prod_const, Finset.card_univ] at hp
  exact hp

theorem symmetricEval_fixed_type_bound (hk : 2 ≤ k) (p : ℝ) (hp : 0 < p)
    (a b : Fin k) (hab : a ≠ b)
    (hnorm : ∀ M, 0 < M → symmetricEval f p (weightedComplete
      (singleEdgeDimensions (edgeBetween a b hab.symm) M)) = M)
    (Z : C → Tensor ℂ (Fin k) V) {left : V a → C} {right : V b → C}
    (hl : Tensor.Reads Z a left) (hr : Tensor.Reads Z b right)
    {h : C → Fin (N + 1)} (base : Types.Words h) :
    (Fintype.card (Types.Words h) : ℝ) * (∏ c, symmetricEval f p (Z c) ^ (h c).val) ≤
      ((k - 1 : ℕ) : ℝ) ^ (1 / p) * symmetricEval f p (∑ c, Z c) ^ N := by
  let L := Fintype.card (Equiv.Perm (Fin k))
  let q : ℝ := 1 / ((L : ℝ) * p)
  let G := weightedComplete (singleEdgeDimensions (edgeBetween a b hab.symm)
    (Fintype.card (Types.Words h)))
  have hK : 0 < ((k - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < k - 1)
  have hb := Real.rpow_le_rpow
    (mul_nonneg (symmetricProduct_nonneg f (ofTensor G))
      (Finset.prod_nonneg (fun c _ => pow_nonneg (symmetricProduct_nonneg f (ofTensor (Z c))) _)))
    (symmetricProduct_fixed_type_bound f hk a b hab Z hl hr base)
    (show 0 ≤ q by dsimp [q]; positivity)
  have hleft :
      (symmetricProduct f (ofTensor G) * ∏ c, symmetricProduct f (ofTensor (Z c)) ^ (h c).val) ^ q =
        symmetricEval f p G * ∏ c, symmetricEval f p (Z c) ^ (h c).val := by
    rw [Real.mul_rpow (symmetricProduct_nonneg f _) (Finset.prod_nonneg
      (fun c _ => pow_nonneg (symmetricProduct_nonneg f _) _)),
      ← Real.finsetProd_rpow _ _ (fun c _ => pow_nonneg (symmetricProduct_nonneg f _) _)]
    congr 1
    apply Finset.prod_congr rfl
    intro c _
    exact (Real.rpow_pow_comm (symmetricProduct_nonneg f _) q _).symm
  have hconstant : ((((k - 1 : ℕ) : ℝ) ^ L) ^ q) = ((k - 1 : ℕ) : ℝ) ^ (1 / p) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hK.le]
    congr 1
    dsimp only [q, L]
    field_simp [(permutationCount_pos (k := k)).ne']
  have hright :
      ((((k - 1 : ℕ) : ℝ) ^ L) * symmetricProduct f (ofTensor (∑ c, Z c)) ^ N) ^ q =
        ((k - 1 : ℕ) : ℝ) ^ (1 / p) * symmetricEval f p (∑ c, Z c) ^ N := by
    rw [Real.mul_rpow (pow_nonneg hK.le _) (pow_nonneg (symmetricProduct_nonneg f _) _),
      hconstant]
    congr 1
    exact (Real.rpow_pow_comm (symmetricProduct_nonneg f _) q N).symm
  rw [hleft, hright] at hb
  rw [hnorm _ (Fintype.card_pos_iff.mpr ⟨base⟩)] at hb
  exact hb

theorem symmetricEval_readable_sum (hk : 2 ≤ k) (p : ℝ) (hp : 0 < p)
    (a b : Fin k) (hab : a ≠ b)
    (hnorm : ∀ M, 0 < M → symmetricEval f p (weightedComplete
      (singleEdgeDimensions (edgeBetween a b hab.symm) M)) = M)
    (Z : C → Tensor ℂ (Fin k) V) {left : V a → C} {right : V b → C}
    (hl : Tensor.Reads Z a left) (hr : Tensor.Reads Z b right) :
    (∑ c, symmetricEval f p (Z c)) ≤ symmetricEval f p (∑ c, Z c) := by
  have hv (c : C) : 0 ≤ symmetricEval f p (Z c) := symmetricValue_nonneg f p _
  have hS : 0 ≤ symmetricEval f p (∑ c, Z c) := symmetricValue_nonneg f p _
  have hK : 0 < ((k - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < k - 1)
  apply le_of_polynomial_power_bound (Finset.sum_nonneg (fun c _ => hv c)) hS
    (((k - 1 : ℕ) : ℝ) ^ (1 / p)) (Real.rpow_pos_of_pos hK _) (Fintype.card C)
  intro n _
  obtain ⟨h, hh⟩ := Types.exists_large_type (N := n) (fun c => symmetricEval f p (Z c))
  by_cases hM : 0 < Fintype.card (Types.Words h)
  · obtain ⟨base⟩ := Fintype.card_pos_iff.mp hM
    have ht := symmetricEval_fixed_type_bound f hk p hp a b hab hnorm Z hl hr base
    calc
      _ ≤ ((n + 1 : ℕ) : ℝ) ^ Fintype.card C *
          ((Fintype.card (Types.Words h) : ℝ) * ∏ c, symmetricEval f p (Z c) ^ (h c).val) := hh
      _ ≤ ((n + 1 : ℕ) : ℝ) ^ Fintype.card C *
          (((k - 1 : ℕ) : ℝ) ^ (1 / p) * symmetricEval f p (∑ c, Z c) ^ n) :=
        mul_le_mul_of_nonneg_left ht (by positivity)
      _ = _ := by push_cast; ring
  · have hz : Fintype.card (Types.Words h) = 0 := by omega
    have hx : (∑ c, symmetricEval f p (Z c)) ^ n ≤ 0 := by simpa only [hz, Nat.cast_zero,
      zero_mul, mul_zero] using hh
    exact hx.trans (by positivity)

theorem normalizedEval_readable_sum (hk : 2 ≤ k) (a b : Fin k) (hab : a ≠ b)
    (Z : C → Tensor ℂ (Fin k) V) {left : V a → C} {right : V b → C}
    (hl : Tensor.Reads Z a left) (hr : Tensor.Reads Z b right) :
    (∑ c, normalizedEval f (Z c)) ≤ normalizedEval f (∑ c, Z c) := by
  exact symmetricEval_readable_sum f hk (meanExponent f) (meanExponent_pos f hk) a b hab
    (fun M hM => normalizedEval_singleEdge f hk (edgeBetween a b hab.symm) (by omega)) Z hl hr

end Lemmata.TensorRank.TensorSemiring
