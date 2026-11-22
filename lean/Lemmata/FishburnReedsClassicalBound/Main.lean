module

public import Lemmata.FishburnReedsClassicalBound.Statement
public import Lemmata.FishburnReedsClassicalBound.Blocks
public import Lemmata.FishburnReedsClassicalBound.Comparison
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.SplitIfs

public section

namespace Lemmata.FishburnReedsClassicalBound

open scoped BigOperators

noncomputable section

variable {R K : Type*} [Fintype R] [Fintype K]

private theorem gram_factor (V : R → K → ℝ) (a b : R → ℝ) :
    gramScore V a b = ∑ k, coord V a k * coord V b k := by
  classical
  unfold gramScore coord
  calc
    _ = ∑ i, ∑ j, ∑ k, (a i * V i k) * (b j * V j k) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = ∑ i, ∑ k, ∑ j, (a i * V i k) * (b j * V j k) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ k, ∑ i, ∑ j, (a i * V i k) * (b j * V j k) := by rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]

private theorem gram_split (V : R → K → ℝ) (a b : R → ℝ) :
    gramScore V a b = energy V (mid a b) - energy V (halfDiff a b) := by
  classical
  rw [gram_factor]
  unfold energy
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  have ha : coord V a k = coord V (mid a b) k + coord V (halfDiff a b) k := by
    unfold coord
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    unfold mid halfDiff
    ring
  have hb : coord V b k = coord V (mid a b) k - coord V (halfDiff a b) k := by
    unfold coord
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    unfold mid halfDiff
    ring
  rw [ha, hb]
  ring

private theorem diagonal_split (a b : R → ℝ) (ha : Signs a) (hb : Signs b) :
    (∑ i, a i * b i) = 2 * agreements a b - (Fintype.card R : ℝ) := by
  classical
  calc
    _ = ∑ i, (2 * (if a i = b i then (1 : ℝ) else 0) - 1) := by
      apply Finset.sum_congr rfl
      intro i _
      rcases ha i with h | h <;> rcases hb i with g | g <;> rw [h, g] <;> norm_num
    _ = _ := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      simp [agreements]

private theorem tri_coord (d : ℕ) (k : Fin d) :
    coord (roots d) (fun _ => 1) k = 2 * (k.val : ℝ) := by
  classical
  have pair (i : Fin d) (j : Fin i.val) :
      (∑ b : Bool, roots d ⟨i, (j,b)⟩ k) =
        2 * (if k = i then (1 : ℝ) else 0) := by
    rw [Fintype.sum_bool]
    simp only [roots]
    split_ifs <;> first | contradiction | norm_num
  calc
    _ = ∑ i : Fin d, ∑ j : Fin i.val, ∑ b : Bool,
        roots d ⟨i, (j,b)⟩ k := by
      simp only [coord, Root, one_mul, Fintype.sum_sigma, Fintype.sum_prod_type]
    _ = ∑ i : Fin d, if k = i then 2 * (i.val : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      simp_rw [pair]
      by_cases hi : k = i <;> simp [hi, mul_comm]
    _ = _ := by simp

private theorem tri_linear_sum (d : ℕ) :
    (∑ i : Fin d, (2 : ℝ) * (i.val : ℝ)) = (d : ℝ)*((d : ℝ)-1) := by
  induction d with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    change (∑ i : Fin n, (2 : ℝ) * (i.val : ℝ)) + 2 * (n : ℝ) = _
    push_cast
    linear_combination ih

private theorem tri_square_sum (d : ℕ) :
    3 * (∑ i : Fin d, (2 * (i.val : ℝ))^2) =
      2 * (d : ℝ) * ((d : ℝ)-1) * (2*(d : ℝ)-1) := by
  induction d with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    change 3 * ((∑ i : Fin n, (2 * (i.val : ℝ))^2) + (2*(n : ℝ))^2) = _
    push_cast
    linear_combination ih

private theorem tri_card (d : ℕ) :
    (Fintype.card (Root d) : ℝ) = (d : ℝ)*((d : ℝ)-1) := by
  calc
    _ = ∑ i : Fin d, (2 : ℝ) * (i.val : ℝ) := by
      simp [Root, Fintype.card_sigma, Fintype.card_prod, Nat.cast_sum, mul_comm]
    _ = _ := tri_linear_sum d

-- DOCS_BEGIN_MAIN
/-- Midpoint and half-difference split the classical score exactly. -/
theorem root_sign_reduction (d : ℕ) (a b : Root d → ℝ)
    (ha : Signs a) (hb : Signs b) :
    value (roots d) a b = 4 * (Fintype.card (Root d) : ℝ) +
      3 * energy (roots d) (mid a b) - 8 * agreements a b -
      3 * energy (roots d) (halfDiff a b) := by
  unfold value
  rw [gram_split, diagonal_split a b ha hb]
  ring

/-- Evaluation of an explicit classical strategy in every order. -/
theorem allplus_value (d : ℕ) :
    value (roots d) (fun _ => 1) (fun _ => 1) =
      2 * (d : ℝ)*((d : ℝ)-1)*(2*(d : ℝ)-3) := by
  calc
    _ = 3 * (∑ k : Fin d, (2 * (k.val : ℝ))^2) -
        4 * (Fintype.card (Root d) : ℝ) := by
      rw [value, gram_factor]
      simp [tri_coord, pow_two]
    _ = _ := by rw [tri_square_sum, tri_card]; ring

/-- Attainment isolates the upper inequality as the outstanding matrix-level bridge. -/
theorem exact_of_upper (d : ℕ) (hu : FixedUpper d) : FixedClassicalValue d := by
  refine ⟨⟨(fun _ => 1), (fun _ => 1), ?_, ?_, allplus_value d⟩, ?_⟩
  · intro i
    exact Or.inl rfl
  · intro i
    exact Or.inl rfl
  · rintro _ ⟨a,b,ha,hb,rfl⟩
    exact hu a b ha hb
-- DOCS_END_MAIN

end
end Lemmata.FishburnReedsClassicalBound
