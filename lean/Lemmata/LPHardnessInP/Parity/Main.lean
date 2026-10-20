module

public import Lemmata.LPHardnessInP.Parity.Statement
public import Lemmata.LPHardnessInP.CostTransfer.Main
public import Lemmata.LPHardnessInP.Formulation.Main
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.LinearCombination

@[expose] public section

namespace Lemmata.LPHardnessInP.Parity

open scoped BigOperators

/-- The local parity identity for an edge, proved for all eight bit triples. -/
theorem violation_bit_formula (x y red : Bool) :
    ((if (if red then x ≠ y else x = y) then 1 else 0 : ℕ) : ZMod 2) =
      1 + bit red + bit x + bit y := by
  cases x <;> cases y <;> cases red <;> decide

theorem two_mul_zero (x : ZMod 2) : 2 * x = 0 := by
  have h : (2 : ZMod 2) = 0 := by decide
  rw [h, zero_mul]

/-- Every element of `ZMod 2` is represented by its Boolean equality-to-one
test. This is a finite, kernel-evaluated argument. -/
theorem bit_decide_eq_one (x : ZMod 2) : bit (decide (x = 1)) = x := by
  fin_cases x
  · change bit (decide ((0 : ZMod 2) = 1)) = 0
    decide
  · change bit (decide ((1 : ZMod 2) = 1)) = 1
    decide

/-- The total violation parity is the sum of the number of selected edges,
the red-edge parity, and both endpoint-label parities. -/
theorem violationCount_parity {n : ℕ} (L : ParityLabel n) (M : ParityMatching n) :
    (violationCount L M : ZMod 2) = 1 := by
  have hperm : ∑ i, bit (L.right (M.perm i)) = ∑ j, bit (L.right j) :=
    Equiv.sum_comp M.perm (fun j => bit (L.right j))
  have hcount : (violationCount L M : ZMod 2) =
      ∑ i, (1 + bit (M.red i) + bit (L.left i) + bit (L.right (M.perm i))) := by
    unfold violationCount
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact violation_bit_formula _ _ _
  rw [hcount]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, M.odd_red, hperm]
  have hlabel := L.label_parity
  have htwo := two_mul_zero (n : ZMod 2)
  linear_combination hlabel + htwo

-- DOCS_BEGIN_MAIN
/-- The structure's parity condition says that the ordinary natural-number
count of its red edges is odd. -/
theorem red_count_odd {n : ℕ} (M : ParityMatching n) :
    Odd (∑ i, if M.red i then 1 else 0 : ℕ) := by
  apply ZMod.natCast_eq_one_iff_odd.mp
  simpa only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, bit] using M.odd_red

/-- Every actual odd-red matching has an odd number of violations. -/
theorem violationCount_odd {n : ℕ} (L : ParityLabel n) (M : ParityMatching n) :
    Odd (violationCount L M) :=
  ZMod.natCast_eq_one_iff_odd.mp (violationCount_parity L M)

/-- In particular, every labeling row has violation count at least one. -/
theorem violationCount_pos {n : ℕ} (L : ParityLabel n) (M : ParityMatching n) :
    1 ≤ violationCount L M := by
  have h := violationCount_odd L M
  rw [Nat.odd_iff] at h
  omega

/-- Colors for the identity permutation that violate precisely at `i₀`. -/
def oneViolationRed {n : ℕ} (L : ParityLabel n) (i₀ : Fin n) (i : Fin n) : Bool :=
  decide ((1 + bit (L.left i) + bit (L.right i) +
    if i = i₀ then 1 else 0 : ZMod 2) = 1)

theorem oneViolationRed_parity {n : ℕ} (L : ParityLabel n) (i₀ : Fin n) :
    ∑ i, bit (oneViolationRed L i₀ i) = 1 := by
  simp only [oneViolationRed, bit_decide_eq_one, Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hlabel := L.label_parity
  have htwo := two_mul_zero (n : ZMod 2)
  linear_combination hlabel + htwo

/-- An actual odd-red perfect matching with a prescribed unique violation. -/
def oneViolationMatching {n : ℕ} (L : ParityLabel n) (i₀ : Fin n) :
    ParityMatching n where
  perm := Equiv.refl _
  red := oneViolationRed L i₀
  odd_red := oneViolationRed_parity L i₀

theorem oneViolationMatching_violates {n : ℕ} (L : ParityLabel n)
    (i₀ i : Fin n) :
    Violates L i ((oneViolationMatching L i₀).perm i)
      ((oneViolationMatching L i₀).red i) ↔ i = i₀ := by
  change (if oneViolationRed L i₀ i then L.left i ≠ L.right i
    else L.left i = L.right i) ↔ i = i₀
  by_cases hi : i = i₀
  · subst i
    cases hleft : L.left i₀ <;> cases hright : L.right i₀ <;>
      simp [oneViolationRed, bit, hleft, hright] <;> decide
  · cases hleft : L.left i <;> cases hright : L.right i <;>
      (simp [oneViolationRed, bit, hleft, hright, hi]; try decide)

theorem oneViolationMatching_count {n : ℕ} (L : ParityLabel n) (i₀ : Fin n) :
    violationCount L (oneViolationMatching L i₀) = 1 := by
  unfold violationCount
  simp only [oneViolationMatching_violates]
  simp

/-- Every labeling row attains exactly one violation when `n` is positive. -/
theorem exists_one_violation {n : ℕ} (hn : 0 < n) (L : ParityLabel n) :
    ∃ M : ParityMatching n, violationCount L M = 1 :=
  ⟨oneViolationMatching L ⟨0, hn⟩, oneViolationMatching_count L ⟨0, hn⟩⟩

/-- The concrete edge costs are strictly positive and have aspect ratio at
most `1 + γ` when the penalty is nonnegative. -/
theorem edgeCost_bounds {n : ℕ} (L : ParityLabel n) {γ : ℝ} (hγ : 0 ≤ γ)
    (i j : Fin n) (red : Bool) :
    1 ≤ edgeCost L γ i j red ∧ edgeCost L γ i j red ≤ 1 + γ := by
  unfold edgeCost
  split_ifs <;> constructor <;> linarith

/-- The actual selected-edge objective equals a fixed baseline plus a
penalty for every violation. -/
theorem matchingCost_eq {n : ℕ} (L : ParityLabel n) (γ : ℝ)
    (M : ParityMatching n) :
    matchingCost L γ M = (n : ℝ) + γ * (violationCount L M : ℝ) := by
  unfold matchingCost edgeCost violationCount
  rw [Nat.cast_sum, Finset.mul_sum, Finset.sum_add_distrib]
  congr 1
  · simp
  · apply Finset.sum_congr rfl
    intro i hi
    split_ifs <;> simp

/-- Each concrete labeling instance has optimum `n + γ`; no optimization
oracle or optimum equality is assumed. -/
theorem matchingCost_minimum {n : ℕ} (hn : 0 < n) (L : ParityLabel n)
    {γ : ℝ} (hγ : 0 ≤ γ) :
    (∀ M : ParityMatching n, (n : ℝ) + γ ≤ matchingCost L γ M) ∧
      (∃ M : ParityMatching n, matchingCost L γ M = (n : ℝ) + γ) := by
  constructor
  · intro M
    rw [matchingCost_eq]
    have hcount : (1 : ℝ) ≤ (violationCount L M : ℝ) := by
      exact_mod_cast violationCount_pos L M
    nlinarith
  · obtain ⟨M, hM⟩ := exists_one_violation hn L
    exact ⟨M, by rw [matchingCost_eq, hM]; simp⟩

/-- Conditional LP lower bound on the actual odd-red bipartite matching
domain. The sole rank-hardness input is the displayed shifted parity matrix
bound. A certified formulation supplies the affine Farkas data explicitly. -/
theorem parity_matching_lp_lower_bound
    {n m K : ℕ} {V : Type*} [AddCommGroup V] [Module ℝ V]
    (hn : 0 < n) (α : ℝ) (hα : 1 < α)
    (C : Lemmata.LPHardnessInP.Formulation.CertifiedLP (V := V)
      (fun (L : ParityLabel n) M => matchingCost L (2 * (α - 1) * n) M)
      (fun _ => ((n : ℝ) + 2 * (α - 1) * n) / α) m)
    (source_lower_bound : (K : ℕ∞) ≤ Lemmata.SpanningTreeMinSplit.nonnegativeRank
      (fun (L : ParityLabel n) (M : ParityMatching n) =>
        (violationCount L M : ℝ) - 1 / (2 * α))) :
    K ≤ m + 1 := by
  have F := Lemmata.LPHardnessInP.Formulation.certifiedSlackFactorization C
  apply Lemmata.LPHardnessInP.CostTransfer.positive_cost_lower_bound
    (fun (L : ParityLabel n) (M : ParityMatching n) => (violationCount L M : ℝ))
    α (n : ℝ) hα (by exact_mod_cast hn) source_lower_bound
  convert F using 1
  funext L M
  dsimp [Lemmata.LPHardnessInP.CostTransfer.costSlack]
  rw [matchingCost_eq]
  ring
-- DOCS_END_MAIN

end Lemmata.LPHardnessInP.Parity
