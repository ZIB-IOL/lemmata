module

public import Lemmata.LPHardnessInP.Parity.Main
public import Lemmata.LPHardnessInP.RankReduction.Main
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

namespace Lemmata.LPHardnessInP.ParityExtension

open scoped BigOperators
open Lemmata.SpanningTreeMinSplit
open Lemmata.LPHardnessInP.Parity

/-- Add `d` pairs with left label one and right label zero. This changes
the total label parity by exactly `d`, as required at order `n+d`. -/
def padLabel {n : ℕ} (d : ℕ) (L : ParityLabel n) : ParityLabel (n + d) where
  left := Fin.addCases L.left (fun _ => true)
  right := Fin.addCases L.right (fun _ => false)
  label_parity := by
    simp only [Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right,
      show bit true = (1 : ZMod 2) from rfl, show bit false = (0 : ZMod 2) from rfl,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one, mul_zero, add_zero, Nat.cast_add]
    have h := L.label_parity
    linear_combination h

/-- Extend the old permutation by fixing the new pairs. -/
def padPermutation {n : ℕ} (d : ℕ) (σ : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin (n + d)) :=
  finSumFinEquiv.symm.trans
    ((Equiv.sumCongr σ (Equiv.refl (Fin d))).trans finSumFinEquiv)

@[simp] theorem padPermutation_old {n : ℕ} (d : ℕ) (σ : Equiv.Perm (Fin n))
    (i : Fin n) :
    padPermutation d σ (Fin.castAdd d i) = Fin.castAdd d (σ i) := by
  simp [padPermutation]

@[simp] theorem padPermutation_new {n : ℕ} (d : ℕ) (σ : Equiv.Perm (Fin n))
    (i : Fin d) :
    padPermutation d σ (Fin.natAdd n i) = Fin.natAdd n i := by
  simp [padPermutation]

/-- Add blue identity edges on the new pairs. The odd red count is unchanged. -/
def padMatching {n : ℕ} (d : ℕ) (M : ParityMatching n) : ParityMatching (n + d) where
  perm := padPermutation d M.perm
  red := Fin.addCases M.red (fun _ => false)
  odd_red := by
    rw [Fin.sum_univ_add]
    simp only [Fin.addCases_left, Fin.addCases_right,
      show bit false = (0 : ZMod 2) from rfl, Finset.sum_const_zero, add_zero]
    exact M.odd_red

@[simp] theorem padLabel_left_old {n : ℕ} (d : ℕ) (L : ParityLabel n) (i : Fin n) :
    (padLabel d L).left (Fin.castAdd d i) = L.left i := by
  simp [padLabel]

@[simp] theorem padLabel_right_old {n : ℕ} (d : ℕ) (L : ParityLabel n) (i : Fin n) :
    (padLabel d L).right (Fin.castAdd d i) = L.right i := by
  simp [padLabel]

@[simp] theorem padLabel_left_new {n : ℕ} (d : ℕ) (L : ParityLabel n) (i : Fin d) :
    (padLabel d L).left (Fin.natAdd n i) = true := by
  simp [padLabel]

@[simp] theorem padLabel_right_new {n : ℕ} (d : ℕ) (L : ParityLabel n) (i : Fin d) :
    (padLabel d L).right (Fin.natAdd n i) = false := by
  simp [padLabel]

@[simp] theorem padMatching_red_old {n : ℕ} (d : ℕ) (M : ParityMatching n)
    (i : Fin n) :
    (padMatching d M).red (Fin.castAdd d i) = M.red i := by
  simp [padMatching]

@[simp] theorem padMatching_red_new {n : ℕ} (d : ℕ) (M : ParityMatching n)
    (i : Fin d) :
    (padMatching d M).red (Fin.natAdd n i) = false := by
  simp [padMatching]

theorem padding_old_violates {n : ℕ} (d : ℕ) (L : ParityLabel n)
    (M : ParityMatching n) (i : Fin n) :
    Violates (padLabel d L) (Fin.castAdd d i)
        ((padMatching d M).perm (Fin.castAdd d i))
        ((padMatching d M).red (Fin.castAdd d i)) ↔
      Violates L i (M.perm i) (M.red i) := by
  simp [Violates, padMatching]

theorem padding_new_nonviolating {n : ℕ} (d : ℕ) (L : ParityLabel n)
    (M : ParityMatching n) (i : Fin d) :
    ¬ Violates (padLabel d L) (Fin.natAdd n i)
        ((padMatching d M).perm (Fin.natAdd n i))
        ((padMatching d M).red (Fin.natAdd n i)) := by
  simp [Violates, padMatching]

-- DOCS_BEGIN_MAIN
/-- Independent padding of labelings and matchings preserves the exact
violation count. This applies also to zero added pairs. -/
theorem padding_violationCount {n : ℕ} (d : ℕ)
    (L : ParityLabel n) (M : ParityMatching n) :
    violationCount (padLabel d L) (padMatching d M) = violationCount L M := by
  unfold violationCount
  rw [Fin.sum_univ_add]
  simp only [padding_old_violates, padding_new_nonviolating, ite_false,
    Finset.sum_const_zero, add_zero]

/-- The shifted parity matrix at order `n` is a pullback of that at order
`n+d` under independent row and column padding maps. -/
theorem shifted_rank_mono_add (n d : ℕ) (r : ℝ) :
    nonnegativeRank
        (fun (L : ParityLabel n) (M : ParityMatching n) => (violationCount L M : ℝ) - r) ≤
      nonnegativeRank
        (fun (L : ParityLabel (n + d)) (M : ParityMatching (n + d)) =>
          (violationCount L M : ℝ) - r) := by
  have h := Lemmata.LPHardnessInP.RankReduction.rank_pullback_le
    (T := fun (L : ParityLabel (n + d)) (M : ParityMatching (n + d)) =>
      (violationCount L M : ℝ) - r) (padLabel d) (padMatching d)
  simpa only [padding_violationCount] using h

/-- Consequently the shifted parity nonnegative rank is monotone in the
number of vertices in each bipartition class. -/
theorem shifted_rank_mono {n N : ℕ} (horder : n ≤ N) (r : ℝ) :
    nonnegativeRank
        (fun (L : ParityLabel n) (M : ParityMatching n) => (violationCount L M : ℝ) - r) ≤
      nonnegativeRank
        (fun (L : ParityLabel N) (M : ParityMatching N) => (violationCount L M : ℝ) - r) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le horder
  exact shifted_rank_mono_add n d r
-- DOCS_END_MAIN

end Lemmata.LPHardnessInP.ParityExtension
