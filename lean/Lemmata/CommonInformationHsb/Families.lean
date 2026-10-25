module

public import Mathlib.Algebra.BigOperators.Option
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Positivity

@[expose] public section

noncomputable section

namespace Lemmata.CommonInformationHsb

open scoped BigOperators

/-- The diagonal matrix with prescribed (possibly zero) diagonal weights. -/
def diagonalMatrix {I : Type*} [DecidableEq I] (p : I → ℝ) (i j : I) : ℝ :=
  if i = j then p i else 0

/-- One heavy atom and `N` equally weighted light atoms. -/
def heavyProbability (N : ℕ) : Option (Fin N) → ℝ
  | none => 1 / 2
  | some _ => 1 / (2 * (N : ℝ))

/-- A diagonal distribution with one half of its mass on a single atom. -/
def heavyDiagonal (N : ℕ) : Option (Fin N) → Option (Fin N) → ℝ :=
  diagonalMatrix (heavyProbability N)

/-- The large block has label `none`; each singleton has its own label. -/
def blockLabel {S r : ℕ} : Fin S ⊕ Fin r → Option (Fin r)
  | .inl _ => none
  | .inr j => some j

/-- One all-ones `S × S` block and `r` singleton blocks. -/
def blockMatrix (S r : ℕ) (i j : Fin S ⊕ Fin r) : ℝ :=
  if blockLabel i = blockLabel j then 1 else 0

@[simp] theorem diagonalMatrix_self {I : Type*} [DecidableEq I] (p : I → ℝ) (i : I) :
    diagonalMatrix p i i = p i := by simp [diagonalMatrix]

@[simp] theorem diagonalMatrix_ne {I : Type*} [DecidableEq I] (p : I → ℝ)
    {i j : I} (h : i ≠ j) : diagonalMatrix p i j = 0 := by simp [diagonalMatrix, h]

theorem diagonalMatrix_nonneg {I : Type*} [DecidableEq I] {p : I → ℝ}
    (hp : ∀ i, 0 ≤ p i) (i j : I) : 0 ≤ diagonalMatrix p i j := by
  unfold diagonalMatrix
  split_ifs <;> simp_all

theorem heavyProbability_nonneg (N : ℕ) (i : Option (Fin N)) :
    0 ≤ heavyProbability N i := by
  cases i <;> simp only [heavyProbability] <;> positivity

@[simp] theorem blockMatrix_inl_inl (S r : ℕ) (i j : Fin S) :
    blockMatrix S r (.inl i) (.inl j) = 1 := by simp [blockMatrix, blockLabel]

@[simp] theorem blockMatrix_inl_inr (S r : ℕ) (i : Fin S) (j : Fin r) :
    blockMatrix S r (.inl i) (.inr j) = 0 := by simp [blockMatrix, blockLabel]

@[simp] theorem blockMatrix_inr_inl (S r : ℕ) (i : Fin r) (j : Fin S) :
    blockMatrix S r (.inr i) (.inl j) = 0 := by simp [blockMatrix, blockLabel]

@[simp] theorem blockMatrix_inr_inr (S r : ℕ) (i j : Fin r) :
    blockMatrix S r (.inr i) (.inr j) = if i = j then 1 else 0 := by
  simp [blockMatrix, blockLabel]

theorem blockMatrix_nonneg (S r : ℕ) (i j : Fin S ⊕ Fin r) :
    0 ≤ blockMatrix S r i j := by
  unfold blockMatrix
  split_ifs <;> norm_num

end Lemmata.CommonInformationHsb
