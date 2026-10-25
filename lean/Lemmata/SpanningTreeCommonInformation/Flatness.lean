module

public import Lemmata.SpanningTreeMinSplit.Main

@[expose] public section

namespace Lemmata.SpanningTreeCommonInformation

open Lemmata.SpanningTreeMinSplit
open scoped BigOperators Classical
noncomputable section

variable {n : ℕ} [NeZero n]

/-- The two orientation certificates of a genuine edge are distinct. -/
theorem zeroCert_ne_reverse (a b : Fin n) (ha : 0 < a) (hb : 0 < b)
    (hab : a ≠ b) : zeroCert a b ha hb ≠ zeroCert b a hb ha := by
  intro h
  exact hab (congrArg (fun c : Cert n => c.2.1.val) h)

/-- Each column factor is an indicator, including the reused diagonal slots. -/
theorem columnFactor_zero_or_one (c : Cert n) (T : Tree n) :
    columnFactor c T = 0 ∨ columnFactor c T = 1 := by
  unfold columnFactor parentFactor
  split_ifs <;> simp

/-- Distinct endpoints prevent both orientation summands from firing. -/
theorem edgeFactor_zero_or_one (e : Edge n) (c : Cert n) :
    edgeFactor e c = 0 ∨ edgeFactor e c = 1 := by
  unfold edgeFactor
  split_ifs with ha h₁ h₂ h₃
  all_goals try simp
  have h := h₂.symm.trans h₃
  exact (zeroCert_ne_reverse _ _ _ _ (ne_of_lt e.property) h).elim

/-- Every full row factor is an indicator, not just nonnegative. -/
theorem fullRowFactor_zero_or_one (c : Cert n) (R : Row n) :
    fullRowFactor c R = 0 ∨ fullRowFactor c R = 1 := by
  cases R with
  | inl S =>
    simp only [fullRowFactor, subtourFactor, rowFactor]
    split_ifs <;> simp
  | inr e => exact edgeFactor_zero_or_one e c

/-- Boolean left witnesses on precisely the published certificate type. -/
def rowWitness (c : Cert n) (R : Row n) : Bool := decide (fullRowFactor c R = 1)

/-- Boolean right witnesses on precisely the published certificate type. -/
def columnWitness (c : Cert n) (T : Tree n) : Bool := decide (columnFactor c T = 1)

theorem fullRowFactor_eq_indicator (c : Cert n) (R : Row n) :
    fullRowFactor c R = if rowWitness c R then 1 else 0 := by
  rcases fullRowFactor_zero_or_one c R with h | h <;> simp [rowWitness, h]

theorem columnFactor_eq_indicator (c : Cert n) (T : Tree n) :
    columnFactor c T = if columnWitness c T then 1 else 0 := by
  rcases columnFactor_zero_or_one c T with h | h <;> simp [columnWitness, h]

/-- Unit Boolean rectangles reconstruct the actual full slack matrix without
adding or deleting any certificate slot. -/
theorem fullSlack_boolean_rectangles (R : Row n) (T : Tree n) :
    fullSlack n R T = ∑ c : Cert n,
      (if rowWitness c R then (1 : ℝ) else 0) *
      (if columnWitness c T then (1 : ℝ) else 0) := by
  rw [fullSlack_eq_sum]
  exact Finset.sum_congr rfl (fun c _ => by
    rw [← fullRowFactor_eq_indicator, ← columnFactor_eq_indicator])

/-- Restricting the same Boolean rectangles to subtour rows adds no factors. -/
theorem subtourSlack_boolean_rectangles (S : Subtour n) (T : Tree n) :
    subtourSlack T S.val = ∑ c : Cert n,
      (if rowWitness c (.inl S) then (1 : ℝ) else 0) *
      (if columnWitness c T then (1 : ℝ) else 0) :=
  fullSlack_boolean_rectangles (.inl S) T

end
end Lemmata.SpanningTreeCommonInformation
