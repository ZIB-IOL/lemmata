module

public import Lemmata.SpanningTreeMinSplit.Trees
public import Lemmata.SpanningTreeMinSplit.Certificates
public import Lemmata.SpanningTreeMinSplit.Rank
public import Mathlib.Tactic.Positivity

@[expose] public section

namespace Lemmata.SpanningTreeMinSplit

open scoped BigOperators Classical
noncomputable section

/-- Proper subtour rows of size at least two. -/
abbrev Subtour (n : ℕ) := {S : Finset (Fin n) // 2 ≤ S.card ∧ S.card < n}

/-- Each unordered edge has its unique increasing pair of endpoints. -/
abbrev Edge (n : ℕ) := {e : Fin n × Fin n // e.1 < e.2}

/-- The full standard slack matrix has both subtour and nonnegativity rows. -/
abbrev Row (n : ℕ) := Subtour n ⊕ Edge n

/-- Actual graph slacks; the cardinality equation is not a slack row. -/
def fullSlack (n : ℕ) : Row n → Tree n → ℝ
  | .inl S, T => subtourSlack T S.val
  | .inr e, T => if T.val.Adj e.val.1 e.val.2 then 1 else 0

theorem subtour_nonempty {n : ℕ} (S : Subtour n) : S.val.Nonempty :=
  Finset.card_pos.mp (lt_of_lt_of_le (by decide : 0 < 2) S.property.1)

variable {n : ℕ} [NeZero n]

/-- Root-zero diagonal slots were zero in the original subtour factorization. -/
def Reused (c : Cert n) : Prop := c.1 = 0 ∧ c.2.2.val = c.2.1.val

/-- These slots now store actual incidences of edges incident to zero. -/
def columnFactor (c : Cert n) (T : Tree n) : ℝ :=
  if Reused c then (if T.val.Adj 0 c.2.1.val then 1 else 0)
  else parentFactor c (parent T c.1)

/-- The repurposed slots have zero coefficients on every subtour row. -/
def subtourFactor (c : Cert n) (S : Finset (Fin n)) (hS : S.Nonempty) : ℝ :=
  if Reused c then 0 else rowFactor c S hS

theorem subtour_product (c : Cert n) (T : Tree n)
    (S : Finset (Fin n)) (hS : S.Nonempty) :
    subtourFactor c S hS * columnFactor c T =
      rowFactor c S hS * parentFactor c (parent T c.1) := by
  by_cases hc : Reused c
  · have hz : parentFactor c (parent T c.1) = 0 := by
      rcases hc with ⟨hr, hw⟩
      simp [parentFactor, ColFires, hw, hr]
    simp [subtourFactor, hc, hz]
  · simp [subtourFactor, columnFactor, hc]

theorem subtour_factorization (T : Tree n) (S : Finset (Fin n)) (hS : S.Nonempty) :
    subtourSlack T S = ∑ c : Cert n, subtourFactor c S hS * columnFactor c T := by
  rw [subtourSlack_eq_splits T S (S.min' hS) (S.min'_mem hS),
    split_sum_eq_factors S hS (parent T)]
  exact Finset.sum_congr rfl (fun c _ => (subtour_product c T S hS).symm)

/-- A root-zero slot, with its two positive markers. -/
def zeroCert (a b : Fin n) (ha : 0 < a) (hb : 0 < b) : Cert n :=
  ⟨0, ⟨⟨a, ha⟩, ⟨b, hb⟩⟩⟩

theorem columnFactor_diagonal (v : Fin n) (hv : 0 < v) (T : Tree n) :
    columnFactor (zeroCert v v hv hv) T = if T.val.Adj 0 v then 1 else 0 := by
  by_cases h : T.val.Adj 0 v <;> simp [columnFactor, Reused, zeroCert, h]

theorem columnFactor_offDiagonal (a b : Fin n) (ha : 0 < a) (hb : 0 < b)
    (hab : a ≠ b) (T : Tree n) :
    columnFactor (zeroCert a b ha hb) T = if parent T 0 a = b then 1 else 0 := by
  simp [columnFactor, Reused, zeroCert, parentFactor, ColFires, Ne.symm hab]

/-- An edge at zero uses a repurposed diagonal slot. Other edges use the two
existing root-zero orientation slots, never new factors. -/
def edgeFactor (e : Edge n) (c : Cert n) : ℝ :=
  if ha : e.val.1 = 0 then
    if c = zeroCert e.val.2 e.val.2
      (lt_of_le_of_lt (Fin.zero_le _) e.property)
      (lt_of_le_of_lt (Fin.zero_le _) e.property) then 1 else 0
  else
    (if c = zeroCert e.val.1 e.val.2
      (lt_of_le_of_ne (Fin.zero_le _) (Ne.symm ha))
      (lt_of_le_of_lt (Fin.zero_le _) e.property) then 1 else 0) +
    (if c = zeroCert e.val.2 e.val.1
      (lt_of_le_of_lt (Fin.zero_le _) e.property)
      (lt_of_le_of_ne (Fin.zero_le _) (Ne.symm ha)) then 1 else 0)

theorem edge_factorization (e : Edge n) (T : Tree n) :
    (if T.val.Adj e.val.1 e.val.2 then (1 : ℝ) else 0) =
      ∑ c : Cert n, edgeFactor e c * columnFactor c T := by
  by_cases ha : e.val.1 = 0
  · simp [edgeFactor, ha, ite_mul, columnFactor_diagonal]
  · have hb : e.val.2 ≠ 0 := ne_of_gt (lt_of_le_of_lt (Fin.zero_le _) e.property)
    simp only [edgeFactor, dite_eq_right ha, add_mul, Finset.sum_add_distrib, ite_mul,
      one_mul, zero_mul]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [columnFactor_offDiagonal _ _ _ _ (ne_of_lt e.property),
      columnFactor_offDiagonal _ _ _ _ (ne_of_gt e.property)]
    exact edge_orientation T 0 e.val.1 e.val.2 ha hb (ne_of_lt e.property)

/-- The row factor for the full matrix. -/
def fullRowFactor (c : Cert n) : Row n → ℝ
  | .inl S => subtourFactor c S.val (subtour_nonempty S)
  | .inr e => edgeFactor e c

theorem columnFactor_nonneg (c : Cert n) (T : Tree n) : 0 ≤ columnFactor c T := by
  unfold columnFactor parentFactor
  split_ifs <;> norm_num

theorem fullRowFactor_nonneg (c : Cert n) (R : Row n) : 0 ≤ fullRowFactor c R := by
  cases R with
  | inl S =>
    simp only [fullRowFactor, subtourFactor, rowFactor]
    split_ifs <;> norm_num
  | inr e =>
    simp only [fullRowFactor, edgeFactor]
    split_ifs <;> norm_num

/-- Entrywise exactness includes the nonnegativity rows. -/
theorem fullSlack_eq_sum (R : Row n) (T : Tree n) :
    fullSlack n R T = ∑ c : Cert n, fullRowFactor c R * columnFactor c T := by
  cases R with
  | inl S => exact subtour_factorization T S.val (subtour_nonempty S)
  | inr e => exact edge_factorization e T

/-- An explicit factorization indexed by the square certificates, including
all edge rows with no increase in the number of factors. -/
def fullFactorization : NonnegativeFactorization (fullSlack n) (Fintype.card (Cert n)) where
  left l R := fullRowFactor ((Fintype.equivFin (Cert n)).symm l) R
  right l T := columnFactor ((Fintype.equivFin (Cert n)).symm l) T
  left_nonneg l R := fullRowFactor_nonneg _ R
  right_nonneg l T := columnFactor_nonneg _ T
  reconstruct R T := by
    rw [fullSlack_eq_sum]
    exact (Fintype.sum_bijective ((Fintype.equivFin (Cert n)).symm)
      (Equiv.bijective _) _ _ (fun _ => rfl)).symm

end
end Lemmata.SpanningTreeMinSplit
