module

public import Lemmata.CocubicCovering.Proof.Quotient
public meta import Lemmata.CocubicCovering.Proof.Quotient
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

set_option Elab.async false

namespace Lemmata.CocubicCovering.CoveringCoordinates

open CoveringQuotient CoveringSymplectic

abbrev Label (y d z : ℕ) := Fin y ⊕ (Fin d × Fin z)

def labelEquiv (y d z : ℕ) : Label y d z ≃ Fin (y + d * z) :=
  (Equiv.sumCongr (Equiv.refl (Fin y)) finProdFinEquiv).trans finSumFinEquiv

def labelIndex {y d z : ℕ} (label : Label y d z) : ℕ :=
  (labelEquiv y d z label).val

theorem labelIndex_injective (y d z : ℕ) :
    Function.Injective (@labelIndex y d z) :=
  Fin.val_injective.comp (labelEquiv y d z).injective

@[simp] theorem labelIndex_inl {y d z : ℕ} (i : Fin y) :
    labelIndex (Sum.inl i : Label y d z) = i.val := rfl

@[simp] theorem labelIndex_inr {y d z : ℕ} (column : Fin d) (slot : Fin z) :
    labelIndex (Sum.inr (column, slot) : Label y d z) =
      y + column.val * z + slot.val := by
  change y + (slot.val + z * column.val) = _
  rw [Nat.mul_comm z column.val]
  omega

def zValue {r t : ℕ} (htr : t ≤ r) (point : Standard Field r)
    (slot : Fin (2 * r - t)) : Field :=
  if h : slot.val < t then point.1 ⟨slot.val, lt_of_lt_of_le h htr⟩ else
    let i : Fin r := ⟨t + (slot.val - t) / 2, by omega⟩
    if (slot.val - t) % 2 = 0 then point.1 i else point.2 i

def xLocal {r t : ℕ} (htr : t ≤ r) (i : Fin r) : Fin (2 * r - t) :=
  ⟨if i.val < t then i.val else t + 2 * (i.val - t), by
    split <;> omega⟩

def yLocal {r t : ℕ} (htr : t ≤ r) (i : Fin r) (hi : t ≤ i.val) :
    Fin (2 * r - t) := ⟨t + 2 * (i.val - t) + 1, by omega⟩

theorem zValue_xLocal {r t : ℕ} (htr : t ≤ r) (point : Standard Field r) (i : Fin r) :
    zValue htr point (xLocal htr i) = point.1 i := by
  by_cases hi : i.val < t
  · have hlt : (xLocal htr i).val < t := by simpa [xLocal, hi]
    simp only [zValue, dif_pos hlt]
    congr 1
    apply Fin.ext
    simp [xLocal, hi]
  · have hlt : ¬(xLocal htr i).val < t := by simp only [xLocal, if_neg hi]; omega
    have hindex : t + ((xLocal htr i).val - t) / 2 = i.val := by
      simp only [xLocal, if_neg hi]
      omega
    have hparity : ((xLocal htr i).val - t) % 2 = 0 := by
      simp only [xLocal, if_neg hi]
      omega
    simp only [zValue, dif_neg hlt, hparity, if_true]
    exact congrArg point.1 (Fin.ext hindex)

theorem zValue_yLocal {r t : ℕ} (htr : t ≤ r) (point : Standard Field r)
    (i : Fin r) (hi : t ≤ i.val) : zValue htr point (yLocal htr i hi) = point.2 i := by
  have hlt : ¬(yLocal htr i hi).val < t := by simp only [yLocal]; omega
  have hindex : t + ((yLocal htr i hi).val - t) / 2 = i.val := by
    simp only [yLocal]
    omega
  have hparity : ¬((yLocal htr i hi).val - t) % 2 = 0 := by
    simp only [yLocal]
    omega
  simp only [zValue, dif_neg hlt, if_neg hparity]
  exact congrArg point.2 (Fin.ext hindex)

def xPolynomial {y d r t : ℕ} (htr : t ≤ r) (column : Fin d) (i : Fin r) :
    Polynomial := variablePolynomial (labelIndex (Sum.inr (column, xLocal htr i) :
      Label y d (2 * r - t)))

def yPolynomial {y d r t : ℕ} (htr : t ≤ r)
    (forced : Fin t → Fin d → Polynomial) (column : Fin d) (i : Fin r) : Polynomial :=
  if hi : i.val < t then forced ⟨i.val, hi⟩ column else
    variablePolynomial (labelIndex (Sum.inr (column, yLocal htr i (by omega)) :
      Label y d (2 * r - t)))

theorem exists_coordinate_assignment {y d r t : ℕ} (htr : t ≤ r)
    (parameters : Fin y → Field) (points : Fin d → Standard Field r) :
    ∃ assignment : ℕ → Field,
      (∀ i : Fin y, assignment i.val = parameters i) ∧
      ∀ (column : Fin d) (slot : Fin (2 * r - t)),
        assignment (y + column.val * (2 * r - t) + slot.val) =
          zValue htr (points column) slot := by
  let values : Label y d (2 * r - t) → Field :=
    Sum.elim parameters (fun point => zValue htr (points point.1) point.2)
  obtain ⟨assignment, hassignment⟩ := exists_assignment_of_injective
    labelIndex (labelIndex_injective y d (2 * r - t)) values
  refine ⟨assignment, ?_, ?_⟩
  · intro i
    exact hassignment (Sum.inl i)
  · intro column slot
    simpa only [labelIndex_inr, values, Sum.elim_inr] using
      hassignment (Sum.inr (column, slot))

theorem eval_xPolynomial {y d r t : ℕ} (htr : t ≤ r)
    (assignment : ℕ → Field) (points : Fin d → Standard Field r)
    (hz : ∀ (column : Fin d) (slot : Fin (2 * r - t)),
      assignment (y + column.val * (2 * r - t) + slot.val) =
        zValue htr (points column) slot) (column : Fin d) (i : Fin r) :
    CoveringIdeal.eval assignment (xPolynomial (y := y) htr column i) =
      (points column).1 i := by
  rw [xPolynomial, eval_variable, labelIndex_inr, hz, zValue_xLocal]

theorem eval_yPolynomial {y d r t : ℕ} (htr : t ≤ r)
    (assignment : ℕ → Field) (points : Fin d → Standard Field r)
    (forced : Fin t → Fin d → Polynomial)
    (hforced : ∀ (i : Fin t) (column : Fin d),
      CoveringIdeal.eval assignment (forced i column) = (points column).2 (Fin.castLE htr i))
    (hz : ∀ (column : Fin d) (slot : Fin (2 * r - t)),
      assignment (y + column.val * (2 * r - t) + slot.val) =
        zValue htr (points column) slot) (column : Fin d) (i : Fin r) :
    CoveringIdeal.eval assignment (yPolynomial (y := y) htr forced column i) =
      (points column).2 i := by
  unfold yPolynomial
  split
  · rename_i hi
    exact hforced ⟨i.val, hi⟩ column
  · rw [eval_variable, labelIndex_inr, hz, zValue_yLocal]

end Lemmata.CocubicCovering.CoveringCoordinates
