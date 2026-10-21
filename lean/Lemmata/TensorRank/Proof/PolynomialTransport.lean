module

public import Lemmata.TensorRank.Proof.PolynomialProduct
public import Lemmata.TensorRank.Proof.Parties
public import Mathlib.Logic.Equiv.Option

@[expose] public section

set_option autoImplicit false

open scoped BigOperators
open Classical

noncomputable section

namespace Lemmata.TensorRank.PolynomialProduct

variable {J : Type*}

abbrev Other (j : J) := {i : J // i ≠ j}

def remaining (a : J → ℕ) (j : J) : Other j → ℕ := fun i => a i.val

abbrev inputPartyEquiv (j : J) : (Bool ⊕ Other j) ≃ Option J where
  toFun
    | .inl false => some j
    | .inl true => none
    | .inr i => some i.val
  invFun
    | none => .inl true
    | some i => if h : i = j then .inl false else .inr ⟨i, h⟩
  left_inv := by
    intro p
    rcases p with q | i
    · cases q <;> simp
    · simp [i.property]
  right_inv := by
    intro p
    cases p with
    | none => rfl
    | some i => by_cases h : i = j <;> simp [h]

@[simp] theorem inputPartyEquiv_false (j : J) : inputPartyEquiv j (.inl false) = some j := rfl
@[simp] theorem inputPartyEquiv_true (j : J) : inputPartyEquiv j (.inl true) = none := rfl
@[simp] theorem inputPartyEquiv_other (j : J) (i : Other j) :
    inputPartyEquiv j (.inr i) = some i.val := rfl

@[simp] theorem inputPartyEquiv_symm_none (j : J) : (inputPartyEquiv j).symm none = .inl true := rfl
@[simp] theorem inputPartyEquiv_symm_self (j : J) :
    (inputPartyEquiv j).symm (some j) = .inl false :=
  (inputPartyEquiv j).symm_apply_apply (.inl false)

@[simp] theorem inputPartyEquiv_symm_other (j : J) (i : Other j) :
    (inputPartyEquiv j).symm (some i.val) = .inr i :=
  (inputPartyEquiv j).symm_apply_apply (.inr i)

variable [Fintype J]

theorem degree_remaining (a : J → ℕ) (j : J) : degree a = a j - 1 + degree (remaining a j) := by
  simpa only [degree, remaining, Fintype.sum_option, Equiv.optionSubtypeNe_none,
    Equiv.optionSubtypeNe_some] using
      ((Equiv.optionSubtypeNe j).sum_comp (fun i => a i - 1)).symm

def inputCoordinateEquiv (a : J → ℕ) (j : J) (hj : 0 < a j) (p : Bool ⊕ Other j) :
    SelectedCoordinate (remaining a j) (a j) p ≃ Coordinate a (inputPartyEquiv j p) :=
  match p with
  | .inl false => Equiv.refl _
  | .inl true => finCongr (by have := degree_remaining a j; omega)
  | .inr _ => Equiv.refl _

theorem selected_relabel_tensor (a : J → ℕ) (j : J) (hj : 0 < a j) :
    Tensor.reindex (fun p => inputCoordinateEquiv a j hj p)
      (Tensor.relabel (inputPartyEquiv j) (tensor a)) = selected (remaining a j) (a j) := by
  funext x
  let y : ∀ p, Coordinate a p := Equiv.piCongrLeft (Coordinate a) (inputPartyEquiv j)
    (fun p => inputCoordinateEquiv a j hj p (x p))
  have hy₀ : (y (some j)).val = (x (.inl false)).val := by
    change ((Equiv.piCongrLeft (Coordinate a) (inputPartyEquiv j)
      (fun p => inputCoordinateEquiv a j hj p (x p))) (inputPartyEquiv j (.inl false))).val = _
    rw [Equiv.piCongrLeft_apply_apply]
    rfl
  have hyᵢ (i : Other j) : (y (some i.val)).val = (x (.inr i)).val := by
    change ((Equiv.piCongrLeft (Coordinate a) (inputPartyEquiv j)
      (fun p => inputCoordinateEquiv a j hj p (x p))) (inputPartyEquiv j (.inr i))).val = _
    rw [Equiv.piCongrLeft_apply_apply]
    rfl
  have hs : (∑ i, (y (some i)).val) = (x (.inl false)).val + (∑ i, (x (.inr i)).val) := by
    rw [← (Equiv.optionSubtypeNe j).sum_comp (fun i => (y (some i)).val), Fintype.sum_option]
    simp only [Equiv.optionSubtypeNe_none, Equiv.optionSubtypeNe_some, hy₀, hyᵢ]
  have hz : (y none).val = (x (.inl true)).val := by
    change ((Equiv.piCongrLeft (Coordinate a) (inputPartyEquiv j)
      (fun p => inputCoordinateEquiv a j hj p (x p))) (inputPartyEquiv j (.inl true))).val = _
    rw [Equiv.piCongrLeft_apply_apply]
    rfl
  change (if (∑ i, (y (some i)).val) = (y none).val then (1 : ℂ) else 0) = _
  rw [hs, hz]
  rfl

theorem selected_restricts_relabel_tensor (a : J → ℕ) (j : J) (hj : 0 < a j) :
    Tensor.Restricts (selected (remaining a j) (a j))
      (Tensor.relabel (inputPartyEquiv j) (tensor a)) := by
  rw [← selected_relabel_tensor a j hj]
  exact Tensor.reindex_restricts _ _

theorem relabel_tensor_restricts_selected (a : J → ℕ) (j : J) (hj : 0 < a j) :
    Tensor.Restricts (Tensor.relabel (inputPartyEquiv j) (tensor a))
      (selected (remaining a j) (a j)) := by
  have h := Tensor.reindex_restricts (fun p => (inputCoordinateEquiv a j hj p).symm)
    (selected (remaining a j) (a j))
  convert h using 1
  rw [← selected_relabel_tensor a j hj]
  funext x
  simp only [Tensor.reindex, Equiv.apply_symm_apply]

end Lemmata.TensorRank.PolynomialProduct
