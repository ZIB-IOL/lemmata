module

public import Lemmata.TensorRank.Proof.PolynomialProduct
public import Lemmata.TensorRank.Proof.Parties
public import Mathlib.Logic.Equiv.Bool

@[expose] public section

set_option autoImplicit false

open scoped BigOperators
open Classical

noncomputable section

namespace Lemmata.TensorRank.PolynomialProduct

variable {J : Type*} [Fintype J]

def tripleWeight (a : J → ℕ) (b : ℕ) (p : Bool ⊕ J) :
    SelectedCoordinate a (3 * b + degree a) p → ℕ :=
  match p with
  | .inl false => fun y => if inputLabel a b y = 1 then 1 else 0
  | .inl true => fun z => if outputLabel a b z = 1 then 0 else 1
  | .inr _ => fun _ => 0

def tripleKernel (a : J → ℕ) (b : ℕ) (p : Bool ⊕ J)
    (y v : SelectedCoordinate a (3 * b + degree a) p) : Polynomial ℂ :=
  Polynomial.X ^ tripleWeight a b p y * if v = y then 1 else 0

private theorem diagonal_polynomialMap {I : Type*} [Fintype I] {V : I → Type*}
    [∀ i, Fintype (V i)] (T : Tensor ℂ I V) (w : ∀ i, V i → ℕ) (x : ∀ i, V i) :
    Tensor.polynomialMap
      (fun i y v => Polynomial.X ^ w i y * if v = y then 1 else 0) T x =
        Polynomial.X ^ (∑ i, w i (x i)) * Polynomial.C (T x) := by
  have hs := congrFun (Tensor.localMap_select (fun _ => id) (fun v => Polynomial.C (T v))) x
  simp only [Tensor.localMap, Tensor.reindex, id_eq] at hs
  simp only [Tensor.polynomialMap, Tensor.localMap, Finset.prod_mul_distrib]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, hs, Finset.prod_pow_eq_pow_sum]

private theorem triple_weight_support (a : J → ℕ) (b : ℕ)
    (x : ∀ p, SelectedCoordinate a (3 * b + degree a) p)
    (hx : (x (.inl false)).val + (∑ j, (x (.inr j)).val) = (x (.inl true)).val) :
    1 ≤ (∑ p, tripleWeight a b p (x p)) ∧
      ((∑ p, tripleWeight a b p (x p)) = 1 ↔
        inputLabel a b (x (.inl false)) = outputLabel a b (x (.inl true))) := by
  have hs := input_sum_le a (fun j => x (.inr j))
  simp only [Fintype.sum_sum_type, Fintype.sum_bool, tripleWeight,
    Finset.sum_const_zero, add_zero]
  unfold inputLabel outputLabel
  split_ifs <;> norm_num at * <;> omega

theorem sum_tripleSector (a : J → ℕ) (b : ℕ)
    (x : ∀ p, SelectedCoordinate a (3 * b + degree a) p) :
    (∑ q : Fin 3, tripleSector a b q) x =
      if inputLabel a b (x (.inl false)) = outputLabel a b (x (.inl true))
        then selected a (3 * b + degree a) x else 0 := by
  by_cases h : inputLabel a b (x (.inl false)) = outputLabel a b (x (.inl true))
  · simp only [Finset.sum_apply, tripleSector, ← h, and_self, ite_true]
    simp
  · rw [ite_eq_right h]
    simp only [Finset.sum_apply, tripleSector]
    apply Finset.sum_eq_zero
    intro q _
    apply ite_eq_right
    exact fun hq => h (hq.1.trans hq.2.symm)

theorem triple_leading (a : J → ℕ) (b : ℕ) :
    Tensor.Leading (Tensor.polynomialMap (tripleKernel a b) (selected a (3 * b + degree a)))
      1 (∑ q : Fin 3, tripleSector a b q) := by
  have hv (x : ∀ p, SelectedCoordinate a (3 * b + degree a) p) :=
    diagonal_polynomialMap (selected a (3 * b + degree a)) (tripleWeight a b) x
  constructor
  · funext x
    change (Tensor.polynomialMap _ _ x).coeff 1 = _
    rw [show Tensor.polynomialMap (tripleKernel a b) _ x = _ from hv x, sum_tripleSector]
    by_cases hx : (x (.inl false)).val + (∑ j, (x (.inr j)).val) = (x (.inl true)).val
    · have hw := (triple_weight_support a b x hx).2
      simp only [selected, hx, ite_true, Polynomial.C_1, mul_one, Polynomial.coeff_X_pow]
      exact if_congr (eq_comm.trans hw) rfl rfl
    · simp only [selected, hx, ite_false, Polynomial.C_0, mul_zero, Polynomial.coeff_zero,
        ite_self]
  · intro d hd
    have hd0 : d = 0 := by omega
    subst d
    funext x
    change (Tensor.polynomialMap _ _ x).coeff 0 = 0
    rw [show Tensor.polynomialMap (tripleKernel a b) _ x = _ from hv x]
    by_cases hx : (x (.inl false)).val + (∑ j, (x (.inr j)).val) = (x (.inl true)).val
    · have hw := (triple_weight_support a b x hx).1
      simp only [selected, hx, ite_true, Polynomial.C_1, mul_one, Polynomial.coeff_X_pow]
      exact ite_eq_right (by omega)
    · simp only [selected, hx, ite_false, Polynomial.C_0, mul_zero, Polynomial.coeff_zero]

theorem triple_degenerates (a : J → ℕ) (b : ℕ) :
    Tensor.Degenerates (∑ q : Fin 3, tripleSector a b q) (selected a (3 * b + degree a)) :=
  ⟨tripleKernel a b, 1, triple_leading a b⟩

def leftEmbedding (a : J → ℕ) (b : ℕ) (p : Bool ⊕ J) :
    SelectedCoordinate a b p → SelectedCoordinate a (3 * b + degree a) p :=
  match p with
  | .inl false => fun y => ⟨y.val, by have := y.isLt; omega⟩
  | .inl true => fun z => ⟨z.val, by have := z.isLt; omega⟩
  | .inr _ => id

theorem leftSector_restricts (a : J → ℕ) (b : ℕ) :
    Tensor.Restricts (selected a b) (tripleSector a b 0) := by
  refine ⟨fun p y v => if v = leftEmbedding a b p y then 1 else 0, ?_⟩
  rw [Tensor.localMap_select]
  funext x
  have hy := (x (.inl false)).isLt
  have hz := (x (.inl true)).isLt
  have hl : inputLabel a b (leftEmbedding a b (.inl false) (x (.inl false))) = 0 := by
    change (if (x (.inl false)).val < b then 0 else
      if (x (.inl false)).val < 2 * b + degree a then 1 else 2) = 0
    exact ite_eq_left hy
  have hr : outputLabel a b (leftEmbedding a b (.inl true) (x (.inl true))) = 0 := by
    change (if (x (.inl true)).val < b + degree a then 0 else
      if (x (.inl true)).val < 2 * b + degree a then 1 else 2) = 0
    exact ite_eq_left hz
  change selected a b x = if _ = 0 ∧ _ = 0 then _ else 0
  rw [hl, hr]
  rfl

def rightEmbedding (a : J → ℕ) (b : ℕ) (p : Bool ⊕ J) :
    SelectedCoordinate a b p → SelectedCoordinate a (3 * b + degree a) p :=
  match p with
  | .inl false => fun y => ⟨2 * b + degree a + y.val, by have := y.isLt; omega⟩
  | .inl true => fun z => ⟨2 * b + degree a + z.val, by have := z.isLt; omega⟩
  | .inr _ => id

theorem rightSector_restricts (a : J → ℕ) (b : ℕ) :
    Tensor.Restricts (selected a b) (tripleSector a b 2) := by
  refine ⟨fun p y v => if v = rightEmbedding a b p y then 1 else 0, ?_⟩
  rw [Tensor.localMap_select]
  funext x
  have hl : inputLabel a b (rightEmbedding a b (.inl false) (x (.inl false))) = 2 := by
    change (if 2 * b + degree a + (x (.inl false)).val < b then 0 else
      if 2 * b + degree a + (x (.inl false)).val < 2 * b + degree a then 1 else 2) = 2
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  have hr : outputLabel a b (rightEmbedding a b (.inl true) (x (.inl true))) = 2 := by
    change (if 2 * b + degree a + (x (.inl true)).val < b + degree a then 0 else
      if 2 * b + degree a + (x (.inl true)).val < 2 * b + degree a then 1 else 2) = 2
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  change selected a b x = if _ = 2 ∧ _ = 2 then _ else 0
  rw [hl, hr]
  simp only [and_self, ite_true, selected, rightEmbedding, id_eq]
  congr 1
  apply propext
  omega

abbrev swapReaders : (Bool ⊕ J) ≃ (Bool ⊕ J) := Equiv.sumCongr Equiv.boolNot (Equiv.refl J)

def middleEmbedding (a : J → ℕ) (b : ℕ) (p : Bool ⊕ J) :
    SelectedCoordinate a b (swapReaders p) → SelectedCoordinate a (3 * b + degree a) p :=
  match p with
  | .inl false => fun y => ⟨b + y.val, by have := y.isLt; omega⟩
  | .inl true => fun z => ⟨b + degree a + z.val, by have := z.isLt; omega⟩
  | .inr _ => Fin.rev

theorem sum_reverse (a : J → ℕ) (x : ∀ j, Fin (a j)) :
    (∑ j, (Fin.rev (x j)).val) + (∑ j, (x j).val) = degree a := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  change (a j - (x j).val - 1) + (x j).val = a j - 1
  have := (x j).isLt
  omega

theorem middleSector_restricts (a : J → ℕ) (b : ℕ) :
    Tensor.Restricts (Tensor.relabel swapReaders (selected a b)) (tripleSector a b 1) := by
  refine ⟨fun p y v => if v = middleEmbedding a b p y then 1 else 0, ?_⟩
  rw [Tensor.localMap_select]
  funext x
  have hy := (x (.inl false)).isLt
  have hz := (x (.inl true)).isLt
  have hs := sum_reverse a (fun j => x (.inr j))
  have hl : inputLabel a b (middleEmbedding a b (.inl false) (x (.inl false))) = 1 := by
    change (if b + (x (.inl false)).val < b then 0 else
      if b + (x (.inl false)).val < 2 * b + degree a then 1 else 2) = 1
    rw [ite_eq_right (by omega), ite_eq_left (by omega)]
  have hr : outputLabel a b (middleEmbedding a b (.inl true) (x (.inl true))) = 1 := by
    change (if b + degree a + (x (.inl true)).val < b + degree a then 0 else
      if b + degree a + (x (.inl true)).val < 2 * b + degree a then 1 else 2) = 1
    rw [ite_eq_right (by omega), ite_eq_left (by omega)]
  change Tensor.relabel swapReaders (selected a b) x = if _ = 1 ∧ _ = 1 then _ else 0
  rw [hl, hr]
  simp only [and_self, ite_true, selected, Tensor.relabel, Equiv.piCongrLeft_apply, middleEmbedding]
  congr 1
  change ((x (.inl true)).val + (∑ j, (x (.inr j)).val) = (x (.inl false)).val) =
    (b + (x (.inl false)).val + (∑ j, (Fin.rev (x (.inr j))).val) =
      b + degree a + (x (.inl true)).val)
  apply propext
  dsimp only [Fin.rev, Equiv.refl_apply] at hs ⊢
  omega

end Lemmata.TensorRank.PolynomialProduct
