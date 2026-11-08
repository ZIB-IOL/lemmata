module

public import Lemmata.RM59.Proof.CatalogForms
public import Lemmata.RM59.Proof.CubicAction
public import Lemmata.RM59.Proof.BinaryValues
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.FinCases

@[expose] public section

namespace Lemmata.RM59.CatalogContractions

open scoped BigOperators Matrix
open Packed CatalogCompute CatalogForms

def basisPoint (i : Fin 9) : Point 9 := Pi.single i 1

theorem point_sum_basis (x : Point 9) : (∑ i, x i • basisPoint i) = x := by
  simpa only [basisPoint, Pi.basisFun_repr, Pi.basisFun_apply] using
    (Pi.basisFun Field (Fin 9)).sum_repr x

def leftValueMap (T : CubicForm) (y z : Point 9) : Point 9 →ₗ[Field] Field :=
  T.toMultilinearMap.toLinearMap ![0, y, z] 0

def middleValueMap (T : CubicForm) (x z : Point 9) : Point 9 →ₗ[Field] Field :=
  T.toMultilinearMap.toLinearMap ![x, 0, z] 1

def rightValueMap (T : CubicForm) (x y : Point 9) : Point 9 →ₗ[Field] Field :=
  T.toMultilinearMap.toLinearMap ![x, y, 0] 2

@[simp] theorem leftValueMap_apply (T : CubicForm) (x y z : Point 9) :
    leftValueMap T y z x = cubicFormValue T x y z := by
  change T (Function.update ![0, y, z] 0 x) = T ![x, y, z]
  congr 1
  funext i
  fin_cases i <;> simp

@[simp] theorem middleValueMap_apply (T : CubicForm) (x y z : Point 9) :
    middleValueMap T x z y = cubicFormValue T x y z := by
  change T (Function.update ![x, 0, z] 1 y) = T ![x, y, z]
  congr 1
  funext i
  fin_cases i <;> simp

@[simp] theorem rightValueMap_apply (T : CubicForm) (x y z : Point 9) :
    rightValueMap T x y z = cubicFormValue T x y z := by
  change T (Function.update ![x, y, 0] 2 z) = T ![x, y, z]
  congr 1
  funext i
  fin_cases i <;> simp

def contractionPoint (T : CubicForm) (x y : Point 9) : Point 9 :=
  fun k => cubicFormValue T x y (basisPoint k)

def leftContractionMap (T : CubicForm) (y : Point 9) : Point 9 →ₗ[Field] Point 9 :=
  LinearMap.pi fun k => leftValueMap T y (basisPoint k)

def rightContractionMap (T : CubicForm) (x : Point 9) : Point 9 →ₗ[Field] Point 9 :=
  LinearMap.pi fun k => middleValueMap T x (basisPoint k)

@[simp] theorem leftContractionMap_apply (T : CubicForm) (x y : Point 9) :
    leftContractionMap T y x = contractionPoint T x y := by
  funext k
  exact leftValueMap_apply T x y (basisPoint k)

@[simp] theorem rightContractionMap_apply (T : CubicForm) (x y : Point 9) :
    rightContractionMap T x y = contractionPoint T x y := by
  funext k
  exact middleValueMap_apply T x y (basisPoint k)

theorem contraction_left_expansion (T : CubicForm) (x y : Point 9) :
    contractionPoint T x y = ∑ i, x i • contractionPoint T (basisPoint i) y := by
  calc
    contractionPoint T x y = leftContractionMap T y (∑ i, x i • basisPoint i) := by
      rw [point_sum_basis, leftContractionMap_apply]
    _ = _ := by simp only [map_sum, map_smul, leftContractionMap_apply]

theorem contraction_right_expansion (T : CubicForm) (x y : Point 9) :
    contractionPoint T x y = ∑ i, y i • contractionPoint T x (basisPoint i) := by
  calc
    contractionPoint T x y = rightContractionMap T x (∑ i, y i • basisPoint i) := by
      rw [point_sum_basis, rightContractionMap_apply]
    _ = _ := by simp only [map_sum, map_smul, rightContractionMap_apply]

theorem value_as_evaluation (T : CubicForm) (x y z : Point 9) :
    cubicFormValue T x y z = SupportForms.evaluation (contractionPoint T x y) z := by
  calc
    cubicFormValue T x y z = rightValueMap T x y (∑ i, z i • basisPoint i) := by
      rw [point_sum_basis, rightValueMap_apply]
    _ = _ := by
      simp only [map_sum, map_smul, smul_eq_mul, rightValueMap_apply]
      rfl

theorem contractionPoint_zero_iff (T : CubicForm) (x y : Point 9) :
    contractionPoint T x y = 0 ↔ ∀ z, cubicFormValue T x y z = 0 := by
  constructor
  · intro h z
    rw [value_as_evaluation, h]
    simp [SupportForms.evaluation]
  · intro h
    funext k
    exact h (basisPoint k)

theorem range_sum_eq {A : Type*} [AddCommMonoid A] (count : ℕ) (f : ℕ → A) :
    ((List.range count).map f).sum = ∑ i : Fin count, f i.val := by
  calc
    ((List.range count).map f).sum = ∑ i ∈ Finset.range count, f i := by
      simpa only [List.toFinset_range] using
        (List.sum_toFinset f (l := List.range count) List.nodup_range).symm
    _ = ∑ i : Fin count, f i.val := Finset.sum_range f

theorem selected_sum (x : PackedPoint) (rows : ℕ → Point 9) :
    ((List.range 9).map fun i => if x.val.testBit i then rows i else 0).sum =
      ∑ i : Fin 9, decodePoint x i • rows i.val := by
  rw [range_sum_eq]
  apply Finset.sum_congr rfl
  intro i _
  cases h : x.val.testBit i.val <;> simp [decodePoint, bitField, h]

def contractionRow (basis : Array (Array ℕ)) (x : PackedPoint) : Array ℕ :=
  (contractions basis 9)[x.val]?.getD #[]

@[simp] theorem contractionRow_size (basis : Array (Array ℕ)) (x : PackedPoint) :
    (contractionRow basis x).size = 9 := by
  simp [contractionRow, contractions, Array.getElem?_ofFn, x.isLt]

theorem contractionRow_entry (basis : Array (Array ℕ)) (x : PackedPoint) (j : Fin 9) :
    (contractionRow basis x)[j.val]?.getD 0 =
      (List.range 9).foldl (fun value i => if x.val.testBit i then
        Nat.xor value ((basis[i]?.getD #[])[j.val]?.getD 0) else value) 0 := by
  simp [contractionRow, contractions, Array.getElem?_ofFn, x.isLt, j.isLt]

theorem natRow_contractionRow (basis : Array (Array ℕ)) (x : PackedPoint) (j : Fin 9) :
    natRow ((contractionRow basis x)[j.val]?.getD 0) =
      ∑ i : Fin 9, decodePoint x i • natRow ((basis[i.val]?.getD #[])[j.val]?.getD 0) := by
  rw [contractionRow_entry, natRow_xor_fold, natRow_zero, zero_add]
  exact selected_sum x _

theorem natRow_contractPair (row : Array ℕ) (hsize : row.size = 9) (y : PackedPoint) :
    natRow (contractPair row y.val) =
      ∑ j : Fin 9, decodePoint y j • natRow (row[j.val]?.getD 0) := by
  rw [contractPair, hsize, natRow_xor_fold, natRow_zero, zero_add]
  exact selected_sum y _

def pairTable (basis : Array (Array ℕ)) : Array (Array ℕ) :=
  BinaryValues.fastPairValues (contractions basis 9)

def pairValue (basis : Array (Array ℕ)) (x y : PackedPoint) : ℕ :=
  ((pairTable basis)[x.val]?.getD #[])[y.val]?.getD 0

theorem pairTable_eq (basis : Array (Array ℕ)) :
    pairTable basis = pairValues (contractions basis 9) := by
  apply BinaryValues.fastPairValues_eq_pairValues
  intro v
  simp [contractions]

theorem pairValue_eq (basis : Array (Array ℕ)) (x y : PackedPoint) :
    pairValue basis x y = contractPair (contractionRow basis x) y.val := by
  rw [pairValue, pairTable_eq]
  simp [pairValues, contractionRow, contractions, Array.getElem?_ofFn, x.isLt, y.isLt]

theorem contractionRow_semantic (T : CubicForm) (basis : Array (Array ℕ))
    (hbasis : ∀ i j : Fin 9,
      natRow ((basis[i.val]?.getD #[])[j.val]?.getD 0) =
        contractionPoint T (basisPoint i) (basisPoint j))
    (x : PackedPoint) (j : Fin 9) :
    natRow ((contractionRow basis x)[j.val]?.getD 0) =
      contractionPoint T (decodePoint x) (basisPoint j) := by
  rw [natRow_contractionRow, contraction_left_expansion]
  apply Finset.sum_congr rfl
  intro i _
  rw [hbasis i j]

theorem pairValue_semantic (T : CubicForm) (basis : Array (Array ℕ))
    (hbasis : ∀ i j : Fin 9,
      natRow ((basis[i.val]?.getD #[])[j.val]?.getD 0) =
        contractionPoint T (basisPoint i) (basisPoint j)) (x y : PackedPoint) :
    natRow (pairValue basis x y) = contractionPoint T (decodePoint x) (decodePoint y) := by
  rw [pairValue_eq, natRow_contractPair _ (contractionRow_size basis x) y,
    contraction_right_expansion]
  apply Finset.sum_congr rfl
  intro j _
  rw [contractionRow_semantic T basis hbasis x j]

def familyBasis (family : Fin 348) : Array (Array ℕ) :=
  coordinateContractions (coefficients (family.val + 1))

theorem family_basis_semantic (family : Fin 348) (i j : Fin 9) :
    natRow (((familyBasis family)[i.val]?.getD #[])[j.val]?.getD 0) =
      contractionPoint (representative family) (basisPoint i) (basisPoint j) := by
  funext k
  simpa only [familyBasis, contractionPoint, cubicFormValue, basisPoint] using
    (representative_basis family i j k).symm

theorem family_pair_semantic (family : Fin 348) (x y : PackedPoint) :
    natRow (pairValue (familyBasis family) x y) =
      contractionPoint (representative family) (decodePoint x) (decodePoint y) :=
  pairValue_semantic _ _ (family_basis_semantic family) x y

end Lemmata.RM59.CatalogContractions
