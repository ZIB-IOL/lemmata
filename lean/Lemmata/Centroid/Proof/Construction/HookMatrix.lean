module

public import Lemmata.Centroid.Proof.Construction.HookTarget
public import Lemmata.Centroid.Proof.Construction.CircuitMatrix
public import Lemmata.Centroid.Proof.Construction.WeightedGrid

@[expose] public section

open scoped BigOperators
open Classical

namespace Lemmata.Centroid.Construction.Hook

noncomputable section

variable {F : Type*} [Field F]

def weight (t : ℕ) (j : ℕ) : Polynomial F :=
  Polynomial.X ^ 2 + if j = 0 then Polynomial.X - Polynomial.C (t : F) * Polynomial.X ^ 2 else 0

def matrixM (n t : ℕ) : Fin n → Option (Fin n) → Polynomial F
  | i, some j => Polynomial.C (if i = j then 1 else 0) + weight t j.val
  | _, none => -(1 + ∑ j : Fin n, weight t j.val)

def matrixH (n : ℕ) : Matrix (Fin n) (Fin n) (Polynomial F) :=
  fun i j => Polynomial.C (if i = j then 1 else 0) + Polynomial.X

def M (n t : ℕ) (i : Fin n) (j : Option (Fin n)) : RatFunc F :=
  algebraMap (Polynomial F) (RatFunc F) (matrixM n t i j)

def H (n : ℕ) : Matrix (Fin n) (Fin n) (RatFunc F) :=
  (algebraMap (Polynomial F) (RatFunc F)).mapMatrix (matrixH n)

theorem matrixM_eval (n t : ℕ) (i j : Fin n) :
    (matrixM (F := F) n t i (some j)).eval 0 = if i = j then 1 else 0 := by
  by_cases hij : i = j <;> by_cases hj : j.val = 0 <;> simp [matrixM, weight, hij, hj]

theorem matrixH_eval (n : ℕ) :
    (Polynomial.evalRingHom (0 : F)).mapMatrix (matrixH n) = 1 := by
  ext i j
  by_cases hij : i = j <;> simp [matrixH, Matrix.one_apply, hij]

theorem M_isUnit (n t : ℕ) : IsUnit (show Matrix (Fin n) (Fin n) (RatFunc F) from fun i j => M n t i (some j)) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  apply isUnit_iff_ne_zero.mpr
  apply Circuit.ratFunc_det_ne_zero_of_eval
  have he : (Polynomial.evalRingHom (0 : F)).mapMatrix
      (show Matrix (Fin n) (Fin n) (Polynomial F) from fun i j => matrixM n t i (some j)) = 1 := by
    ext i j
    change (matrixM (F := F) n t i (some j)).eval 0 = if i = j then 1 else 0
    exact matrixM_eval n t i j
  rw [he, Matrix.det_one]
  exact one_ne_zero

theorem H_isUnit (n : ℕ) : IsUnit (H (F := F) n) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  apply isUnit_iff_ne_zero.mpr
  apply Circuit.ratFunc_det_ne_zero_of_eval
  rw [matrixH_eval, Matrix.det_one]
  exact one_ne_zero

theorem M_ne_zero (n t : ℕ) (i : Fin n) (j : Option (Fin n)) : M (F := F) n t i j ≠ 0 := by
  apply RatFunc.algebraMap_ne_zero
  intro hz
  cases j with
  | none =>
    have he := congrArg (fun p : Polynomial F => p.eval 0) hz
    have hw (j : Fin n) : (weight (F := F) t j.val).eval 0 = 0 := by
      by_cases hj : j.val = 0 <;> simp [weight, hj]
    simp only [matrixM, Polynomial.eval_neg, Polynomial.eval_add, Polynomial.eval_one,
      Polynomial.eval_finsetSum, hw, Finset.sum_const_zero, add_zero, Polynomial.eval_zero] at he
    exact neg_ne_zero.mpr one_ne_zero he
  | some j =>
    by_cases hij : i = j
    · have he := congrArg (fun p : Polynomial F => p.eval 0) hz
      rw [matrixM_eval, ite_eq_left hij, Polynomial.eval_zero] at he
      exact one_ne_zero he
    · by_cases hj : j.val = 0
      · have he := congrArg (fun p : Polynomial F => p.coeff 1) hz
        simp [matrixM, weight, hij, hj, Polynomial.coeff_X_pow] at he
      · have he := congrArg (fun p : Polynomial F => p.coeff 2) hz
        simp [matrixM, weight, hij, hj, Polynomial.coeff_X_pow] at he

theorem H_ne_zero (n : ℕ) (i j : Fin n) : H (F := F) n i j ≠ 0 := by
  apply RatFunc.algebraMap_ne_zero
  intro hz
  have he := congrArg (fun p : Polynomial F => p.coeff 1) hz
  by_cases hij : i = j <;> simp [matrixH, hij, Polynomial.coeff_one] at he

theorem sum_M (n t : ℕ) (i : Fin n) : (∑ j, M (F := F) n t i j) = 0 := by
  have he : (∑ j : Option (Fin n), matrixM (F := F) n t i j) = 0 := by
    simp only [Fintype.sum_option, matrixM, Finset.sum_add_distrib, apply_ite Polynomial.C,
      Polynomial.C_1, Polynomial.C_0, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    ring
  change (∑ j, algebraMap (Polynomial F) (RatFunc F) (matrixM n t i j)) = 0
  rw [← map_sum, he, map_zero]

def gridPoint (n t : ℕ) (j : Option (Fin n)) (k : Fin n) : Fin n → RatFunc F :=
  fun i => M n t i j * H n i k

def h (n t : ℕ) (ht : t ≤ n) : Fin n → RatFunc F :=
  ∑ j : Fin t, fun i => M n t i (some (j.castLE ht))

theorem h_eq (n t : ℕ) (ht₀ : 0 < t) (ht : t ≤ n) (i : Fin n) :
    h (F := F) n t ht i = (if i.val < t then 1 else 0) + RatFunc.X := by
  have hsum : (∑ j : Fin t, weight (F := F) t j.val) = Polynomial.X := by
    let z : Fin t := ⟨0, ht₀⟩
    have he (j : Fin t) : j.val = 0 ↔ j = z := by simp [z, Fin.ext_iff]
    simp only [weight, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, he, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    simp only [map_natCast]
    ring
  have hdelta : (∑ j : Fin t, Polynomial.C (if i = j.castLE ht then (1 : F) else 0)) =
      Polynomial.C (if i.val < t then 1 else 0) := by
    by_cases hi : i.val < t
    · let j : Fin t := ⟨i.val, hi⟩
      have he (k : Fin t) : i = k.castLE ht ↔ k = j := by simp [j, Fin.ext_iff, eq_comm]
      simp [he, hi]
    · have he (j : Fin t) : i ≠ j.castLE ht := by
        intro hij
        have hv := congrArg Fin.val hij
        change i.val = j.val at hv
        have hjlt := j.isLt
        omega
      simp [hi, he]
  simp only [h, Finset.sum_apply]
  simp only [M, matrixM]
  rw [← map_sum, Finset.sum_add_distrib, hdelta]
  have hw : (∑ j : Fin t, weight (F := F) t (j.castLE ht).val) = Polynomial.X := hsum
  rw [hw, map_add]
  by_cases hi : i.val < t <;> simp [hi]

def v (n : ℕ) : RatFunc F := 1 + (n : RatFunc F) * RatFunc.X

theorem v_ne_zero (n : ℕ) : v (F := F) n ≠ 0 := by
  have he : v (F := F) n = algebraMap (Polynomial F) (RatFunc F)
      (1 + Polynomial.C (n : F) * Polynomial.X) := by simp [v]
  rw [he]
  apply RatFunc.algebraMap_ne_zero
  intro hz
  have he := congrArg (fun p : Polynomial F => p.eval 0) hz
  simp at he

theorem sum_H (n : ℕ) (i : Fin n) : (∑ k, H (F := F) n i k) = v n := by
  simp only [H, RingHom.mapMatrix_apply, Matrix.map_apply, matrixH, map_add]
  have hc (k : Fin n) : algebraMap (Polynomial F) (RatFunc F) (Polynomial.C (if i = k then (1 : F) else 0)) =
      if i = k then 1 else 0 := by split_ifs <;> simp
  simp_rw [hc]
  simp [v, Finset.sum_add_distrib]

def g (n t : ℕ) (j : Option (Fin n)) : Fin n → RatFunc F := fun i => M n t i j * v n
def d (n t : ℕ) (ht : t ≤ n) (k : Fin n) : Fin n → RatFunc F := fun i => h n t ht i * H n i k

theorem sum_grid_row (n t : ℕ) (j : Option (Fin n)) : (∑ k, gridPoint (F := F) n t j k) = g n t j := by
  ext i
  simp only [Finset.sum_apply, gridPoint, ← Finset.mul_sum, sum_H, g]

theorem sum_grid_column (n t : ℕ) (k : Fin n) : (∑ j, gridPoint (F := F) n t j k) = 0 := by
  ext i
  simp only [Finset.sum_apply, gridPoint, ← Finset.sum_mul, sum_M, zero_mul, Pi.zero_apply]

theorem sum_grid_selected (n t : ℕ) (ht : t ≤ n) (k : Fin n) :
    (∑ j : Fin t, gridPoint (F := F) n t (some (j.castLE ht)) k) = d n t ht k := by
  ext i
  simp only [Finset.sum_apply, gridPoint, ← Finset.sum_mul, d, h]

def supportPolynomial (n t : ℕ) : Matrix (Fin n) (Fin n) (Polynomial F) :=
  fun i j => if j.val < t then matrixM n t i (some j) else
    Polynomial.C (if i = j then 1 else 0) + Polynomial.C (if i.val < t then 1 else 0) + Polynomial.X

theorem supportPolynomial_eval_det (n t : ℕ) :
    ((Polynomial.evalRingHom (0 : F)).mapMatrix (supportPolynomial n t)).det = 1 := by
  let A := (Polynomial.evalRingHom (0 : F)).mapMatrix (supportPolynomial n t)
  have hup : A.IsUpperTriangular := by
    intro i j hij
    change j < i at hij
    have hne : i ≠ j := (ne_of_gt hij)
    by_cases hj : j.val < t
    · simp [A, supportPolynomial, hj, matrixM_eval, hne]
    · have hi : ¬ i.val < t := by have hh := Fin.lt_def.mp hij; omega
      simp [A, supportPolynomial, hj, hi, hne]
  have hd (i : Fin n) : A i i = 1 := by
    by_cases hi : i.val < t <;> simp [A, supportPolynomial, hi, matrixM_eval]
  rw [Matrix.det_of_isUpperTriangular hup]
  simp only [hd, Finset.prod_const_one]

def normalizedPoint (n t : ℕ) (j : Fin n) : Fin n → RatFunc F :=
  fun i => algebraMap (Polynomial F) (RatFunc F) (supportPolynomial n t i j)

theorem normalizedPoint_span (n t : ℕ) :
    Submodule.span (RatFunc F) (Set.range (normalizedPoint (F := F) n t)) = ⊤ := by
  let A : Matrix (Fin n) (Fin n) (RatFunc F) := (algebraMap (Polynomial F) (RatFunc F)).mapMatrix
    (supportPolynomial n t)
  have hA : IsUnit A := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    apply isUnit_iff_ne_zero.mpr
    apply Circuit.ratFunc_det_ne_zero_of_eval
    rw [supportPolynomial_eval_det]
    exact one_ne_zero
  have hrange : LinearMap.range A.mulVecLin = ⊤ :=
    LinearMap.range_eq_top.mpr (Matrix.mulVec_surjective_iff_isUnit.mpr hA)
  rw [Matrix.range_mulVecLin] at hrange
  exact hrange

def mixedPoint (n t : ℕ) (ht : t ≤ n) (j : Fin n) : Fin n → RatFunc F :=
  if j.val < t then g n t (some j) else d n t ht j

def mixedScale (n t : ℕ) (j : Fin n) : RatFunc F := if j.val < t then v n else RatFunc.X

theorem mixedScale_ne_zero (n t : ℕ) (j : Fin n) : mixedScale (F := F) n t j ≠ 0 := by
  unfold mixedScale
  split_ifs
  · exact v_ne_zero n
  · exact RatFunc.X_ne_zero

theorem mixedPoint_eq (n t : ℕ) (ht₀ : 0 < t) (ht : t ≤ n) (j : Fin n) :
    mixedPoint (F := F) n t ht j = mixedScale (F := F) n t j • normalizedPoint (F := F) n t j := by
  ext i
  by_cases hj : j.val < t
  · simp only [mixedPoint, mixedScale, normalizedPoint, supportPolynomial, hj, ite_true,
      g, M, Pi.smul_apply, smul_eq_mul, mul_comm]
  · simp only [mixedPoint, mixedScale, normalizedPoint, supportPolynomial, hj, ite_false,
      d, Pi.smul_apply, smul_eq_mul, map_add, H, RingHom.mapMatrix_apply, Matrix.map_apply, matrixH]
    have hc (q : Prop) [Decidable q] : algebraMap (Polynomial F) (RatFunc F)
        (Polynomial.C (if q then (1 : F) else 0)) = if q then 1 else 0 := by split_ifs <;> simp
    rw [h_eq n t ht₀ ht, hc (i = j), hc (i.val < t)]
    change ((if i.val < t then 1 else 0) + (RatFunc.X : RatFunc F)) * ((if i = j then 1 else 0) + RatFunc.X) =
      RatFunc.X * (((if i = j then 1 else 0) + if i.val < t then 1 else 0) + RatFunc.X)
    by_cases hij : i = j
    · subst i; simp only [hj, ite_false, ite_true]; ring
    · simp only [hij, ite_false, zero_add]; ring

theorem mixedPoint_span (n t : ℕ) (ht₀ : 0 < t) (ht : t ≤ n) :
    Submodule.span (RatFunc F) (Set.range (mixedPoint (F := F) n t ht)) = ⊤ := by
  apply top_unique
  rw [← normalizedPoint_span (F := F) n t]
  apply Submodule.span_le.mpr
  rintro _ ⟨j, rfl⟩
  have hm := Submodule.smul_mem
    (Submodule.span (RatFunc F) (Set.range (mixedPoint (F := F) n t ht)))
    (mixedScale (F := F) n t j)⁻¹ (Submodule.subset_span ⟨j, rfl⟩)
  rw [mixedPoint_eq n t ht₀ ht, smul_smul, inv_mul_cancel₀ (mixedScale_ne_zero n t j), one_smul] at hm
  exact hm

def etaPolynomial (t : ℕ) (j : Fin t) : Polynomial F :=
  Polynomial.X + if j.val = 0 then 1 - Polynomial.C (t : F) * Polynomial.X else 0

def eta (t : ℕ) (j : Fin t) : RatFunc F :=
  algebraMap (Polynomial F) (RatFunc F) (etaPolynomial t j)

theorem eta_ne_zero (t : ℕ) (j : Fin t) : eta (F := F) t j ≠ 0 := by
  apply RatFunc.algebraMap_ne_zero
  intro hz
  by_cases hj : j.val = 0
  · have he := congrArg (fun p : Polynomial F => p.eval 0) hz
    simp [etaPolynomial, hj] at he
  · have he := congrArg (fun p : Polynomial F => p.coeff 1) hz
    simp [etaPolynomial, hj] at he

theorem sum_eta (t : ℕ) (ht : 0 < t) : (∑ j, eta (F := F) t j) = 1 := by
  let z : Fin t := ⟨0, ht⟩
  have he (j : Fin t) : j.val = 0 ↔ j = z := by simp [z, Fin.ext_iff]
  have hp : (∑ j, etaPolynomial (F := F) t j) = 1 := by
    simp only [etaPolynomial, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, he, Finset.sum_ite_eq', Finset.mem_univ, ite_true, map_natCast]
    ring
  change (∑ j, algebraMap (Polynomial F) (RatFunc F) (etaPolynomial t j)) = 1
  rw [← map_sum, hp, map_one]

theorem grid_row_span (n t : ℕ) (j : Option (Fin n)) :
    Submodule.span (RatFunc F) (Set.range (gridPoint (F := F) n t j)) = ⊤ := by
  let D : Matrix (Fin n) (Fin n) (RatFunc F) := Matrix.diagonal (fun i => M n t i j)
  have hD : IsUnit D := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    apply isUnit_iff_ne_zero.mpr
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => M_ne_zero n t i j)
  have hA : IsUnit (D * H (F := F) n) := hD.mul (H_isUnit n)
  have hrange : LinearMap.range (D * H (F := F) n).mulVecLin = ⊤ :=
    LinearMap.range_eq_top.mpr (Matrix.mulVec_surjective_iff_isUnit.mpr hA)
  rw [Matrix.range_mulVecLin] at hrange
  have he : (D * H (F := F) n).col = gridPoint n t j := by
    ext k i
    simp [D, Matrix.diagonal_mul, gridPoint]
  rwa [he] at hrange

theorem grid_column_span (n t : ℕ) (k : Fin n) :
    Submodule.span (RatFunc F) (Set.range (fun j : Fin n => gridPoint (F := F) n t (some j) k)) = ⊤ := by
  let D : Matrix (Fin n) (Fin n) (RatFunc F) := Matrix.diagonal (fun i => H n i k)
  let B : Matrix (Fin n) (Fin n) (RatFunc F) := fun i j => M n t i (some j)
  have hD : IsUnit D := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    apply isUnit_iff_ne_zero.mpr
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => H_ne_zero n i k)
  have hA : IsUnit (D * B) := hD.mul (M_isUnit n t)
  have hrange : LinearMap.range (D * B).mulVecLin = ⊤ :=
    LinearMap.range_eq_top.mpr (Matrix.mulVec_surjective_iff_isUnit.mpr hA)
  rw [Matrix.range_mulVecLin] at hrange
  have he : (D * B).col = (fun j : Fin n => gridPoint (F := F) n t (some j) k) := by
    ext j i
    change (∑ r : Fin n, (if i = r then H (F := F) n i k else 0) * M n t r (some j)) =
      M n t i (some j) * H n i k
    simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    exact mul_comm _ _
  rwa [he] at hrange

end

end Lemmata.Centroid.Construction.Hook
