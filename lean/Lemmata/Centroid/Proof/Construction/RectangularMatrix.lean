module

public import Lemmata.Centroid.Proof.Construction.CircuitMatrix
public import Lemmata.Centroid.Proof.Construction.RectangularTarget
public import Lemmata.Centroid.Proof.Construction.WeightedGrid

@[expose] public section

open scoped BigOperators
open Classical

namespace Lemmata.Centroid.Construction.Rectangular

noncomputable section

variable {F : Type*} [Field F]

def matrixM (n : ℕ) : Matrix (Fin n) (Fin n) (Polynomial F) :=
  fun i j => Polynomial.C (if i = j then 1 else 0) + Polynomial.X

abbrev M (n : ℕ) := (algebraMap (Polynomial F) (RatFunc F)).mapMatrix (matrixM n)

def B (n : ℕ) : RatFunc F :=
  algebraMap (Polynomial F) (RatFunc F) (1 + Polynomial.C (n : F) * Polynomial.X)

def D (t : ℕ) : RatFunc F :=
  algebraMap (Polynomial F) (RatFunc F) (1 - Polynomial.C (t : F) * Polynomial.X)

theorem B_eq (n : ℕ) : B (F := F) n = 1 + (n : RatFunc F) * RatFunc.X := by
  simp only [B, map_add, map_one, map_mul, map_natCast]
  rfl

theorem D_eq (t : ℕ) : D (F := F) t = 1 - (t : RatFunc F) * RatFunc.X := by
  simp only [D, map_sub, map_one, map_mul, map_natCast]
  rfl

theorem B_ne_zero (n : ℕ) : B (F := F) n ≠ 0 := by
  apply RatFunc.algebraMap_ne_zero
  intro h
  have hc := congrArg (fun p : Polynomial F => p.coeff 0) h
  simp at hc

theorem D_ne_zero (t : ℕ) : D (F := F) t ≠ 0 := by
  apply RatFunc.algebraMap_ne_zero
  intro h
  have hc := congrArg (fun p : Polynomial F => p.coeff 0) h
  simp at hc

theorem M_apply (n : ℕ) (i j : Fin n) :
    M (F := F) n i j = (if i = j then 1 else 0) + RatFunc.X := by
  change algebraMap (Polynomial F) (RatFunc F)
    (Polynomial.C (if i = j then 1 else 0) + Polynomial.X) = _
  rw [map_add]
  split_ifs <;> simp

theorem M_isUnit (n : ℕ) : IsUnit (M (F := F) n) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  apply isUnit_iff_ne_zero.mpr
  apply Circuit.ratFunc_det_ne_zero_of_eval
  have he : (Polynomial.evalRingHom (0 : F)).mapMatrix (matrixM (F := F) n) = 1 := by
    ext i j
    by_cases h : i = j <;> simp [matrixM, Matrix.one_apply, h]
  rw [he, Matrix.det_one]
  exact one_ne_zero

theorem M_ne_zero (n : ℕ) (i j : Fin n) : M (F := F) n i j ≠ 0 := by
  apply RatFunc.algebraMap_ne_zero
  intro h
  have hc := congrArg (fun p : Polynomial F => p.coeff 1) h
  by_cases h : i = j <;> simp [matrixM, h, Polynomial.coeff_one] at hc

def H (n t : ℕ) : Fin n → Option (Fin n) → RatFunc F
  | _, none => -RatFunc.X * B (F := F) n / D (F := F) t
  | i, some j => (if i = j then 1 else 0) + RatFunc.X

theorem H_ne_zero (n t : ℕ) (i : Fin n) (j : Option (Fin n)) : H (F := F) n t i j ≠ 0 := by
  cases j with
  | none => exact div_ne_zero (mul_ne_zero (neg_ne_zero.mpr RatFunc.X_ne_zero) (B_ne_zero n)) (D_ne_zero t)
  | some j => exact by rw [H, ← M_apply]; exact M_ne_zero n i j

def relation (n t : ℕ) : Option (Fin n) → RatFunc F
  | none => D (F := F) t
  | some _ => RatFunc.X

theorem relation_ne_zero (n t : ℕ) (j : Option (Fin n)) : relation (F := F) n t j ≠ 0 := by
  cases j with
  | none => exact D_ne_zero t
  | some _ => exact RatFunc.X_ne_zero

theorem relation_H (n t : ℕ) (i : Fin n) :
    (∑ j, relation (F := F) n t j * H n t i j) = 0 := by
  rw [Fintype.sum_option]
  simp only [relation, H]
  rw [mul_div_cancel₀ _ (D_ne_zero t)]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, B_eq]
  ring

def lambda (n t : ℕ) (j : Fin n) : Option (Fin n) → RatFunc F
  | none => -D (F := F) t / (RatFunc.X * B (F := F) n ^ 2)
  | some r =>
    if j = r then (2 - (n : RatFunc F)) / (B (F := F) n * B (F := F) 1)
    else (1 + 2 * RatFunc.X) / (RatFunc.X * B (F := F) n * B (F := F) 1)

theorem lambda_sum (n t : ℕ) (r : Fin n) :
    (∑ j, lambda (F := F) n t j (some r)) =
      (n : RatFunc F) * ((1 + 2 * RatFunc.X) / (RatFunc.X * B (F := F) n * B (F := F) 1)) +
        (2 - (n : RatFunc F)) / (B (F := F) n * B (F := F) 1) -
          (1 + 2 * RatFunc.X) / (RatFunc.X * B (F := F) n * B (F := F) 1) := by
  let α : RatFunc F := (1 + 2 * RatFunc.X) / (RatFunc.X * B (F := F) n * B (F := F) 1)
  let β : RatFunc F := (2 - (n : RatFunc F)) / (B (F := F) n * B (F := F) 1)
  have he (j : Fin n) : lambda (F := F) n t j (some r) = α + if j = r then β - α else 0 := by
    by_cases h : j = r <;> simp [lambda, h, α, β]
  simp_rw [he]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  change (n : RatFunc F) * α + (β - α) = (n : RatFunc F) * α + β - α
  ring

def gridPoint (n t : ℕ) (j : Fin n) (r : Option (Fin n)) : Fin n → RatFunc F :=
  fun a => M n a j * H n t a r

theorem gridPoint_lambda (n t : ℕ) (r : Option (Fin n)) :
    (∑ j, lambda (F := F) n t j r • gridPoint (F := F) n t j r) = 1 := by
  ext a
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply, gridPoint, M_apply]
  simp only [mul_add, add_mul, mul_ite, ite_mul, one_mul, mul_zero, zero_mul]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ a)]
  rw [← Finset.sum_mul]
  cases r with
  | none =>
    simp only [lambda, H, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp [RatFunc.X_ne_zero, B_ne_zero (F := F) n, D_ne_zero (F := F) t]
    rw [B_eq]
    ring
  | some r =>
    rw [lambda_sum]
    by_cases h : a = r
    all_goals simp only [lambda, H, h, ite_true, ite_false]
    all_goals field_simp [RatFunc.X_ne_zero, B_ne_zero (F := F) n, B_ne_zero (F := F) 1]
    all_goals simp only [B_eq, Nat.cast_one, one_mul]
    all_goals ring

end

end Lemmata.Centroid.Construction.Rectangular
