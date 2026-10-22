module

public import Lemmata.Centroid.Proof.Construction.RectangularMatrix

@[expose] public section

open scoped BigOperators
open Classical

namespace Lemmata.Centroid.Construction.Rectangular

noncomputable section

variable {F : Type*} [Field F]

def hPrime (n t : ℕ) (ht : t ≤ n) (j : Fin n) : Fin n → RatFunc F :=
  ∑ k : Option (Fin t), (relation (F := F) n t (selected ht k) * lambda (F := F) n t j (selected ht k)) •
    gridPoint (F := F) n t j (selected ht k)

def supportPolynomial (n t : ℕ) (ht : t ≤ n) : Matrix (Fin n) (Fin n) (Polynomial F) :=
  fun i j => (1 - Polynomial.C (t : F) * Polynomial.X) * (1 + Polynomial.X) * matrixM n i j +
    ∑ r : Fin t,
      if j = r.castLE ht then
        Polynomial.X * Polynomial.C (2 - (n : F)) * matrixM n i (r.castLE ht) * matrixM n i j
      else (1 + Polynomial.C 2 * Polynomial.X) * matrixM n i (r.castLE ht) * matrixM n i j

theorem supportPolynomial_eval (n t : ℕ) (ht : t ≤ n) :
    (Polynomial.evalRingHom (0 : F)).mapMatrix (supportPolynomial (F := F) n t ht) = 1 := by
  ext i j
  have hz (r : Fin t) : Polynomial.eval (0 : F)
      (if j = r.castLE ht then
        Polynomial.X * Polynomial.C (2 - (n : F)) * matrixM n i (r.castLE ht) * matrixM n i j
      else (1 + Polynomial.C 2 * Polynomial.X) * matrixM n i (r.castLE ht) * matrixM n i j) = 0 := by
    by_cases hj : j = r.castLE ht
    · simp [hj]
    · by_cases hi : i = r.castLE ht
      · subst i
        simp [hj, matrixM, Ne.symm hj]
      · simp [hj, matrixM, hi]
  change Polynomial.eval 0 (supportPolynomial n t ht i j) = _
  simp only [supportPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_finsetSum]
  rw [Finset.sum_eq_zero (by intro r hr; exact hz r)]
  by_cases hij : i = j <;> simp [matrixM, Matrix.one_apply, hij]

theorem scaled_none (n t : ℕ) (i j : Fin n) :
    (B (F := F) n * B (F := F) 1) *
      (relation (F := F) n t none * lambda (F := F) n t j none * gridPoint (F := F) n t j none i) =
        D (F := F) t * B (F := F) 1 * M (F := F) n i j := by
  unfold relation lambda gridPoint H
  field_simp [RatFunc.X_ne_zero, B_ne_zero (F := F) n, D_ne_zero (F := F) t]

theorem scaled_some (n t : ℕ) (i j r : Fin n) :
    (B (F := F) n * B (F := F) 1) *
      (relation (F := F) n t (some r) * lambda (F := F) n t j (some r) * gridPoint (F := F) n t j (some r) i) =
      if j = r then RatFunc.X * (2 - (n : RatFunc F)) * M (F := F) n i r * M (F := F) n i j
      else (1 + 2 * RatFunc.X) * M (F := F) n i r * M (F := F) n i j := by
  unfold relation gridPoint H
  dsimp only
  erw [← M_apply]
  by_cases h : j = r
  all_goals simp only [lambda, h, ite_true, ite_false]
  all_goals field_simp [RatFunc.X_ne_zero, B_ne_zero (F := F) n, B_ne_zero (F := F) 1]

theorem supportPolynomial_map (n t : ℕ) (ht : t ≤ n) (i j : Fin n) :
    algebraMap (Polynomial F) (RatFunc F) (supportPolynomial n t ht i j) =
      (B (F := F) n * B (F := F) 1) * hPrime (F := F) n t ht j i := by
  let φ := algebraMap (Polynomial F) (RatFunc F)
  have h1 : φ (1 + Polynomial.X) = B (F := F) 1 := by
    simp [φ, B, map_add, map_one]
  have hc : φ (Polynomial.C (2 - (n : F))) = 2 - (n : RatFunc F) := by
    simp only [map_sub, map_ofNat, map_natCast]
  have h2 : φ (1 + Polynomial.C 2 * Polynomial.X) = 1 + 2 * RatFunc.X := by
    rw [map_add, map_one, map_mul]
    have hc2 : φ (Polynomial.C (2 : F)) = 2 := by simp only [map_ofNat]
    rw [hc2]
    rfl
  change φ (supportPolynomial n t ht i j) = _
  simp only [hPrime, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fintype.sum_option,
    selected, Option.map_none, Option.map_some]
  rw [mul_add, Finset.mul_sum, scaled_none]
  simp_rw [scaled_some]
  unfold supportPolynomial
  rw [map_add, map_mul, map_mul, map_sum, h1]
  change D (F := F) t * B (F := F) 1 * M (F := F) n i j + _ = _
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  split_ifs <;> simp only [map_mul, hc]
  · rfl
  · rw [h2]
    rfl

theorem hPrime_matrix_isUnit (n t : ℕ) (ht : t ≤ n) :
    IsUnit (show Matrix (Fin n) (Fin n) (RatFunc F) from fun i j => hPrime (F := F) n t ht j i) := by
  have hs : ((algebraMap (Polynomial F) (RatFunc F)).mapMatrix
      (supportPolynomial n t ht)).det ≠ 0 := by
    apply Circuit.ratFunc_det_ne_zero_of_eval
    rw [supportPolynomial_eval, Matrix.det_one]
    exact one_ne_zero
  have he : (algebraMap (Polynomial F) (RatFunc F)).mapMatrix (supportPolynomial n t ht) =
      (B (F := F) n * B (F := F) 1) •
        (show Matrix (Fin n) (Fin n) (RatFunc F) from fun i j => hPrime (F := F) n t ht j i) := by
    ext i j
    exact supportPolynomial_map n t ht i j
  rw [he, Matrix.det_smul] at hs
  exact (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr ((mul_ne_zero_iff.mp hs).2))

theorem hPrime_span (n t : ℕ) (ht : t ≤ n) :
    Submodule.span (RatFunc F) (Set.range (hPrime (F := F) n t ht)) = ⊤ := by
  let A : Matrix (Fin n) (Fin n) (RatFunc F) := fun i j => hPrime (F := F) n t ht j i
  have hu : IsUnit A := hPrime_matrix_isUnit n t ht
  have hrange : LinearMap.range A.mulVecLin = ⊤ :=
    LinearMap.range_eq_top.mpr (Matrix.mulVec_surjective_iff_isUnit.mpr hu)
  rw [Matrix.range_mulVecLin] at hrange
  exact hrange

end

end Lemmata.Centroid.Construction.Rectangular
