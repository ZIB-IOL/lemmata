module

public import Lemmata.Centroid.Proof.Construction.CircuitSpans
public import Lemmata.Centroid.Proof.Construction.CircuitConcise
public import Lemmata.Centroid.Proof.Construction.PolynomialFrame

@[expose] public section

open scoped BigOperators
open Classical

namespace Lemmata.Centroid.Construction.Circuit

noncomputable section

variable {F : Type*} [Field F]

def variationC (q ν : ℕ) : Fin (q + 1) → (A q ν ⊕ Option (Fin q)) → RatFunc F :=
  Fin.lastCases 0 (fun j => Realization.basisVector (Sum.inr (some j)))

def activeVariation (q ν : ℕ) : A q ν → (A q ν ⊕ Option (Fin q)) → RatFunc F :=
  Sum.elim (variationC q ν) (fun _ => 0)

@[simp] theorem variationC_castSucc (q ν : ℕ) (j : Fin q) (c : A q ν ⊕ Option (Fin q)) :
    variationC (F := F) q ν j.castSucc c = Realization.basisVector (Sum.inr (some j)) c := by
  simp [variationC]

@[simp] theorem variationC_last (q ν : ℕ) (c : A q ν ⊕ Option (Fin q)) :
    variationC (F := F) q ν (Fin.last q) c = 0 := by
  simp [variationC]

def oldPolynomial (q ν : ℕ)
    (e : (A q ν → RatFunc F) ≃ₗ[RatFunc F] (A q ν → RatFunc F))
    (p : A q ν × A q ν) : ∀ i, Core q ν i → Polynomial (RatFunc F) :=
  factors q ν (fun a => Polynomial.C (normalizedPoint q ν e p.1 p.2 a))
    (fun b => Polynomial.C (Realization.basisVector (Sum.inl p.1) b))
    (fun c => Polynomial.C (oldPoint q ν e p 2 c) - Polynomial.X *
      Polynomial.C (diagonalCoefficient (F := F) q ν p.1 p.2 * activeVariation q ν p.1 c))

def extraPolynomial (q ν : ℕ)
    (e : (A q ν → RatFunc F) ≃ₗ[RatFunc F] (A q ν → RatFunc F))
    (j : Fin (q + 1)) : ∀ i, Core q ν i → Polynomial (RatFunc F) :=
  factors q ν (fun a => Polynomial.C (normalizedPoint q ν e (Sum.inl j) (Sum.inl j) a))
    (fun b => Polynomial.C (Realization.basisVector (Sum.inl (Sum.inl j)) b) +
      Polynomial.X * Polynomial.C (Realization.basisVector (Sum.inr ()) b))
    (fun c => Polynomial.C (Realization.basisVector (Sum.inr none) c) +
      Polynomial.X * Polynomial.C (variationC q ν j c))

def polynomialPoint (q ν : ℕ)
    (e : (A q ν → RatFunc F) ≃ₗ[RatFunc F] (A q ν → RatFunc F)) :
    PointIndex q ν → ∀ i, Core q ν i → Polynomial (RatFunc F) :=
  Sum.elim (oldPolynomial q ν e) (extraPolynomial q ν e)

theorem polynomialPoint_coeff_zero (q ν : ℕ)
    (e : (A q ν → RatFunc F) ≃ₗ[RatFunc F] (A q ν → RatFunc F))
    (p : PointIndex q ν) (i : Fin 3) (a : Core q ν i) :
    (polynomialPoint q ν e p i a).coeff 0 = basePoint q ν e p i a := by
  cases p <;> fin_cases i <;>
    simp [polynomialPoint, basePoint, oldPolynomial, extraPolynomial, oldPoint, extraPoint,
      factors_zero, factors_one, factors_two]
  rfl

theorem oldPolynomial_coeff_one (q ν : ℕ)
    (e : (A q ν → RatFunc F) ≃ₗ[RatFunc F] (A q ν → RatFunc F))
    (p : A q ν × A q ν) (x : ∀ i, Core q ν i) :
    (Tensor.simple (oldPolynomial q ν e p) x).coeff 1 =
      -(normalizedPoint q ν e p.1 p.2 (x 0) * Realization.basisVector (Sum.inl p.1) (x 1) *
        diagonalCoefficient (F := F) q ν p.1 p.2 * activeVariation q ν p.1 (x 2)) := by
  simp only [Tensor.simple, Fin.prod_univ_three, oldPolynomial, factors_zero, factors_one,
    factors_two, Polynomial.mul_coeff_one, Polynomial.mul_coeff_zero, Polynomial.coeff_sub,
    Polynomial.coeff_C, Polynomial.coeff_X, one_ne_zero, ite_false, ite_true,
    zero_mul, mul_zero, add_zero, zero_add, zero_sub,
    Lemmata.TensorRank.Tensor.pure]
  ring

theorem oldPolynomial_coeff_two (q ν : ℕ)
    (e : (A q ν → RatFunc F) ≃ₗ[RatFunc F] (A q ν → RatFunc F))
    (p : A q ν × A q ν) (x : ∀ i, Core q ν i) :
    (Tensor.simple (oldPolynomial q ν e p) x).coeff 2 = 0 := by
  simp only [Tensor.simple, Fin.prod_univ_three, oldPolynomial, factors_zero, factors_one,
    factors_two, BigCentroid.mul_coeff_two, Polynomial.mul_coeff_one,
    Polynomial.mul_coeff_zero, Polynomial.coeff_sub, Polynomial.coeff_C,
    Polynomial.coeff_X,
    Lemmata.TensorRank.Tensor.pure]
  simp

theorem extraPolynomial_coeff_one (q ν : ℕ)
    (e : (A q ν → RatFunc F) ≃ₗ[RatFunc F] (A q ν → RatFunc F))
    (j : Fin (q + 1)) (x : ∀ i, Core q ν i) :
    (Tensor.simple (extraPolynomial q ν e j) x).coeff 1 =
      normalizedPoint q ν e (Sum.inl j) (Sum.inl j) (x 0) *
        Realization.basisVector (Sum.inl (Sum.inl j)) (x 1) * variationC q ν j (x 2) +
      normalizedPoint q ν e (Sum.inl j) (Sum.inl j) (x 0) *
        Realization.basisVector (Sum.inr ()) (x 1) * Realization.basisVector (Sum.inr none) (x 2) := by
  simp only [Tensor.simple, Fin.prod_univ_three, extraPolynomial, factors_zero, factors_one,
    factors_two, Polynomial.mul_coeff_one, Polynomial.mul_coeff_zero, Polynomial.coeff_add,
    Polynomial.coeff_C,
    Lemmata.TensorRank.Tensor.pure]
  simp

theorem extraPolynomial_coeff_two (q ν : ℕ)
    (e : (A q ν → RatFunc F) ≃ₗ[RatFunc F] (A q ν → RatFunc F))
    (j : Fin (q + 1)) (x : ∀ i, Core q ν i) :
    (Tensor.simple (extraPolynomial q ν e j) x).coeff 2 =
      normalizedPoint q ν e (Sum.inl j) (Sum.inl j) (x 0) *
        Realization.basisVector (Sum.inr ()) (x 1) * variationC q ν j (x 2) := by
  simp only [Tensor.simple, Fin.prod_univ_three, extraPolynomial, factors_zero, factors_one,
    factors_two, BigCentroid.mul_coeff_two, Polynomial.mul_coeff_one,
    Polynomial.mul_coeff_zero, Polynomial.coeff_add, Polynomial.coeff_C,
    Polynomial.coeff_X,
    Lemmata.TensorRank.Tensor.pure]
  simp

theorem normalizedPoint_sum (q ν : ℕ) (hq : 0 < q)
    (e : (A q ν → RatFunc F) ≃ₗ[RatFunc F] (A q ν → RatFunc F)) :
    (∑ j : Fin (q + 1), normalizedPoint q ν e (Sum.inl j) (Sum.inl j)) = 0 := by
  have hv : ∀ j, normalizedPoint q ν e (Sum.inl j) (Sum.inl j) =
      e (hadamardColumn (F := F) q ν j) := by
    intro j
    unfold normalizedPoint
    congr 1
    ext a
    exact (map_mul (algebraMap (Polynomial F) (RatFunc F)) _ _).symm
  simp_rw [hv]
  rw [← map_sum, hadamardColumn_sum q ν hq, map_zero]

theorem sum_oldPolynomial_coeff_one (q ν : ℕ)
    (e : (A q ν → RatFunc F) ≃ₗ[RatFunc F] (A q ν → RatFunc F))
    (x : ∀ i, Core q ν i) :
    (∑ p : A q ν × A q ν, (Tensor.simple (oldPolynomial q ν e p) x).coeff 1) =
      -(∑ j : Fin (q + 1), normalizedPoint q ν e (Sum.inl j) (Sum.inl j) (x 0) *
        Realization.basisVector (Sum.inl (Sum.inl j)) (x 1) * variationC q ν j (x 2)) := by
  simp_rw [oldPolynomial_coeff_one]
  rw [Finset.sum_neg_distrib]
  congr 1
  rw [Fintype.sum_prod_type]
  have h := sum_active_diagonal q ν (fun j k => normalizedPoint q ν e j k (x 0) *
    Realization.basisVector (Sum.inl j) (x 1) * activeVariation q ν j (x 2))
  convert h using 1
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  unfold diagonalCoefficient
  split_ifs <;> ring
  rfl

theorem sum_extraPolynomial_coeff_one (q ν : ℕ) (hq : 0 < q)
    (e : (A q ν → RatFunc F) ≃ₗ[RatFunc F] (A q ν → RatFunc F))
    (x : ∀ i, Core q ν i) :
    (∑ j : Fin (q + 1), (Tensor.simple (extraPolynomial q ν e j) x).coeff 1) =
      ∑ j : Fin (q + 1), normalizedPoint q ν e (Sum.inl j) (Sum.inl j) (x 0) *
        Realization.basisVector (Sum.inl (Sum.inl j)) (x 1) * variationC q ν j (x 2) := by
  simp_rw [extraPolynomial_coeff_one]
  rw [Finset.sum_add_distrib]
  have hz : (∑ j : Fin (q + 1), normalizedPoint q ν e (Sum.inl j) (Sum.inl j) (x 0) *
      Realization.basisVector (Sum.inr ()) (x 1) * Realization.basisVector (Sum.inr none) (x 2)) = 0 := by
    rw [← Finset.sum_mul, ← Finset.sum_mul]
    let a : A q ν := x 0
    have hh := congrFun (normalizedPoint_sum q ν hq e) a
    simp only [Finset.sum_apply, Pi.zero_apply] at hh
    erw [hh, zero_mul, zero_mul]
  rw [hz, add_zero]

theorem polynomialPoint_coeff_one (q ν : ℕ) (hq : 0 < q)
    (e : (A q ν → RatFunc F) ≃ₗ[RatFunc F] (A q ν → RatFunc F))
    (x : ∀ i, Core q ν i) :
    ((∑ p, Tensor.simple (polynomialPoint q ν e p)) x).coeff 1 = 0 := by
  simp only [Finset.sum_apply, Fintype.sum_sum_type,
    polynomialPoint, Sum.elim_inl, Sum.elim_inr]
  erw [Polynomial.coeff_add]
  simp only [Polynomial.finsetSum_coeff]
  erw [sum_oldPolynomial_coeff_one, sum_extraPolynomial_coeff_one q ν hq e x]
  exact neg_add_cancel _

theorem tau_map (q ν : ℕ) (x : ∀ i, Core q ν i) :
    algebraMap F (RatFunc F) (tau q ν x) =
      ∑ j : Fin q, Realization.basisVector (F := RatFunc F) (Sum.inl j.castSucc) (x 0) *
        Realization.basisVector (Sum.inr ()) (x 1) *
        Realization.basisVector (Sum.inr (some j)) (x 2) := by
  simp only [tau, Finset.sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  calc
    _ = Realization.basisVector (F := RatFunc F)
        (assignment q ν (Sum.inl j.castSucc) (Sum.inr ()) (Sum.inr (some j))) x :=
      congrFun (Realization.map_basisVector (algebraMap F (RatFunc F)) _) x
    _ = _ := by
      rw [← Realization.simple_basisVector]
      simp only [Tensor.simple, Fin.prod_univ_three, assignment_zero, assignment_one, assignment_two,
        Lemmata.TensorRank.Tensor.pure]
      rfl

theorem polynomialPoint_coeff_two (q ν : ℕ)
    (e : (A q ν → RatFunc F) ≃ₗ[RatFunc F] (A q ν → RatFunc F))
    (he : ∀ j : Fin q, e (hadamardColumn (F := F) q ν j.castSucc) =
      Pi.single (Sum.inl j.castSucc) 1) (x : ∀ i, Core q ν i) :
    ((∑ p, Tensor.simple (polynomialPoint q ν e p)) x).coeff 2 =
      algebraMap F (RatFunc F) (tau q ν x) := by
  simp only [Finset.sum_apply, Fintype.sum_sum_type,
    polynomialPoint, Sum.elim_inl, Sum.elim_inr]
  erw [Polynomial.coeff_add]
  simp only [Polynomial.finsetSum_coeff, oldPolynomial_coeff_two,
    Finset.sum_const_zero, zero_add, extraPolynomial_coeff_two]
  rw [Fin.sum_univ_castSucc]
  have hlast := variationC_last (F := F) q ν (x 2)
  have hcast (j : Fin q) := variationC_castSucc (F := F) q ν j (x 2)
  simp only [hlast, mul_zero, add_zero, hcast,
    normalizedPoint_active q ν e he]
  exact (tau_map (F := F) q ν x).symm

theorem rationalBorderRankAtMost (q ν : ℕ) (hq : 0 < q) :
    Tensor.RationalBorderRankAtMost (tensor (F := F) q ν)
      ((q + 1 + ν) * (q + 2 + ν) + (q + 1)) := by
  obtain ⟨e, he⟩ := exists_circuit_normalizer (F := F) q ν hq
  have hr := Realization.rational_second_order_realization_core (pairs (F := F) q ν)
    (tau q ν) (polynomialPoint q ν e) (basePoint q ν e)
    (polynomialPoint_coeff_zero q ν e) (basePoint_rankAtMost q ν e)
    (frameSpans q ν hq e he) (polynomialPoint_coeff_one q ν hq e)
    (polynomialPoint_coeff_two q ν e he)
  have hc : Fintype.card (PointIndex q ν) + (q + 1 + ν) =
      (q + 1 + ν) * (q + 2 + ν) + (q + 1) := by
    simp only [PointIndex, A, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
    ring
  rwa [hc] at hr

end

end Lemmata.Centroid.Construction.Circuit
