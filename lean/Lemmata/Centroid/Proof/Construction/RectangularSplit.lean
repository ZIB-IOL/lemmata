module

public import Lemmata.Centroid.Proof.Construction.RectangularFrames
public import Lemmata.Centroid.Proof.Construction.PolynomialFrame

@[expose] public section

open scoped BigOperators
open Classical

namespace Lemmata.Centroid.Construction.Rectangular

noncomputable section

variable {F : Type*} [Field F]

def variationB (n t : ℕ) : Option (Fin t) → (Option (Fin n) ⊕ Fin t) → RatFunc F
  | none => 0
  | some j => Realization.basisVector (Sum.inr j)

def variationC (n t : ℕ) : Option (Fin t) → (Option (Fin n) ⊕ Fin t) → RatFunc F
  | none => -∑ j : Fin t, Realization.basisVector (Sum.inr j)
  | some j => Realization.basisVector (Sum.inr j)

def oldVariation (n t : ℕ) (ht : t ≤ n) (j : Fin n) (r : Option (Fin n)) :
    (Option (Fin n) ⊕ Fin t) → RatFunc F :=
  ∑ k : Fin t, if selected ht (some k) = r then
    lambda (F := F) n t j r • Realization.basisVector (Sum.inr k) else 0

def oldPolynomial (n t : ℕ) (ht : t ≤ n) (p : Fin n × Option (Fin n)) :
    ∀ i, Core n t i → Polynomial (RatFunc F) :=
  factors n t (fun a => Polynomial.C (gridPoint (F := F) n t p.1 p.2 a))
    (fun b => Polynomial.C (oldPoint (F := F) n t ht p 1 b) -
      Polynomial.X * Polynomial.C (oldVariation (F := F) n t ht p.1 p.2 b))
    (fun c => Polynomial.C (Realization.basisVector (Sum.inl p.2) c))

def extraPolynomial (n t : ℕ) (ht : t ≤ n) (k : Option (Fin t)) :
    ∀ i, Core n t i → Polynomial (RatFunc F) :=
  factors n t (fun _ => 1)
    (fun b => Polynomial.C (Realization.basisVector (Sum.inl none) b) +
      Polynomial.X * Polynomial.C (variationB (F := F) n t k b))
    (fun c => Polynomial.C (Realization.basisVector (Sum.inl (selected ht k)) c) +
      Polynomial.X * Polynomial.C (variationC (F := F) n t k c))

def polynomialPoint (n t : ℕ) (ht : t ≤ n) :
    PointIndex n t → ∀ i, Core n t i → Polynomial (RatFunc F) :=
  Sum.elim (oldPolynomial (F := F) n t ht) (extraPolynomial (F := F) n t ht)

theorem polynomialPoint_coeff_zero (n t : ℕ) (ht : t ≤ n)
    (p : PointIndex n t) (i : Fin 3) (a : Core n t i) :
    (polynomialPoint (F := F) n t ht p i a).coeff 0 = basePoint (F := F) n t ht p i a := by
  cases p <;> fin_cases i <;>
    simp [polynomialPoint, basePoint, oldPolynomial, extraPolynomial, oldPoint, extraPoint,
      factors_zero, factors_one, factors_two]
  rfl

theorem oldPolynomial_coeff_one (n t : ℕ) (ht : t ≤ n) (p : Fin n × Option (Fin n))
    (x : ∀ i, Core n t i) :
    (Tensor.simple (oldPolynomial (F := F) n t ht p) x).coeff 1 =
      -(gridPoint (F := F) n t p.1 p.2 (x 0) *
        oldVariation (F := F) n t ht p.1 p.2 (x 1) * Realization.basisVector (Sum.inl p.2) (x 2)) := by
  simp only [Tensor.simple, Fin.prod_univ_three, oldPolynomial, factors_zero, factors_one,
    factors_two, Polynomial.mul_coeff_one, Polynomial.mul_coeff_zero, Polynomial.coeff_sub,
    Polynomial.coeff_C, Polynomial.coeff_X, one_ne_zero, ite_false, ite_true,
    zero_mul, mul_zero, add_zero, zero_add, zero_sub,
    Lemmata.TensorRank.Tensor.pure]
  ring

theorem oldPolynomial_coeff_two (n t : ℕ) (ht : t ≤ n) (p : Fin n × Option (Fin n))
    (x : ∀ i, Core n t i) : (Tensor.simple (oldPolynomial (F := F) n t ht p) x).coeff 2 = 0 := by
  simp only [Tensor.simple, Fin.prod_univ_three, oldPolynomial, factors_zero, factors_one,
    factors_two, BigCentroid.mul_coeff_two, Polynomial.mul_coeff_one,
    Polynomial.mul_coeff_zero, Polynomial.coeff_sub, Polynomial.coeff_C, Polynomial.coeff_X,
    Lemmata.TensorRank.Tensor.pure]
  simp

theorem extraPolynomial_coeff_one (n t : ℕ) (ht : t ≤ n) (k : Option (Fin t))
    (x : ∀ i, Core n t i) :
    (Tensor.simple (extraPolynomial (F := F) n t ht k) x).coeff 1 =
      Realization.basisVector (Sum.inl none) (x 1) * variationC (F := F) n t k (x 2) +
        variationB (F := F) n t k (x 1) * Realization.basisVector (Sum.inl (selected ht k)) (x 2) := by
  simp only [Tensor.simple, Fin.prod_univ_three, extraPolynomial, factors_zero, factors_one,
    factors_two, one_mul, Polynomial.mul_coeff_one, Polynomial.mul_coeff_zero,
    Polynomial.coeff_add, Polynomial.coeff_C,
    Lemmata.TensorRank.Tensor.pure]
  simp

theorem extraPolynomial_coeff_two (n t : ℕ) (ht : t ≤ n) (k : Option (Fin t))
    (x : ∀ i, Core n t i) :
    (Tensor.simple (extraPolynomial (F := F) n t ht k) x).coeff 2 =
      variationB (F := F) n t k (x 1) * variationC (F := F) n t k (x 2) := by
  simp only [Tensor.simple, Fin.prod_univ_three, extraPolynomial, factors_zero, factors_one,
    factors_two, one_mul, BigCentroid.mul_coeff_two, Polynomial.mul_coeff_one,
    Polynomial.mul_coeff_zero, Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_X,
    Lemmata.TensorRank.Tensor.pure]
  simp

theorem variationC_sum (n t : ℕ) : (∑ k, variationC (F := F) n t k) = 0 := by
  rw [Fintype.sum_option]
  simp only [variationC, neg_add_cancel]

theorem oldVariation_inl (n t : ℕ) (ht : t ≤ n) (j : Fin n) (r b : Option (Fin n)) :
    oldVariation (F := F) n t ht j r (Sum.inl b) = 0 := by
  simp only [oldVariation, Finset.sum_apply, ite_apply, Pi.smul_apply, smul_eq_mul,
    Pi.zero_apply]
  apply Finset.sum_eq_zero
  intro k hk
  split_ifs <;> simp [Realization.basisVector]

theorem oldVariation_inr (n t : ℕ) (ht : t ≤ n) (j : Fin n) (r : Option (Fin n)) (k : Fin t) :
    oldVariation (F := F) n t ht j r (Sum.inr k) =
      if selected ht (some k) = r then lambda (F := F) n t j r else 0 := by
  simp only [oldVariation, Finset.sum_apply]
  rw [Finset.sum_eq_single k]
  · split_ifs <;> simp_all [Realization.basisVector]
  · intro c hc hck
    split_ifs <;> simp [Pi.smul_apply, Realization.basisVector, Ne.symm hck]
  · intro hk
    exact (hk (Finset.mem_univ _)).elim

theorem sum_oldPolynomial_coeff_one (n t : ℕ) (ht : t ≤ n) (x : ∀ i, Core n t i) :
    (∑ p, (Tensor.simple (oldPolynomial (F := F) n t ht p) x).coeff 1) =
      -(∑ k : Fin t, Realization.basisVector (F := RatFunc F) (Sum.inr k) (x 1) *
        Realization.basisVector (Sum.inl (selected ht (some k))) (x 2)) := by
  simp_rw [oldPolynomial_coeff_one]
  rw [Finset.sum_neg_distrib]
  congr 1
  rcases h1 : x 1 with b | k
  · simp [oldVariation_inl, Realization.basisVector]
  · simp only [Fintype.sum_prod_type, oldVariation_inr,
      mul_ite, ite_mul, mul_zero, zero_mul]
    have hd (j : Fin n) : (∑ r : Option (Fin n),
        if selected ht (some k) = r then gridPoint (F := F) n t j r (x 0) *
          lambda (F := F) n t j r * Realization.basisVector (Sum.inl r) (x 2) else 0) =
        gridPoint (F := F) n t j (selected ht (some k)) (x 0) *
          lambda (F := F) n t j (selected ht (some k)) *
          Realization.basisVector (Sum.inl (selected ht (some k))) (x 2) := by
      rw [Finset.sum_eq_single (selected ht (some k))]
      · simp
      · intro r hr hrk
        simp [Ne.symm hrk]
      · intro hk
        exact (hk (Finset.mem_univ _)).elim
    simp_rw [hd]
    rw [← Finset.sum_mul]
    have hg := congrFun (gridPoint_lambda (F := F) n t (selected ht (some k))) (x 0)
    erw [Finset.sum_apply, Pi.one_apply] at hg
    have hg' : (∑ j, gridPoint (F := F) n t j (selected ht (some k)) (x 0) *
        lambda (F := F) n t j (selected ht (some k))) = 1 := by
      calc
        _ = ∑ j, (lambda (F := F) n t j (selected ht (some k)) •
            gridPoint (F := F) n t j (selected ht (some k))) (x 0) := by
          apply Finset.sum_congr rfl
          intro j hj
          change gridPoint (F := F) n t j (selected ht (some k)) (x 0) *
              lambda (F := F) n t j (selected ht (some k)) =
            lambda (F := F) n t j (selected ht (some k)) *
              gridPoint (F := F) n t j (selected ht (some k)) (x 0)
          exact mul_comm _ _
        _ = 1 := hg
    rw [hg', one_mul]
    symm
    rw [Finset.sum_eq_single k]
    · simp [Realization.basisVector]
    · intro j hj hjk
      simp [Realization.basisVector, Ne.symm hjk]
    · intro hk
      exact (hk (Finset.mem_univ _)).elim

theorem sum_extraPolynomial_coeff_one (n t : ℕ) (ht : t ≤ n) (x : ∀ i, Core n t i) :
    (∑ k, (Tensor.simple (extraPolynomial (F := F) n t ht k) x).coeff 1) =
      ∑ k : Fin t, Realization.basisVector (F := RatFunc F) (Sum.inr k) (x 1) *
        Realization.basisVector (Sum.inl (selected ht (some k))) (x 2) := by
  simp_rw [extraPolynomial_coeff_one]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hc := congrFun (variationC_sum (F := F) n t) (x 2)
  erw [Finset.sum_apply, Pi.zero_apply] at hc
  rw [hc, mul_zero, zero_add, Fintype.sum_option]
  change (0 : RatFunc F) * _ + _ = _
  simp only [zero_mul, zero_add, variationB]

theorem polynomialPoint_coeff_one (n t : ℕ) (ht : t ≤ n) (x : ∀ i, Core n t i) :
    ((∑ p, Tensor.simple (polynomialPoint (F := F) n t ht p)) x).coeff 1 = 0 := by
  simp only [Finset.sum_apply, Fintype.sum_sum_type, polynomialPoint, Sum.elim_inl, Sum.elim_inr]
  erw [Polynomial.coeff_add]
  simp only [Polynomial.finsetSum_coeff]
  erw [sum_oldPolynomial_coeff_one, sum_extraPolynomial_coeff_one]
  exact neg_add_cancel _

theorem tau_map (n t : ℕ) (x : ∀ i, Core n t i) :
    algebraMap F (RatFunc F) (tau n t x) =
      ∑ k : Fin t, Realization.basisVector (F := RatFunc F) (Sum.inr k) (x 1) *
        Realization.basisVector (Sum.inr k) (x 2) := by
  simp only [tau, Finset.sum_apply, map_sum]
  have hm (k : Fin t) (a : Fin n) :
      algebraMap F (RatFunc F) (Realization.basisVector (F := F)
        (assignment n t a (Sum.inr k) (Sum.inr k)) x) =
        Realization.basisVector (F := RatFunc F) a (x 0) *
          Realization.basisVector (Sum.inr k) (x 1) * Realization.basisVector (Sum.inr k) (x 2) := by
    calc
      _ = Realization.basisVector (F := RatFunc F)
          (assignment n t a (Sum.inr k) (Sum.inr k)) x :=
        congrFun (Realization.map_basisVector (algebraMap F (RatFunc F)) _) x
      _ = _ := by
        have h := congrFun (Realization.simple_basisVector (F := RatFunc F)
          (assignment n t a (Sum.inr k) (Sum.inr k))) x
        simp only [Tensor.simple, Fin.prod_univ_three, assignment_zero, assignment_one,
          assignment_two,
          Lemmata.TensorRank.Tensor.pure] at h
        exact h.symm
  simp_rw [hm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  have hs : (∑ a : Fin n, Realization.basisVector (F := RatFunc F) a (x 0)) = 1 := by
    rw [Finset.sum_eq_single (show Fin n from x 0)]
    · exact ite_eq_left rfl
    · intro a ha hax
      simp [Realization.basisVector, Ne.symm hax]
    · intro hx
      exact (hx (Finset.mem_univ _)).elim
  rw [hs, one_mul]

theorem polynomialPoint_coeff_two (n t : ℕ) (ht : t ≤ n) (x : ∀ i, Core n t i) :
    ((∑ p, Tensor.simple (polynomialPoint (F := F) n t ht p)) x).coeff 2 =
      algebraMap F (RatFunc F) (tau n t x) := by
  simp only [Finset.sum_apply, Fintype.sum_sum_type, polynomialPoint, Sum.elim_inl, Sum.elim_inr]
  erw [Polynomial.coeff_add]
  simp only [Polynomial.finsetSum_coeff, oldPolynomial_coeff_two, Finset.sum_const_zero,
    zero_add, extraPolynomial_coeff_two]
  rw [Fintype.sum_option]
  change (0 : RatFunc F) * _ + _ = _
  simp only [zero_mul, zero_add, variationB, variationC]
  exact (tau_map (F := F) n t x).symm

end

end Lemmata.Centroid.Construction.Rectangular
