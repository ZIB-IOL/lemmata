module

/-
Copyright (c) 2026 Kirill Khoruzhii. Licensed under Apache-2.0.
Modified for the arbitrary-field tensor-rank formalization; namespace and imports
adapted for Lemmata. See docs/tensor-rank/NOTICE.txt for upstream attribution
and modification notices, and docs/tensor-rank/LICENSE.txt for the license.
-/

public import Lemmata.TensorRank.Def.Polynomial
public import Lemmata.TensorRank.Proof.Products
public import Lemmata.TensorRank.Proof.Maps
public import Lemmata.TensorRank.Proof.Growth
public import Lemmata.TensorRank.Proof.DirectSum
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Degree.Support

@[expose] public section

set_option autoImplicit false

open scoped BigOperators
open Classical

namespace Lemmata.TensorRank.Tensor

universe u v w z

variable {R : Type u} [CommSemiring R] {I : Type v} [Fintype I]

private theorem product_monomial (d : I → ℕ) (a : I → R) :
    (∏ i, Polynomial.monomial (d i) (a i)) =
      Polynomial.monomial (∑ i, d i) (∏ i, a i) := by
  have h (s : Finset I) : (∏ i ∈ s, Polynomial.monomial (d i) (a i)) =
      Polynomial.monomial (∑ i ∈ s, d i) (∏ i ∈ s, a i) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      simp only [Finset.prod_insert hi, Finset.sum_insert hi, ih,
        Polynomial.monomial_mul_monomial]
  exact h Finset.univ

theorem coefficient_prod_eq_sum (p : I → Polynomial R) (D e : ℕ)
    (hD : ∀ i, (p i).natDegree ≤ D) :
    (∏ i, p i).coeff e = ∑ d : I → Fin (D + 1),
      if (∑ i, (d i : ℕ)) = e then ∏ i, (p i).coeff (d i) else 0 := by
  have hp (i : I) : p i = ∑ j : Fin (D + 1),
      Polynomial.monomial (j : ℕ) ((p i).coeff j) := by
    exact ((p i).as_sum_range' (D + 1) (Nat.lt_succ_of_le (hD i))).trans
      (Fin.sum_univ_eq_sum_range
        (fun j : ℕ => Polynomial.monomial j ((p i).coeff j)) (D + 1)).symm
  have hx : (∏ i, p i) = ∑ d : I → Fin (D + 1),
      Polynomial.monomial (∑ i, (d i : ℕ)) (∏ i, (p i).coeff (d i)) := by
    calc
      _ = ∏ i, ∑ j : Fin (D + 1),
          Polynomial.monomial (j : ℕ) ((p i).coeff j) :=
        Finset.prod_congr rfl (fun i _ => hp i)
      _ = ∑ d : I → Fin (D + 1),
          ∏ i, Polynomial.monomial (d i : ℕ) ((p i).coeff (d i)) :=
        Fintype.prod_sum _
      _ = _ := Finset.sum_congr rfl (fun d _ => product_monomial _ _)
  rw [hx, Polynomial.finsetSum_coeff]
  exact Finset.sum_congr rfl (fun d _ => Polynomial.coeff_monomial)

private theorem coeff_product_leading {m e : ℕ} (p : Fin m → Polynomial R)
    (h : ∀ i j, j < e → (p i).coeff j = 0) :
    (∏ i, p i).coeff (e * m) = ∏ i, (p i).coeff e := by
  have hd (i : Fin m) : Polynomial.X ^ e ∣ p i :=
    Polynomial.X_pow_dvd_iff.mpr (h i)
  choose q hq using hd
  have hp : (∏ i, p i) = Polynomial.X ^ (e * m) * ∏ i, q i := by
    simp [hq, Finset.prod_mul_distrib, ← pow_mul]
  have hc (i : Fin m) : (p i).coeff e = (q i).coeff 0 := by
    rw [hq i]
    simpa using Polynomial.coeff_X_pow_mul (q i) e 0
  rw [hp]
  simpa [hc, Polynomial.coeff_zero_prod] using
    Polynomial.coeff_X_pow_mul (∏ i, q i) (e * m) 0

omit [Fintype I] in
theorem Leading.power_coefficient {V : I → Type w} {P : Tensor (Polynomial R) I V} {T : Tensor R I V}
    {e : ℕ} (h : Leading P e T) (m : ℕ) :
    coefficient (power P m) (e * m) = power T m := by
  funext x
  change (∏ j : Fin m, P (fun i => x i j)).coeff (e * m) = _
  rw [coeff_product_leading _ (fun j d hd => congrFun (h.2 d hd) (fun i => x i j))]
  simp only [← h.1, coefficient, power]

variable {V : I → Type w} [∀ i, Fintype (V i)] {W : I → Type z}

theorem localMap_scale_party (A : ∀ i, W i → V i → R) (T : Tensor R I V) (i₀ : I) (c : R) :
    localMap (fun i y x => (if i = i₀ then c else 1) * A i y x) T = c • localMap A T := by
  funext y
  simp only [localMap, Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib]
  have hc : (∏ i : I, if i = i₀ then c else 1) = c := by simp
  simp only [hc, Finset.mul_sum, mul_assoc]

theorem linear_combination_restricts_copies [Nonempty I] (T : Tensor R I V) (l : ℕ)
    (A : Fin l → ∀ i, W i → V i → R) (c : Fin l → R) :
    Restricts (∑ q, c q • localMap (A q) T) (copies l T) := by
  let i₀ : I := Classical.arbitrary I
  refine ⟨fun i y x => (if i = i₀ then c x.1 else 1) * A x.1 i y x.2, ?_⟩
  rw [localMap_copies]
  exact Finset.sum_congr rfl (fun q _ => (localMap_scale_party (A q) T i₀ (c q)).symm)

theorem coefficient_polynomialMap_eq_sum
    (A : ∀ i, W i → V i → Polynomial R) (T : Tensor R I V) (D e : ℕ)
    (hD : ∀ i y x, (A i y x).natDegree ≤ D) :
    coefficient (polynomialMap A T) e = ∑ d : I → Fin (D + 1),
      (if (∑ i, (d i : ℕ)) = e then (1 : R) else 0) •
        localMap (fun i y x => (A i y x).coeff (d i)) T := by
  funext y
  simp only [coefficient, polynomialMap, localMap, Polynomial.finsetSum_coeff,
    Polynomial.coeff_mul_C, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp_rw [coefficient_prod_eq_sum _ D e (fun i => hD i (y i) _)]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  by_cases hd : (∑ i, (d i : ℕ)) = e <;> simp [hd]

theorem coefficient_polynomialMap_restricts_copies [Nonempty I]
    (A : ∀ i, W i → V i → Polynomial R) (T : Tensor R I V) (D e : ℕ)
    (hD : ∀ i y x, (A i y x).natDegree ≤ D) :
    Restricts (coefficient (polynomialMap A T) e)
      (copies ((D + 1) ^ Fintype.card I) T) := by
  let l := (D + 1) ^ Fintype.card I
  let f : (I → Fin (D + 1)) ≃ Fin l := Fintype.equivFinOfCardEq (by simp [l])
  have hs : coefficient (polynomialMap A T) e = ∑ q : Fin l,
      (if (∑ i, (f.symm q i : ℕ)) = e then (1 : R) else 0) •
        localMap (fun i y x => (A i y x).coeff (f.symm q i)) T := by
    rw [coefficient_polynomialMap_eq_sum A T D e hD]
    exact Fintype.sum_equiv f _ _ (fun d => by simp)
  rw [hs]
  exact linear_combination_restricts_copies T l
    (fun q i y x => (A i y x).coeff (f.symm q i)) _

theorem polynomialMap_power (A : ∀ i, W i → V i → Polynomial R)
    (T : Tensor R I V) (n : ℕ) :
    polynomialMap (powerKernel A n) (power T n) = power (polynomialMap A T) n := by
  have hc : (fun x => Polynomial.C (power T n x)) =
      power (fun x => Polynomial.C (T x)) n := by
    funext x
    simp only [power, map_prod]
  change localMap (powerKernel A n) (fun x => Polynomial.C (power T n x)) = _
  rw [hc, localMap_power]
  rfl

omit [Fintype I] [∀ i, Fintype (V i)] in
theorem natDegree_powerKernel_le (A : ∀ i, W i → V i → Polynomial R)
    (D n : ℕ) (hD : ∀ i y x, (A i y x).natDegree ≤ D)
    (i : I) (y : Fin n → W i) (x : Fin n → V i) :
    (powerKernel A n i y x).natDegree ≤ D * n := by
  calc
    _ ≤ ∑ j : Fin n, (A i (y j) (x j)).natDegree := Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ _j : Fin n, D := Finset.sum_le_sum (fun j _ => hD i (y j) (x j))
    _ = _ := by simp [Nat.mul_comm]

variable {F : Type u} [Field F] [Nonempty I]

theorem power_restricts_copies_of_polynomial_leading
    (A : ∀ i, W i → V i → Polynomial F) (T : Tensor F I V) (S : Tensor F I W)
    (D e n : ℕ) (hD : ∀ i y x, (A i y x).natDegree ≤ D)
    (h : Leading (polynomialMap A T) e S) :
    Restricts (power S n) (copies ((D * n + 1) ^ Fintype.card I) (power T n)) := by
  rw [← h.power_coefficient n, ← polynomialMap_power]
  exact coefficient_polynomialMap_restricts_copies (powerKernel A n) (power T n)
    (D * n) (e * n) (natDegree_powerKernel_le A D n hD)

variable [∀ i, Fintype (W i)]

theorem Degenerates.exists_power_copies {S : Tensor F I W} {T : Tensor F I V}
    (h : Degenerates S T) : ∃ D, ∀ n,
      Restricts (power S n) (copies ((D * n + 1) ^ Fintype.card I) (power T n)) := by
  obtain ⟨A, e, h⟩ := h
  let D := (Finset.univ : Finset (Σ i, W i × V i)).sup
    (fun p => (A p.1 p.2.1 p.2.2).natDegree)
  have hD (i : I) (y : W i) (x : V i) : (A i y x).natDegree ≤ D :=
    Finset.le_sup (f := fun p : Σ i, W i × V i => (A p.1 p.2.1 p.2.2).natDegree)
      (Finset.mem_univ ⟨i, y, x⟩)
  exact ⟨D, fun n => power_restricts_copies_of_polynomial_leading A T S D e n hD h⟩

theorem Degenerates.asymptoticRank_le
    {S : Tensor F I W} {T : Tensor F I V} (h : Degenerates S T) :
    asymptoticRank S ≤ asymptoticRank T := by
  obtain ⟨D, hD⟩ := h.exists_power_copies
  let k := Fintype.card I
  apply asymptoticRank_le_of_polynomial_rank_power S T (((D : ℝ) + 1) ^ k)
    (by positivity) k
  intro n _hn
  have hcopies : rank (copies ((D * n + 1) ^ k) (power T n)) ≤
      (D * n + 1) ^ k * rank (power T n) := by
    exact (rank_product_le (diagonal (R := F) (I := I) ((D * n + 1) ^ k))
      (power T n)).trans (Nat.mul_le_mul_right _ (rank_diagonal_le _))
  have hr : (rank (power S n) : ℝ) ≤
      ((D : ℝ) * n + 1) ^ k * (rank (power T n) : ℝ) := by
    exact_mod_cast (hD n).rank_le.trans hcopies
  apply hr.trans
  rw [← mul_pow]
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
  apply pow_le_pow_left₀ (by positivity)
  nlinarith [Nat.cast_nonneg (α := ℝ) D, Nat.cast_nonneg (α := ℝ) n]

end Lemmata.TensorRank.Tensor
