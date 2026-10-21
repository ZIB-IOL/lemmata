module

public import Lemmata.TensorRank.Def.Polynomial
public import Lemmata.TensorRank.Proof.Products
public import Lemmata.TensorRank.Proof.Maps
public import Lemmata.TensorRank.Proof.Growth
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.BigOperators

@[expose] public section

set_option autoImplicit false

open scoped BigOperators
open Classical

namespace Lemmata.TensorRank.Tensor

universe u v w

variable {R : Type u} [CommSemiring R] {I : Type v} [Fintype I] {V : I → Type w}

theorem RankLE.smul {T : Tensor R I V} {r : ℕ} (h : RankLE T r) (a : R) :
    RankLE (a • T) r := by
  obtain ⟨c, v, rfl⟩ := h
  refine ⟨fun j => a * c j, v, ?_⟩
  funext x
  simp [Finset.mul_sum, mul_assoc]

theorem rankLE_sum_fin (n r : ℕ) (T : Fin n → Tensor R I V)
    (h : ∀ j, RankLE (T j) r) : RankLE (∑ j, T j) (n * r) := by
  induction n with
  | zero => simpa using rankLE_zero (R := R) (I := I) (V := V) 0
  | succ n ih =>
    rw [Fin.sum_univ_succ]
    simpa [Nat.succ_mul, Nat.add_comm] using
      (h 0).add (ih (fun j => T j.succ) (fun j => h j.succ))

variable {F : Type u} [Field F]

theorem RankLE.evaluate {P : Tensor (Polynomial F) I V} {r : ℕ}
    (h : RankLE P r) (t : F) : RankLE (evaluate P t) r := by
  obtain ⟨c, v, rfl⟩ := h
  refine ⟨fun j => Polynomial.eval t (c j), fun j i a => Polynomial.eval t (v j i a), ?_⟩
  funext x
  change Polynomial.eval t (∑ j, c j * pure (v j) x) = _
  simp [pure, Polynomial.eval_finsetSum, Polynomial.eval_prod]

omit [Fintype I] in
theorem coefficient_eq_interpolation {D : ℕ} (P : Tensor (Polynomial F) I V)
    (nodes : Fin (D + 1) → F) (hnodes : Function.Injective nodes)
    (hD : DegreeLE P D) (e : ℕ) :
    coefficient P e = ∑ j,
      (Lagrange.basis Finset.univ nodes j).coeff e • evaluate P (nodes j) := by
  funext x
  have hd : (P x).degree < (Finset.univ : Finset (Fin (D + 1))).card := by
    apply lt_of_le_of_lt (Polynomial.degree_le_of_natDegree_le (hD x))
    rw [Finset.card_univ, Fintype.card_fin]
    exact_mod_cast Nat.lt_succ_self D
  have h := congrArg (fun p : Polynomial F => p.coeff e)
    (Lagrange.eq_interpolate hnodes.injOn hd)
  simpa [coefficient, evaluate, Lagrange.interpolate_apply,
    Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, mul_comm] using h

theorem rankLE_coefficient [Infinite F] (P : Tensor (Polynomial F) I V)
    (D r e : ℕ) (hD : DegreeLE P D) (hr : ∀ t, RankLE (evaluate P t) r) :
    RankLE (coefficient P e) ((D + 1) * r) := by
  let nodes : Fin (D + 1) → F := fun j => Infinite.natEmbedding F j.val
  have hinj : Function.Injective nodes := by
    intro i j h
    exact Fin.ext ((Infinite.natEmbedding F).injective h)
  rw [coefficient_eq_interpolation P nodes hinj hD e]
  exact rankLE_sum_fin _ _ _ (fun j => (hr (nodes j)).smul _)

omit [Fintype I] in
theorem evaluate_power (P : Tensor (Polynomial F) I V) (t : F) (m : ℕ) :
    evaluate (power P m) t = power (evaluate P t) m := by
  funext x
  simp [evaluate, power, Polynomial.eval_prod]

omit [Fintype I] in
theorem DegreeLE.power {P : Tensor (Polynomial F) I V} {D : ℕ}
    (h : DegreeLE P D) (m : ℕ) : DegreeLE (power P m) (D * m) := by
  intro x
  calc
    (Lemmata.TensorRank.Tensor.power P m x).natDegree ≤ ∑ j : Fin m, (P (fun i => x i j)).natDegree :=
      Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ _j : Fin m, D := Finset.sum_le_sum (fun j _ => h (fun i => x i j))
    _ = D * m := by simp [Nat.mul_comm]

private theorem coeff_product_leading {m e : ℕ} (p : Fin m → Polynomial F)
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
theorem Leading.power_coefficient {P : Tensor (Polynomial F) I V} {T : Tensor F I V}
    {e : ℕ} (h : Leading P e T) (m : ℕ) :
    coefficient (power P m) (e * m) = power T m := by
  funext x
  change (∏ j : Fin m, P (fun i => x i j)).coeff (e * m) = _
  rw [coeff_product_leading _ (fun j d hd => congrFun (h.2 d hd) (fun i => x i j))]
  simp only [← h.1, coefficient, power]

theorem rankLE_power_of_leading [Infinite F] (P : Tensor (Polynomial F) I V)
    (T : Tensor F I V) (e D r m : ℕ) (h : Leading P e T) (hD : DegreeLE P D)
    (hr : ∀ t, RankLE (evaluate P t) r) :
    RankLE (power T m) ((D * m + 1) * r ^ m) := by
  rw [← h.power_coefficient m]
  apply rankLE_coefficient (power P m) (D * m) (r ^ m) (e * m) (hD.power m)
  intro t
  rw [evaluate_power]
  exact (hr t).power m

theorem rank_power_le_of_leading [Infinite F] [∀ i, Fintype (V i)]
    (P : Tensor (Polynomial F) I V) (T : Tensor F I V) (e D r m : ℕ)
    (h : Leading P e T) (hD : DegreeLE P D) (hr : ∀ t, RankLE (evaluate P t) r) :
    rank (power T m) ≤ (D * m + 1) * r ^ m :=
  (rank_le_iff _ _).mpr (rankLE_power_of_leading P T e D r m h hD hr)

theorem exists_degree_bound [∀ i, Fintype (V i)] (P : Tensor (Polynomial F) I V) :
    ∃ D, DegreeLE P D := by
  refine ⟨(Finset.univ : Finset (∀ i, V i)).sup (fun x => (P x).natDegree), ?_⟩
  intro x
  exact Finset.le_sup (f := fun x : ∀ i, V i => (P x).natDegree) (Finset.mem_univ x)

theorem asymptoticRank_le_of_leading_degree [Infinite F] [∀ i, Fintype (V i)]
    (P : Tensor (Polynomial F) I V) (T : Tensor F I V) (e D r : ℕ)
    (h : Leading P e T) (hD : DegreeLE P D) (hr : ∀ t, RankLE (evaluate P t) r) :
    asymptoticRank T ≤ r := by
  apply asymptoticRank_le_of_polynomial_power_bound T ((D : ℝ) + 1) r
    (by positivity) (by positivity) 1
  intro m _hm
  have hbudget : (rank (power T m) : ℝ) ≤ ((D : ℝ) * m + 1) * (r : ℝ) ^ m := by
    exact_mod_cast rank_power_le_of_leading P T e D r m h hD hr
  apply hbudget.trans
  simp only [pow_one]
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg (Nat.cast_nonneg r) m)
  nlinarith [Nat.cast_nonneg (α := ℝ) D, Nat.cast_nonneg (α := ℝ) m]

theorem asymptoticRank_le_of_leading [Infinite F] [∀ i, Fintype (V i)]
    (P : Tensor (Polynomial F) I V) (T : Tensor F I V) (e r : ℕ)
    (h : Leading P e T) (hr : ∀ t, RankLE (evaluate P t) r) :
    asymptoticRank T ≤ r := by
  obtain ⟨D, hD⟩ := exists_degree_bound P
  exact asymptoticRank_le_of_leading_degree P T e D r h hD hr

variable {W : I → Type*} [∀ i, Fintype (V i)]

theorem evaluate_polynomialMap (A : ∀ i, W i → V i → Polynomial F)
    (T : Tensor F I V) (t : F) :
    evaluate (polynomialMap A T) t = localMap (fun i y x => (A i y x).eval t) T := by
  funext y
  simp [evaluate, polynomialMap, localMap, Polynomial.eval_finsetSum, Polynomial.eval_prod]

theorem rankLE_power_of_polynomialMap_leading [Infinite F]
    (A : ∀ i, W i → V i → Polynomial F) (T : Tensor F I V) (S : Tensor F I W)
    (e D m : ℕ) (h : Leading (polynomialMap A T) e S)
    (hD : DegreeLE (polynomialMap A T) D) :
    RankLE (power S m) ((D * m + 1) * rank (power T m)) := by
  rw [← h.power_coefficient m]
  apply rankLE_coefficient (power (polynomialMap A T) m) (D * m)
    (rank (power T m)) (e * m) (hD.power m)
  intro t
  rw [evaluate_power, evaluate_polynomialMap, ← localMap_power]
  exact (rankLE_rank (power T m)).localMap _

theorem rank_power_le_of_polynomialMap_leading [Infinite F] [∀ i, Fintype (W i)]
    (A : ∀ i, W i → V i → Polynomial F) (T : Tensor F I V) (S : Tensor F I W)
    (e D m : ℕ) (h : Leading (polynomialMap A T) e S)
    (hD : DegreeLE (polynomialMap A T) D) :
    rank (power S m) ≤ (D * m + 1) * rank (power T m) :=
  (rank_le_iff _ _).mpr (rankLE_power_of_polynomialMap_leading A T S e D m h hD)

theorem Degenerates.asymptoticRank_le [Infinite F] [∀ i, Fintype (W i)]
    {S : Tensor F I W} {T : Tensor F I V} (h : Degenerates S T) :
    asymptoticRank S ≤ asymptoticRank T := by
  obtain ⟨A, e, h⟩ := h
  obtain ⟨D, hD⟩ := exists_degree_bound (polynomialMap A T)
  apply asymptoticRank_le_of_linear_rank_power S T D 1 (by positivity) (by positivity)
  intro m _hm
  exact_mod_cast rank_power_le_of_polynomialMap_leading A T S e D m h hD

end Lemmata.TensorRank.Tensor
