module

public import Lemmata.Centroid.Def.Rank
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.BigOperators

@[expose] public section

open scoped BigOperators
open Classical

namespace Lemmata.Centroid

universe u v w

namespace PolynomialKernel

variable {F : Type u} [Field F]

theorem coeff_eq_sum_eval {J : Type*} [Fintype J] [DecidableEq J]
    (nodes : J → F) (hnodes : Function.Injective nodes)
    (p : Polynomial F) (d : ℕ) (hdegree : p.degree < Fintype.card J) :
    p.coeff d = ∑ j, p.eval (nodes j) *
      (Lagrange.basis Finset.univ nodes j).coeff d := by
  have hinj : Set.InjOn nodes (↑(Finset.univ : Finset J)) := hnodes.injOn
  have hinterp := Lagrange.eq_interpolate hinj (by simpa using hdegree) (f := p)
  calc
    p.coeff d = (Lagrange.interpolate Finset.univ nodes
        (fun j => p.eval (nodes j))).coeff d := congrArg (fun q => q.coeff d) hinterp
    _ = _ := by
      simp only [Lagrange.interpolate_apply, Polynomial.finsetSum_coeff,
        Polynomial.coeff_C_mul]

end PolynomialKernel

namespace Tensor

variable {F : Type u} {ι : Type v} {V : ι → Type w}
variable [Field F] [Fintype ι] [Nonempty ι]

omit [Nonempty ι] in
theorem rankAtMost_sum {J : Type*} (s : Finset J)
    (T : J → Tensor F ι V) (r : J → ℕ)
    (h : ∀ j ∈ s, RankAtMost (T j) (r j)) :
    RankAtMost (∑ j ∈ s, T j) (∑ j ∈ s, r j) := by
  induction s using Finset.induction_on with
  | empty => simpa using rankAtMost_zero (R := F) (ι := ι) (V := V)
  | @insert j s hj ih =>
      rw [Finset.sum_insert hj, Finset.sum_insert hj]
      exact (h j (Finset.mem_insert_self _ _)).add
        (ih (fun q hq => h q (Finset.mem_insert_of_mem hq)))

/-- Coefficient extraction from any family whose evaluations have bounded rank. -/
theorem rankAtMost_coeff_of_eval {J : Type*} [Fintype J] [DecidableEq J]
    (nodes : J → F) (hnodes : Function.Injective nodes)
    (P : Tensor (Polynomial F) ι V) (r d : ℕ)
    (heval : ∀ j, RankAtMost (mapCoefficients (Polynomial.evalRingHom (nodes j)) P) r)
    (hdegree : ∀ x, (P x).degree < Fintype.card J) :
    RankAtMost (fun x => (P x).coeff d) (Fintype.card J * r) := by
  let w : J → F := fun j => (Lagrange.basis Finset.univ nodes j).coeff d
  have h := rankAtMost_sum Finset.univ
    (fun j => w j • mapCoefficients (Polynomial.evalRingHom (nodes j)) P)
    (fun _ => r) (fun j _ => (heval j).smul (w j))
  have heq : (fun x => (P x).coeff d) =
      ∑ j, w j • mapCoefficients (Polynomial.evalRingHom (nodes j)) P := by
    funext x
    rw [PolynomialKernel.coeff_eq_sum_eval nodes hnodes _ d (hdegree x)]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mapCoefficients]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [heq]
  simpa [Nat.mul_comm] using h

theorem RankAtMost.coeff {J : Type*} [Fintype J] [DecidableEq J]
    (nodes : J → F) (hnodes : Function.Injective nodes)
    {P : Tensor (Polynomial F) ι V} {r : ℕ} (hP : RankAtMost P r)
    (d : ℕ) (hdegree : ∀ x, (P x).degree < Fintype.card J) :
    RankAtMost (fun x => (P x).coeff d) (Fintype.card J * r) :=
  rankAtMost_coeff_of_eval nodes hnodes P r d
    (fun j => hP.mapCoefficients (Polynomial.evalRingHom (nodes j))) hdegree

/-- The budget bounds ranks at nonzero evaluation points. -/
theorem rank_power_of_polynomial_budget [CharZero F]
    (P : Tensor (Polynomial F) ι V) (T : Tensor F ι V) (r D : ℕ)
    (hconstant : ∀ x, (P x).coeff 0 = T x)
    (hrank : ∀ t : F, t ≠ 0 → RankAtMost (mapCoefficients (Polynomial.evalRingHom t) P) r)
    (hdegree : ∀ x, (P x).natDegree ≤ D) (n : ℕ) :
    RankAtMost (power T n) ((D*n+1)*r^n) := by
  let nodes : Fin (D*n+1) → F := fun j => ((j.val+1 : ℕ) : F)
  have hinj : Function.Injective nodes := by
    intro i j h
    apply Fin.ext
    exact Nat.add_right_cancel (Nat.cast_injective h)
  have hnodes (j : Fin (D*n+1)) : nodes j ≠ 0 := by
    dsimp [nodes]
    exact Nat.cast_ne_zero.mpr (Nat.succ_ne_zero j.val)
  have heval (j : Fin (D*n+1)) :
      RankAtMost (mapCoefficients (Polynomial.evalRingHom (nodes j)) (power P n)) (r^n) := by
    have h := (hrank (nodes j) (hnodes j)).power n
    have heq : mapCoefficients (Polynomial.evalRingHom (nodes j)) (power P n) =
        power (mapCoefficients (Polynomial.evalRingHom (nodes j)) P) n := by
      funext x
      simp only [mapCoefficients, power, map_prod, Lemmata.TensorRank.Tensor.power]
    rw [heq]
    exact h
  have hd (x : ∀ i, Fin n → V i) :
      (power P n x).degree < Fintype.card (Fin (D*n+1)) := by
    have hnat : (power P n x).natDegree ≤ D*n := by
      calc
        _ ≤ ∑ j, (P (fun i => x i j)).natDegree := Polynomial.natDegree_prod_le _ _
        _ ≤ ∑ _j : Fin n, D := Finset.sum_le_sum (fun j _ => hdegree (fun i => x i j))
        _ = D*n := by simp [Nat.mul_comm]
    simp only [Fintype.card_fin]
    exact lt_of_le_of_lt (Polynomial.degree_le_of_natDegree_le hnat)
      (WithBot.coe_lt_coe.mpr (Nat.lt_succ_self (D*n)))
  have h := rankAtMost_coeff_of_eval nodes hinj (power P n) (r^n) 0 heval hd
  have heq : (fun x => (power P n x).coeff 0) = power T n := by
    funext x
    simp only [power, Polynomial.coeff_zero_prod, hconstant, Lemmata.TensorRank.Tensor.power]
  rw [heq, Fintype.card_fin] at h
  exact h

end Tensor

/-- A supplied polynomial decomposition, with a prescribed leading tensor.
The order and degree are explicit, so all interpolation costs remain finite. -/
structure PolynomialApproximation {F : Type u} {ι : Type v} {V : ι → Type w}
    [Field F] [Fintype ι] (T : Tensor F ι V) (r d D : ℕ) where
  polynomial : Tensor (Polynomial F) ι V
  rank_bound : Tensor.RankAtMost polynomial r
  vanishes : ∀ x k, k < d → (polynomial x).coeff k = 0
  leading : ∀ x, (polynomial x).coeff d = T x
  degree_bound : ∀ x, (polynomial x).degree ≤ D

namespace PolynomialApproximation

variable {F : Type u} {ι : Type v} {V : ι → Type w}
variable [Field F] [Fintype ι] [Nonempty ι]
variable {T : Tensor F ι V} {r d D : ℕ}

noncomputable def normalized (A : PolynomialApproximation T r d D) :
    Tensor (Polynomial F) ι V :=
  fun x => Classical.choose (Polynomial.X_pow_dvd_iff.mpr (A.vanishes x))

omit [Nonempty ι] in
theorem polynomial_eq (A : PolynomialApproximation T r d D) (x : ∀ i, V i) :
    A.polynomial x = Polynomial.X^d * A.normalized x :=
  Classical.choose_spec (Polynomial.X_pow_dvd_iff.mpr (A.vanishes x))

omit [Nonempty ι] in
theorem normalized_constant (A : PolynomialApproximation T r d D) (x : ∀ i, V i) :
    (A.normalized x).coeff 0 = T x := by
  have h := A.leading x
  rw [A.polynomial_eq] at h
  simpa only [Polynomial.coeff_X_pow_mul', le_refl, ite_true, Nat.sub_self] using h

omit [Nonempty ι] in
theorem power_polynomial_eq (A : PolynomialApproximation T r d D) (n : ℕ)
    (x : ∀ i, Fin n → V i) :
    Tensor.power A.polynomial n x =
      Polynomial.X^(d*n) * Tensor.power A.normalized n x := by
  simp [Tensor.power, A.polynomial_eq, Finset.prod_mul_distrib, ← pow_mul]

noncomputable def power (A : PolynomialApproximation T r d D) (n : ℕ) :
    PolynomialApproximation (Tensor.power T n) (r^n) (d*n) (D*n) where
  polynomial := Tensor.power A.polynomial n
  rank_bound := A.rank_bound.power n
  vanishes := by
    intro x k hk
    rw [A.power_polynomial_eq]
    simp only [Polynomial.coeff_X_pow_mul', Nat.not_le_of_lt hk, ite_false]
  leading := by
    intro x
    rw [A.power_polynomial_eq]
    simp only [Polynomial.coeff_X_pow_mul', le_refl, ite_true, Nat.sub_self,
      Tensor.power, Polynomial.coeff_zero_prod, A.normalized_constant,
      Lemmata.TensorRank.Tensor.power]
  degree_bound := by
    intro x
    apply Polynomial.degree_le_of_natDegree_le
    calc
      (Tensor.power A.polynomial n x).natDegree ≤
          ∑ j, (A.polynomial (fun i => x i j)).natDegree :=
        Polynomial.natDegree_prod_le _ _
      _ ≤ ∑ _j : Fin n, D := by
        apply Finset.sum_le_sum
        intro j _
        exact Polynomial.natDegree_le_of_degree_le (A.degree_bound (fun i => x i j))
      _ = D*n := by simp [Nat.mul_comm]

theorem rank_power [CharZero F] (A : PolynomialApproximation T r d D) (n : ℕ) :
    Tensor.RankAtMost (Tensor.power T n) ((D*n+1)*r^n) := by
  let nodes : Fin (D*n+1) → F := fun j => (j.val : F)
  have hinj : Function.Injective nodes := by
    intro i j h
    apply Fin.ext
    exact Nat.cast_injective h
  have hd (x : ∀ i, Fin n → V i) :
      ((A.power n).polynomial x).degree < Fintype.card (Fin (D*n+1)) := by
    simp only [Fintype.card_fin]
    exact lt_of_le_of_lt ((A.power n).degree_bound x)
      (WithBot.coe_lt_coe.mpr (Nat.lt_succ_self (D*n)))
  have h := (A.power n).rank_bound.coeff nodes hinj (d*n) hd
  have heq : (fun x => ((A.power n).polynomial x).coeff (d*n)) = Tensor.power T n := by
    funext x
    exact (A.power n).leading x
  rw [heq, Fintype.card_fin] at h
  exact h

theorem rank_normalized_eval (A : PolynomialApproximation T r d D)
    (t : F) (ht : t ≠ 0) :
    Tensor.RankAtMost (Tensor.mapCoefficients (Polynomial.evalRingHom t) A.normalized) r := by
  have h := (A.rank_bound.mapCoefficients (Polynomial.evalRingHom t)).smul ((t^d)⁻¹)
  have heq : (t^d)⁻¹ • Tensor.mapCoefficients (Polynomial.evalRingHom t) A.polynomial =
      Tensor.mapCoefficients (Polynomial.evalRingHom t) A.normalized := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, Tensor.mapCoefficients]
    change (t^d)⁻¹ * (A.polynomial x).eval t = (A.normalized x).eval t
    rw [A.polynomial_eq, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
    rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero d ht), one_mul]
  rw [heq] at h
  exact h

end PolynomialApproximation
end Lemmata.Centroid
