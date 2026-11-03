module

/-
Copyright (c) 2026 Kirill Khoruzhii. Licensed under Apache-2.0.
Modified for the arbitrary-field tensor-rank formalization; namespace and imports
adapted for Lemmata. See docs/tensor-rank/NOTICE.txt for upstream attribution
and modification notices, and docs/tensor-rank/LICENSE.txt for the license.
-/

public import Lemmata.TensorRank.Def.Polynomial
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
public import Mathlib.Algebra.Polynomial.Coeff
public import Lean.Elab.Tactic.Omega

@[expose] public section

set_option autoImplicit false

open scoped BigOperators
open Classical

noncomputable section

namespace Lemmata.TensorRank.PolynomialInterpolation

variable {𝕜 : Type*} [Field 𝕜]

def node (L : ℕ) (i : Fin L) : Polynomial 𝕜 := Polynomial.X ^ i.val

def dual (L : ℕ) (s t : Fin L) : Polynomial 𝕜 :=
  (Matrix.vandermonde (node (𝕜 := 𝕜) L)).adjugate s t

def determinant (L : ℕ) : Polynomial 𝕜 :=
  (Matrix.vandermonde (node (𝕜 := 𝕜) L)).det

theorem node_injective (L : ℕ) : Function.Injective (node (𝕜 := 𝕜) L) := by
  intro i j h
  apply Fin.ext
  simpa only [node, Polynomial.natDegree_X_pow] using congrArg Polynomial.natDegree h

theorem determinant_ne_zero (L : ℕ) : determinant (𝕜 := 𝕜) L ≠ 0 :=
  Matrix.det_vandermonde_ne_zero_iff.mpr (node_injective L)

theorem filter (L : ℕ) (s : Fin L) (m : ℕ) (hm : m < L) :
    (∑ t, dual (𝕜 := 𝕜) L s t * node L t ^ m) =
      if m = s.val then determinant (𝕜 := 𝕜) L else 0 := by
  have h := congrFun (congrFun
    (Matrix.adjugate_mul (Matrix.vandermonde (node (𝕜 := 𝕜) L))) s) ⟨m, hm⟩
  simpa only [Matrix.mul_apply, Matrix.vandermonde_apply, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Fin.ext_iff,
    dual, determinant, eq_comm] using h

end Lemmata.TensorRank.PolynomialInterpolation

namespace Lemmata.TensorRank.Tensor

variable {𝕜 : Type*} [Field 𝕜]

private theorem coeff_mul_first (p q : Polynomial 𝕜) (d e : ℕ)
    (hp : ∀ j < d, p.coeff j = 0) (hq : ∀ j < e, q.coeff j = 0) :
    (p * q).coeff (d + e) = p.coeff d * q.coeff e := by
  rw [Polynomial.coeff_mul, Finset.sum_eq_single_of_mem (d, e)]
  · exact Finset.mem_antidiagonal.mpr rfl
  rintro ⟨i, j⟩ hij hne
  have heq : i + j = d + e := Finset.mem_antidiagonal.mp hij
  by_cases hi : i < d
  · rw [hp i hi, zero_mul]
  · have hj : j < e := by
      by_contra hn
      have hi' : d ≤ i := by omega
      have hj' : e ≤ j := by omega
      have : i = d ∧ j = e := by omega
      exact hne (Prod.ext this.1 this.2)
    rw [hq j hj, mul_zero]

theorem Leading.polynomial_mul {I : Type*} {V : I → Type*}
    {P : Tensor (Polynomial 𝕜) I V} {T : Tensor 𝕜 I V} {e : ℕ}
    (h : Leading P e T) (q : Polynomial 𝕜) (d : ℕ)
    (hq : ∀ j < d, q.coeff j = 0) :
    Leading (fun x => q * P x) (d + e) (q.coeff d • T) := by
  constructor
  · funext x
    change (q * P x).coeff (d + e) = q.coeff d * T x
    rw [coeff_mul_first q (P x) d e hq]
    · exact congrArg (fun a => q.coeff d * a) (congrFun h.1 x)
    · intro j hj
      exact congrFun (h.2 j hj) x
  · intro j hj
    funext x
    change (q * P x).coeff j = 0
    rw [Polynomial.coeff_mul]
    apply Finset.sum_eq_zero
    rintro ⟨a, b⟩ hab
    have hab' : a + b = j := Finset.mem_antidiagonal.mp hab
    by_cases ha : a < d
    · rw [hq a ha, zero_mul]
    · have hb : b < e := by omega
      rw [show (P x).coeff b = 0 from congrFun (h.2 b hb) x, mul_zero]

theorem Leading.polynomial_mul_normalized {I : Type*} {V : I → Type*}
    {P : Tensor (Polynomial 𝕜) I V} {T : Tensor 𝕜 I V} {e : ℕ}
    (h : Leading P e T) (q : Polynomial 𝕜) (hq : q ≠ 0) :
    Leading (fun x => Polynomial.C ((q.coeff q.natTrailingDegree)⁻¹) * q * P x)
      (q.natTrailingDegree + e) T := by
  have hc := Polynomial.coeff_natTrailingDegree_ne_zero.mpr hq
  have hq' := h.polynomial_mul q q.natTrailingDegree
    (fun _ hj => Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hj)
  have hn := hq'.polynomial_mul (Polynomial.C ((q.coeff q.natTrailingDegree)⁻¹)) 0
    (fun _ hj => (Nat.not_lt_zero _ hj).elim)
  simpa only [Polynomial.coeff_C_zero, zero_add, smul_smul, inv_mul_cancel₀ hc,
    one_smul, mul_assoc] using hn

end Lemmata.TensorRank.Tensor
