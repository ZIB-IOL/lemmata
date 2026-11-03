module

/-
Copyright (c) 2026 Kirill Khoruzhii. Licensed under Apache-2.0.
Modified for the arbitrary-field tensor-rank formalization; namespace and imports
adapted for Lemmata. See docs/tensor-rank/NOTICE.txt for upstream attribution
and modification notices, and docs/tensor-rank/LICENSE.txt for the license.
-/

public import Lemmata.TensorRank.Def.PolynomialProduct
public import Lemmata.TensorRank.Proof.PolynomialInterpolation
public import Lemmata.TensorRank.Proof.DirectSum
public import Lemmata.TensorRank.Proof.Readability
public import Mathlib.Data.Fintype.BigOperators

@[expose] public section

set_option autoImplicit false

open scoped BigOperators
open Classical

noncomputable section

namespace Lemmata.TensorRank.PolynomialProduct

variable {𝕜 : Type*} [Field 𝕜]


variable {J : Type*} [Fintype J]

theorem input_sum_le (a : J → ℕ) (x : ∀ j, Fin (a j)) :
    (∑ j, (x j).val) ≤ degree a := by
  exact Finset.sum_le_sum fun j _ => by have := (x j).isLt; omega

def interpolationKernel (a : J → ℕ) (c : 𝕜) :
    ∀ p, Coordinate a p → Fin (degree a + 1) → Polynomial 𝕜
  | none, z, t => Polynomial.C c * PolynomialInterpolation.dual (degree a + 1) z t
  | some _, x, t => PolynomialInterpolation.node (degree a + 1) t ^ x.val

theorem polynomialMap_interpolationKernel (a : J → ℕ) (c : 𝕜) :
    Tensor.polynomialMap (interpolationKernel a c)
        (Tensor.diagonal (R := 𝕜) (I := Option J) (degree a + 1)) =
      fun x => Polynomial.C c * PolynomialInterpolation.determinant (degree a + 1) *
        Polynomial.C (tensor (𝕜 := 𝕜) a x) := by
  have hdiag :
      (fun x => Polynomial.C
        (Tensor.diagonal (R := 𝕜) (I := Option J) (degree a + 1) x)) =
      Tensor.diagonal (R := Polynomial 𝕜) (I := Option J) (degree a + 1) := by
    funext x
    simp [Tensor.diagonal]
  rw [Tensor.polynomialMap, hdiag, Tensor.localMap_diagonal]
  funext x
  simp only [Finset.sum_apply, Tensor.pure, Fintype.prod_option, interpolationKernel,
    Finset.prod_pow_eq_pow_sum, mul_assoc]
  rw [← Finset.mul_sum, PolynomialInterpolation.filter]
  · unfold tensor
    split_ifs <;> simp
  · exact Nat.lt_succ_of_le (input_sum_le a (fun j => x (some j)))

theorem tensor_degenerates_diagonal (a : J → ℕ) :
    Tensor.Degenerates (tensor (𝕜 := 𝕜) a)
      (Tensor.diagonal (R := 𝕜) (I := Option J) (degree a + 1)) := by
  let D := PolynomialInterpolation.determinant (𝕜 := 𝕜) (degree a + 1)
  let c := (D.coeff D.natTrailingDegree)⁻¹
  have hconst :
      Tensor.Leading (fun x => Polynomial.C (tensor (𝕜 := 𝕜) a x)) 0 (tensor (𝕜 := 𝕜) a) := by
    constructor
    · funext x
      simp only [Tensor.coefficient, Polynomial.coeff_C_zero]
    · intro j hj
      omega
  have hD : D ≠ 0 := PolynomialInterpolation.determinant_ne_zero (degree a + 1)
  have hlead := hconst.polynomial_mul_normalized D hD
  refine ⟨interpolationKernel a c, D.natTrailingDegree, ?_⟩
  rw [polynomialMap_interpolationKernel]
  simpa only [Nat.add_zero, D, c] using hlead


theorem tensor_ne_zero (a : J → ℕ) (ha : ∀ j, 0 < a j) : tensor (𝕜 := 𝕜) a ≠ 0 := by
  let x : ∀ p, Coordinate a p := fun p => match p with
    | none => ⟨0, by omega⟩
    | some j => ⟨0, ha j⟩
  intro h
  have he := congrFun h x
  simp [tensor, x] at he

theorem selected_ne_zero (a : J → ℕ) (b : ℕ) (ha : ∀ j, 0 < a j) (hb : 0 < b) :
    selected (𝕜 := 𝕜) a b ≠ 0 := by
  let x : ∀ p, SelectedCoordinate a b p := fun p => match p with
    | .inl false => ⟨0, hb⟩
    | .inl true => ⟨0, by omega⟩
    | .inr j => ⟨0, ha j⟩
  intro h
  have he := congrFun h x
  simp [selected, x] at he

end Lemmata.TensorRank.PolynomialProduct
