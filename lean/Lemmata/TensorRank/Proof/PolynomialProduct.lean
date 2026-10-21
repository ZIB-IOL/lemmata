module

public import Lemmata.TensorRank.Def.PolynomialProduct
public import Lemmata.TensorRank.Proof.Interpolation
public import Lemmata.TensorRank.Proof.Readability
public import Mathlib.Data.Fintype.BigOperators

@[expose] public section

set_option autoImplicit false

open scoped BigOperators
open Classical

namespace Lemmata.TensorRank.PolynomialProduct

variable {J : Type*} [Fintype J]

theorem input_sum_le (a : J → ℕ) (x : ∀ j, Fin (a j)) :
    (∑ j, (x j).val) ≤ degree a := by
  exact Finset.sum_le_sum fun j _ => by have := (x j).isLt; omega

theorem rankLE_tensor (a : J → ℕ) : Tensor.RankLE (tensor a) (degree a + 1) := by
  let nodes : Fin (degree a + 1) → ℂ := fun j => j.val
  have hn : Function.Injective nodes := fun i j h => Fin.ext (Nat.cast_injective h)
  refine ⟨fun _ => 1, fun t p => match p with
    | none => fun z => (Lagrange.basis Finset.univ nodes t).coeff z.val
    | some j => fun x => nodes t ^ x.val, ?_⟩
  funext x
  have hd : (Polynomial.X ^ (∑ j, (x (some j)).val) : Polynomial ℂ).degree <
      (Finset.univ : Finset (Fin (degree a + 1))).card := by
    rw [Polynomial.degree_X_pow, Finset.card_univ, Fintype.card_fin]
    exact_mod_cast Nat.lt_succ_of_le (input_sum_le a (fun j => x (some j)))
  have h := congrArg (fun p : Polynomial ℂ => p.coeff (x none).val)
    (Lagrange.eq_interpolate hn.injOn hd)
  simpa only [tensor, Polynomial.coeff_X_pow, Lagrange.interpolate_apply,
    Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.eval_pow,
    Polynomial.eval_X, Tensor.pure, Fintype.prod_option, one_mul, Finset.prod_pow_eq_pow_sum,
    eq_comm, mul_comm]
    using h

theorem rank_tensor_le (a : J → ℕ) : Tensor.rank (tensor a) ≤ degree a + 1 :=
  (Tensor.rank_le_iff _ _).mpr (rankLE_tensor a)

theorem asymptoticRank_tensor_le (a : J → ℕ) : Tensor.asymptoticRank (tensor a) ≤ degree a + 1 :=
  (Tensor.asymptoticRank_le_rank _).trans (by exact_mod_cast rank_tensor_le a)

theorem rankLE_selected (a : J → ℕ) (b : ℕ) : Tensor.RankLE (selected a b) (b + degree a) := by
  let nodes : Fin (b + degree a) → ℂ := fun j => j.val
  have hn : Function.Injective nodes := fun i j h => Fin.ext (Nat.cast_injective h)
  refine ⟨fun _ => 1, fun t p => match p with
    | .inl false => fun y => nodes t ^ y.val
    | .inl true => fun z => (Lagrange.basis Finset.univ nodes t).coeff z.val
    | .inr _ => fun x => nodes t ^ x.val, ?_⟩
  funext x
  have hd : (Polynomial.X ^ ((x (.inl false)).val + ∑ j, (x (.inr j)).val) :
      Polynomial ℂ).degree < (Finset.univ : Finset (Fin (b + degree a))).card := by
    rw [Polynomial.degree_X_pow, Finset.card_univ, Fintype.card_fin]
    have hs := input_sum_le a (fun j => x (.inr j))
    have hy := (x (.inl false)).isLt
    exact_mod_cast (by omega : (x (.inl false)).val + (∑ j, (x (.inr j)).val) < b + degree a)
  have h := congrArg (fun p : Polynomial ℂ => p.coeff (x (.inl true)).val)
    (Lagrange.eq_interpolate hn.injOn hd)
  simp only [Polynomial.coeff_X_pow, Lagrange.interpolate_apply,
    Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.eval_pow,
    Polynomial.eval_X] at h
  simpa only [selected, Tensor.pure, Fintype.prod_sum_type, Fintype.prod_bool,
    one_mul, Finset.prod_pow_eq_pow_sum, pow_add, eq_comm, mul_comm, mul_left_comm, mul_assoc]
    using h

theorem rank_selected_le (a : J → ℕ) (b : ℕ) : Tensor.rank (selected a b) ≤ b + degree a :=
  (Tensor.rank_le_iff _ _).mpr (rankLE_selected a b)

theorem tensor_ne_zero (a : J → ℕ) (ha : ∀ j, 0 < a j) : tensor a ≠ 0 := by
  let x : ∀ p, Coordinate a p := fun p => match p with
    | none => ⟨0, by omega⟩
    | some j => ⟨0, ha j⟩
  intro h
  have he := congrFun h x
  simp [tensor, x] at he

theorem selected_ne_zero (a : J → ℕ) (b : ℕ) (ha : ∀ j, 0 < a j) (hb : 0 < b) :
    selected a b ≠ 0 := by
  let x : ∀ p, SelectedCoordinate a b p := fun p => match p with
    | .inl false => ⟨0, hb⟩
    | .inl true => ⟨0, by omega⟩
    | .inr j => ⟨0, ha j⟩
  intro h
  have he := congrFun h x
  simp [selected, x] at he

theorem tripleSector_reads_input (a : J → ℕ) (b : ℕ) :
    Tensor.Reads (tripleSector a b) (.inl false) (inputLabel a b) := by
  intro q x h
  by_contra hn
  exact h (by simp only [tripleSector, hn, false_and, ite_false])

theorem tripleSector_reads_output (a : J → ℕ) (b : ℕ) :
    Tensor.Reads (tripleSector a b) (.inl true) (outputLabel a b) := by
  intro q x h
  by_contra hn
  exact h (by simp only [tripleSector, hn, and_false, ite_false])

end Lemmata.TensorRank.PolynomialProduct
