module

public import Lemmata.CocubicCovering.Proof.Polynomial
public meta import Lemmata.CocubicCovering.Proof.Polynomial
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Algebra.BigOperators.Ring.List
public import Mathlib.Data.List.Sort
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.Nat.BitIndices

@[expose] public section

set_option Elab.async false

namespace Lemmata.CocubicCovering.CoveringIdeal

open CoveringPolynomial

abbrev Polynomial := List ℕ

def evalMonomial (assignment : ℕ → Field) (mask : ℕ) : Field :=
  evalMonomialField assignment mask.bitIndices.toFinset

def eval (assignment : ℕ → Field) (polynomial : Polynomial) : Field :=
  (polynomial.map (evalMonomial assignment)).sum

def cancel : Polynomial → Polynomial
  | [] => []
  | [first] => [first]
  | first :: second :: rest =>
      if first = second then cancel rest else first :: cancel (second :: rest)

def merge : ℕ → Polynomial → Polynomial → Polynomial
  | 0, left, right => left ++ right
  | _ + 1, [], right => right
  | _ + 1, left, [] => left
  | fuel + 1, first :: left, second :: right =>
      if first ≤ second then first :: merge fuel left (second :: right)
      else second :: merge fuel (first :: left) right

def sort : ℕ → Polynomial → Polynomial
  | 0, polynomial => polynomial
  | _ + 1, [] => []
  | _ + 1, [first] => [first]
  | fuel + 1, first :: second :: rest =>
      let polynomial := first :: second :: rest
      let middle := polynomial.length / 2
      merge polynomial.length (sort fuel (polynomial.take middle))
        (sort fuel (polynomial.drop middle))

def normalize (polynomial : Polynomial) : Polynomial :=
  cancel (sort polynomial.length polynomial)

def products (left right : Polynomial) : Polynomial :=
  left.flatMap fun first => right.map fun second => first ||| second

structure Multiple where
  input : ℕ
  coefficient : Polynomial
  deriving DecidableEq

def expansion (inputs : List Polynomial) (certificate : List Multiple) : Polynomial :=
  certificate.flatMap fun multiple =>
    normalize (products (inputs[multiple.input]?.getD []) multiple.coefficient)

def check (inputs : List Polynomial) (certificate : List Multiple) : Bool :=
  decide (normalize (expansion inputs certificate) = [0])

@[simp] theorem eval_nil (assignment : ℕ → Field) : eval assignment [] = 0 := rfl

@[simp] theorem eval_cons (assignment : ℕ → Field) (first : ℕ) (rest : Polynomial) :
    eval assignment (first :: rest) = evalMonomial assignment first + eval assignment rest := by
  simp only [eval, List.map_cons, List.sum_cons]

theorem eval_append (assignment : ℕ → Field) (left right : Polynomial) :
    eval assignment (left ++ right) = eval assignment left + eval assignment right := by
  simp only [eval, List.map_append, List.sum_append]

theorem evalMonomial_or (assignment : ℕ → Field) (left right : ℕ) :
    evalMonomial assignment (left ||| right) =
      evalMonomial assignment left * evalMonomial assignment right := by
  have hu : (left ||| right).bitIndices.toFinset =
      left.bitIndices.toFinset ∪ right.bitIndices.toFinset := by
    ext i
    simp only [List.mem_toFinset, Nat.mem_bitIndices, Nat.testBit_lor,
      Finset.mem_union, Bool.or_eq_true_iff]
  unfold evalMonomial
  rw [hu, evalMonomialField_union]

theorem eval_cancel (assignment : ℕ → Field) :
    ∀ polynomial, eval assignment (cancel polynomial) = eval assignment polynomial
  | [] => rfl
  | [first] => rfl
  | first :: second :: rest => by
      by_cases h : first = second
      · simp only [cancel, if_pos h]
        rw [eval_cancel assignment rest]
        subst second
        simp only [eval_cons, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
      · simp only [cancel, if_neg h, eval_cons]
        rw [eval_cancel assignment (second :: rest)]
        rw [eval_cons]

theorem eval_normalize (assignment : ℕ → Field) (polynomial : Polynomial) :
    eval assignment (normalize polynomial) = eval assignment polynomial := by
  rw [normalize, eval_cancel]
  have hmerge : ∀ fuel left right,
      eval assignment (merge fuel left right) = eval assignment left + eval assignment right := by
    intro fuel
    induction fuel with
    | zero => intro left right; exact eval_append assignment left right
    | succ fuel ih =>
        intro left right
        cases left with
        | nil => simp [merge]
        | cons first left =>
            cases right with
            | nil => simp [merge]
            | cons second right =>
                by_cases h : first ≤ second
                · simp only [merge, if_pos h, eval_cons, ih, add_assoc]
                · simp only [merge, if_neg h, eval_cons, ih]
                  ac_rfl
  have hsort : ∀ fuel polynomial,
      eval assignment (sort fuel polynomial) = eval assignment polynomial := by
    intro fuel
    induction fuel with
    | zero => intro polynomial; rfl
    | succ fuel ih =>
        intro polynomial
        cases polynomial with
        | nil => rfl
        | cons first rest =>
            cases rest with
            | nil => rfl
            | cons second rest =>
                simp only [sort, hmerge, ih, ← eval_append, List.take_append_drop]
  exact hsort _ polynomial

theorem eval_products (assignment : ℕ → Field) (left right : Polynomial) :
    eval assignment (products left right) = eval assignment left * eval assignment right := by
  induction left with
  | nil => simp [products]
  | cons first rest ih =>
      simp only [products, List.flatMap_cons, eval_append]
      have he : eval assignment (right.map fun second => first ||| second) =
          evalMonomial assignment first * eval assignment right := by
        simp only [eval, List.map_map, Function.comp_def, evalMonomial_or,
          List.sum_map_mul_left]
      rw [he]
      change evalMonomial assignment first * eval assignment right +
        eval assignment (products rest right) = _
      rw [ih, eval_cons, add_mul]

theorem eval_expansion_zero (assignment : ℕ → Field) (inputs : List Polynomial)
    (hinputs : ∀ polynomial ∈ inputs, eval assignment polynomial = 0) :
    ∀ certificate, eval assignment (expansion inputs certificate) = 0
  | [] => rfl
  | multiple :: rest => by
      simp only [expansion, List.flatMap_cons, eval_append, eval_normalize, eval_products]
      have hz : eval assignment (inputs[multiple.input]?.getD []) = 0 := by
        cases hi : inputs[multiple.input]? with
        | none => simp only [hi, Option.getD_none, eval_nil]
        | some polynomial =>
            simp only [hi, Option.getD_some]
            exact hinputs polynomial (List.mem_of_getElem? hi)
      rw [hz, zero_mul, zero_add]
      exact eval_expansion_zero assignment inputs hinputs rest

theorem check_sound (inputs : List Polynomial) (certificate : List Multiple)
    (accepted : check inputs certificate = true) :
    ¬∃ assignment : ℕ → Field, ∀ polynomial ∈ inputs, eval assignment polynomial = 0 := by
  rintro ⟨assignment, hinputs⟩
  have he : normalize (expansion inputs certificate) = [0] := of_decide_eq_true accepted
  have hz := eval_expansion_zero assignment inputs hinputs certificate
  rw [← eval_normalize assignment, he] at hz
  have hc : eval assignment [0] = 1 := by
    simp [eval, evalMonomial, evalMonomialField]
  exact one_ne_zero (hc.symm.trans hz)

theorem linear_control :
    check [[0, 1], [1]] [⟨0, [0]⟩, ⟨1, [0]⟩] = true := by native_decide

theorem nonlinear_control :
    check [[0, 1], [3], [0, 2]] [⟨0, [2]⟩, ⟨1, [0]⟩, ⟨2, [0]⟩] = true := by native_decide

theorem invalid_reference_control : check [] [⟨0, [0]⟩] = false := by native_decide

end Lemmata.CocubicCovering.CoveringIdeal
