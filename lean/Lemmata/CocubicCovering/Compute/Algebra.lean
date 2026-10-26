module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Algebra.BigOperators.Ring.List
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.Nat.BitIndices
public import Mathlib.Data.List.Range

@[expose] public section

namespace Lemmata.CocubicCovering.Compute
abbrev Field := ZMod 2
end Lemmata.CocubicCovering.Compute

namespace Lemmata.CocubicCovering.Compute.Algebra.Boolean

abbrev Monomial := Finset ℕ
abbrev Polynomial := List Monomial

def evalMonomial (assignment : ℕ → Bool) (monomial : Monomial) : Bool :=
  decide (∀ v ∈ monomial, assignment v = true)

def eval (assignment : ℕ → Bool) : Polynomial → Bool
  | [] => false
  | monomial :: rest => Bool.xor (evalMonomial assignment monomial) (eval assignment rest)

theorem evalMonomial_insert (assignment : ℕ → Bool) (v : ℕ) (term : Monomial) :
    evalMonomial assignment (insert v term) =
      (assignment v && evalMonomial assignment term) := by
  rw [Bool.eq_iff_iff]
  simp [evalMonomial]

end Lemmata.CocubicCovering.Compute.Algebra.Boolean

namespace Lemmata.CocubicCovering.Compute.Algebra.Monomial

open scoped BigOperators
open Algebra.Boolean

def ofBool : Bool → Field
  | false => 0
  | true => 1

@[simp] theorem ofBool_false : ofBool false = 0 := rfl
@[simp] theorem ofBool_true : ofBool true = 1 := rfl

@[simp] theorem ofBool_xor (a b : Bool) : ofBool (Bool.xor a b) = ofBool a + ofBool b := by
  cases a <;> cases b <;> decide

@[simp] theorem ofBool_and (a b : Bool) : ofBool (a && b) = ofBool a * ofBool b := by
  cases a <;> cases b <;> decide

@[simp] theorem ofBool_eq_zero_iff (b : Bool) : ofBool b = 0 ↔ b = false := by
  cases b <;> decide

def toBool (a : Field) : Bool := decide (a = 1)

@[simp] theorem ofBool_toBool (a : Field) : ofBool (toBool a) = a := by
  rcases eq_zero_or_one_of_sq_eq_self (ZMod.pow_card a) with h | h <;>
    simp [toBool, h, ofBool]

@[simp] theorem toBool_ofBool (a : Bool) : toBool (ofBool a) = a := by
  cases a <;> decide

def evalMonomialField (assignment : ℕ → Field) (term : Monomial) : Field :=
  ∏ v ∈ term, assignment v

def evalField (assignment : ℕ → Field) : Polynomial → Field
  | [] => 0
  | term :: rest => evalMonomialField assignment term + evalField assignment rest

theorem evalMonomialField_ofBool (assignment : ℕ → Bool) (term : Monomial) :
    evalMonomialField (fun v => ofBool (assignment v)) term =
      ofBool (evalMonomial assignment term) := by
  induction term using Finset.induction_on with
  | empty => simp [evalMonomialField, evalMonomial, ofBool]
  | @insert v term hv ih =>
      rw [evalMonomial_insert, ofBool_and]
      simpa only [evalMonomialField, Finset.prod_insert hv] using
        congrArg (fun a => ofBool (assignment v) * a) ih

theorem evalField_ofBool (assignment : ℕ → Bool) (polynomial : Polynomial) :
    evalField (fun v => ofBool (assignment v)) polynomial =
      ofBool (Algebra.Boolean.eval assignment polynomial) := by
  induction polynomial with
  | nil => rfl
  | cons term rest ih =>
      simp only [evalField, Algebra.Boolean.eval, ofBool_xor,
        evalMonomialField_ofBool, ih]

theorem evalField_eq_ofBool (assignment : ℕ → Field) (polynomial : Polynomial) :
    evalField assignment polynomial =
      ofBool (Algebra.Boolean.eval (fun v => toBool (assignment v)) polynomial) := by
  have h : (fun v => ofBool (toBool (assignment v))) = assignment := by
    funext v
    exact ofBool_toBool (assignment v)
  simpa only [h] using evalField_ofBool (fun v => toBool (assignment v)) polynomial

theorem evalMonomialField_eq_ofBool (assignment : ℕ → Field) (term : Monomial) :
    evalMonomialField assignment term =
      ofBool (evalMonomial (fun v => toBool (assignment v)) term) := by
  simpa only [ofBool_toBool] using
    evalMonomialField_ofBool (fun v => toBool (assignment v)) term

theorem evalMonomial_union (assignment : ℕ → Bool) (left right : Monomial) :
    evalMonomial assignment (left ∪ right) =
      (evalMonomial assignment left && evalMonomial assignment right) := by
  rw [Bool.eq_iff_iff]
  simp only [evalMonomial, decide_eq_true_eq, Bool.and_eq_true, Finset.forall_mem_union]

theorem evalMonomialField_union (assignment : ℕ → Field) (left right : Monomial) :
    evalMonomialField assignment (left ∪ right) =
      evalMonomialField assignment left * evalMonomialField assignment right := by
  rw [evalMonomialField_eq_ofBool assignment (left ∪ right), evalMonomial_union,
    ofBool_and, ← evalMonomialField_eq_ofBool assignment left,
    ← evalMonomialField_eq_ofBool assignment right]

end Lemmata.CocubicCovering.Compute.Algebra.Monomial

namespace Lemmata.CocubicCovering.Compute.Algebra

open Algebra.Monomial

abbrev Polynomial := List ℕ

def evalMonomial (assignment : ℕ → Field) (mask : ℕ) : Field :=
  evalMonomialField assignment mask.bitIndices.toFinset

def eval (assignment : ℕ → Field) (polynomial : Polynomial) : Field :=
  (polynomial.map (evalMonomial assignment)).sum

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

end Lemmata.CocubicCovering.Compute.Algebra

namespace Lemmata.CocubicCovering.Compute.Algebra.Bits

open Algebra

def decodeIndices (size mask : ℕ) : List ℕ :=
  (List.range size).filter fun i => mask.testBit i

def polynomial (dictionary : ℕ → ℕ) (size mask : ℕ) : Polynomial :=
  (decodeIndices size mask).map dictionary

def check (left right output : ℕ) : Bool :=
  decide (left ^^^ right = output)

private theorem eval_filter_cons (assignment : ℕ → Field) (dictionary : ℕ → ℕ)
    (mask first : ℕ) (rest : List ℕ) :
    eval assignment (((first :: rest).filter fun i => mask.testBit i).map dictionary) =
      (if mask.testBit first then evalMonomial assignment (dictionary first) else 0) +
        eval assignment ((rest.filter fun i => mask.testBit i).map dictionary) := by
  cases h : mask.testBit first <;> simp [h, eval_cons]

private theorem eval_filter_xor (assignment : ℕ → Field) (dictionary : ℕ → ℕ)
    (left right : ℕ) : ∀ indices : List ℕ,
    eval assignment ((indices.filter fun i => (left ^^^ right).testBit i).map dictionary) =
      eval assignment ((indices.filter fun i => left.testBit i).map dictionary) +
        eval assignment ((indices.filter fun i => right.testBit i).map dictionary) := by
  intro indices
  induction indices with
  | nil => simp
  | cons first rest ih =>
      have hhead :
          (if (left ^^^ right).testBit first then
              evalMonomial assignment (dictionary first) else 0) =
            (if left.testBit first then evalMonomial assignment (dictionary first) else 0) +
              (if right.testBit first then evalMonomial assignment (dictionary first) else 0) := by
        rw [Nat.testBit_xor]
        cases hleft : left.testBit first <;> cases hright : right.testBit first <;>
          simp [CharTwo.add_self_eq_zero]
      simp only [eval_filter_cons]
      rw [hhead, ih]
      ac_rfl

theorem eval_xor (assignment : ℕ → Field) (dictionary : ℕ → ℕ)
    (size left right : ℕ) :
    eval assignment (polynomial dictionary size (left ^^^ right)) =
      eval assignment (polynomial dictionary size left) +
        eval assignment (polynomial dictionary size right) :=
  eval_filter_xor assignment dictionary left right (List.range size)

end Lemmata.CocubicCovering.Compute.Algebra.Bits

namespace Lemmata.CocubicCovering.Compute.Algebra.Bits

open Algebra Algebra.Bits

def encodeIndices (indices : List ℕ) : ℕ :=
  indices.foldr (fun i mask => (2 ^ i) ^^^ mask) 0

@[simp] theorem encodeIndices_nil : encodeIndices [] = 0 := rfl

@[simp] theorem encodeIndices_cons (i : ℕ) (indices : List ℕ) :
    encodeIndices (i :: indices) = (2 ^ i) ^^^ encodeIndices indices := rfl

private theorem decodeIndices_two_pow (size i : ℕ) (hi : i < size) :
    decodeIndices size (2 ^ i) = [i] := by
  have he : (fun j : ℕ => (2 ^ i).testBit j) = fun j => j == i := by
    funext j
    by_cases hij : i = j
    · subst j
      simp [Nat.testBit_two_pow]
    · simp [Nat.testBit_two_pow, hij, Ne.symm hij]
  rw [decodeIndices, he, List.filter_beq, List.count_range, if_pos hi]
  rfl

@[simp] theorem eval_zero (assignment : ℕ → Field) (dictionary : ℕ → ℕ) (size : ℕ) :
    eval assignment (polynomial dictionary size 0) = 0 := by
  simp [polynomial, decodeIndices]

theorem eval_two_pow (assignment : ℕ → Field) (dictionary : ℕ → ℕ)
    (size i : ℕ) (hi : i < size) :
    eval assignment (polynomial dictionary size (2 ^ i)) =
      evalMonomial assignment (dictionary i) := by
  rw [polynomial, decodeIndices_two_pow size i hi]
  simp

theorem eval_encodeIndices (assignment : ℕ → Field) (dictionary : ℕ → ℕ) (size : ℕ) :
    ∀ indices : List ℕ, (∀ i ∈ indices, i < size) →
      eval assignment (polynomial dictionary size (encodeIndices indices)) =
        eval assignment (indices.map dictionary) := by
  intro indices
  induction indices with
  | nil => intro _; simp
  | cons first rest ih =>
      intro hbound
      have hfirst : first < size := hbound first (by simp)
      have hrest : ∀ i ∈ rest, i < size := fun i hi => hbound i (by simp [hi])
      rw [encodeIndices_cons, eval_xor, eval_two_pow assignment dictionary size first hfirst,
        ih hrest]
      rfl

end Lemmata.CocubicCovering.Compute.Algebra.Bits
