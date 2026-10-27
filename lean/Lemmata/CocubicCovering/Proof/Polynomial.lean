module

public import Lemmata.CocubicCovering.Proof.Certificate
public meta import Lemmata.CocubicCovering.Proof.Certificate
public import Lemmata.CocubicCovering.Proof.Model
public meta import Lemmata.CocubicCovering.Proof.Model
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

@[expose] public section

set_option Elab.async false

namespace Lemmata.CocubicCovering.CoveringPolynomial

open scoped BigOperators
open CoveringCertificate

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
      ofBool (CoveringCertificate.eval assignment polynomial) := by
  induction polynomial with
  | nil => rfl
  | cons term rest ih =>
      simp only [evalField, CoveringCertificate.eval, ofBool_xor,
        evalMonomialField_ofBool, ih]

theorem evalField_eq_ofBool (assignment : ℕ → Field) (polynomial : Polynomial) :
    evalField assignment polynomial =
      ofBool (CoveringCertificate.eval (fun v => toBool (assignment v)) polynomial) := by
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

theorem evalField_toggle (assignment : ℕ → Field) (term : Monomial)
    (polynomial : Polynomial) :
    evalField assignment (toggle term polynomial) =
      evalMonomialField assignment term + evalField assignment polynomial := by
  have h := evalMonomialField_ofBool (fun v => toBool (assignment v)) term
  simp only [ofBool_toBool] at h
  rw [evalField_eq_ofBool, eval_toggle, ofBool_xor,
    ← evalField_eq_ofBool, ← h]

theorem evalField_add (assignment : ℕ → Field) (left right : Polynomial) :
    evalField assignment (add left right) = evalField assignment left + evalField assignment right := by
  rw [evalField_eq_ofBool, eval_add, ofBool_xor, ← evalField_eq_ofBool,
    ← evalField_eq_ofBool]

theorem evalField_multiplyVariable (assignment : ℕ → Field) (v : ℕ)
    (polynomial : Polynomial) :
    evalField assignment (multiplyVariable v polynomial) = assignment v * evalField assignment polynomial := by
  rw [evalField_eq_ofBool, eval_multiplyVariable, ofBool_and, ofBool_toBool,
    ← evalField_eq_ofBool]

def multiplyTerm (term : Monomial) : Polynomial → Polynomial
  | [] => []
  | first :: rest => toggle (term ∪ first) (multiplyTerm term rest)

def multiply : Polynomial → Polynomial → Polynomial
  | [], _ => []
  | term :: rest, right => add (multiplyTerm term right) (multiply rest right)

theorem evalField_multiplyTerm (assignment : ℕ → Field) (term : Monomial)
    (polynomial : Polynomial) :
    evalField assignment (multiplyTerm term polynomial) =
      evalMonomialField assignment term * evalField assignment polynomial := by
  induction polynomial with
  | nil => simp [multiplyTerm, evalField]
  | cons first rest ih =>
      rw [multiplyTerm, evalField_toggle, ih, evalMonomialField_union, evalField, mul_add]

theorem evalField_multiply (assignment : ℕ → Field) (left right : Polynomial) :
    evalField assignment (multiply left right) = evalField assignment left * evalField assignment right := by
  induction left with
  | nil => simp [multiply, evalField]
  | cons term rest ih =>
      rw [multiply, evalField_add, evalField_multiplyTerm, ih, evalField, add_mul]

theorem check_sound_field (inputs : List Polynomial) (trace : List Instruction)
    (hcheck : check inputs trace = true) :
    ¬∃ assignment : ℕ → Field, ∀ polynomial ∈ inputs, evalField assignment polynomial = 0 := by
  rintro ⟨assignment, hinputs⟩
  apply check_sound inputs trace hcheck
  refine ⟨fun v => toBool (assignment v), ?_⟩
  intro polynomial hp
  apply (ofBool_eq_zero_iff _).mp
  rw [← evalField_eq_ofBool]
  exact hinputs polynomial hp

def finiteMonomial (m : ℕ) (term : Monomial) : Finset (Fin m) :=
  Finset.univ.filter fun i => i.val ∈ term

theorem finiteMonomial_card_le (m : ℕ) (term : Monomial) :
    (finiteMonomial m term).card ≤ term.card := by
  apply Finset.card_le_card_of_injOn (fun i : Fin m => i.val)
  · intro i hi
    exact (Finset.mem_filter.mp hi).2
  · intro i hi j hj hij
    exact Fin.ext hij

def Bounded (m : ℕ) (polynomial : Polynomial) : Prop :=
  ∀ term ∈ polynomial, ∀ v ∈ term, v < m

theorem eval_finiteMonomial (m : ℕ) (term : Monomial)
    (hterm : ∀ v ∈ term, v < m) (assignment : ℕ → Field) :
    Covering.monomial (finiteMonomial m term) (fun i => assignment i.val) =
      evalMonomialField assignment term := by
  rw [Covering.monomial, Fintype.prod_ite_mem]
  unfold finiteMonomial evalMonomialField
  apply Finset.prod_bij (fun i _ => i.val)
  · intro i hi
    exact (Finset.mem_filter.mp hi).2
  · intro i hi j hj hij
    exact Fin.ext hij
  · intro v hv
    exact ⟨⟨v, hterm v hv⟩, by simp [hv], rfl⟩
  · intro i hi
    rfl

def decode (m : ℕ) : Polynomial → Covering.ANF m
  | [] => 0
  | term :: rest => Pi.single (finiteMonomial m term) 1 + decode m rest

theorem eval_single {m : ℕ} (term : Finset (Fin m)) (x : Vector m) :
    Covering.eval (Pi.single term 1) x = Covering.monomial term x := by
  simp [Covering.eval, Pi.single_apply]

theorem eval_anf_add {m : ℕ} (p q : Covering.ANF m) (x : Vector m) :
    Covering.eval (p + q) x = Covering.eval p x + Covering.eval q x :=
  congrArg (fun f : Covering.BooleanFunction m => f x) ((Covering.evalLinear m).map_add p q)

theorem eval_decode (m : ℕ) (polynomial : Polynomial) (hpolynomial : Bounded m polynomial)
    (assignment : ℕ → Field) :
    Covering.eval (decode m polynomial) (fun i => assignment i.val) =
      evalField assignment polynomial := by
  induction polynomial with
  | nil => simp [decode, Covering.eval, evalField]
  | cons term rest ih =>
      rw [decode, eval_anf_add, eval_single,
        eval_finiteMonomial m term (hpolynomial term (by simp)) assignment,
        ih (fun t ht => hpolynomial t (by simp [ht])), evalField]

theorem decode_degreeLE (m : ℕ) (polynomial : Polynomial) (r : ℕ)
    (hdegree : ∀ term ∈ polynomial, term.card ≤ r) :
    Covering.DegreeLE (decode m polynomial) r := by
  induction polynomial with
  | nil => intro s hs; rfl
  | cons term rest ih =>
      intro s hs
      have hne : s ≠ finiteMonomial m term := by
        intro heq
        have hc := (finiteMonomial_card_le m term).trans (hdegree term (by simp))
        rw [← heq] at hc
        omega
      have hz := ih (fun t ht => hdegree t (by simp [ht])) s hs
      simp [decode, Pi.single_apply, hne, Ne.symm hne, hz]

theorem decode_mem_reedMuller (m : ℕ) (polynomial : Polynomial) (r : ℕ)
    (hdegree : ∀ term ∈ polynomial, term.card ≤ r) :
    Covering.eval (decode m polynomial) ∈ Covering.reedMuller m r :=
  Covering.mem_reedMuller_iff.mpr ⟨decode m polynomial, decode_degreeLE m polynomial r hdegree, rfl⟩

end Lemmata.CocubicCovering.CoveringPolynomial
