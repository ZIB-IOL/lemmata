module

public import Mathlib.Data.Bool.Basic
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.List.Basic

@[expose] public section

set_option Elab.async false

namespace Lemmata.CocubicCovering.CoveringCertificate

abbrev Monomial := Finset ℕ
abbrev Polynomial := List Monomial

def evalMonomial (assignment : ℕ → Bool) (monomial : Monomial) : Bool :=
  decide (∀ v ∈ monomial, assignment v = true)

def eval (assignment : ℕ → Bool) : Polynomial → Bool
  | [] => false
  | monomial :: rest => Bool.xor (evalMonomial assignment monomial) (eval assignment rest)

def toggle (monomial : Monomial) : Polynomial → Polynomial
  | [] => [monomial]
  | term :: rest => if monomial = term then rest else term :: toggle monomial rest

def add : Polynomial → Polynomial → Polynomial
  | [], right => right
  | term :: rest, right => toggle term (add rest right)

def multiplyVariable (v : ℕ) : Polynomial → Polynomial
  | [] => []
  | term :: rest => toggle (insert v term) (multiplyVariable v rest)

theorem evalMonomial_insert (assignment : ℕ → Bool) (v : ℕ) (term : Monomial) :
    evalMonomial assignment (insert v term) =
      (assignment v && evalMonomial assignment term) := by
  rw [Bool.eq_iff_iff]
  simp [evalMonomial]

theorem eval_toggle (assignment : ℕ → Bool) (monomial : Monomial) (polynomial : Polynomial) :
    eval assignment (toggle monomial polynomial) =
      Bool.xor (evalMonomial assignment monomial) (eval assignment polynomial) := by
  induction polynomial with
  | nil => simp [toggle, eval]
  | cons term rest ih =>
      by_cases h : monomial = term
      · subst term
        simp only [toggle, ite_true, eval]
        cases evalMonomial assignment monomial <;> cases eval assignment rest <;> rfl
      · simp only [toggle, if_neg h, eval, ih]
        exact Bool.xor_left_comm _ _ _

theorem eval_add (assignment : ℕ → Bool) (left right : Polynomial) :
    eval assignment (add left right) = Bool.xor (eval assignment left) (eval assignment right) := by
  induction left with
  | nil => simp [add, eval]
  | cons term rest ih => simp [add, eval_toggle, ih, eval]

theorem eval_multiplyVariable (assignment : ℕ → Bool) (v : ℕ) (polynomial : Polynomial) :
    eval assignment (multiplyVariable v polynomial) =
      (assignment v && eval assignment polynomial) := by
  induction polynomial with
  | nil => simp [multiplyVariable, eval]
  | cons term rest ih =>
      rw [multiplyVariable, eval_toggle, evalMonomial_insert, ih, eval]
      cases assignment v <;> cases evalMonomial assignment term <;>
        cases eval assignment rest <;> rfl

/-- References count backwards from the most recently derived polynomial. -/
inductive Instruction where
  | input (index : ℕ)
  | add (left right : ℕ)
  | multiplyVariable (v source : ℕ)
  deriving DecidableEq

def step (inputs derived : List Polynomial) : Instruction → Option Polynomial
  | .input index => inputs[index]?
  | .add left right => do
      let first ← derived[left]?
      let second ← derived[right]?
      return add first second
  | .multiplyVariable v source =>
      (derived[source]?).map (multiplyVariable v)

def run (inputs : List Polynomial) : List Instruction → List Polynomial → Option Polynomial
  | [], derived => derived.head?
  | instruction :: rest, derived => do
      let polynomial ← step inputs derived instruction
      run inputs rest (polynomial :: derived)

def check (inputs : List Polynomial) (trace : List Instruction) : Bool :=
  match run inputs trace [] with
  | none => false
  | some polynomial => decide (polynomial = [∅])

theorem step_sound (assignment : ℕ → Bool) (inputs derived : List Polynomial)
    (hinputs : ∀ polynomial ∈ inputs, eval assignment polynomial = false)
    (hderived : ∀ polynomial ∈ derived, eval assignment polynomial = false)
    (instruction : Instruction) (polynomial : Polynomial)
    (hstep : step inputs derived instruction = some polynomial) :
    eval assignment polynomial = false := by
  cases instruction with
  | input index =>
      exact hinputs polynomial (List.mem_of_getElem? hstep)
  | add left right =>
      cases hleft : derived[left]? with
      | none => simp [step, hleft] at hstep
      | some first =>
          cases hright : derived[right]? with
          | none => simp [step, hleft, hright] at hstep
          | some second =>
              simp [step, hleft, hright] at hstep
              subst polynomial
              rw [eval_add, hderived first (List.mem_of_getElem? hleft),
                hderived second (List.mem_of_getElem? hright)]
              rfl
  | multiplyVariable v source =>
      cases hsource : derived[source]? with
      | none => simp [step, hsource] at hstep
      | some first =>
          simp [step, hsource] at hstep
          subst polynomial
          rw [eval_multiplyVariable, hderived first (List.mem_of_getElem? hsource)]
          simp

theorem run_sound (assignment : ℕ → Bool) (inputs : List Polynomial)
    (hinputs : ∀ polynomial ∈ inputs, eval assignment polynomial = false)
    (trace : List Instruction) :
    ∀ derived, (∀ polynomial ∈ derived, eval assignment polynomial = false) →
      ∀ polynomial, run inputs trace derived = some polynomial →
        eval assignment polynomial = false := by
  induction trace with
  | nil =>
      intro derived hderived polynomial hrun
      cases derived with
      | nil => simp [run] at hrun
      | cons first rest =>
          simp [run] at hrun
          subst polynomial
          exact hderived first (by simp)
  | cons instruction rest ih =>
      intro derived hderived polynomial hrun
      cases hstep : step inputs derived instruction with
      | none => simp [run, hstep] at hrun
      | some first =>
          simp [run, hstep] at hrun
          apply ih (first :: derived) ?_ polynomial hrun
          intro term hterm
          rcases List.mem_cons.mp hterm with heq | hterm
          · rw [heq]
            exact step_sound assignment inputs derived hinputs hderived instruction first hstep
          · exact hderived term hterm

theorem check_sound (inputs : List Polynomial) (trace : List Instruction)
    (hcheck : check inputs trace = true) :
    ¬∃ assignment : ℕ → Bool, ∀ polynomial ∈ inputs, eval assignment polynomial = false := by
  rintro ⟨assignment, hinputs⟩
  cases hrun : run inputs trace [] with
  | none => simp [check, hrun] at hcheck
  | some polynomial =>
      have hconstant : polynomial = [∅] := by simpa [check, hrun] using hcheck
      have hzero := run_sound assignment inputs hinputs trace [] (by simp) polynomial hrun
      simpa [hconstant, eval, evalMonomial] using hzero

theorem linear_control :
    check [[{0}], [∅, {0}]] [.input 0, .input 1, .add 0 1] = true := by decide

theorem nonlinear_control :
    check [[∅, {0}], [{0, 1}], [∅, {1}]]
      [.input 0, .multiplyVariable 1 0, .input 1, .add 0 1, .input 2, .add 0 1] = true := by decide

theorem idempotence_control : multiplyVariable 0 [∅, {0}] = [] := by decide

theorem invalid_reference_control : check [] [.input 0] = false := by decide

end Lemmata.CocubicCovering.CoveringCertificate
