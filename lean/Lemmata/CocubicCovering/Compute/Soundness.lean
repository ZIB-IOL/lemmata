module

public import Lemmata.CocubicCovering.Compute.Polynomial
public meta import Lemmata.CocubicCovering.Compute.Polynomial
public import Lemmata.CocubicCovering.Compute.EncodingSound
public meta import Lemmata.CocubicCovering.Compute.EncodingSound

@[expose] public section

namespace Lemmata.CocubicCovering.Compute.Polynomial

open Algebra

theorem result_sound {dictionary : Nat → Nat} {size : Nat} {inputs : Inputs}
    (row : Row dictionary size inputs) (hrow : row.bits = 1)
    (hsize : 0 < size) (hconstant : dictionary 0 = 0) :
    ¬ ∃ assignment : Nat → Field, ∀ p ∈ inputs, eval assignment p = 0 :=
  Encoding.Derives.refutes (.cast hrow row.valid) hsize hconstant

theorem refutes_sound (numVars rounds : Nat) (inputs : Inputs)
    (accepted : refutes numVars rounds inputs = true) :
    ¬ ∃ assignment : Nat → Field, ∀ p ∈ inputs, eval assignment p = 0 := by
  obtain ⟨hformat, hresult⟩ := Bool.and_eq_true_iff.mp accepted
  have hformat := of_decide_eq_true hformat
  cases hrun : solve numVars rounds inputs with
  | none => simp only [hrun, Option.any_none, Bool.false_eq_true] at hresult
  | some row =>
      have hrow : row.bits = 1 := by
        simpa only [hrun, Option.any_some, beq_iff_eq] using hresult
      exact result_sound row hrow hformat.1 hformat.2

end Lemmata.CocubicCovering.Compute.Polynomial
