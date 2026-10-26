module

public import Lemmata.CocubicCovering.Proof.Affine
public meta import Lemmata.CocubicCovering.Proof.Affine
public import Lemmata.CocubicCovering.Proof.Polynomial
public meta import Lemmata.CocubicCovering.Proof.Polynomial

@[expose] public section

set_option Elab.async false

namespace Lemmata.CocubicCovering.CoveringEncoding

open CoveringCertificate CoveringPolynomial CoveringAffine

def pointedVector {n : ℕ} (labels : Fin n → ℕ) (assignment : ℕ → Field) :
    Vector (n + 1) :=
  Fin.lastCases 1 fun i => assignment (labels i)

theorem evalRow_two_pow {n : ℕ} (i : Fin n) (v : Vector n) :
    evalRow (2 ^ i.val) v = v i := by
  simp only [evalRow, Nat.testBit_two_pow, decide_eq_true_eq, Fin.val_inj]
  simp

def encodeMonomial {n : ℕ} (labels : Fin n → ℕ) (term : Monomial) : Option ℕ :=
  if term = ∅ then some (2 ^ n) else
    ((List.finRange n).find? fun i => decide (term = {labels i})).map
      fun i => 2 ^ i.val

def encode {n : ℕ} (labels : Fin n → ℕ) : Polynomial → Option ℕ
  | [] => some 0
  | term :: rest =>
      match encodeMonomial labels term, encode labels rest with
      | some first, some tail => some (first ^^^ tail)
      | _, _ => none

theorem encodeMonomial_sound {n : ℕ} (labels : Fin n → ℕ) (term : Monomial)
    (row : ℕ) (h : encodeMonomial labels term = some row) (assignment : ℕ → Field) :
    evalMonomialField assignment term = evalRow row (pointedVector labels assignment) := by
  by_cases he : term = ∅
  · subst term
    simp only [encodeMonomial, ite_true, Option.some.injEq] at h
    rw [← h]
    simpa [pointedVector, evalMonomialField] using
      (evalRow_two_pow (Fin.last n) (pointedVector labels assignment)).symm
  · simp only [encodeMonomial, if_neg he, Option.map_eq_some_iff] at h
    rcases h with ⟨i, hi, hrow⟩
    have hterm : term = {labels i} := of_decide_eq_true
      (List.find?_some (p := fun j : Fin n => decide (term = {labels j})) hi)
    rw [hterm, ← hrow]
    simpa [pointedVector, evalMonomialField] using
      (evalRow_two_pow i.castSucc (pointedVector labels assignment)).symm

theorem encode_sound {n : ℕ} (labels : Fin n → ℕ) (polynomial : Polynomial)
    (row : ℕ) (h : encode labels polynomial = some row) (assignment : ℕ → Field) :
    evalField assignment polynomial = evalRow row (pointedVector labels assignment) := by
  induction polynomial generalizing row with
  | nil =>
      simp only [encode, Option.some.injEq] at h
      rw [← h]
      simp [evalField]
  | cons term rest ih =>
      cases ht : encodeMonomial labels term with
      | none => simp [encode, ht] at h
      | some first =>
          cases hr : encode labels rest with
          | none => simp [encode, ht, hr] at h
          | some tail =>
              have hrow : first ^^^ tail = row := by
                simpa only [encode, ht, hr, Option.some.injEq] using h
              rw [← hrow, evalRow_xor]
              exact congrArg₂ (fun a b : Field => a + b)
                (encodeMonomial_sound labels term first ht assignment) (ih tail hr)

end Lemmata.CocubicCovering.CoveringEncoding
