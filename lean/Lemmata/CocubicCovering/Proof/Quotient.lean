module

public import Lemmata.CocubicCovering.Proof.Ideal
public meta import Lemmata.CocubicCovering.Proof.Ideal
public import Lemmata.CocubicCovering.Proof.Schur
public meta import Lemmata.CocubicCovering.Proof.Schur
public import Lemmata.CocubicCovering.Proof.Symplectic
public meta import Lemmata.CocubicCovering.Proof.Symplectic

@[expose] public section

set_option Elab.async false

namespace Lemmata.CocubicCovering.CoveringQuotient

open CoveringIdeal CoveringPolynomial
open scoped BigOperators

abbrev Polynomial := CoveringIdeal.Polynomial

def sumPolynomials (polynomials : List Polynomial) : Polynomial := polynomials.flatten

def finiteSum {n : ℕ} (polynomials : Fin n → Polynomial) : Polynomial :=
  sumPolynomials ((List.finRange n).map polynomials)

def constant (value : Bool) : Polynomial := if value then [0] else []

def variablePolynomial (index : ℕ) : Polynomial := [2 ^ index]

def scale (value : Bool) (polynomial : Polynomial) : Polynomial :=
  if value then polynomial else []

theorem eval_sumPolynomials (assignment : ℕ → Field) (polynomials : List Polynomial) :
    CoveringIdeal.eval assignment (sumPolynomials polynomials) =
      (polynomials.map (CoveringIdeal.eval assignment)).sum := by
  induction polynomials with
  | nil => rfl
  | cons first rest ih =>
      simpa only [sumPolynomials, List.flatten_cons, CoveringIdeal.eval_append,
        List.map_cons, List.sum_cons] using congrArg (CoveringIdeal.eval assignment first + ·) ih

theorem eval_finiteSum {n : ℕ} (assignment : ℕ → Field)
    (polynomials : Fin n → Polynomial) :
    CoveringIdeal.eval assignment (finiteSum polynomials) =
      ∑ i, CoveringIdeal.eval assignment (polynomials i) := by
  rw [finiteSum, eval_sumPolynomials, List.map_map,
    ← List.sum_toFinset _ (List.nodup_finRange n), List.toFinset_finRange]
  rfl

@[simp] theorem eval_constant (assignment : ℕ → Field) (value : Bool) :
    CoveringIdeal.eval assignment (constant value) = ofBool value := by
  cases value <;> simp [constant, CoveringIdeal.eval, CoveringIdeal.evalMonomial,
    evalMonomialField]

@[simp] theorem eval_variable (assignment : ℕ → Field) (index : ℕ) :
    CoveringIdeal.eval assignment (variablePolynomial index) = assignment index := by
  simp [variablePolynomial, CoveringIdeal.eval, CoveringIdeal.evalMonomial, evalMonomialField]

@[simp] theorem eval_scale (assignment : ℕ → Field) (value : Bool)
    (polynomial : Polynomial) :
    CoveringIdeal.eval assignment (scale value polynomial) =
      ofBool value * CoveringIdeal.eval assignment polynomial := by
  cases value <;> simp [scale]

def affinePolynomial {y : ℕ} (base : Bool) (directions : Fin y → Bool) : Polynomial :=
  constant base ++ finiteSum (fun i => scale (directions i) (variablePolynomial i.val))

theorem eval_affinePolynomial {y : ℕ} (assignment : ℕ → Field)
    (base : Bool) (directions : Fin y → Bool) :
    CoveringIdeal.eval assignment (affinePolynomial base directions) =
      ofBool base + ∑ i, ofBool (directions i) * assignment i.val := by
  simp only [affinePolynomial, CoveringIdeal.eval_append, eval_constant,
    eval_finiteSum, eval_scale, eval_variable]

def schurPolynomial {a d : ℕ} (inverse : Fin a → Fin a → Bool)
    (cross : Fin a → Fin d → Polynomial) (first second : Fin d) : Polynomial :=
  finiteSum fun i => finiteSum fun j =>
    scale (inverse i j) (products (cross i first) (cross j second))

theorem eval_schurPolynomial {a d : ℕ} (assignment : ℕ → Field)
    (inverse : Fin a → Fin a → Bool) (cross : Fin a → Fin d → Polynomial)
    (first second : Fin d) :
    CoveringIdeal.eval assignment (schurPolynomial inverse cross first second) =
      (Matrix.transpose (fun i j => CoveringIdeal.eval assignment (cross i j)) *
        Matrix.of (fun i j => ofBool (inverse i j)) *
        Matrix.of (fun i j => CoveringIdeal.eval assignment (cross i j))) first second := by
  simp only [schurPolynomial, eval_finiteSum, eval_scale, eval_products,
    Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Finset.sum_mul]
  dsimp only [Matrix.transpose]
  simp only [Matrix.of_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

def symplecticPolynomial {r d : ℕ}
    (x y : Fin d → Fin r → Polynomial) (first second : Fin d) : Polynomial :=
  finiteSum fun i => products (x first i) (y second i) ++ products (y first i) (x second i)

theorem eval_symplecticPolynomial {r d : ℕ} (assignment : ℕ → Field)
    (x y : Fin d → Fin r → Polynomial) (first second : Fin d) :
    CoveringIdeal.eval assignment (symplecticPolynomial x y first second) =
      CoveringSymplectic.standardBilin r
        ((fun i => CoveringIdeal.eval assignment (x first i)),
          fun i => CoveringIdeal.eval assignment (y first i))
        ((fun i => CoveringIdeal.eval assignment (x second i)),
          fun i => CoveringIdeal.eval assignment (y second i)) := by
  simp only [symplecticPolynomial, eval_finiteSum, CoveringIdeal.eval_append,
    eval_products, CoveringSymplectic.standardBilin_apply, CharTwo.sub_eq_add,
    Finset.sum_add_distrib]

def rawPolynomial {a r d : ℕ} (inverse : Fin a → Fin a → Bool)
    (cross : Fin a → Fin d → Polynomial) (outside : Fin d → Fin d → Polynomial)
    (x y : Fin d → Fin r → Polynomial) (first second : Fin d) : Polynomial :=
  outside first second ++ schurPolynomial inverse cross first second ++
    symplecticPolynomial x y first second

theorem eval_rawPolynomial {a r d : ℕ} (assignment : ℕ → Field)
    (inverse : Fin a → Fin a → Bool) (cross : Fin a → Fin d → Polynomial)
    (outside : Fin d → Fin d → Polynomial) (x y : Fin d → Fin r → Polynomial)
    (first second : Fin d) :
    CoveringIdeal.eval assignment (rawPolynomial inverse cross outside x y first second) =
      CoveringIdeal.eval assignment (outside first second) +
        (Matrix.transpose (fun i j => CoveringIdeal.eval assignment (cross i j)) *
          Matrix.of (fun i j => ofBool (inverse i j)) *
          Matrix.of (fun i j => CoveringIdeal.eval assignment (cross i j))) first second +
        CoveringSymplectic.standardBilin r
          ((fun i => CoveringIdeal.eval assignment (x first i)),
            fun i => CoveringIdeal.eval assignment (y first i))
          ((fun i => CoveringIdeal.eval assignment (x second i)),
            fun i => CoveringIdeal.eval assignment (y second i)) := by
  simp only [rawPolynomial, CoveringIdeal.eval_append,
    eval_schurPolynomial, eval_symplecticPolynomial]

theorem eval_rawPolynomial_of_gram {a r d : ℕ} (assignment : ℕ → Field)
    (inverse : Fin a → Fin a → Bool) (cross : Fin a → Fin d → Polynomial)
    (outside : Fin d → Fin d → Polynomial) (x y : Fin d → Fin r → Polynomial)
    (D R : Matrix (Fin d) (Fin d) Field)
    (houtside : ∀ i j, D i j = CoveringIdeal.eval assignment (outside i j) + R i j)
    (hgram : ∀ i j,
      CoveringSymplectic.standardBilin r
        ((fun k => CoveringIdeal.eval assignment (x i k)),
          fun k => CoveringIdeal.eval assignment (y i k))
        ((fun k => CoveringIdeal.eval assignment (x j k)),
          fun k => CoveringIdeal.eval assignment (y j k)) =
      CoveringSchur.schur (fun i j => ofBool (inverse i j))
        (fun i j => CoveringIdeal.eval assignment (cross i j))
        (Matrix.transpose (fun i j => CoveringIdeal.eval assignment (cross i j))) D i j)
    (first second : Fin d) :
    CoveringIdeal.eval assignment (rawPolynomial inverse cross outside x y first second) =
      R first second := by
  rw [eval_rawPolynomial, hgram]
  simp only [CoveringSchur.schur, Matrix.sub_apply]
  rw [houtside, CharTwo.sub_eq_add]
  have hc : ∀ u v w : Field, u + v + (u + w + v) = w := by
    intro u v w
    calc
      u + v + (u + w + v) = (u + u) + (v + v) + w := by ring
      _ = w := by simp [CharTwo.add_self_eq_zero]
  exact hc _ _ _

def quotientPolynomial {p q : ℕ} (keep : Fin q → Fin p → Bool)
    (raw : Fin p → Polynomial) (target : Fin q) : Polynomial :=
  finiteSum fun pair => scale (keep target pair) (raw pair)

theorem eval_quotientPolynomial {p q : ℕ} (assignment : ℕ → Field)
    (keep : Fin q → Fin p → Bool) (raw : Fin p → Polynomial) (target : Fin q) :
    CoveringIdeal.eval assignment (quotientPolynomial keep raw target) =
      ∑ pair, ofBool (keep target pair) * CoveringIdeal.eval assignment (raw pair) := by
  simp only [quotientPolynomial, eval_finiteSum, eval_scale]

theorem quotientPolynomial_vanishes {p q w : ℕ} (assignment : ℕ → Field)
    (keep : Fin q → Fin p → Bool) (raw : Fin p → Polynomial)
    (directions : Fin w → Fin p → Field) (coefficients : Fin w → Field)
    (hraw : ∀ pair, CoveringIdeal.eval assignment (raw pair) =
      ∑ k, coefficients k * directions k pair)
    (hannihilate : ∀ target k, ∑ pair, ofBool (keep target pair) * directions k pair = 0)
    (target : Fin q) :
    CoveringIdeal.eval assignment (quotientPolynomial keep raw target) = 0 := by
  rw [eval_quotientPolynomial]
  simp_rw [hraw, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro k hk
  calc
    (∑ pair, ofBool (keep target pair) * (coefficients k * directions k pair)) =
        coefficients k * ∑ pair, ofBool (keep target pair) * directions k pair := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro pair hpair
      ring
    _ = 0 := by rw [hannihilate target k, mul_zero]

theorem exists_assignment_of_injective {ι : Type*} (index : ι → ℕ)
    (hinjective : Function.Injective index) (value : ι → Field) :
    ∃ assignment : ℕ → Field, ∀ i, assignment (index i) = value i := by
  classical
  exact ⟨Function.extend index value (fun _ => 0),
    fun i => hinjective.extend_apply value (fun _ => 0) i⟩

end Lemmata.CocubicCovering.CoveringQuotient
