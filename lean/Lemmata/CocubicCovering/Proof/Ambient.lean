module

public import Lemmata.CocubicCovering.Proof.Realization
public meta import Lemmata.CocubicCovering.Proof.Realization

@[expose] public section

set_option Elab.async false

namespace Lemmata.CocubicCovering.CoveringAmbient

open scoped BigOperators
open Covering CoveringPolynomial CoveringCertificate
open CoveringPairing CoveringEncoding CoveringCongruence CoveringCovarianceData

def dimension (a : Fin 2) : ℕ := 10 + a.val

def extra (a : Fin 2) : Monomial := if a = 0 then {7, 8, 9} else {8, 9, 10}

def cubic (a : Fin 2) : CubicCoefficients (dimension a) :=
  exampleCubic (dimension a) (extra a)

def form (a : Fin 2) : ANF (dimension a) := cubicComplement (cubic a)

def sparseForm (a : Fin 2) : Polynomial :=
  (CoveringMatrix.cubic ++ [extra a]).map fun term => Finset.range (dimension a) \ term

theorem dimension_ge (a : Fin 2) : 9 ≤ dimension a := by
  unfold dimension
  omega

set_option maxRecDepth 16384 in
set_option maxHeartbeats 3000000 in
def decode_sparseForm_decision (a : Fin 2) : Decidable (decode (dimension a) (sparseForm a) = form a) :=
  inferInstance

@[noinline, never_extract]
def decode_sparseForm_check (a : Fin 2) : Bool :=
  @decide (decode (dimension a) (sparseForm a) = form a) (decode_sparseForm_decision a)

theorem decode_sparseForm_check_sound (a : Fin 2) (computed : decode_sparseForm_check a = true) :
    decode (dimension a) (sparseForm a) = form a := by
  unfold decode_sparseForm_check at computed
  exact @of_decide_eq_true (decode (dimension a) (sparseForm a) = form a) (decode_sparseForm_decision a) computed

set_option maxRecDepth 16384 in
set_option maxHeartbeats 3000000 in
theorem decode_sparseForm (a : Fin 2) : decode (dimension a) (sparseForm a) = form a := by
  have computed : ∀ (a : Fin 2), decode_sparseForm_check a = true := by native_decide
  exact decode_sparseForm_check_sound a (computed a)

def sparseForm_bounded_decision (a : Fin 2) : Decidable (Bounded (dimension a) (sparseForm a)) :=
  (by unfold Bounded; infer_instance)

@[noinline, never_extract]
def sparseForm_bounded_check (a : Fin 2) : Bool :=
  @decide (Bounded (dimension a) (sparseForm a)) (sparseForm_bounded_decision a)

theorem sparseForm_bounded_check_sound (a : Fin 2) (computed : sparseForm_bounded_check a = true) :
    Bounded (dimension a) (sparseForm a) := by
  unfold sparseForm_bounded_check at computed
  exact @of_decide_eq_true (Bounded (dimension a) (sparseForm a)) (sparseForm_bounded_decision a) computed

theorem sparseForm_bounded (a : Fin 2) : Bounded (dimension a) (sparseForm a) := by
  have computed : ∀ (a : Fin 2), sparseForm_bounded_check a = true := by native_decide
  exact sparseForm_bounded_check_sound a (computed a)

theorem multiplier_bounded (a : Fin 2) (i : Fin 24) :
    Bounded (dimension a) (CoveringMatrix.multiplier i) := by
  intro term hterm v hv
  exact (CoveringEmbedding.multiplier_bounded i term hterm v hv).trans_le (dimension_ge a)

def multiplier_product_bounded_decision (a : Fin 2) (i : Fin 24) : Decidable (Bounded (dimension a) (multiply (CoveringMatrix.multiplier i) (sparseForm a))) :=
  (by unfold Bounded; infer_instance)

@[noinline, never_extract]
def multiplier_product_bounded_check (a : Fin 2) (i : Fin 24) : Bool :=
  @decide (Bounded (dimension a) (multiply (CoveringMatrix.multiplier i) (sparseForm a))) (multiplier_product_bounded_decision a i)

theorem multiplier_product_bounded_check_sound (a : Fin 2) (i : Fin 24) (computed : multiplier_product_bounded_check a i = true) :
    Bounded (dimension a) (multiply (CoveringMatrix.multiplier i) (sparseForm a)) := by
  unfold multiplier_product_bounded_check at computed
  exact @of_decide_eq_true (Bounded (dimension a) (multiply (CoveringMatrix.multiplier i) (sparseForm a))) (multiplier_product_bounded_decision a i) computed

theorem multiplier_product_bounded (a : Fin 2) (i : Fin 24) :
    Bounded (dimension a) (multiply (CoveringMatrix.multiplier i) (sparseForm a)) := by
  have computed : ∀ (a : Fin 2) (i : Fin 24), multiplier_product_bounded_check a i = true := by native_decide
  exact multiplier_product_bounded_check_sound a i (computed a i)

def multiplier_product_degree_decision (a : Fin 2) (i : Fin 24) : Decidable (∀ term ∈ multiply (CoveringMatrix.multiplier i) (sparseForm a),
      term.card ≤ dimension a - 2) :=
  inferInstance

@[noinline, never_extract]
def multiplier_product_degree_check (a : Fin 2) (i : Fin 24) : Bool :=
  @decide (∀ term ∈ multiply (CoveringMatrix.multiplier i) (sparseForm a),
      term.card ≤ dimension a - 2) (multiplier_product_degree_decision a i)

theorem multiplier_product_degree_check_sound (a : Fin 2) (i : Fin 24) (computed : multiplier_product_degree_check a i = true) :
    ∀ term ∈ multiply (CoveringMatrix.multiplier i) (sparseForm a),
      term.card ≤ dimension a - 2 := by
  unfold multiplier_product_degree_check at computed
  exact @of_decide_eq_true (∀ term ∈ multiply (CoveringMatrix.multiplier i) (sparseForm a),
      term.card ≤ dimension a - 2) (multiplier_product_degree_decision a i) computed

theorem multiplier_product_degree (a : Fin 2) (i : Fin 24) :
    ∀ term ∈ multiply (CoveringMatrix.multiplier i) (sparseForm a),
      term.card ≤ dimension a - 2 := by
  have computed : ∀ (a : Fin 2) (i : Fin 24), multiplier_product_degree_check a i = true := by native_decide
  exact multiplier_product_degree_check_sound a i (computed a i)

def multiplierFunction (a : Fin 2) (i : Fin 24) : BooleanFunction (dimension a) :=
  Covering.eval (decode (dimension a) (CoveringMatrix.multiplier i))

def multiplierLinear (a : Fin 2) : Vector 24 →ₗ[Field] BooleanFunction (dimension a) where
  toFun v := ∑ i, v i • multiplierFunction a i
  map_add' v w := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c v := by simp [Finset.smul_sum, smul_smul]

theorem multiplier_mem (a : Fin 2) (i : Fin 24) :
    multiplierFunction a i ∈ reedMuller (dimension a) 2 :=
  decode_mem_reedMuller _ _ _ (CoveringEmbedding.multiplier_degree i)

theorem multiplier_product_mem (a : Fin 2) (i : Fin 24) :
    multiplierFunction a i * Covering.eval (form a) ∈
      reedMuller (dimension a) (dimension a - 2) := by
  have heq : Covering.eval (decode (dimension a)
      (multiply (CoveringMatrix.multiplier i) (sparseForm a))) =
        multiplierFunction a i * Covering.eval (form a) := by
    funext x
    change Covering.eval (decode (dimension a)
      (multiply (CoveringMatrix.multiplier i) (sparseForm a))) x =
        Covering.eval (decode (dimension a) (CoveringMatrix.multiplier i)) x *
          Covering.eval (form a) x
    rw [CoveringEmbedding.eval_decode_at _ (multiplier_product_bounded a i),
      evalField_multiply, ← CoveringEmbedding.eval_decode_at _ (multiplier_bounded a i),
      ← CoveringEmbedding.eval_decode_at _ (sparseForm_bounded a), decode_sparseForm]
  rw [← heq]
  exact decode_mem_reedMuller _ _ _ (multiplier_product_degree a i)

theorem multiplierLinear_mem (a : Fin 2) (v : Vector 24) :
    multiplierLinear a v ∈ reedMuller (dimension a) 2 := by
  change (∑ i : Fin 24, v i • multiplierFunction a i) ∈ reedMuller (dimension a) 2
  apply (reedMuller (dimension a) 2).sum_mem
  intro i hi
  exact (reedMuller (dimension a) 2).smul_mem (v i) (multiplier_mem a i)

theorem multiplierLinear_products (a : Fin 2) (v : Vector 24) :
    multiplierLinear a v * Covering.eval (form a) ∈
      reedMuller (dimension a) (dimension a - 2) := by
  have heq : multiplierLinear a v * Covering.eval (form a) =
      ∑ i : Fin 24, v i • (multiplierFunction a i * Covering.eval (form a)) := by
    funext x
    simp [multiplierLinear, Finset.sum_mul, mul_assoc]
  rw [heq]
  apply (reedMuller (dimension a) (dimension a - 2)).sum_mem
  intro i hi
  exact (reedMuller (dimension a) (dimension a - 2)).smul_mem (v i)
    (multiplier_product_mem a i)

theorem affine_dimension_lower (a : Fin 2) (h : BooleanFunction (dimension a))
    (hh : h ∈ reedMuller (dimension a) (dimension a - 4)) :
    dimension a + 1 ≤ Module.finrank Field (affineOnSupport (Covering.eval (form a) + h)) := by
  fin_cases a
  · exact form10_affine_dimension_lower h hh
  · exact form11_affine_dimension_lower h hh

theorem weight_lower (a : Fin 2) (h : BooleanFunction (dimension a))
    (hh : h ∈ reedMuller (dimension a) (dimension a - 4)) :
    2 * (dimension a + 1) + Module.finrank Field
      (LinearMap.range (supportGram (Covering.eval (form a) + h) (multiplierLinear a))) ≤
        weight (Covering.eval (form a) + h) := by
  have hm := dimension_ge a
  have hweight := weight_bound_of_correction (by omega) (Covering.eval (form a)) h
    (cubicComplement_mem (cubic a)) hh (multiplierLinear a)
    (multiplierLinear_mem a) (multiplierLinear_products a)
  have hdim := affine_dimension_lower a h hh
  omega

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
def cubic_constant_count_decision (a : Fin 2) : Decidable (∀ s : Finset (Fin 9),
      (∑ t : {t : Finset (Fin (dimension a)) // t.card = 3},
        if t.val ⊆ finiteMonomial (dimension a) (s.image Fin.val) then cubic a t else 0) =
          constantCount CoveringMatrix.cubic (s.image Fin.val)) :=
  inferInstance

@[noinline, never_extract]
def cubic_constant_count_check (a : Fin 2) : Bool :=
  @decide (∀ s : Finset (Fin 9),
      (∑ t : {t : Finset (Fin (dimension a)) // t.card = 3},
        if t.val ⊆ finiteMonomial (dimension a) (s.image Fin.val) then cubic a t else 0) =
          constantCount CoveringMatrix.cubic (s.image Fin.val)) (cubic_constant_count_decision a)

theorem cubic_constant_count_check_sound (a : Fin 2) (computed : cubic_constant_count_check a = true) :
    ∀ s : Finset (Fin 9),
      (∑ t : {t : Finset (Fin (dimension a)) // t.card = 3},
        if t.val ⊆ finiteMonomial (dimension a) (s.image Fin.val) then cubic a t else 0) =
          constantCount CoveringMatrix.cubic (s.image Fin.val) := by
  unfold cubic_constant_count_check at computed
  exact @of_decide_eq_true (∀ s : Finset (Fin 9),
      (∑ t : {t : Finset (Fin (dimension a)) // t.card = 3},
        if t.val ⊆ finiteMonomial (dimension a) (s.image Fin.val) then cubic a t else 0) =
          constantCount CoveringMatrix.cubic (s.image Fin.val)) (cubic_constant_count_decision a) computed

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem cubic_constant_count (a : Fin 2) :
    ∀ s : Finset (Fin 9),
      (∑ t : {t : Finset (Fin (dimension a)) // t.card = 3},
        if t.val ⊆ finiteMonomial (dimension a) (s.image Fin.val) then cubic a t else 0) =
          constantCount CoveringMatrix.cubic (s.image Fin.val) := by
  have computed : ∀ (a : Fin 2), cubic_constant_count_check a = true := by native_decide
  exact cubic_constant_count_check_sound a (computed a)

theorem form_monomial_moment (a : Fin 2) (s : Monomial) (hs : ∀ v ∈ s, v < 9) :
    (∑ x : Vector (dimension a), monomial (finiteMonomial (dimension a) s) x *
      Covering.eval (form a) x) = constantCount CoveringMatrix.cubic s := by
  rw [form, cocubic_moment_subset]
  have h := cubic_constant_count a (finiteMonomial 9 s)
  rw [image_finiteMonomial s hs] at h
  exact h

def parameterCoefficients (a : Fin 2) (p : ANF (dimension a)) (n : ℕ) : Field :=
  p ((finiteMonomial (dimension a) (CoveringMatrix.ambient \ n.bitIndices.toFinset))ᶜ)

theorem parameterCoefficients_index (a : Fin 2) (p : ANF (dimension a))
    (s : Monomial) (hs : ∀ v ∈ s, v < 9) :
    parameterCoefficients a p (CoveringMatrix.parameterIndex (CoveringMatrix.ambient \ s)) =
      p ((finiteMonomial (dimension a) s)ᶜ) := by
  have hsub : s ⊆ CoveringMatrix.ambient := by
    intro v hv
    exact Finset.mem_range.mpr (hs v hv)
  simp [parameterCoefficients, CoveringMatrix.parameterIndex, sdiff_sdiff_eq_self hsub]

theorem evalMonomialField_at {m : ℕ} (term : Monomial) (hterm : ∀ v ∈ term, v < m)
    (x : Vector m) :
    evalMonomialField (CoveringEmbedding.extendAssignment x) term =
      monomial (finiteMonomial m term) x := by
  have hr : (fun i : Fin m => CoveringEmbedding.extendAssignment x i.val) = x := by
    funext i
    simp [CoveringEmbedding.extendAssignment, i.isLt]
  simpa only [hr] using
    (eval_finiteMonomial m term hterm (CoveringEmbedding.extendAssignment x)).symm

theorem finiteMonomial_union {m : ℕ} (left right : Monomial) :
    finiteMonomial m (left ∪ right) = finiteMonomial m left ∪ finiteMonomial m right := by
  ext i
  simp [finiteMonomial]

theorem pair_moment (a : Fin 2) (p : ANF (dimension a))
    (hp : DegreeLE p (dimension a - 4)) (left right : Monomial)
    (hleft : ∀ v ∈ left, v < 9) (hright : ∀ v ∈ right, v < 9)
    (hdleft : left.card ≤ 2) (hdright : right.card ≤ 2) :
    (∑ x : Vector (dimension a),
      evalMonomialField (CoveringEmbedding.extendAssignment x) left *
        evalMonomialField (CoveringEmbedding.extendAssignment x) right *
          (Covering.eval (form a) + Covering.eval p) x) =
      evalField (parameterCoefficients a p) (CoveringMatrix.pairEquation left right) := by
  have hm := dimension_ge a
  have hs : ∀ v ∈ left ∪ right, v < 9 := by
    intro v hv
    exact (Finset.mem_union.mp hv).elim (hleft v) (hright v)
  have hleftm : ∀ v ∈ left, v < dimension a := fun v hv => (hleft v hv).trans_le hm
  have hrightm : ∀ v ∈ right, v < dimension a := fun v hv => (hright v hv).trans_le hm
  have hsm : ∀ v ∈ left ∪ right, v < dimension a := fun v hv => (hs v hv).trans_le hm
  have hc : (left ∪ right).card ≤ 4 := by
    have hu := Finset.card_union_le left right
    omega
  have hfc : (finiteMonomial (dimension a) (left ∪ right)).card ≤ 4 :=
    (finiteMonomial_card_le _ _).trans hc
  simp_rw [evalMonomialField_at left hleftm, evalMonomialField_at right hrightm,
    ← monomial_union, ← finiteMonomial_union, Pi.add_apply, mul_add]
  rw [Finset.sum_add_distrib, form_monomial_moment a _ hs,
    lower_degree_moment (by omega) p hp _ hfc, finiteMonomial_card _ hsm,
    evalField_pairEquation, parameterCoefficients_index a p _ hs]

def rowEquation (left : Monomial) (right : Polynomial) : Polynomial :=
  right.foldr (fun term rest => add (CoveringMatrix.pairEquation left term) rest) []

private theorem row_moment_of_pair {X : Type} [Fintype X]
    (assignment : ℕ → Field) (values : X → ℕ → Field) (g : X → Field)
    (left : Monomial) (right : Polynomial)
    (hpairs : ∀ term ∈ right,
      (∑ x, evalMonomialField (values x) left * evalMonomialField (values x) term * g x) =
        evalField assignment (CoveringMatrix.pairEquation left term)) :
    (∑ x, evalMonomialField (values x) left * evalField (values x) right * g x) =
      evalField assignment (rowEquation left right) := by
  induction right with
  | nil => simp [rowEquation, evalField]
  | cons term rest ih =>
      have hi := ih (fun t ht => hpairs t (by simp [ht]))
      change (∑ x, evalMonomialField (values x) left *
        (evalMonomialField (values x) term + evalField (values x) rest) * g x) =
          evalField assignment (add (CoveringMatrix.pairEquation left term) (rowEquation left rest))
      simp_rw [mul_add, add_mul]
      rw [Finset.sum_add_distrib, evalField_add, hpairs term (by simp), hi]

theorem equation_moment_of_pair {X : Type} [Fintype X]
    (assignment : ℕ → Field) (values : X → ℕ → Field) (g : X → Field)
    (left right : Polynomial)
    (hpairs : ∀ first ∈ left, ∀ second ∈ right,
      (∑ x, evalMonomialField (values x) first * evalMonomialField (values x) second * g x) =
        evalField assignment (CoveringMatrix.pairEquation first second)) :
    (∑ x, evalField (values x) left * evalField (values x) right * g x) =
      evalField assignment (CoveringMatrix.equation left right) := by
  induction left with
  | nil => simp [CoveringMatrix.equation, evalField]
  | cons term rest ih =>
      have hi := ih (fun t ht => hpairs t (by simp [ht]))
      change (∑ x,
        (evalMonomialField (values x) term + evalField (values x) rest) *
          evalField (values x) right * g x) =
            evalField assignment (add (rowEquation term right) (CoveringMatrix.equation rest right))
      simp_rw [add_mul]
      rw [Finset.sum_add_distrib, evalField_add,
        row_moment_of_pair assignment values g term right (hpairs term (by simp)), hi]

theorem multiplierLinear_basis (a : Fin 2) (i : Fin 24) :
    multiplierLinear a (Pi.single i 1) = multiplierFunction a i := by
  simp [multiplierLinear, Pi.single_apply]

theorem coordinate_gram (a : Fin 2) (p : ANF (dimension a))
    (hp : DegreeLE p (dimension a - 4)) (i j : Fin 24) :
    supportGram (Covering.eval (form a) + Covering.eval p) (multiplierLinear a)
      (Pi.single i 1) (Pi.single j 1) =
        evalField (parameterCoefficients a p)
          (CoveringMatrix.equation (CoveringMatrix.multiplier i) (CoveringMatrix.multiplier j)) := by
  rw [supportGram_apply, multiplierLinear_basis, multiplierLinear_basis]
  change (∑ x : Vector (dimension a),
    Covering.eval (decode (dimension a) (CoveringMatrix.multiplier i)) x *
      Covering.eval (decode (dimension a) (CoveringMatrix.multiplier j)) x *
        (Covering.eval (form a) + Covering.eval p) x) = _
  simp_rw [CoveringEmbedding.eval_decode_at _ (multiplier_bounded a i),
    CoveringEmbedding.eval_decode_at _ (multiplier_bounded a j)]
  apply equation_moment_of_pair
  intro left hleft right hright
  exact pair_moment a p hp left right (CoveringEmbedding.multiplier_bounded i left hleft)
    (CoveringEmbedding.multiplier_bounded j right hright)
    (CoveringEmbedding.multiplier_degree i left hleft)
    (CoveringEmbedding.multiplier_degree j right hright)

theorem exists_pointed_realization (a : Fin 2) (h : BooleanFunction (dimension a))
    (hh : h ∈ reedMuller (dimension a) (dimension a - 4)) :
    ∃ v : Vector 127, v (Fin.last 126) = 1 ∧
      supportGram (Covering.eval (form a) + h) (multiplierLinear a) =
        Matrix.toBilin' (coefficientMatrix matrixRows v) := by
  obtain ⟨p, hp, rfl⟩ := mem_reedMuller_iff.mp hh
  let v := pointedVector parameterMasks (parameterCoefficients a p)
  refine ⟨v, ?_, ?_⟩
  · change Fin.lastCases (motive := fun _ : Fin 127 => Field) (1 : Field)
      (fun i : Fin 126 => parameterCoefficients a p (parameterMasks i)) (Fin.last 126) = 1
    rw [Fin.lastCases_last]
  · apply (Pi.basisFun Field (Fin 24)).ext
    intro i
    apply (Pi.basisFun Field (Fin 24)).ext
    intro j
    simpa only [Pi.basisFun_apply, Matrix.toBilin'_single] using
      (coordinate_gram a p hp i j).trans
        (congrFun (congrFun (matrix_equations (parameterCoefficients a p)) i) j)

theorem packed_weight_reduction (a : Fin 2) (h : BooleanFunction (dimension a))
    (hh : h ∈ reedMuller (dimension a) (dimension a - 4)) :
    ∃ v : Vector 127, v (Fin.last 126) = 1 ∧
      2 * (dimension a + 1) + Module.finrank Field
        (LinearMap.range (Matrix.toBilin' (coefficientMatrix matrixRows v))) ≤
          weight (Covering.eval (form a) + h) := by
  obtain ⟨v, hv, hgram⟩ := exists_pointed_realization a h hh
  refine ⟨v, hv, ?_⟩
  have hweight := weight_lower a h hh
  rw [hgram] at hweight
  exact hweight

theorem form10_packed_weight_reduction (h : BooleanFunction 10) (hh : h ∈ reedMuller 10 6) :
    ∃ v : Vector 127, v (Fin.last 126) = 1 ∧
      22 + Module.finrank Field
        (LinearMap.range (Matrix.toBilin' (coefficientMatrix matrixRows v))) ≤
          weight (Covering.eval form10 + h) :=
  packed_weight_reduction 0 h hh

theorem form11_packed_weight_reduction (h : BooleanFunction 11) (hh : h ∈ reedMuller 11 7) :
    ∃ v : Vector 127, v (Fin.last 126) = 1 ∧
      24 + Module.finrank Field
        (LinearMap.range (Matrix.toBilin' (coefficientMatrix matrixRows v))) ≤
          weight (Covering.eval form11 + h) :=
  packed_weight_reduction 1 h hh

end Lemmata.CocubicCovering.CoveringAmbient
