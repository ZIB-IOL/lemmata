module

public import Lemmata.CocubicCovering.Proof.Embedding
public meta import Lemmata.CocubicCovering.Proof.Embedding
public import Lemmata.CocubicCovering.Proof.Moments
public meta import Lemmata.CocubicCovering.Proof.Moments
public import Mathlib.Combinatorics.Colex

@[expose] public section

set_option Elab.async false

namespace Lemmata.CocubicCovering.CoveringPairing

open scoped BigOperators
open Covering CoveringPolynomial CoveringCertificate CoveringEmbedding

def parameterCoefficients (p : ANF 9) (n : ℕ) : Field :=
  p (finiteMonomial 9 n.bitIndices.toFinset)

def parameterAssignment (p : ANF 9) (n : ℕ) : Bool := toBool (parameterCoefficients p n)

theorem parameterCoefficients_index (p : ANF 9) (s : Monomial) :
    parameterCoefficients p (CoveringMatrix.parameterIndex s) = p (finiteMonomial 9 s) := by
  simp [parameterCoefficients, CoveringMatrix.parameterIndex]

theorem finiteMonomial_complement (s : Monomial) :
    finiteMonomial 9 (CoveringMatrix.ambient \ s) = (finiteMonomial 9 s)ᶜ := by
  ext i
  simp [finiteMonomial, CoveringMatrix.ambient, i.isLt]

theorem image_finiteMonomial {m : ℕ} (s : Monomial) (hs : ∀ v ∈ s, v < m) :
    (finiteMonomial m s).image Fin.val = s := by
  apply Finset.Subset.antisymm
  · intro v hv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
    exact (Finset.mem_filter.mp hi).2
  · intro v hv
    exact Finset.mem_image.mpr ⟨⟨v, hs v hv⟩, by simp [finiteMonomial, hv], rfl⟩

theorem finiteMonomial_card {m : ℕ} (s : Monomial) (hs : ∀ v ∈ s, v < m) :
    (finiteMonomial m s).card = s.card := by
  have h := Finset.card_image_of_injective (f := fun i : Fin m => i.val) (finiteMonomial m s)
    (fun i j hij => (Fin.ext hij : i = j))
  rw [image_finiteMonomial s hs] at h
  exact h.symm

def constantPolynomial (cubics : List Monomial) (s : Monomial) : Polynomial :=
  cubics.foldr (fun term rest => if term ⊆ s then toggle ∅ rest else rest) []

def constantCount (cubics : List Monomial) (s : Monomial) : Field :=
  (cubics.map fun term => if term ⊆ s then (1 : Field) else 0).sum

theorem evalField_constantPolynomial (assignment : ℕ → Field)
    (cubics : List Monomial) (s : Monomial) :
    evalField assignment (constantPolynomial cubics s) = constantCount cubics s := by
  induction cubics with
  | nil => rfl
  | cons term rest ih =>
      change evalField assignment
        (if term ⊆ s then toggle ∅ (constantPolynomial rest s) else constantPolynomial rest s) =
          (if term ⊆ s then (1 : Field) else 0) + constantCount rest s
      by_cases hs : term ⊆ s <;>
        simp [hs, evalField_toggle, evalMonomialField, ih]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
def cubic9_constant_count_decision (s : Finset (Fin 9)) : Decidable ((∑ t : {t : Finset (Fin 9) // t.card = 3}, if t.val ⊆ s then cubic9 t else 0) =
        constantCount (CoveringMatrix.cubic ++ [{6, 7, 8}]) (s.image Fin.val)) :=
  inferInstance

@[noinline, never_extract]
def cubic9_constant_count_check (s : Finset (Fin 9)) : Bool :=
  @decide ((∑ t : {t : Finset (Fin 9) // t.card = 3}, if t.val ⊆ s then cubic9 t else 0) =
        constantCount (CoveringMatrix.cubic ++ [{6, 7, 8}]) (s.image Fin.val)) (cubic9_constant_count_decision s)

theorem cubic9_constant_count_check_sound (s : Finset (Fin 9)) (computed : cubic9_constant_count_check s = true) :
    (∑ t : {t : Finset (Fin 9) // t.card = 3}, if t.val ⊆ s then cubic9 t else 0) =
        constantCount (CoveringMatrix.cubic ++ [{6, 7, 8}]) (s.image Fin.val) := by
  unfold cubic9_constant_count_check at computed
  exact @of_decide_eq_true ((∑ t : {t : Finset (Fin 9) // t.card = 3}, if t.val ⊆ s then cubic9 t else 0) =
        constantCount (CoveringMatrix.cubic ++ [{6, 7, 8}]) (s.image Fin.val)) (cubic9_constant_count_decision s) computed

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem cubic9_constant_count :
    ∀ s : Finset (Fin 9),
      (∑ t : {t : Finset (Fin 9) // t.card = 3}, if t.val ⊆ s then cubic9 t else 0) =
        constantCount (CoveringMatrix.cubic ++ [{6, 7, 8}]) (s.image Fin.val) := by
  have computed : ∀ (s : Finset (Fin 9)), cubic9_constant_count_check s = true := by native_decide
  intro s
  exact cubic9_constant_count_check_sound s (computed s)

theorem form9_monomial_moment (s : Monomial) (hs : ∀ v ∈ s, v < 9) :
    (∑ x : Vector 9, monomial (finiteMonomial 9 s) x * Covering.eval form9 x) =
      constantCount (CoveringMatrix.cubic ++ [{6, 7, 8}]) s := by
  rw [show form9 = cubicComplement cubic9 from rfl, cocubic_moment_subset,
    cubic9_constant_count, image_finiteMonomial s hs]

theorem evalField_pairEquation (assignment : ℕ → Field) (left right : Monomial) :
    evalField assignment (CoveringMatrix.pairEquation left right) =
      constantCount CoveringMatrix.cubic (left ∪ right) +
        if (left ∪ right).card = 4 then
          assignment (CoveringMatrix.parameterIndex (CoveringMatrix.ambient \ (left ∪ right)))
        else 0 := by
  change evalField assignment (add (constantPolynomial CoveringMatrix.cubic (left ∪ right))
    (if (left ∪ right).card = 4 then
      [{CoveringMatrix.parameterIndex (CoveringMatrix.ambient \ (left ∪ right))}] else [])) = _
  rw [evalField_add, evalField_constantPolynomial]
  by_cases h : (left ∪ right).card = 4 <;>
    simp [h, evalField, evalMonomialField]

theorem evalMonomialField_at (term : Monomial) (hterm : ∀ v ∈ term, v < 9)
    (x : Vector 9) :
    evalMonomialField (extendAssignment x) term = monomial (finiteMonomial 9 term) x := by
  have hr : (fun i : Fin 9 => extendAssignment x i.val) = x := by
    funext i
    simp [extendAssignment, i.isLt]
  simpa only [hr] using (eval_finiteMonomial 9 term hterm (extendAssignment x)).symm

theorem finiteMonomial_union (left right : Monomial) :
    finiteMonomial 9 (left ∪ right) = finiteMonomial 9 left ∪ finiteMonomial 9 right := by
  ext i
  simp [finiteMonomial]

theorem pair_moment (p : ANF 9) (hp : DegreeLE p 5) (left right : Monomial)
    (hleft : ∀ v ∈ left, v < 9) (hright : ∀ v ∈ right, v < 9)
    (hdleft : left.card ≤ 2) (hdright : right.card ≤ 2)
    (hextra : ¬({6, 7, 8} : Monomial) ⊆ left ∪ right) :
    (∑ x : Vector 9,
      evalMonomialField (extendAssignment x) left *
        evalMonomialField (extendAssignment x) right * (Covering.eval form9 + Covering.eval p) x) =
      evalField (parameterCoefficients p) (CoveringMatrix.pairEquation left right) := by
  have hs : ∀ v ∈ left ∪ right, v < 9 := by
    intro v hv
    exact (Finset.mem_union.mp hv).elim (hleft v) (hright v)
  have hc : (left ∪ right).card ≤ 4 := by
    have hu := Finset.card_union_le left right
    omega
  have hfc : (finiteMonomial 9 (left ∪ right)).card ≤ 4 :=
    (finiteMonomial_card_le 9 _).trans hc
  simp_rw [evalMonomialField_at left hleft, evalMonomialField_at right hright,
    ← monomial_union, ← finiteMonomial_union, Pi.add_apply, mul_add]
  rw [Finset.sum_add_distrib, form9_monomial_moment _ hs,
    lower_degree_moment (by decide) p hp _ hfc, finiteMonomial_card _ hs,
    evalField_pairEquation, parameterCoefficients_index, finiteMonomial_complement]
  simp [constantCount, hextra, List.map_append, List.sum_append]

def rowEquation (left : Monomial) (right : Polynomial) : Polynomial :=
  right.foldr (fun term rest => add (CoveringMatrix.pairEquation left term) rest) []

private theorem row_moment_of_pair (assignment : ℕ → Field) (g : BooleanFunction 9)
    (left : Monomial) (right : Polynomial)
    (hpairs : ∀ term ∈ right,
      (∑ x : Vector 9, evalMonomialField (extendAssignment x) left *
        evalMonomialField (extendAssignment x) term * g x) =
          evalField assignment (CoveringMatrix.pairEquation left term)) :
    (∑ x : Vector 9, evalMonomialField (extendAssignment x) left *
      evalField (extendAssignment x) right * g x) =
        evalField assignment (rowEquation left right) := by
  induction right with
  | nil => simp [rowEquation, evalField]
  | cons term rest ih =>
      have hi := ih (fun t ht => hpairs t (by simp [ht]))
      change (∑ x : Vector 9, evalMonomialField (extendAssignment x) left *
        (evalMonomialField (extendAssignment x) term + evalField (extendAssignment x) rest) * g x) =
          evalField assignment (add (CoveringMatrix.pairEquation left term) (rowEquation left rest))
      simp_rw [mul_add, add_mul]
      rw [Finset.sum_add_distrib, evalField_add, hpairs term (by simp), hi]

theorem equation_moment_of_pair (assignment : ℕ → Field) (g : BooleanFunction 9)
    (left right : Polynomial)
    (hpairs : ∀ first ∈ left, ∀ second ∈ right,
      (∑ x : Vector 9, evalMonomialField (extendAssignment x) first *
        evalMonomialField (extendAssignment x) second * g x) =
          evalField assignment (CoveringMatrix.pairEquation first second)) :
    (∑ x : Vector 9, evalField (extendAssignment x) left *
      evalField (extendAssignment x) right * g x) =
        evalField assignment (CoveringMatrix.equation left right) := by
  induction left with
  | nil => simp [CoveringMatrix.equation, evalField]
  | cons term rest ih =>
      have hi := ih (fun t ht => hpairs t (by simp [ht]))
      change (∑ x : Vector 9,
        (evalMonomialField (extendAssignment x) term + evalField (extendAssignment x) rest) *
          evalField (extendAssignment x) right * g x) =
            evalField assignment (add (rowEquation term right) (CoveringMatrix.equation rest right))
      simp_rw [add_mul]
      rw [Finset.sum_add_distrib, evalField_add,
        row_moment_of_pair assignment g term right (hpairs term (by simp)), hi]

def multipliers_avoid_extra_decision (i j : Fin 24) : Decidable (∀ left ∈ CoveringMatrix.multiplier i,
      ∀ right ∈ CoveringMatrix.multiplier j,
        ¬({6, 7, 8} : Monomial) ⊆ left ∪ right) :=
  inferInstance

@[noinline, never_extract]
def multipliers_avoid_extra_check (i j : Fin 24) : Bool :=
  @decide (∀ left ∈ CoveringMatrix.multiplier i,
      ∀ right ∈ CoveringMatrix.multiplier j,
        ¬({6, 7, 8} : Monomial) ⊆ left ∪ right) (multipliers_avoid_extra_decision i j)

theorem multipliers_avoid_extra_check_sound (i j : Fin 24) (computed : multipliers_avoid_extra_check i j = true) :
    ∀ left ∈ CoveringMatrix.multiplier i,
      ∀ right ∈ CoveringMatrix.multiplier j,
        ¬({6, 7, 8} : Monomial) ⊆ left ∪ right := by
  unfold multipliers_avoid_extra_check at computed
  exact @of_decide_eq_true (∀ left ∈ CoveringMatrix.multiplier i,
      ∀ right ∈ CoveringMatrix.multiplier j,
        ¬({6, 7, 8} : Monomial) ⊆ left ∪ right) (multipliers_avoid_extra_decision i j) computed

theorem multipliers_avoid_extra :
    ∀ i j : Fin 24, ∀ left ∈ CoveringMatrix.multiplier i,
      ∀ right ∈ CoveringMatrix.multiplier j,
        ¬({6, 7, 8} : Monomial) ⊆ left ∪ right := by
  have computed : ∀ (i j : Fin 24), multipliers_avoid_extra_check i j = true := by native_decide
  intro i j
  exact multipliers_avoid_extra_check_sound i j (computed i j)

theorem multiplierLinear_basis (i : Fin 24) :
    multiplierLinear (Pi.single i 1) = multiplierFunction i := by
  simp [multiplierLinear, Pi.single_apply]

theorem coordinate_gram (p : ANF 9) (hp : DegreeLE p 5) (i j : Fin 24) :
    supportGram (Covering.eval form9 + Covering.eval p) multiplierLinear
      (Pi.single i 1) (Pi.single j 1) =
        ofBool (CoveringMatrix.matrix (parameterAssignment p) i j) := by
  rw [supportGram_apply, multiplierLinear_basis, multiplierLinear_basis]
  change (∑ x : Vector 9, Covering.eval (decode 9 (CoveringMatrix.multiplier i)) x *
    Covering.eval (decode 9 (CoveringMatrix.multiplier j)) x *
      (Covering.eval form9 + Covering.eval p) x) = _
  simp_rw [eval_decode_at _ (multiplier_bounded i), eval_decode_at _ (multiplier_bounded j)]
  rw [equation_moment_of_pair (parameterCoefficients p) _ _ _ ?_]
  · exact evalField_eq_ofBool (parameterCoefficients p)
      (CoveringMatrix.equation (CoveringMatrix.multiplier i) (CoveringMatrix.multiplier j))
  · intro left hleft right hright
    exact pair_moment p hp left right (multiplier_bounded i left hleft)
      (multiplier_bounded j right hright) (multiplier_degree i left hleft)
      (multiplier_degree j right hright) (multipliers_avoid_extra i j left hleft right hright)

theorem exists_parameter_assignment (h : BooleanFunction 9) (hh : h ∈ reedMuller 9 5) :
    ∃ assignment : ℕ → Bool, ∀ i j : Fin 24,
      supportGram (Covering.eval form9 + h) multiplierLinear (Pi.single i 1) (Pi.single j 1) =
        ofBool (CoveringMatrix.matrix assignment i j) := by
  obtain ⟨p, hp, rfl⟩ := mem_reedMuller_iff.mp hh
  exact ⟨parameterAssignment p, coordinate_gram p hp⟩

end Lemmata.CocubicCovering.CoveringPairing
