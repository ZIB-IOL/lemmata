module

public import Lemmata.RM59.Proof.CubicForms
public import Lemmata.RM59.Proof.Packed
public import Lemmata.RM59.Proof.Descent
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring
public meta import Lean.Elab.Tactic.Omega

@[expose] public section

namespace Lemmata.RM59.SupportForms

open scoped BigOperators

def evaluation (x : Point 9) : Point 9 →ₗ[Field] Field where
  toFun s := ∑ i, s i * x i
  map_add' s t := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' r s := by
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
    apply Finset.sum_congr rfl
    intro i _
    ring

@[simp] theorem evaluation_single (x : Point 9) (i : Fin 9) :
    evaluation x (Pi.single i 1) = x i := by
  simp [evaluation, Pi.single_apply]

def pointForm (x : Point 9) : MultilinearMap Field (fun _ : Fin 3 => Point 9) Field :=
  (MultilinearMap.mkPiAlgebra Field (Fin 3) Field).compLinearMap fun _ => evaluation x

def supportForm (P : Finset (Point 9)) :
    MultilinearMap Field (fun _ : Fin 3 => Point 9) Field := ∑ x ∈ P, pointForm x

theorem field_mul_repeat (a b : Field) : a * (a * b) = a * b := by
  rw [← mul_assoc, field_mul_self]

theorem monomial_pair (x : Point 9) (i j : Fin 9) :
    monomial {i, j} x = x i * x j := by
  by_cases h : i = j <;> simp_all [monomial_eq_prod, field_mul_self]

theorem monomial_triple (x : Point 9) (i j k : Fin 9) :
    monomial {i, j, k} x = x i * x j * x k := by
  by_cases hij : i = j <;> by_cases hik : i = k <;> by_cases hjk : j = k <;>
    simp_all [monomial_eq_prod, mul_assoc, mul_left_comm, mul_comm, field_mul_self, field_mul_repeat]

theorem supportForm_apply (P : Finset (Point 9)) (v : Fin 3 → Point 9) :
    supportForm P v = ∑ x ∈ P,
      evaluation x (v 0) * evaluation x (v 1) * evaluation x (v 2) := by
  simp [supportForm, pointForm, MultilinearMap.compLinearMap_apply,
    MultilinearMap.mkPiAlgebra_apply, Fin.prod_univ_succ, mul_assoc]

theorem supportForm_basis (P : Finset (Point 9)) (v : Fin 3 → Fin 9) :
    supportForm P (fun r => Pi.single (v r) 1) = supportMoment P {v 0, v 1, v 2} := by
  simp [supportForm, pointForm, MultilinearMap.compLinearMap_apply,
    MultilinearMap.mkPiAlgebra_apply, Fin.prod_univ_succ,
    supportMoment, monomial_triple, mul_assoc]

theorem packed_supportForm_basis (word : List Packed.PackedPoint) (hword : word.Nodup)
    (v : Fin 3 → Fin 9) :
    supportForm (Packed.decodeWord word) (fun r => Pi.single (v r) 1) =
      Packed.bitField (Packed.packedMoment word (Packed.encodeMask {v 0, v 1, v 2}).val) := by
  rw [supportForm_basis]
  have h := Packed.packedMoment_decodeWord word hword
    (Packed.encodeMask {v 0, v 1, v 2})
  rw [Packed.decodeMask_encodeMask] at h
  exact h.symm

theorem supportForm_eq_of_matchSupportMoments {P Q : Finset (Point 9)}
    (h : MatchSupportMoments 3 P Q) : supportForm P = supportForm Q := by
  apply Module.Basis.ext_multilinear (fun _ => Pi.basisFun Field (Fin 9))
  intro v
  simp only [Pi.basisFun_apply, supportForm_basis]
  exact h _ Finset.card_le_three

theorem matchSupportMoments_of_supportForm_eq {P Q : Finset (Point 9)}
    (h : supportForm P = supportForm Q)
    (hconstant : supportMoment P ∅ = supportMoment Q ∅) :
    MatchSupportMoments 3 P Q := by
  intro s hs
  have hcoeff (v : Fin 3 → Fin 9) :
      supportMoment P {v 0, v 1, v 2} = supportMoment Q {v 0, v 1, v 2} := by
    have heq := congrArg (fun f : MultilinearMap Field (fun _ : Fin 3 => Point 9) Field =>
      f fun r => Pi.single (v r) 1) h
    simpa only [supportForm_basis] using heq
  have hc : s.card = 0 ∨ s.card = 1 ∨ s.card = 2 ∨ s.card = 3 := by omega
  rcases hc with hc | hc | hc | hc
  · have : s = ∅ := Finset.card_eq_zero.mp hc
    simpa only [this] using hconstant
  · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hc
    simpa using hcoeff ![i, i, i]
  · obtain ⟨i, j, _, rfl⟩ := Finset.card_eq_two.mp hc
    simpa using hcoeff ![i, j, j]
  · obtain ⟨i, j, k, _, _, _, rfl⟩ := Finset.card_eq_three.mp hc
    simpa using hcoeff ![i, j, k]

abbrev LowerZero (P : Finset (Point 9)) : Prop :=
  ∀ s, s.card ≤ 2 → supportMoment P s = 0

theorem evaluation_sum_eq_zero (P : Finset (Point 9)) (hP : LowerZero P)
    (a : Point 9) : (∑ x ∈ P, evaluation x a) = 0 := by
  calc
    (∑ x ∈ P, evaluation x a) = ∑ i, a i * supportMoment P {i} := by
      change (∑ x ∈ P, ∑ i, a i * x i) = ∑ i, a i * supportMoment P {i}
      simp only [supportMoment, monomial_singleton, Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [hP {i} (by simp), mul_zero]

theorem evaluation_pair_sum_eq_zero (P : Finset (Point 9)) (hP : LowerZero P)
    (a b : Point 9) : (∑ x ∈ P, evaluation x a * evaluation x b) = 0 := by
  calc
    (∑ x ∈ P, evaluation x a * evaluation x b) =
        ∑ i, ∑ j, ∑ x ∈ P, (a i * x i) * (b j * x j) := by
      change (∑ x ∈ P, (∑ i, a i * x i) * (∑ j, b j * x j)) =
        ∑ i, ∑ j, ∑ x ∈ P, (a i * x i) * (b j * x j)
      calc
        _ = ∑ x ∈ P, ∑ i, ∑ j, (a i * x i) * (b j * x j) := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [Finset.sum_mul]
          simp only [Finset.mul_sum]
        _ = _ := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.sum_comm]
    _ = ∑ i, ∑ j, (a i * b j) * supportMoment P {i, j} := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      simp only [supportMoment, Finset.mul_sum, monomial_pair]
      apply Finset.sum_congr rfl
      intro x hx
      ring
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      apply Finset.sum_eq_zero
      intro j hj
      rw [hP {i, j} Finset.card_le_two, mul_zero]

private theorem supportForm_repeat_left (P : Finset (Point 9)) (hP : LowerZero P)
    (a b : Point 9) : supportForm P ![a, a, b] = 0 := by
  rw [supportForm_apply]
  change (∑ x ∈ P, evaluation x a * evaluation x a * evaluation x b) = 0
  simpa only [field_mul_self] using evaluation_pair_sum_eq_zero P hP a b

private theorem supportForm_repeat_right (P : Finset (Point 9)) (hP : LowerZero P)
    (a b : Point 9) : supportForm P ![a, b, b] = 0 := by
  rw [supportForm_apply]
  change (∑ x ∈ P, evaluation x a * evaluation x b * evaluation x b) = 0
  simpa only [mul_assoc, field_mul_self] using evaluation_pair_sum_eq_zero P hP a b

private theorem supportForm_repeat_outer (P : Finset (Point 9)) (hP : LowerZero P)
    (a b : Point 9) : supportForm P ![a, b, a] = 0 := by
  rw [supportForm_apply]
  change (∑ x ∈ P, evaluation x a * evaluation x b * evaluation x a) = 0
  have heq (x : Point 9) : evaluation x a * evaluation x b * evaluation x a =
      evaluation x a * evaluation x b := by
    rw [mul_right_comm, field_mul_self]
  simp_rw [heq]
  exact evaluation_pair_sum_eq_zero P hP a b

def alternatingSupportForm (P : Finset (Point 9)) (hP : LowerZero P) : CubicForm where
  __ := supportForm P
  map_eq_zero_of_eq' v i j he hij := by
    change supportForm P v = 0
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · change v 0 = v 1 at he
      have hv : v = ![v 0, v 0, v 2] := by
        funext r
        fin_cases r <;> simp [he]
      rw [hv]
      exact supportForm_repeat_left P hP (v 0) (v 2)
    · change v 0 = v 2 at he
      have hv : v = ![v 0, v 1, v 0] := by
        funext r
        fin_cases r <;> simp [he]
      rw [hv]
      exact supportForm_repeat_outer P hP (v 0) (v 1)
    · change v 1 = v 0 at he
      have hv : v = ![v 0, v 0, v 2] := by
        funext r
        fin_cases r <;> simp [he]
      rw [hv]
      exact supportForm_repeat_left P hP (v 0) (v 2)
    · exact (hij rfl).elim
    · change v 1 = v 2 at he
      have hv : v = ![v 0, v 1, v 1] := by
        funext r
        fin_cases r <;> simp [he]
      rw [hv]
      exact supportForm_repeat_right P hP (v 0) (v 1)
    · change v 2 = v 0 at he
      have hv : v = ![v 0, v 1, v 0] := by
        funext r
        fin_cases r <;> simp [he]
      rw [hv]
      exact supportForm_repeat_outer P hP (v 0) (v 1)
    · change v 2 = v 1 at he
      have hv : v = ![v 0, v 1, v 1] := by
        funext r
        fin_cases r <;> simp [he]
      rw [hv]
      exact supportForm_repeat_right P hP (v 0) (v 1)
    · exact (hij rfl).elim

@[simp] theorem alternatingSupportForm_apply (P : Finset (Point 9)) (hP : LowerZero P)
    (v : Fin 3 → Point 9) : alternatingSupportForm P hP v = supportForm P v := rfl

theorem evaluation_comm (x a : Point 9) : evaluation x a = evaluation a x := by
  simp [evaluation, mul_comm]

def pullback (g : Point 9 →ₗ[Field] Point 9) : Point 9 →ₗ[Field] Point 9 where
  toFun a := fun i => evaluation (g (Pi.single i 1)) a
  map_add' a b := by ext i; simp
  map_smul' r a := by ext i; simp

theorem evaluation_map (g : Point 9 →ₗ[Field] Point 9) (x a : Point 9) :
    evaluation (g x) a = evaluation x (pullback g a) := by
  have hx : (∑ i, x i • Pi.single i (1 : Field)) = x := by
    simpa only [Pi.basisFun_repr, Pi.basisFun_apply] using
      (Pi.basisFun Field (Fin 9)).sum_repr x
  calc
    evaluation (g x) a = evaluation a (g x) := evaluation_comm _ _
    _ = ∑ i, x i * evaluation a (g (Pi.single i 1)) := by
      conv_lhs => rw [← hx]
      simp only [map_sum, map_smul, smul_eq_mul]
    _ = evaluation x (pullback g a) := by
      change (∑ i, x i * evaluation a (g (Pi.single i 1))) =
        ∑ i, evaluation (g (Pi.single i 1)) a * x i
      apply Finset.sum_congr rfl
      intro i hi
      rw [evaluation_comm]
      ring

theorem supportForm_image (P : Finset (Point 9)) (g : Point 9 →ₗ[Field] Point 9)
    (hg : Function.Injective g) :
    supportForm (P.image g) = (supportForm P).compLinearMap fun _ => pullback g := by
  ext v
  simp only [supportForm_apply, MultilinearMap.compLinearMap_apply]
  rw [Finset.sum_image hg.injOn]
  simp only [evaluation_map]

theorem lowerZero_image (P : Finset (Point 9)) (hP : LowerZero P)
    (g : Point 9 →ₗ[Field] Point 9) (hg : Function.Injective g) :
    LowerZero (P.image g) := by
  intro s hs
  rw [supportMoment, Finset.sum_image hg.injOn]
  have hc : s.card = 0 ∨ s.card = 1 ∨ s.card = 2 := by omega
  rcases hc with hc | hc | hc
  · have : s = ∅ := Finset.card_eq_zero.mp hc
    subst s
    simpa only [supportMoment, monomial_empty] using hP ∅ (by simp)
  · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hc
    simpa only [monomial_singleton, ← evaluation_map, evaluation_single] using
      evaluation_sum_eq_zero P hP (pullback g (Pi.single i 1))
  · obtain ⟨i, j, _, rfl⟩ := Finset.card_eq_two.mp hc
    simpa only [monomial_pair, ← evaluation_map, evaluation_single] using
      evaluation_pair_sum_eq_zero P hP (pullback g (Pi.single i 1))
        (pullback g (Pi.single j 1))

theorem alternatingSupportForm_image (P : Finset (Point 9)) (hP : LowerZero P)
    (g : Point 9 →ₗ[Field] Point 9) (hg : Function.Injective g) :
    alternatingSupportForm (P.image g) (lowerZero_image P hP g hg) =
      (alternatingSupportForm P hP).compLinearMap (pullback g) := by
  apply AlternatingMap.coe_multilinearMap_injective
  exact supportForm_image P g hg

theorem evaluation_add_point (x t a : Point 9) :
    evaluation (x + t) a = evaluation x a + evaluation t a := by
  simp [evaluation, mul_add, Finset.sum_add_distrib]

theorem lowerZero_translate (P : Finset (Point 9)) (hP : LowerZero P) (t : Point 9) :
    LowerZero (translateSupport P t) := by
  have hconstant : (P.card : Field) = 0 := by
    simpa only [supportMoment_empty_index] using hP ∅ (by simp)
  have hfirst (i : Fin 9) : (∑ x ∈ P, x i) = 0 := by
    simpa only [supportMoment, monomial_singleton] using hP {i} (by simp)
  intro s hs
  rw [translateSupport_moments_two P t hconstant hfirst s hs]
  exact hP s hs

theorem supportForm_translate (P : Finset (Point 9)) (hP : LowerZero P) (t : Point 9) :
    supportForm (translateSupport P t) = supportForm P := by
  ext v
  simp only [supportForm_apply, translateSupport]
  have hinj : Function.Injective (fun x : Point 9 => x + t) :=
    fun _ _ h => add_right_cancel h
  rw [Finset.sum_image hinj.injOn]
  simp only [evaluation_add_point]
  have hconstant : (P.card : Field) = 0 := by
    simpa only [supportMoment_empty_index] using hP ∅ (by simp)
  let a := evaluation t (v 0)
  let b := evaluation t (v 1)
  let c := evaluation t (v 2)
  change (∑ x ∈ P, (evaluation x (v 0) + a) * (evaluation x (v 1) + b) *
      (evaluation x (v 2) + c)) = _
  calc
    _ = (∑ x ∈ P, evaluation x (v 0) * evaluation x (v 1) * evaluation x (v 2)) +
        a * (∑ x ∈ P, evaluation x (v 1) * evaluation x (v 2)) +
        b * (∑ x ∈ P, evaluation x (v 0) * evaluation x (v 2)) +
        c * (∑ x ∈ P, evaluation x (v 0) * evaluation x (v 1)) +
        (a * b) * (∑ x ∈ P, evaluation x (v 2)) +
        (a * c) * (∑ x ∈ P, evaluation x (v 1)) +
        (b * c) * (∑ x ∈ P, evaluation x (v 0)) + (P.card : Field) * (a * b * c) := by
      simp only [add_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum,
        Finset.sum_mul, Finset.sum_const, nsmul_eq_mul]
      ring
    _ = _ := by
      rw [evaluation_pair_sum_eq_zero P hP, evaluation_pair_sum_eq_zero P hP,
        evaluation_pair_sum_eq_zero P hP, evaluation_sum_eq_zero P hP,
        evaluation_sum_eq_zero P hP, evaluation_sum_eq_zero P hP, hconstant]
      ring

theorem alternatingSupportForm_translate (P : Finset (Point 9)) (hP : LowerZero P)
    (t : Point 9) :
    alternatingSupportForm (translateSupport P t) (lowerZero_translate P hP t) =
      alternatingSupportForm P hP := by
  apply AlternatingMap.coe_multilinearMap_injective
  exact supportForm_translate P hP t

end Lemmata.RM59.SupportForms
