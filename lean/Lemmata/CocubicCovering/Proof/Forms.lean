module

public import Lemmata.CocubicCovering.Proof.Bound
public meta import Lemmata.CocubicCovering.Proof.Bound
public import Mathlib.Tactic.FinCases

@[expose] public section

set_option Elab.async false

namespace Lemmata.CocubicCovering.Covering

open scoped BigOperators

def commonTriples : List (Finset ℕ) :=
  [{0, 3, 6}, {0, 4, 7}, {0, 5, 8},
   {1, 3, 7}, {1, 4, 6}, {1, 4, 8}, {1, 5, 6},
   {2, 3, 8}, {2, 4, 6}, {2, 5, 7}, {2, 5, 8}]

def exampleCubic (m : ℕ) (extra : Finset ℕ) : CubicCoefficients m :=
  fun s => if s.val.image Fin.val ∈ commonTriples ++ [extra] then 1 else 0

def cubic9 : CubicCoefficients 9 := exampleCubic 9 {6, 7, 8}
def cubic10 : CubicCoefficients 10 := exampleCubic 10 {7, 8, 9}
def cubic11 : CubicCoefficients 11 := exampleCubic 11 {8, 9, 10}

def form9 : ANF 9 := cubicComplement cubic9
def form10 : ANF 10 := cubicComplement cubic10
def form11 : ANF 11 := cubicComplement cubic11

theorem form9_mem : eval form9 ∈ reedMuller 9 6 := cubicComplement_mem cubic9
theorem form10_mem : eval form10 ∈ reedMuller 10 7 := cubicComplement_mem cubic10
theorem form11_mem : eval form11 ∈ reedMuller 11 8 := cubicComplement_mem cubic11

abbrev Pair (m : ℕ) := {s : Finset (Fin m) // s.card = 2}

def contractionEntry {m : ℕ} (c : CubicCoefficients m) (s : Pair m) (i : Fin m) :
    Field :=
  if hi : i ∈ s.val then 0 else c ⟨insert i s.val, by
    rw [Finset.card_insert_of_notMem hi, s.property]⟩

def coefficientContraction {m : ℕ} (c : CubicCoefficients m) :
    Vector m →ₗ[Field] (Pair m → Field) where
  toFun v s := ∑ i, v i * contractionEntry c s i
  map_add' v w := by
    funext s
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' a v := by
    funext s
    simp [mul_assoc, Finset.mul_sum]

@[simp] theorem coefficientContraction_apply {m : ℕ} (c : CubicCoefficients m)
    (v : Vector m) (s : Pair m) :
    coefficientContraction c v s = ∑ i, v i * contractionEntry c s i := rfl

theorem contraction_injective_of_pivots {m : ℕ} (c : CubicCoefficients m)
    (pairs : Fin m → Pair m)
    (h : ∀ i j, contractionEntry c (pairs i) j = if i = j then 1 else 0) :
    Function.Injective (coefficientContraction c) := by
  intro v w hvw
  funext i
  have hi := congrFun hvw (pairs i)
  simpa [coefficientContraction, h] using hi

def pivots9 (i : Fin 9) : Pair 9 :=
  ⟨(![{3, 6}, {3, 7}, {3, 8}, {0, 6}, {0, 7}, {0, 8}, {0, 3}, {0, 4}, {0, 5}]) i,
    by fin_cases i <;> decide⟩

def pivots10 (i : Fin 10) : Pair 10 :=
  ⟨(![{3, 6}, {3, 7}, {3, 8}, {0, 6}, {0, 7}, {0, 8}, {0, 3}, {0, 4}, {0, 5},
    {7, 8}]) i, by fin_cases i <;> decide⟩

def pivots11 (i : Fin 11) : Pair 11 :=
  ⟨(![{3, 6}, {3, 7}, {3, 8}, {0, 6}, {0, 7}, {0, 8}, {0, 3}, {0, 4}, {0, 5},
    {8, 10}, {8, 9}]) i, by fin_cases i <;> decide⟩

theorem cubic9_contraction_injective : Function.Injective (coefficientContraction cubic9) := by
  apply contraction_injective_of_pivots cubic9 pivots9
  intro i j
  fin_cases i <;> fin_cases j <;> native_decide

theorem cubic10_contraction_injective : Function.Injective (coefficientContraction cubic10) := by
  apply contraction_injective_of_pivots cubic10 pivots10
  intro i j
  fin_cases i <;> fin_cases j <;> native_decide

theorem cubic11_contraction_injective : Function.Injective (coefficientContraction cubic11) := by
  apply contraction_injective_of_pivots cubic11 pivots11
  intro i j
  fin_cases i <;> fin_cases j <;> native_decide

theorem monomial_mem_reedMuller {m r : ℕ} (s : Finset (Fin m)) (hs : s.card ≤ r) :
    monomial s ∈ reedMuller m r := by
  apply mem_reedMuller_iff.mpr
  refine ⟨Pi.single s 1, ?_, ?_⟩
  · intro t ht
    by_cases hts : t = s
    · subst t
      omega
    · simp [Pi.single_apply, hts, Ne.symm hts]
  · funext x
    simp [eval, Pi.single_apply]

@[simp] theorem monomial_singleton {m : ℕ} (i : Fin m) (x : Vector m) :
    monomial {i} x = x i := by
  unfold monomial
  rw [Finset.prod_eq_single i]
  · simp
  · intro j hj hji
    simp [hji]
  · simp

theorem monomial_insert {m : ℕ} (i : Fin m) (s : Finset (Fin m)) (x : Vector m) :
    monomial (insert i s) x = x i * monomial s x := by
  simpa using monomial_union {i} s x

theorem monomial_moment {m : ℕ} (p : ANF m) (s : Finset (Fin m)) :
    (∑ x : Vector m, monomial s x * eval p x) =
      ∑ t, p t * if t ∪ s = Finset.univ then 1 else 0 := by
  classical
  calc
    _ = ∑ t, p t * (∑ x : Vector m, monomial (t ∪ s) x) := by
      simp_rw [eval, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro t ht
      simp [Finset.mul_sum, monomial_union, mul_assoc, mul_left_comm, mul_comm]
    _ = _ := by simp_rw [sum_monomial]

theorem cubic_moment {m : ℕ} (c : CubicCoefficients m)
    (s : {s : Finset (Fin m) // s.card = 3}) :
    (∑ x : Vector m, monomial s.val x * eval (cubicComplement c) x) = c s := by
  classical
  rw [monomial_moment]
  rw [Finset.sum_eq_single s.valᶜ]
  · have hu : s.valᶜ ∪ s.val = Finset.univ := by
      rw [Finset.union_comm, Finset.union_compl]
    simp [cubicComplement, s.property, hu]
  · intro t ht hts
    by_cases hc : tᶜ.card = 3
    · have hn : t ∪ s.val ≠ Finset.univ := by
        intro hu
        have hsub : tᶜ ⊆ s.val := by
          intro i hi
          have hiu : i ∈ t ∪ s.val := by rw [hu]; simp
          exact (Finset.mem_union.mp hiu).resolve_left (Finset.mem_compl.mp hi)
        have heq : tᶜ = s.val :=
          Finset.eq_of_subset_of_card_le hsub (by rw [hc, s.property])
        exact hts (by simpa using congrArg (fun u : Finset (Fin m) => uᶜ) heq)
      simp [hn]
    · simp [cubicComplement, hc]
  · simp

def affineFunctionLinear (m : ℕ) : (Field × Vector m) →ₗ[Field] BooleanFunction m where
  toFun a x := a.1 + ∑ i, a.2 i * x i
  map_add' a b := by
    funext x
    simp [add_mul, Finset.sum_add_distrib, add_assoc, add_comm, add_left_comm]
  map_smul' a v := by
    funext x
    simp [mul_add, Finset.mul_sum, mul_assoc]

@[simp] theorem affineFunctionLinear_apply {m : ℕ} (a : Field × Vector m) (x : Vector m) :
    affineFunctionLinear m a x = a.1 + ∑ i, a.2 i * x i := rfl

theorem affineFunction_mem {m : ℕ} (a : Field × Vector m) :
    affineFunctionLinear m a ∈ reedMuller m 1 := by
  have hc : (fun _ : Vector m => a.1) ∈ reedMuller m 1 := by
    have he : a.1 • monomial (∅ : Finset (Fin m)) = (fun _ : Vector m => a.1) := by
      funext x
      simp [monomial]
    rw [← he]
    exact (reedMuller m 1).smul_mem a.1 (monomial_mem_reedMuller ∅ (by simp))
  have hl : (∑ i : Fin m, a.2 i • monomial {i}) ∈ reedMuller m 1 := by
    apply (reedMuller m 1).sum_mem
    intro i hi
    exact (reedMuller m 1).smul_mem _ (monomial_mem_reedMuller {i} (by simp))
  have heq : affineFunctionLinear m a =
      (fun _ : Vector m => a.1) + ∑ i : Fin m, a.2 i • monomial {i} := by
    funext x
    simp [affineFunctionLinear]
  rw [heq]
  exact (reedMuller m 1).add_mem hc hl

theorem cubic_correction_moment {m : ℕ} (hm : 4 ≤ m) (c : CubicCoefficients m)
    (h : BooleanFunction m) (hh : h ∈ reedMuller m (m - 4))
    (s : {s : Finset (Fin m) // s.card = 3}) :
    (∑ x : Vector m, monomial s.val x * (eval (cubicComplement c) + h) x) = c s := by
  simp_rw [Pi.add_apply, mul_add]
  rw [Finset.sum_add_distrib, cubic_moment]
  have hz : (∑ x : Vector m, monomial s.val x * h x) = 0 :=
    sum_mul_reedMuller_eq_zero (monomial_mem_reedMuller s.val s.property.le) hh (by omega)
  rw [hz, add_zero]

theorem quadratic_correction_moment {m : ℕ} (hm : 4 ≤ m) (c : CubicCoefficients m)
    (h : BooleanFunction m) (hh : h ∈ reedMuller m (m - 4)) (s : Pair m) :
    (∑ x : Vector m, monomial s.val x * (eval (cubicComplement c) + h) x) = 0 := by
  apply sum_mul_reedMuller_eq_zero (monomial_mem_reedMuller s.val s.property.le)
    ((reedMuller m (m - 3)).add_mem (cubicComplement_mem c)
      (reedMuller_mono (by omega) hh))
  omega

theorem coordinate_quadratic_moment {m : ℕ} (hm : 4 ≤ m) (c : CubicCoefficients m)
    (h : BooleanFunction m) (hh : h ∈ reedMuller m (m - 4))
    (s : Pair m) (i : Fin m) :
    (∑ x : Vector m, x i * monomial s.val x * (eval (cubicComplement c) + h) x) =
      contractionEntry c s i := by
  simp_rw [← monomial_insert]
  by_cases hi : i ∈ s.val
  · simpa [Finset.insert_eq_of_mem hi, contractionEntry, hi] using
      quadratic_correction_moment hm c h hh s
  · have hc : (insert i s.val).card = 3 := by
      rw [Finset.card_insert_of_notMem hi, s.property]
    simpa [contractionEntry, hi] using
      cubic_correction_moment hm c h hh ⟨insert i s.val, hc⟩

theorem affine_quadratic_moment {m : ℕ} (hm : 4 ≤ m) (c : CubicCoefficients m)
    (h : BooleanFunction m) (hh : h ∈ reedMuller m (m - 4))
    (a : Field × Vector m) (s : Pair m) :
    (∑ x : Vector m, affineFunctionLinear m a x * monomial s.val x *
      (eval (cubicComplement c) + h) x) = coefficientContraction c a.2 s := by
  calc
    _ = a.1 * (∑ x : Vector m, monomial s.val x * (eval (cubicComplement c) + h) x) +
        ∑ i, a.2 i * (∑ x : Vector m,
          x i * monomial s.val x * (eval (cubicComplement c) + h) x) := by
      simp only [affineFunctionLinear_apply, add_mul, Finset.sum_mul,
        Finset.sum_add_distrib]
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum, mul_assoc]
    _ = _ := by
      rw [quadratic_correction_moment hm c h hh s]
      simp only [mul_zero, zero_add, coordinate_quadratic_moment hm c h hh,
        coefficientContraction_apply]

theorem affineSupport_injective {m : ℕ} (hm : 4 ≤ m) (c : CubicCoefficients m)
    (h : BooleanFunction m) (hh : h ∈ reedMuller m (m - 4))
    (hc : ∃ s, c s ≠ 0) (hinj : Function.Injective (coefficientContraction c)) :
    Function.Injective ((restrictSupport (eval (cubicComplement c) + h)).comp
      (affineFunctionLinear m)) := by
  apply LinearMap.ker_eq_bot.mp
  apply (Submodule.eq_bot_iff _).mpr
  intro a ha
  have hsupp : ∀ x : Support (eval (cubicComplement c) + h),
      affineFunctionLinear m a x = 0 := fun x => congrFun ha x
  have hpoint : ∀ x : Vector m,
      affineFunctionLinear m a x * (eval (cubicComplement c) + h) x = 0 := by
    intro x
    by_cases hx : (eval (cubicComplement c) + h) x = 0
    · simp [hx]
    · rw [hsupp ⟨x, hx⟩, zero_mul]
  have hcontract : coefficientContraction c a.2 = 0 := by
    ext s
    rw [← affine_quadratic_moment hm c h hh a s]
    apply Finset.sum_eq_zero
    intro x hx
    rw [mul_right_comm, hpoint x, zero_mul]
  have hlin : a.2 = 0 := hinj (by simpa using hcontract)
  have hex : ∃ x : Vector m, (eval (cubicComplement c) + h) x ≠ 0 := by
    by_contra hn
    push_neg at hn
    obtain ⟨s, hs⟩ := hc
    have hz := cubic_correction_moment hm c h hh s
    simp only [hn, mul_zero, Finset.sum_const_zero] at hz
    exact hs hz.symm
  obtain ⟨x, hx⟩ := hex
  have hconst : a.1 = 0 := by
    have hz := hpoint x
    have hev : affineFunctionLinear m a x = a.1 := by simp [affineFunctionLinear, hlin]
    rw [hev] at hz
    exact (mul_eq_zero.mp hz).resolve_right hx
  exact Prod.ext hconst hlin

theorem affineOnSupport_finrank_lower {m : ℕ} (hm : 4 ≤ m) (c : CubicCoefficients m)
    (h : BooleanFunction m) (hh : h ∈ reedMuller m (m - 4))
    (hc : ∃ s, c s ≠ 0) (hinj : Function.Injective (coefficientContraction c)) :
    m + 1 ≤ Module.finrank Field (affineOnSupport (eval (cubicComplement c) + h)) := by
  let g := eval (cubicComplement c) + h
  let e := (restrictSupport g).comp (affineFunctionLinear m)
  let e' := e.codRestrict (affineOnSupport g) fun a =>
    ⟨affineFunctionLinear m a, affineFunction_mem a, rfl⟩
  have he : Function.Injective e' := by
    intro a b hab
    apply affineSupport_injective hm c h hh hc hinj
    exact congrArg Subtype.val hab
  have hd := LinearMap.finrank_le_finrank_of_injective he
  simpa only [Module.finrank_prod, Module.finrank_self,
    Module.finrank_fintype_fun_eq_card, Fintype.card_fin, add_comm] using hd

theorem form9_affine_dimension_lower (h : BooleanFunction 9)
    (hh : h ∈ reedMuller 9 5) :
    10 ≤ Module.finrank Field (affineOnSupport (eval form9 + h)) := by
  apply affineOnSupport_finrank_lower (by decide) cubic9 h hh
  · exact ⟨⟨{0, 3, 6}, by decide⟩, by native_decide⟩
  · exact cubic9_contraction_injective

theorem form10_affine_dimension_lower (h : BooleanFunction 10)
    (hh : h ∈ reedMuller 10 6) :
    11 ≤ Module.finrank Field (affineOnSupport (eval form10 + h)) := by
  apply affineOnSupport_finrank_lower (by decide) cubic10 h hh
  · exact ⟨⟨{0, 3, 6}, by decide⟩, by native_decide⟩
  · exact cubic10_contraction_injective

theorem form11_affine_dimension_lower (h : BooleanFunction 11)
    (hh : h ∈ reedMuller 11 7) :
    12 ≤ Module.finrank Field (affineOnSupport (eval form11 + h)) := by
  apply affineOnSupport_finrank_lower (by decide) cubic11 h hh
  · exact ⟨⟨{0, 3, 6}, by decide⟩, by native_decide⟩
  · exact cubic11_contraction_injective

theorem cocubic_weight_reduction {m : ℕ} (hm : 4 ≤ m) (c : CubicCoefficients m)
    (h : BooleanFunction m) (hh : h ∈ reedMuller m (m - 4))
    (hc : ∃ s, c s ≠ 0) (hinj : Function.Injective (coefficientContraction c)) :
    2 * (m + 1) + Module.finrank Field (LinearMap.range
      (supportGram (eval (cubicComplement c) + h)
        (admissibleQuadratics (eval (cubicComplement c))).subtype)) ≤
      weight (eval (cubicComplement c) + h) := by
  have hdim := affineOnSupport_finrank_lower hm c h hh hc hinj
  have hweight := admissibleQuadratics_weight_bound hm
    (eval (cubicComplement c)) h (cubicComplement_mem c) hh
  omega

end Lemmata.CocubicCovering.Covering
