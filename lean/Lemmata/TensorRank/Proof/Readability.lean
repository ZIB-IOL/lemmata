module

public import Lemmata.TensorRank.Def.Readability
public import Lemmata.TensorRank.Proof.Separation

@[expose] public section

set_option autoImplicit false

open scoped BigOperators
open Classical

noncomputable section

namespace Lemmata.TensorRank.Tensor

variable {R I : Type*} [CommSemiring R] [Fintype I]
variable {V W U : I → Type*} [∀ i, Fintype (V i)]

theorem localMap_constants (A : ∀ i, W i → V i → R) (T : Tensor R I V) :
    (fun y => Polynomial.C (localMap A T y)) =
      localMap (fun i y x => Polynomial.C (A i y x)) (fun x => Polynomial.C (T x)) := by
  funext y
  simp only [localMap, map_sum, map_mul, map_prod]

theorem coefficient_constantMap (A : ∀ i, W i → V i → R)
    (P : Tensor (Polynomial R) I V) (e : ℕ) :
    coefficient (localMap (fun i y x => Polynomial.C (A i y x)) P) e =
      localMap A (coefficient P e) := by
  funext y
  simp only [coefficient, localMap, Polynomial.finsetSum_coeff]
  simp_rw [← map_prod (Polynomial.C : R →+* Polynomial R), Polynomial.coeff_C_mul]

theorem Leading.constantMap {P : Tensor (Polynomial R) I V} {e : ℕ} {T : Tensor R I V}
    (h : Leading P e T) (A : ∀ i, W i → V i → R) :
    Leading (localMap (fun i y x => Polynomial.C (A i y x)) P) e (localMap A T) := by
  constructor
  · rw [coefficient_constantMap, h.1]
  · intro j hj
    rw [coefficient_constantMap, h.2 j hj, localMap_zero]

theorem Restricts.copies {S : Tensor R I W} {T : Tensor R I V}
    (h : Restricts S T) (l : ℕ) : Restricts (copies l S) (copies l T) :=
  (Restricts.refl (diagonal (R := R) (I := I) l)).product h

variable [∀ i, Fintype (W i)]

theorem Degenerates.restricts_right {S : Tensor R I U} {T : Tensor R I W}
    {Q : Tensor R I V} (h : Degenerates S T) (hT : Restricts T Q) : Degenerates S Q := by
  obtain ⟨A, e, h⟩ := h
  obtain ⟨B, rfl⟩ := hT
  refine ⟨fun i y x => ∑ w, A i y w * Polynomial.C (B i w x), e, ?_⟩
  simpa only [polynomialMap, localMap_constants, localMap_comp] using h

theorem Degenerates.restricts_left {S : Tensor R I U} {T : Tensor R I W}
    {Q : Tensor R I V} (h : Degenerates T Q) (hS : Restricts S T) : Degenerates S Q := by
  obtain ⟨A, e, h⟩ := h
  obtain ⟨B, rfl⟩ := hS
  refine ⟨fun i y x => ∑ w, Polynomial.C (B i y w) * A i w x, e, ?_⟩
  simpa only [polynomialMap, localMap_comp] using h.constantMap B

end Lemmata.TensorRank.Tensor

namespace Lemmata.TensorRank.Separation

universe u

variable {r M : ℕ} {V : Party r → Type u}

def sharedInput (p : Party r) (y : SharedCoordinate V M p) : V p :=
  match p with
  | .inl _ => y.2
  | .inr _ => y

def readerMask (left : V (.inl false) → Fin M) (right : V (.inl true) → Fin M)
    (p : Party r) (y : SharedCoordinate V M p) : ℂ :=
  match p with
  | .inl false => if left y.2 = y.1 then 1 else 0
  | .inl true => if right y.2 = y.1 then 1 else 0
  | .inr _ => 1

def readerKernel (left : V (.inl false) → Fin M) (right : V (.inl true) → Fin M)
    (p : Party r) (y : SharedCoordinate V M p) (v : V p) : ℂ :=
  readerMask left right p y * if v = sharedInput p y then 1 else 0

private theorem selected_map {R P : Type*} [CommSemiring R] [Fintype P]
    {V W : P → Type*} [∀ p, Fintype (V p)] (T : Tensor R P V)
    (f : ∀ p, W p → V p) (a : ∀ p, W p → R) (y : ∀ p, W p) :
    Tensor.localMap (fun p y x => a p y * if x = f p y then 1 else 0) T y =
      (∏ p, a p (y p)) * T (fun p => f p (y p)) := by
  have hs := congrFun (Tensor.localMap_select f T) y
  simp only [Tensor.localMap, Tensor.reindex] at hs
  simp only [Tensor.localMap, Finset.prod_mul_distrib]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, hs]

theorem readerMap_value [∀ p, Fintype (V p)]
    (left : V (.inl false) → Fin M) (right : V (.inl true) → Fin M)
    (T : Tensor ℂ (Party r) V) (x : ∀ p, SharedCoordinate V M p) :
    Tensor.localMap (readerKernel left right) T x =
      ((if left (x (.inl false)).2 = (x (.inl false)).1 then 1 else 0) *
        (if right (x (.inl true)).2 = (x (.inl true)).1 then 1 else 0)) * T (sharedBase x) := by
  change Tensor.localMap (fun p y v => readerMask left right p y *
    if v = sharedInput p y then 1 else 0) T x = _
  rw [selected_map]
  have hb : (fun p => sharedInput p (x p)) = sharedBase x := by
    funext p
    cases p <;> rfl
  rw [hb]
  simp only [Fintype.prod_sum_type, Fintype.prod_bool, readerMask, Finset.prod_const_one,
    mul_one]
  ring

theorem readerMap_sum [∀ p, Fintype (V p)]
    (Z : Fin M → Tensor ℂ (Party r) V)
    {left : V (.inl false) → Fin M} {right : V (.inl true) → Fin M}
    (hleft : Tensor.Reads Z (.inl false) left) (hright : Tensor.Reads Z (.inl true) right) :
    Tensor.localMap (readerKernel left right) (∑ q, Z q) = sharedSum Z := by
  funext x
  rw [readerMap_value]
  simp only [Finset.sum_apply, Finset.mul_sum]
  have ht (q : Fin M) :
      ((if left (x (.inl false)).2 = (x (.inl false)).1 then 1 else 0) *
        (if right (x (.inl true)).2 = (x (.inl true)).1 then 1 else 0)) * Z q (sharedBase x) =
      if (x (.inl false)).1 = q ∧ (x (.inl true)).1 = q then Z q (sharedBase x) else 0 := by
    by_cases hz : Z q (sharedBase x) = 0
    · simp [hz]
    · have hl := hleft q (sharedBase x) hz
      have hr := hright q (sharedBase x) hz
      change left (x (.inl false)).2 = q at hl
      change right (x (.inl true)).2 = q at hr
      rw [hl, hr]
      by_cases ha : q = (x (.inl false)).1
      · by_cases hb : q = (x (.inl true)).1
        · rw [ite_eq_left ha, ite_eq_left hb, ite_eq_left ⟨ha.symm, hb.symm⟩]
          simp
        · rw [ite_eq_left ha, ite_eq_right hb, ite_eq_right (fun h => hb h.2.symm)]
          simp
      · by_cases hb : q = (x (.inl true)).1
        · rw [ite_eq_right ha, ite_eq_left hb, ite_eq_right (fun h => ha h.1.symm)]
          simp
        · rw [ite_eq_right ha, ite_eq_right hb, ite_eq_right (fun h => ha h.1.symm)]
          simp
  simp_rw [ht]
  change (∑ q : Fin M, if (x (.inl false)).1 = q ∧ (x (.inl true)).1 = q then
    Z q (sharedBase x) else 0) = _
  by_cases hh : (x (.inl false)).1 = (x (.inl true)).1
  · simp [sharedSum, hh]
  · rw [sharedSum, ite_eq_right hh]
    apply Finset.sum_eq_zero
    intro q _
    have hn : ¬ ((x (.inl false)).1 = q ∧ (x (.inl true)).1 = q) :=
      fun h => hh (h.1.trans h.2.symm)
    exact ite_eq_right hn

theorem sharedSum_restricts_sum [∀ p, Fintype (V p)]
    (Z : Fin M → Tensor ℂ (Party r) V)
    {left : V (.inl false) → Fin M} {right : V (.inl true) → Fin M}
    (hleft : Tensor.Reads Z (.inl false) left) (hright : Tensor.Reads Z (.inl true) right) :
    Tensor.Restricts (sharedSum Z) (∑ q, Z q) :=
  ⟨readerKernel left right, (readerMap_sum Z hleft hright).symm⟩

theorem separated_degenerates_sum [∀ p, Fintype (V p)] (hM : 0 < M)
    (Z : Fin M → Tensor ℂ (Party r) V)
    {left : V (.inl false) → Fin M} {right : V (.inl true) → Fin M}
    (hleft : Tensor.Reads Z (.inl false) left) (hright : Tensor.Reads Z (.inl true) right) :
    Tensor.Degenerates (separatedSum Z) (Tensor.copies (period r M) (∑ q, Z q)) :=
  (separated_degenerates hM Z).restricts_right ((sharedSum_restricts_sum Z hleft hright).copies _)

theorem separated_asymptoticRank_sum_le [∀ p, Fintype (V p)] (hM : 0 < M)
    (Z : Fin M → Tensor ℂ (Party r) V)
    {left : V (.inl false) → Fin M} {right : V (.inl true) → Fin M}
    (hleft : Tensor.Reads Z (.inl false) left) (hright : Tensor.Reads Z (.inl true) right) :
    Tensor.asymptoticRank (separatedSum Z) ≤
      (period r M : ℝ) * Tensor.asymptoticRank (∑ q, Z q) := by
  exact (separated_degenerates_sum hM Z hleft hright).asymptoticRank_le.trans
    (Tensor.asymptoticRank_copies_le _ _)

end Lemmata.TensorRank.Separation
