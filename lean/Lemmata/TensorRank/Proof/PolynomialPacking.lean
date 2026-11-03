module

/-
Copyright (c) 2026 Kirill Khoruzhii. Licensed under Apache-2.0.
Modified for the arbitrary-field tensor-rank formalization; namespace and imports
adapted for Lemmata. See docs/tensor-rank/NOTICE.txt for upstream attribution
and modification notices, and docs/tensor-rank/LICENSE.txt for the license.
-/

public import Lemmata.TensorRank.Def.PolynomialPacking
public import Lemmata.TensorRank.Proof.PolynomialReaders
public import Lemmata.TensorRank.Proof.Parties
public import Mathlib.Logic.Equiv.Bool

@[expose] public section

set_option autoImplicit false

open scoped BigOperators
open Classical

noncomputable section

namespace Lemmata.TensorRank.PolynomialProduct.Packing

variable {𝕜 : Type*} [Field 𝕜] {J : Type*} [Fintype J]

theorem sector_reads_input (a : J → ℕ) (b c : ℕ) :
    Tensor.Reads (sector (𝕜 := 𝕜) a b c) (.inl false) (inputLabel a b c) := by
  intro q x hx
  by_contra h
  exact hx (by simp [sector, h])

theorem sector_reads_output (a : J → ℕ) (b c : ℕ) :
    Tensor.Reads (sector (𝕜 := 𝕜) a b c) (.inl true) (outputLabel a b c) := by
  intro q x hx
  by_contra h
  exact hx (by simp [sector, h])

theorem sum_sector (a : J → ℕ) (b c : ℕ) :
    (∑ q, sector (𝕜 := 𝕜) a b c q) = target (𝕜 := 𝕜) a b c := by
  funext x
  cases hy : x (.inl false) with
  | inl y =>
    cases hz : x (.inl true) with
    | inl z =>
      by_cases h : y.1 = z.1 <;> simp [sector, inputLabel, outputLabel, target, hy, hz, h]
    | inr z => simp [sector, inputLabel, outputLabel, target, hy, hz]
  | inr y =>
    cases hz : x (.inl true) <;> simp [sector, inputLabel, outputLabel, target, hy, hz]

def normalEmbedding (a : J → ℕ) (b c : ℕ) (l : Fin (c + 1)) (p : Bool ⊕ J) :
    SelectedCoordinate a b p → Coordinate a b c p :=
  match p with
  | .inl false => fun y => .inl (l, y)
  | .inl true => fun z => .inl (l, Fin.cast (by unfold length; omega) z)
  | .inr _ => id

theorem normal_restricts (a : J → ℕ) (b c : ℕ) (l : Fin (c + 1)) :
    Tensor.Restricts (selected (𝕜 := 𝕜) a b) (sector (𝕜 := 𝕜) a b c (some l)) := by
  refine ⟨fun p y v => if v = normalEmbedding a b c l p y then 1 else 0, ?_⟩
  rw [Tensor.localMap_select]
  funext x
  simp [Tensor.reindex, sector, inputLabel, outputLabel, target, normalEmbedding, selected]

abbrev swapReaders : (Bool ⊕ J) ≃ (Bool ⊕ J) := Equiv.sumCongr Equiv.boolNot (Equiv.refl J)

def middleEmbedding (a : J → ℕ) (b c : ℕ) (p : Bool ⊕ J) :
    SelectedCoordinate a b (swapReaders p) → Coordinate a b c p :=
  match p with
  | .inl false => fun y => .inr (Fin.cast (by unfold length; omega) y)
  | .inl true => Sum.inr
  | .inr _ => Fin.rev

theorem sum_reverse (a : J → ℕ) (x : ∀ j, Fin (a j)) :
    (∑ j, (Fin.rev (x j)).val) + (∑ j, (x j).val) = degree a := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  change (a j - (x j).val - 1) + (x j).val = a j - 1
  have := (x j).isLt
  omega

theorem middle_restricts (a : J → ℕ) (b c : ℕ) :
    Tensor.Restricts (Tensor.relabel swapReaders (selected (𝕜 := 𝕜) a b))
      (sector (𝕜 := 𝕜) a b c none) := by
  refine ⟨fun p y v => if v = middleEmbedding a b c p y then 1 else 0, ?_⟩
  rw [Tensor.localMap_select]
  funext x
  have hs := sum_reverse a (fun j => x (.inr j))
  simp only [Tensor.reindex, sector, inputLabel, outputLabel, middleEmbedding,
    and_self, ite_true, target, selected, Tensor.relabel, Equiv.piCongrLeft_apply]
  congr 1
  change ((x (.inl true)).val + (∑ j, (x (.inr j)).val) = (x (.inl false)).val) =
    ((x (.inl false)).val + (∑ j, (Fin.rev (x (.inr j))).val) =
      degree a + (x (.inl true)).val)
  apply propext
  dsimp only [Fin.rev, Equiv.refl_apply] at hs ⊢
  omega

def sourceOutput (a : J → ℕ) (b c : ℕ) (u : Fin (b + 1) × Fin c)
    (x : ∀ j, Fin (a j)) : Fin (b + 1 + degree a) × Fin c :=
  (⟨u.1.val + ∑ j, (x j).val, by
      have := input_sum_le a x
      have := u.1.isLt
      omega⟩, u.2)

theorem source_value (a : J → ℕ) (b c : ℕ) (u : Fin (b + 1) × Fin c)
    (v : Fin (b + 1 + degree a) × Fin c) (x : ∀ j, Fin (a j)) :
    source (𝕜 := 𝕜) a b c (assemble u v (fun j => (x j, PUnit.unit))) =
      if v = sourceOutput a b c u x then 1 else 0 := by
  have he : u.1.val + (∑ j, (x j).val) = v.1.val ↔ v.1 = (sourceOutput a b c u x).1 := by
    exact ⟨fun h => Fin.ext h.symm, fun h => by rw [h]; rfl⟩
  change ((if u.1.val + (∑ j, (x j).val) = v.1.val then (1 : 𝕜) else 0) *
    (if u.2 = v.2 then 1 else 0)) = if v = sourceOutput a b c u x then 1 else 0
  simp only [he]
  have hpoint : v = sourceOutput a b c u x ↔ v.1 = (sourceOutput a b c u x).1 ∧ v.2 = u.2 := by
    rw [Prod.ext_iff]
    rfl
  simp only [hpoint]
  by_cases h₁ : v.1 = (sourceOutput a b c u x).1 <;> by_cases h₂ : v.2 = u.2 <;>
    simp [h₁, h₂, eq_comm] <;> exact Ne.symm h₂

theorem polynomialMap_value (a : J → ℕ) (b c : ℕ) (hc : count a b ≤ c)
    (x : ∀ p, Coordinate a b c p) :
    Tensor.polynomialMap (kernel (𝕜 := 𝕜) a b c hc) (source (𝕜 := 𝕜) a b c) x =
      ∑ u : Fin (b + 1) × Fin c, encode (𝕜 := 𝕜) a b c hc (x (.inl false)) u *
        decode (𝕜 := 𝕜) a b c (x (.inl true)) (sourceOutput a b c u (fun j => x (.inr j))) := by
  rw [Tensor.polynomialMap]
  have hk : kernel (𝕜 := 𝕜) a b c hc = twoReaderKernel (encode a b c hc) (decode a b c)
      (fun _ y => (y, PUnit.unit)) := by
    funext p
    rcases p with ⟨⟨⟩⟩ | j <;> funext y v <;> simp only [kernel, twoReaderKernel] <;>
      split_ifs <;> rfl
  rw [hk]
  rw [localMap_twoReaders]
  apply Finset.sum_congr rfl
  intro u _
  simp_rw [source_value]
  simp

theorem polynomialMap_split (a : J → ℕ) (b c : ℕ) (hc : count a b ≤ c)
    (x : ∀ p, Coordinate a b c p) :
    Tensor.polynomialMap (kernel (𝕜 := 𝕜) a b c hc) (source (𝕜 := 𝕜) a b c) x =
      match x (.inl false) with
      | .inl y =>
          (if h : y.1.val < c then decode a b c (x (.inl true))
            (sourceOutput a b c (positiveSource a b c y.1 y.2 h) (fun j => x (.inr j))) else 0) -
          (if h : 0 < y.1.val then decode a b c (x (.inl true))
            (sourceOutput a b c (negativeSource a b c y.1 y.2 h) (fun j => x (.inr j))) else 0)
      | .inr y => Polynomial.X * decode a b c (x (.inl true))
          (sourceOutput a b c (middleSource a b c y hc) (fun j => x (.inr j))) := by
  rw [polynomialMap_value a b c hc]
  cases hy : x (.inl false) with
  | inl y =>
    by_cases hp : y.1.val < c <;> by_cases hn : 0 < y.1.val <;>
      simp [encode, hp, hn, sub_mul, Finset.sum_sub_distrib]
  | inr y =>
    simp only [encode, mul_assoc]
    rw [← Finset.mul_sum]
    simp

private def scalarWeight (q k h j z : ℕ) : 𝕜 :=
  if k + h < q then
    if k ≤ j ∧ j + z = k + h then 1 else 0
  else -(if j < k ∧ j + z = k + h then 1 else 0)

private theorem scalarWeight_difference (s b c l p k h I : ℕ) (hc : s + 2 * b ≤ c)
    (hl : l ≤ c) (hp : p < b) (hk : k ≤ c)
    (hh : h < s + b) (hI : I ≤ s) :
    (if l < c then scalarWeight (𝕜 := 𝕜) (s + b) k h l (p + I) else 0) -
      (if 0 < l then scalarWeight (𝕜 := 𝕜) (s + b) k h (l - 1) (p + 1 + I) else 0) =
        if l = k ∧ p + I = h then 1 else 0 := by
  unfold scalarWeight
  split_ifs <;> simp_all <;> omega

private theorem middle_difference (s b c l p z I : ℕ) (hc : s + 2 * b ≤ c)
    (hl : l ≤ c) (hp : p < b) (hz : z < b) (hI : I ≤ s) :
    (if l < c then (if l + (p + I) = s + b + z then (1 : Polynomial 𝕜) else 0) else 0) -
      (if 0 < l then (if (l - 1) + (p + 1 + I) = s + b + z then 1 else 0) else 0) = 0 := by
  split_ifs <;> simp_all <;> omega

set_option backward.isDefEq.respectTransparency false in
theorem normal_weight (a : J → ℕ) (b c : ℕ) (hc : count a b ≤ c) (y : Fin (c + 1) × Fin b)
    (z : Fin (c + 1) × Fin (length a b)) (x : ∀ j, Fin (a j)) :
    (if h : y.1.val < c then fullWeight (𝕜 := 𝕜) a b c z
      (sourceOutput a b c (positiveSource a b c y.1 y.2 h) x) else 0) -
    (if h : 0 < y.1.val then fullWeight (𝕜 := 𝕜) a b c z
      (sourceOutput a b c (negativeSource a b c y.1 y.2 h) x) else 0) =
      if y.1 = z.1 ∧ y.2.val + (∑ j, (x j).val) = z.2.val then 1 else 0 := by
  have hh := scalarWeight_difference (𝕜 := 𝕜) (degree a) b c y.1.val y.2.val z.1.val z.2.val
    (∑ j, (x j).val) hc (Nat.lt_succ_iff.mp y.1.isLt) y.2.isLt
    (Nat.lt_succ_iff.mp z.1.isLt) z.2.isLt (input_sum_le a x)
  by_cases hp : y.1.val < c <;> by_cases hn : 0 < y.1.val <;>
    simp only [hp, hn, dite_true, dite_false] <;>
    simpa only [fullWeight, scalarWeight, sourceOutput, positiveSource, negativeSource,
      length, Fin.ext_iff, hp, hn, dite_true, dite_false, ite_true, ite_false] using hh

set_option backward.isDefEq.respectTransparency false in
theorem normal_middle (a : J → ℕ) (b c : ℕ) (hc : count a b ≤ c) (y : Fin (c + 1) × Fin b)
    (z : Fin b) (x : ∀ j, Fin (a j)) :
    (if h : y.1.val < c then decode (𝕜 := 𝕜) a b c (.inr z)
      (sourceOutput a b c (positiveSource a b c y.1 y.2 h) x) else 0) -
    (if h : 0 < y.1.val then decode (𝕜 := 𝕜) a b c (.inr z)
      (sourceOutput a b c (negativeSource a b c y.1 y.2 h) x) else 0) = 0 := by
  have hh := middle_difference (𝕜 := 𝕜) (degree a) b c y.1.val y.2.val z.val
    (∑ j, (x j).val) hc (Nat.lt_succ_iff.mp y.1.isLt) y.2.isLt z.isLt (input_sum_le a x)
  by_cases hp : y.1.val < c <;> by_cases hn : 0 < y.1.val <;>
    simp only [hp, hn, dite_true, dite_false] <;>
    simpa only [decode, sourceOutput, positiveSource, negativeSource, length,
      hp, hn, dite_true, dite_false, ite_true, ite_false] using hh

theorem normal_full (a : J → ℕ) (b c : ℕ) (hc : count a b ≤ c) (y : Fin (c + 1) × Fin b)
    (z : Fin (c + 1) × Fin (length a b)) (x : ∀ j, Fin (a j)) :
    (if h : y.1.val < c then decode (𝕜 := 𝕜) a b c (.inl z)
      (sourceOutput a b c (positiveSource a b c y.1 y.2 h) x) else 0) -
    (if h : 0 < y.1.val then decode (𝕜 := 𝕜) a b c (.inl z)
      (sourceOutput a b c (negativeSource a b c y.1 y.2 h) x) else 0) =
      Polynomial.X * Polynomial.C
        (if y.1 = z.1 ∧ y.2.val + (∑ j, (x j).val) = z.2.val then (1 : 𝕜) else 0) := by
  calc
    _ = (Polynomial.X : Polynomial 𝕜) * Polynomial.C
        ((if h : y.1.val < c then fullWeight (𝕜 := 𝕜) a b c z
          (sourceOutput a b c (positiveSource a b c y.1 y.2 h) x) else 0) -
        (if h : 0 < y.1.val then fullWeight (𝕜 := 𝕜) a b c z
          (sourceOutput a b c (negativeSource a b c y.1 y.2 h) x) else 0)) := by
      by_cases hp : y.1.val < c <;> by_cases hn : 0 < y.1.val <;>
        simp [decode, hp, hn, map_sub, mul_sub]
    _ = _ := congrArg (fun w : 𝕜 => (Polynomial.X : Polynomial 𝕜) * Polynomial.C w)
      (normal_weight a b c hc y z x)

theorem leading (a : J → ℕ) (b c : ℕ) (hc : count a b ≤ c) :
    Tensor.Leading (Tensor.polynomialMap (kernel (𝕜 := 𝕜) a b c hc) (source (𝕜 := 𝕜) a b c)) 1
      (target (𝕜 := 𝕜) a b c) := by
  have he (n : ℕ) (hn : n ≤ 1) (x : ∀ p, Coordinate a b c p) :
      (Tensor.polynomialMap (kernel (𝕜 := 𝕜) a b c hc) (source (𝕜 := 𝕜) a b c) x).coeff n =
        if n = 1 then target (𝕜 := 𝕜) a b c x else 0 := by
    rw [polynomialMap_split a b c hc]
    cases hy : x (.inl false) with
    | inl y =>
      cases hz : x (.inl true) with
      | inl z =>
        dsimp only
        rw [normal_full a b c hc]
        split_ifs <;> simp_all [target, hy, hz, Polynomial.coeff_X, eq_comm]
      | inr z =>
        dsimp only
        rw [normal_middle a b c hc]
        simp [target, hy, hz]
    | inr y =>
      cases hz : x (.inl true) with
      | inl z =>
        dsimp only
        have hn2 : ¬ 2 ≤ n := by omega
        simp only [decode, target, hy, hz, ite_self]
        rw [← mul_assoc, ← pow_two, Polynomial.coeff_X_pow_mul']
        simp [hn2]
      | inr z =>
        dsimp only
        have heq : (sourceOutput a b c (middleSource a b c y hc) (fun j => x (.inr j))).2.val +
            (sourceOutput a b c (middleSource a b c y hc) (fun j => x (.inr j))).1.val = length a b + z.val ↔
            y.val + (∑ j, (x (.inr j)).val) = degree a + z.val := by
          simp only [middleSource, sourceOutput]
          unfold length
          omega
        simp only [decode, heq]
        split_ifs <;> simp_all [target, hy, hz, Polynomial.coeff_X, eq_comm]
  constructor
  · funext x
    exact (he 1 le_rfl x).trans (ite_eq_left rfl)
  · intro n hn
    funext x
    exact (he n (by omega) x).trans (ite_eq_right (by omega))

theorem target_degenerates (a : J → ℕ) (b c : ℕ) (hc : count a b ≤ c) :
    Tensor.Degenerates (target (𝕜 := 𝕜) a b c) (source (𝕜 := 𝕜) a b c) :=
  ⟨kernel a b c hc, 1, leading a b c hc⟩

end Lemmata.TensorRank.PolynomialProduct.Packing
