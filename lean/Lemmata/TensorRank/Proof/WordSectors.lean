module

public import Lemmata.TensorRank.Proof.Types
public import Lemmata.TensorRank.Proof.IndexedProduct
public import Lemmata.TensorRank.Proof.Readability

@[expose] public section

set_option autoImplicit false

open scoped BigOperators
open Classical

noncomputable section

namespace Lemmata.TensorRank.Tensor

variable {R I C : Type*} [CommSemiring R] {V : I → Type*} {N : ℕ}

def wordTensor (Z : C → Tensor R I V) (w : Fin N → C) :
    Tensor R I (fun i => Fin N → V i) := indexedProduct (fun j => Z (w j))

variable [Fintype C]

theorem power_sum_words (Z : C → Tensor R I V) (N : ℕ) :
    power (∑ c, Z c) N = ∑ w : Fin N → C, wordTensor Z w := by
  funext x
  simp only [power, wordTensor, indexedProduct, Finset.sum_apply]
  exact Fintype.prod_sum _

def typeSector (Z : C → Tensor R I V) (h : C → Fin (N + 1)) :
    Tensor R I (fun i => Fin N → V i) := ∑ w : Types.Words h, wordTensor Z w.val

theorem power_sum_types (Z : C → Tensor R I V) (N : ℕ) :
    power (∑ c, Z c) N = ∑ h : C → Fin (N + 1), typeSector Z h := by
  rw [power_sum_words]
  exact (Fintype.sum_fiberwise Types.histogram (wordTensor Z)).symm

theorem typeSector_eq_filter (Z : C → Tensor R I V) (h : C → Fin (N + 1)) :
    typeSector Z h = ∑ w : Fin N → C,
      if Types.histogram w = h then wordTensor Z w else 0 := by
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype _ (by simp) (wordTensor Z)).symm

def wordCoordinate {w z : Fin N → C} (h : Types.histogram w = Types.histogram z) (i : I) :
    (Fin N → V i) ≃ (Fin N → V i) :=
  Equiv.arrowCongr (Types.wordEquiv h) (Equiv.refl _)

omit [Fintype C] in
theorem wordTensor_reindex (Z : C → Tensor R I V) {w z : Fin N → C}
    (h : Types.histogram w = Types.histogram z) :
    reindex (fun i => wordCoordinate h i) (wordTensor Z z) = wordTensor Z w := by
  funext x
  change (∏ j, Z (z j) (fun i => x i ((Types.wordEquiv h).symm j))) = _
  rw [← Equiv.prod_comp (Types.wordEquiv h)
    (fun j => Z (z j) (fun i => x i ((Types.wordEquiv h).symm j)))]
  simp only [Equiv.symm_apply_apply, Types.wordEquiv_map]
  rfl

omit [Fintype C] in
theorem Reads.wordTensor {Z : C → Tensor R I V} {reader : I} {label : V reader → C}
    (h : Reads Z reader label) (N : ℕ) :
    Reads (wordTensor Z (N := N)) reader (fun x j => label (x j)) := by
  intro w x hx
  funext j
  apply h (w j) (fun i => x i j)
  intro hz
  exact hx (Finset.prod_eq_zero (Finset.mem_univ j) hz)

theorem typeSector_eq_mask (Z : C → Tensor R I V) {reader : I} {label : V reader → C}
    (hr : Reads Z reader label) (h : C → Fin (N + 1)) :
    typeSector Z h = fun x =>
      if Types.histogram (fun j => label (x reader j)) = h then power (∑ c, Z c) N x else 0 := by
  rw [typeSector_eq_filter, power_sum_words]
  funext x
  simp only [Finset.sum_apply, ite_apply, Pi.zero_apply]
  by_cases hp : Types.histogram (fun j => label (x reader j)) = h
  · rw [ite_eq_left hp]
    apply Finset.sum_congr rfl
    intro w _
    by_cases hz : wordTensor Z w x = 0
    · simp [hz]
    · have hw := hr.wordTensor N w x hz
      change (fun j => label (x reader j)) = w at hw
      have hh : Types.histogram w = h := by rw [← hw]; exact hp
      exact ite_eq_left hh
  · rw [ite_eq_right hp]
    apply Finset.sum_eq_zero
    intro w _
    by_cases hz : wordTensor Z w x = 0
    · simp [hz]
    · have hw := hr.wordTensor N w x hz
      change (fun j => label (x reader j)) = w at hw
      have hh : ¬ Types.histogram w = h := by
        intro hh
        apply hp
        rw [hw]
        exact hh
      exact ite_eq_right hh

variable [Fintype I] [∀ i, Fintype (V i)]

omit [Fintype C] in
theorem rank_wordTensor_eq (Z : C → Tensor R I V) {w z : Fin N → C}
    (h : Types.histogram w = Types.histogram z) : rank (wordTensor Z w) = rank (wordTensor Z z) := by
  rw [← wordTensor_reindex Z h, rank_reindex]

omit [Fintype C] in
theorem asymptoticRank_wordTensor_eq (Z : C → Tensor R I V) {w z : Fin N → C}
    (h : Types.histogram w = Types.histogram z) :
    asymptoticRank (wordTensor Z w) = asymptoticRank (wordTensor Z z) := by
  rw [← wordTensor_reindex Z h, asymptoticRank_reindex]

omit [Fintype C] in
theorem wordTensor_restricts_wordTensor (Z : C → Tensor R I V) {w z : Fin N → C}
    (h : Types.histogram w = Types.histogram z) : Restricts (wordTensor Z w) (wordTensor Z z) := by
  rw [← wordTensor_reindex Z h]
  exact reindex_restricts _ _

theorem coordinateFilter_restricts (T : Tensor R I V) (reader : I)
    (P : V reader → Prop) [DecidablePred P] :
    Restricts (fun x => if P (x reader) then T x else 0) T := by
  let a (i : I) (y : V i) : R :=
    if h : i = reader then (if P (h ▸ y) then 1 else 0) else 1
  let A (i : I) (y x : V i) : R := a i y * if x = y then 1 else 0
  refine ⟨A, ?_⟩
  funext y
  have ha : (∏ i, a i (y i)) = if P (y reader) then 1 else 0 := by
    calc
      _ = a reader (y reader) := Finset.prod_eq_single_of_mem reader (Finset.mem_univ _)
        (fun i _ hi => by simp [a, hi])
      _ = _ := by simp [a]
  have hs := congrFun (localMap_select (fun _ => id) T) y
  change (∑ x, (∏ i, if x i = y i then 1 else 0) * T x) = T y at hs
  change _ = ∑ x, (∏ i, a i (y i) * if x i = y i then 1 else 0) * T x
  simp only [Finset.prod_mul_distrib]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, hs, ha]
  split_ifs <;> simp

theorem typeSector_restricts_power (Z : C → Tensor R I V)
    {reader : I} {label : V reader → C} (hr : Reads Z reader label)
    (h : C → Fin (N + 1)) : Restricts (typeSector Z h) (power (∑ c, Z c) N) := by
  rw [typeSector_eq_mask Z hr h]
  exact coordinateFilter_restricts (power (∑ c, Z c) N) reader
    (fun (y : Fin N → V reader) => Types.histogram (fun j => label (y j)) = h)

end Lemmata.TensorRank.Tensor
