module

public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public section

namespace Lemmata.Centroid.Linear

open Classical

noncomputable section

variable {F I : Type*} [Field F] [Fintype I] [LinearOrder I]

def IsLeading (S : Submodule F (I → F)) (i : I) : Prop :=
  ∃ v ∈ S, v i ≠ 0 ∧ ∀ j < i, v j = 0

def leadingPositions (S : Submodule F (I → F)) : Finset I :=
  Finset.univ.filter (IsLeading S)

omit [Fintype I] in theorem IsLeading.mono {S T : Submodule F (I → F)} (hST : S ≤ T) {i : I}
    (hi : IsLeading S i) : IsLeading T i := by
  obtain ⟨v, hv, hvi, hzero⟩ := hi
  exact ⟨v, hST hv, hvi, hzero⟩

@[simp] theorem mem_leadingPositions (S : Submodule F (I → F)) (i : I) :
    i ∈ leadingPositions S ↔ IsLeading S i := by simp [leadingPositions]

theorem exists_leading_of_ne_zero {v : I → F} (hv : v ≠ 0) :
    ∃ i, v i ≠ 0 ∧ ∀ j < i, v j = 0 := by
  have hex : ∃ i, v i ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext h)
  let s := Finset.univ.filter (fun i => v i ≠ 0)
  have hs : s.Nonempty := by
    obtain ⟨i, hi⟩ := hex
    exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩⟩
  refine ⟨s.min' hs, (Finset.mem_filter.1 (Finset.min'_mem s hs)).2, ?_⟩
  intro j hj
  by_contra hjv
  have hmem : j ∈ s := Finset.mem_filter.2 ⟨Finset.mem_univ _, hjv⟩
  exact (not_lt_of_ge (Finset.min'_le s j hmem)) hj

def leadingRestriction (S : Submodule F (I → F)) : S →ₗ[F] (leadingPositions S → F) where
  toFun v i := v.val i.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem leadingRestriction_injective (S : Submodule F (I → F)) :
    Function.Injective (leadingRestriction S) := by
  intro v w h
  have heq : v.val - w.val = 0 := by
    by_contra hne
    obtain ⟨i, hi, hzero⟩ := exists_leading_of_ne_zero hne
    have himem : i ∈ leadingPositions S :=
      (mem_leadingPositions S i).2 ⟨v.val - w.val, S.sub_mem v.property w.property, hi, hzero⟩
    have hvw := congrFun h ⟨i, himem⟩
    exact hi (sub_eq_zero.2 hvw)
  exact Subtype.ext (sub_eq_zero.1 heq)

theorem finrank_le_card_leadingPositions (S : Submodule F (I → F)) :
    Module.finrank F S ≤ (leadingPositions S).card := by
  have h := LinearMap.finrank_le_finrank_of_injective (leadingRestriction_injective S)
  simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] using h

theorem card_leadingPositions_le_finrank (S : Submodule F (I → F)) :
    (leadingPositions S).card ≤ Module.finrank F S := by
  let v : leadingPositions S → S := fun i =>
    ⟨Classical.choose ((mem_leadingPositions S i.val).1 i.property),
      (Classical.choose_spec ((mem_leadingPositions S i.val).1 i.property)).1⟩
  have hv (i : leadingPositions S) : (v i).val i.val ≠ 0 ∧ ∀ j < i.val, (v i).val j = 0 :=
    (Classical.choose_spec ((mem_leadingPositions S i.val).1 i.property)).2
  let M : Matrix (leadingPositions S) (leadingPositions S) F :=
    fun i j => (v i).val j.val
  have htri : M.IsUpperTriangular := by
    intro i j hij
    exact (hv i).2 j hij
  have hdet : M.det ≠ 0 := by
    rw [Matrix.det_of_isUpperTriangular htri]
    exact Finset.prod_ne_zero_iff.2 fun i _ => (hv i).1
  have hrows := Matrix.linearIndependent_rows_of_det_ne_zero hdet
  have hvind : LinearIndependent F v :=
    LinearIndependent.of_comp (leadingRestriction S) hrows
  simpa only [Fintype.card_coe] using hvind.fintype_card_le_finrank

theorem card_leadingPositions (S : Submodule F (I → F)) :
    (leadingPositions S).card = Module.finrank F S :=
  Nat.le_antisymm (card_leadingPositions_le_finrank S) (finrank_le_card_leadingPositions S)

variable {J : Type*} [Fintype J] [LinearOrder J]

def pullback (f : J → I) : (I → F) →ₗ[F] (J → F) where
  toFun v j := v (f j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Fintype I] [Fintype J] in
theorem IsLeading.pullback {S : Submodule F (I → F)} {f : J → I} (hf : StrictMono f)
    {j : J} (hj : IsLeading S (f j)) : IsLeading (S.map (pullback f)) j := by
  obtain ⟨v, hv, hvj, hzero⟩ := hj
  refine ⟨Lemmata.Centroid.Linear.pullback f v, ⟨v, hv, rfl⟩, hvj, ?_⟩
  intro k hk
  exact hzero _ (hf hk)

theorem leadingPositions_pullback {S : Submodule F (I → F)} {f : J → I} (hf : StrictMono f)
    {j : J} (hj : f j ∈ leadingPositions S) : j ∈ leadingPositions (S.map (pullback f)) := by
  rw [mem_leadingPositions] at hj ⊢
  exact hj.pullback hf

end

end Lemmata.Centroid.Linear
