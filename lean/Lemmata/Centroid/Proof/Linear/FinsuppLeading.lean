module

public import Lemmata.Centroid.Proof.Linear.Leading
public import Mathlib.LinearAlgebra.Finsupp.Defs
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Algebra.Group.Finsupp

@[expose] public section

noncomputable section

open scoped BigOperators
open Classical

namespace Lemmata.Centroid.Linear

variable {F I : Type*} [Field F] [LinearOrder I]

def IsFinsuppLeading (S : Submodule F (I →₀ F)) (i : I) : Prop :=
  ∃ v ∈ S, v i ≠ 0 ∧ ∀ j < i, v j = 0

theorem IsFinsuppLeading.mono {S T : Submodule F (I →₀ F)} (hST : S ≤ T)
    {i : I} (hi : IsFinsuppLeading S i) : IsFinsuppLeading T i := by
  obtain ⟨v, hv, hi, hz⟩ := hi
  exact ⟨v, hST hv, hi, hz⟩

theorem IsFinsuppLeading.mapDomain {J : Type*} [LinearOrder J]
    {f : I → J} (hf : StrictMono f) {S : Submodule F (I →₀ F)} {i : I}
    (hi : IsFinsuppLeading S i) :
    IsFinsuppLeading (S.map (Finsupp.lmapDomain F F f)) (f i) := by
  obtain ⟨v, hv, hvi, hz⟩ := hi
  refine ⟨Finsupp.mapDomain f v, ⟨v, hv, rfl⟩, ?_, ?_⟩
  · simpa only [Finsupp.mapDomain_apply_of_injective hf.injective] using hvi
  · intro j hj
    by_cases hmem : j ∈ Set.range f
    · obtain ⟨k, rfl⟩ := hmem
      rw [Finsupp.mapDomain_apply_of_injective hf.injective]
      exact hz k (hf.lt_iff_lt.mp hj)
    · exact Finsupp.mapDomain_of_notMem_range v j hmem

def finsuppSupportBound (S : Submodule F (I →₀ F)) [FiniteDimensional F S] : Finset I := by
  letI : Module.Free F S := Module.Free.of_divisionRing F S
  exact Finset.univ.biUnion fun j : Fin (Module.finrank F S) => ((Module.finBasis F S) j).1.support

theorem eq_zero_outside_finsuppSupportBound (S : Submodule F (I →₀ F))
    [FiniteDimensional F S] (v : S) {i : I} (hi : i ∉ finsuppSupportBound S) :
    v.1 i = 0 := by
  let : Module.Free F S := Module.Free.of_divisionRing F S
  let b := Module.finBasis F S
  let e : S →ₗ[F] F := (Finsupp.lapply i).comp S.subtype
  have hb (j : Fin (Module.finrank F S)) : e (b j) = 0 := by
    change (b j).1 i = 0
    apply Finsupp.notMem_support_iff.mp
    intro hh
    exact hi (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hh⟩)
  have h := congrArg e (b.sum_repr v)
  change e v = 0
  simpa only [map_sum, map_smul, hb, smul_zero, Finset.sum_const_zero] using h.symm

def boundedFinsuppCoefficients (D : Finset I) : (I →₀ F) →ₗ[F] (D → F) :=
  LinearMap.pi fun i => Finsupp.lapply i.1

omit [LinearOrder I] in
@[simp] theorem boundedFinsuppCoefficients_apply (D : Finset I) (v : I →₀ F) (i : D) :
    boundedFinsuppCoefficients D v i = v i.1 := rfl

def finsuppCoefficientMap (S : Submodule F (I →₀ F)) [FiniteDimensional F S] :
    S →ₗ[F] (finsuppSupportBound S → F) :=
  (boundedFinsuppCoefficients (finsuppSupportBound S)).comp S.subtype

theorem finsuppCoefficientMap_injective (S : Submodule F (I →₀ F))
    [FiniteDimensional F S] : Function.Injective (finsuppCoefficientMap S) := by
  intro v w h
  apply Subtype.ext
  ext i
  by_cases hi : i ∈ finsuppSupportBound S
  · exact congrFun h ⟨i, hi⟩
  · rw [eq_zero_outside_finsuppSupportBound S v hi,
      eq_zero_outside_finsuppSupportBound S w hi]

def finsuppLeadingTerms (S : Submodule F (I →₀ F)) [FiniteDimensional F S] : Finset I :=
  (leadingPositions (LinearMap.range (finsuppCoefficientMap S))).map
    ⟨Subtype.val, Subtype.val_injective⟩

theorem isLeading_finsuppCoefficientMap (S : Submodule F (I →₀ F))
    [FiniteDimensional F S] (i : finsuppSupportBound S) :
    IsLeading (LinearMap.range (finsuppCoefficientMap S)) i ↔ IsFinsuppLeading S i.1 := by
  constructor
  · rintro ⟨_, ⟨v, rfl⟩, hv, hz⟩
    refine ⟨v.1, v.2, hv, ?_⟩
    intro j hj
    by_cases hmem : j ∈ finsuppSupportBound S
    · exact hz ⟨j, hmem⟩ hj
    · exact eq_zero_outside_finsuppSupportBound S v hmem
  · rintro ⟨v, hv, hi, hz⟩
    refine ⟨finsuppCoefficientMap S ⟨v, hv⟩, ⟨⟨v, hv⟩, rfl⟩, hi, ?_⟩
    intro j hj
    exact hz j.1 hj

@[simp] theorem mem_finsuppLeadingTerms (S : Submodule F (I →₀ F))
    [FiniteDimensional F S] (i : I) : i ∈ finsuppLeadingTerms S ↔ IsFinsuppLeading S i := by
  constructor
  · intro hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
    exact (isLeading_finsuppCoefficientMap S j).mp ((mem_leadingPositions _ _).mp hj)
  · intro hi
    have hmem : i ∈ finsuppSupportBound S := by
      by_contra hn
      obtain ⟨v, hv, hvi, _⟩ := hi
      exact hvi (eq_zero_outside_finsuppSupportBound S ⟨v, hv⟩ hn)
    exact Finset.mem_map.mpr ⟨⟨i, hmem⟩,
      (mem_leadingPositions _ _).mpr ((isLeading_finsuppCoefficientMap S ⟨i, hmem⟩).mpr hi), rfl⟩

theorem card_finsuppLeadingTerms (S : Submodule F (I →₀ F)) [FiniteDimensional F S] :
    (finsuppLeadingTerms S).card = Module.finrank F S := by
  rw [finsuppLeadingTerms, Finset.card_map, card_leadingPositions]
  exact LinearMap.finrank_range_of_inj (finsuppCoefficientMap_injective S)

end Lemmata.Centroid.Linear
