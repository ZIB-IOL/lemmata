module

public import Lemmata.Centroid.Proof.Construction

@[expose] public section

open scoped BigOperators
open Classical

namespace Lemmata.Centroid.Realization

noncomputable section

variable {F ι : Type*} [Field F] [Fintype ι]
variable {U L : ι → Type*} [∀ i, Fintype (U i)] [∀ i, Fintype (L i)]

def basisVector {X : Type*} (a : X) : X → F := fun x => if x = a then 1 else 0

theorem simple_basisVector {V : ι → Type*} (a : ∀ i, V i) :
    Tensor.simple (fun i => basisVector (F := F) (a i)) = basisVector a := by
  ext x
  by_cases h : x = a
  · subst x
    simp [Tensor.simple, basisVector]
  · have hx : ∃ i, x i ≠ a i := by
      by_contra! hx
      exact h (funext hx)
    obtain ⟨i, hi⟩ := hx
    rw [basisVector, ite_eq_right h]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [basisVector, hi])

theorem oppositeSimple_basisVector {V : ι → Type*} (a : ∀ i, V i) (i : ι) :
    BigCentroid.oppositeSimple (fun j => basisVector (F := F) (a j)) i =
      basisVector (fun j : {j // j ≠ i} => a j.val) :=
  simple_basisVector _

omit [∀ i, Fintype (L i)] in
theorem pairEmbedding_basisVector (i : ι) (p : Opposite U i) (x : ∀ j, Coordinates U L j) :
    pairEmbedding i (basisVector (F := F) p) x =
      ∏ j : {j // j ≠ i}, coreEntry j.val (x j.val) (p j) := by
  simp [pairEmbedding, basisVector, ite_mul]

omit [∀ i, Fintype (L i)] in
theorem coreEmbedding_basisVector (a : ∀ i, U i) (x : ∀ j, Coordinates U L j) :
    coreEmbedding (basisVector (F := F) a) x = ∏ i, coreEntry i (x i) (a i) := by
  simp [coreEmbedding, Tensor.localMap, basisVector, mul_ite]

omit [∀ i, Fintype (U i)] in
theorem coordinate_mem_compatibleSpace (P : PairFamily F U L) (a : ∀ i, U i)
    (hP : ∀ i, ∃ l, P i l = basisVector (fun j : {j // j ≠ i} => a j.val)) :
    basisVector (F := F) a ∈ compatibleSpace P := by
  apply (Submodule.mem_iInf _).mpr
  intro i
  obtain ⟨l, hl⟩ := hP i
  refine ⟨fun u k => (if u = a i then 1 else 0) * (if k = l then 1 else 0), ?_⟩
  ext x
  change (∑ k, ((if x i = a i then 1 else 0) * (if k = l then 1 else 0)) *
    P i k (fun j => x j.val)) = basisVector a x
  rw [Finset.sum_eq_single l]
  · rw [hl]
    by_cases hx : x = a
    · subst x; simp [basisVector]
    · by_cases hxi : x i = a i
      · have hr : (fun j : {j // j ≠ i} => x j.val) ≠
            (fun j : {j // j ≠ i} => a j.val) := by
          intro h
          apply hx
          funext j
          by_cases hji : j = i
          · subst j; exact hxi
          · exact congrFun h ⟨j, hji⟩
        simp [basisVector, hx, hxi, hr]
      · simp [basisVector, hx, hxi]
  · intro k hk hkl
    simp [hkl]
  · simp

theorem monomial_centroid_lower_bound [Nonempty ι] [∀ i, Nonempty (U i)]
    {J : Type*} [Fintype J] (P : PairFamily F U L) (τ : Tensor F ι U)
    (a : J → ∀ i, U i) (ha : Function.Injective a)
    (hP : ∀ j i, ∃ l, P i l = basisVector (fun k : {k // k ≠ i} => a j k.val)) :
    1 + Fintype.card J ≤ Module.finrank F (Tensor.centroid (tensor P τ)) := by
  have hli : LinearIndependent F (fun j => basisVector (F := F) (a j)) := by
    convert (Pi.linearIndependent_single_one (∀ i, U i) F).comp a ha using 1
    ext j x
    simp [basisVector, Pi.single_apply]
  have hspan : Submodule.span F (Set.range (fun j => basisVector (F := F) (a j))) ≤
      compatibleSpace P := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact coordinate_mem_compatibleSpace P (a j) (hP j)
  have hdim : Fintype.card J ≤ Module.finrank F (compatibleSpace P) := by
    rw [← finrank_span_eq_card hli]
    exact Submodule.finrank_mono hspan
  exact (Nat.add_le_add_left hdim 1).trans (centroid_lower_bound P τ)

theorem prod_other_zero (f : Fin 3 → F) [Fintype {j : Fin 3 // j ≠ 0}] :
    (∏ j : {j : Fin 3 // j ≠ 0}, f j.val) = f 1 * f 2 := by
  rw [← Finset.prod_subtype ({1, 2} : Finset (Fin 3)) (by intro j; fin_cases j <;> simp) f]
  simp

theorem prod_other_one (f : Fin 3 → F) [Fintype {j : Fin 3 // j ≠ 1}] :
    (∏ j : {j : Fin 3 // j ≠ 1}, f j.val) = f 0 * f 2 := by
  rw [← Finset.prod_subtype ({0, 2} : Finset (Fin 3)) (by intro j; fin_cases j <;> simp) f]
  simp

theorem prod_other_two (f : Fin 3 → F) [Fintype {j : Fin 3 // j ≠ 2}] :
    (∏ j : {j : Fin 3 // j ≠ 2}, f j.val) = f 0 * f 1 := by
  rw [← Finset.prod_subtype ({0, 1} : Finset (Fin 3)) (by intro j; fin_cases j <;> simp) f]
  simp

theorem map_basisVector {K X : Type*} [Field K] (φ : F →+* K) (a : X) :
    (fun x => φ (basisVector (F := F) a x)) = basisVector (F := K) a := by
  ext x
  by_cases h : x = a <;> simp [basisVector, h]

theorem oppositeSimple_zero {V : Fin 3 → Type*} (u : ∀ i, V i → F)
    (p : BigCentroid.Opposite V 0) :
    BigCentroid.oppositeSimple u 0 p =
      u 1 (p ⟨1, by decide⟩) * u 2 (p ⟨2, by decide⟩) := by
  let f : Fin 3 → F := ![1, u 1 (p ⟨1, by decide⟩), u 2 (p ⟨2, by decide⟩)]
  unfold BigCentroid.oppositeSimple Tensor.simple Lemmata.TensorRank.Tensor.pure
  trans ∏ j : {j : Fin 3 // j ≠ 0}, f j.val
  · apply Finset.prod_congr (by ext j; simp)
    intro j hj
    rcases j with ⟨j, hj⟩
    fin_cases j <;> first | rfl | contradiction
  · exact prod_other_zero f

theorem oppositeSimple_one {V : Fin 3 → Type*} (u : ∀ i, V i → F)
    (p : BigCentroid.Opposite V 1) :
    BigCentroid.oppositeSimple u 1 p =
      u 0 (p ⟨0, by decide⟩) * u 2 (p ⟨2, by decide⟩) := by
  let f : Fin 3 → F := ![u 0 (p ⟨0, by decide⟩), 1, u 2 (p ⟨2, by decide⟩)]
  unfold BigCentroid.oppositeSimple Tensor.simple Lemmata.TensorRank.Tensor.pure
  trans ∏ j : {j : Fin 3 // j ≠ 1}, f j.val
  · apply Finset.prod_congr (by ext j; simp)
    intro j hj
    rcases j with ⟨j, hj⟩
    fin_cases j <;> first | rfl | contradiction
  · exact prod_other_one f

theorem oppositeSimple_two {V : Fin 3 → Type*} (u : ∀ i, V i → F)
    (p : BigCentroid.Opposite V 2) :
    BigCentroid.oppositeSimple u 2 p =
      u 0 (p ⟨0, by decide⟩) * u 1 (p ⟨1, by decide⟩) := by
  let f : Fin 3 → F := ![u 0 (p ⟨0, by decide⟩), u 1 (p ⟨1, by decide⟩), 1]
  unfold BigCentroid.oppositeSimple Tensor.simple Lemmata.TensorRank.Tensor.pure
  trans ∏ j : {j : Fin 3 // j ≠ 2}, f j.val
  · apply Finset.prod_congr (by ext j; simp)
    intro j hj
    rcases j with ⟨j, hj⟩
    fin_cases j <;> first | rfl | contradiction
  · exact prod_other_two f

end

end Lemmata.Centroid.Realization
