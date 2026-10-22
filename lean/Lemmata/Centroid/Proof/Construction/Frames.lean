module

public import Lemmata.Centroid.Proof.Construction

@[expose] public section

open scoped BigOperators
open Classical

namespace Lemmata.Centroid.Realization

noncomputable section

variable {F ι : Type*} [Field F] [Fintype ι]
variable {U L : ι → Type*} [∀ i, Fintype (U i)] [∀ i, Fintype (L i)]

def mapPairs {K : Type*} [Field K] (φ : F →+* K) (P : PairFamily F U L) :
    PairFamily K U L := fun i l p => φ (P i l p)

omit [Fintype ι] [∀ i, Fintype (U i)] [∀ i, Fintype (L i)] in
theorem map_coreEntry {K : Type*} [Field K] (φ : F →+* K)
    (i : ι) (x : Coordinates U L i) (a : U i) :
    φ (coreEntry i x a) = coreEntry i x a := by
  cases x <;> simp [coreEntry]

omit [∀ i, Fintype (L i)] in
theorem map_tensor {K : Type*} [Field K] (φ : F →+* K)
    (P : PairFamily F U L) (τ : Tensor F ι U) :
    Tensor.mapCoefficients φ (tensor P τ) =
      tensor (mapPairs φ P) (Tensor.mapCoefficients φ τ) := by
  ext x
  simp only [Tensor.mapCoefficients, tensor, Pi.add_apply, Finset.sum_apply,
    map_add, map_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    unfold sector
    cases x i with
    | inl a => exact map_zero _
    | inr l => simp [pairEmbedding, mapPairs, map_sum, map_prod, map_coreEntry]
  · simp [coreEmbedding, Tensor.localMap, map_coreEntry]

def coreFactor (u : ∀ i, U i → F) : ∀ i, Coordinates U L i → F :=
  fun i => Sum.elim (u i) (fun _ => 0)

def dualFactor (l : ∀ i, L i → F) : ∀ i, Coordinates U L i → F :=
  fun i => Sum.elim (fun _ => 0) (l i)

def FrameSpans {J : Type*} (P : PairFamily F U L) (u : J → ∀ i, U i → F) : Prop :=
  ∀ i l, P i l ∈ Submodule.span F (Set.range (fun q => BigCentroid.oppositeSimple (u q) i))

omit [∀ i, Fintype (L i)] in
theorem coreFactor_sum_rank {J : Type*} [Fintype J]
    (u : J → ∀ i, U i → F) {w : ℕ}
    (h : Tensor.RankAtMost (∑ q, Tensor.simple (u q)) w) :
    Tensor.RankAtMost (∑ q, Tensor.simple (coreFactor (L := L) (u q))) w := by
  have hs (v : ∀ i, U i → F) :
      Tensor.localMap (coreEntry (L := L)) (Tensor.simple v) = Tensor.simple (coreFactor v) := by
    rw [Tensor.localMap_simple]
    congr 1
    funext i x
    cases x <;> simp [coreEntry, coreFactor]
  have hh := h.localMap (coreEntry (L := L))
  simpa only [Tensor.localMap_sum, hs] using hh

omit [∀ i, Fintype (L i)] in
theorem FrameSpans.exists_dualFactor {J : Type*} [Fintype J]
    (P : PairFamily F U L) (u : J → ∀ i, U i → F) (h : FrameSpans P u) :
    ∃ l : J → ∀ i, L i → F, ∀ i p (x : ∀ j, Coordinates U L j),
      (∑ q, l q i p * ∏ j ∈ Finset.univ.erase i, coreFactor (u q) j (x j)) =
        pairEmbedding i (P i p) x := by
  have hex (i : ι) (p : L i) : ∃ l : J → F,
      (∑ q, l q • BigCentroid.oppositeSimple (u q) i) = P i p :=
    (Submodule.mem_span_range_iff_exists_fun F).mp (h i p)
  choose l hl using hex
  refine ⟨fun q i p => l i p q, fun i p x => ?_⟩
  let A : ∀ j : {j // j ≠ i}, Coordinates U L j.val → U j.val → F :=
    fun j => coreEntry j.val
  have hs (v : ∀ j : {j // j ≠ i}, U j.val → F) :
      Tensor.localMap A (Tensor.simple v) = Tensor.simple
        (fun j => Sum.elim (v j) (fun _ => 0)) := by
    rw [Tensor.localMap_simple]
    congr 1
    funext j y
    cases y <;> simp [A, coreEntry]
  have hh := congrArg (Tensor.localMap A) (hl i p)
  simp only [Tensor.localMap_sum, Tensor.localMap_smul, BigCentroid.oppositeSimple, hs] at hh
  have hv := congrFun hh (fun j : {j // j ≠ i} => x j.val)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Tensor.simple,
    Lemmata.TensorRank.Tensor.pure] at hv
  rw [show (∑ q, l i p q * ∏ j ∈ Finset.univ.erase i, coreFactor (u q) j (x j)) =
      ∑ q, l i p q * ∏ j : {j // j ≠ i}, coreFactor (u q) j.val (x j.val) from by
        congr 1
        funext q
        rw [Finset.prod_subtype (p := fun j => j ≠ i) _ (by simp)]]
  convert hv using 1
  · unfold coreFactor
    rfl
  · simp only [Tensor.localMap, pairEmbedding, A, mul_comm, Lemmata.TensorRank.Tensor.localMap]
    apply Finset.sum_congr (by ext a; simp)
    intro a ha
    congr 1

omit [∀ i, Fintype (L i)] in
theorem frame_variation {r : ℕ} (P : PairFamily F U L)
    (u : Fin r → ∀ i, U i → F) (l : Fin r → ∀ i, L i → F)
    (hspan : ∀ i p (x : ∀ j, Coordinates U L j),
      (∑ q, l q i p * ∏ j ∈ Finset.univ.erase i, coreFactor (u q) j (x j)) =
        pairEmbedding i (P i p) x) :
    (∑ q, BigCentroid.firstVariation (coreFactor (u q)) (dualFactor (l q))) =
      tensor P 0 := by
  ext x
  simp only [tensor, map_zero, add_zero, Finset.sum_apply, BigCentroid.firstVariation]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  cases hx : x i with
  | inl a => simp [dualFactor, sector, hx]
  | inr p => simpa [dualFactor, sector, hx] using hspan i p x

theorem rational_spanning_frame [Nonempty ι] {J : Type*} [Fintype J]
    (P : PairFamily F U L) (u : J → ∀ i, U i → RatFunc F) {w : ℕ}
    (hQ : Tensor.RankAtMost (∑ q, Tensor.simple (u q)) w)
    (hs : FrameSpans (mapPairs (algebraMap F (RatFunc F)) P) u) :
    Tensor.RationalBorderRankAtMost (tensor P 0) (Fintype.card J + w) := by
  obtain ⟨l, hl⟩ := FrameSpans.exists_dualFactor _ u hs
  let e : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  apply BigCentroid.rational_first_order_frame (fun q => coreFactor (u (e q)))
    (fun q => dualFactor (l (e q)))
  · have hh := coreFactor_sum_rank (L := L) u hQ
    rw [show (∑ q, Tensor.simple (coreFactor (L := L) (u (e q)))) =
      ∑ q : J, Tensor.simple (coreFactor (L := L) (u q)) from
        e.sum_comp (fun q => Tensor.simple (coreFactor (L := L) (u q)))]
    exact hh
  · rw [map_tensor, Tensor.mapCoefficients_zero]
    apply frame_variation
    intro i p x
    rw [show (∑ q, l (e q) i p * ∏ j ∈ Finset.univ.erase i,
      coreFactor (u (e q)) j (x j)) = ∑ q : J,
      l q i p * ∏ j ∈ Finset.univ.erase i, coreFactor (u q) j (x j) from
        e.sum_comp (fun q => l q i p * ∏ j ∈ Finset.univ.erase i,
          coreFactor (u q) j (x j))]
    exact hl i p x

end

end Lemmata.Centroid.Realization

namespace Lemmata.Centroid.BigCentroid

noncomputable section

variable {F ι : Type*} [Field F] [Fintype ι] [Nonempty ι]
variable {V : ι → Type*} [∀ i, Fintype (V i)]

theorem second_order_polynomial_certificate {r w : ℕ}
    (u : Fin r → ∀ i, V i → Polynomial F) (T : Tensor F ι V)
    (hQ : Tensor.RankAtMost
      (∑ q, Tensor.simple (fun i a => (u q i a).coeff 0)) w)
    (hlinear : ∀ x, ((∑ q, Tensor.simple (u q)) x).coeff 1 = 0)
    (hquadratic : ∀ x, ((∑ q, Tensor.simple (u q)) x).coeff 2 = T x) :
    ∃ D, Nonempty (PolynomialApproximation T (r + w) 2 D) := by
  let Q : Tensor F ι V := ∑ q, Tensor.simple (fun i a => (u q i a).coeff 0)
  let P : Tensor (Polynomial F) ι V :=
    (∑ q, Tensor.simple (u q)) +
      (-1 : Polynomial F) • Tensor.mapCoefficients Polynomial.C Q
  have hr : Tensor.RankAtMost P (r + w) :=
    (show Tensor.RankAtMost (∑ q, Tensor.simple (u q)) r from ⟨u, rfl⟩).add
      ((hQ.mapCoefficients Polynomial.C).smul (-1))
  have hzero (x : ∀ i, V i) : (P x).coeff 0 = 0 := by
    simp [P, Q, Tensor.simple, Tensor.mapCoefficients,
      Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_finsetSum, Polynomial.eval_prod]
  have hcoeff (x : ∀ i, V i) (k : ℕ) (hk : k ≠ 0) :
      (P x).coeff k = ((∑ q, Tensor.simple (u q)) x).coeff k := by
    simp [P, Tensor.mapCoefficients, Polynomial.coeff_C, hk]
  let D := Finset.univ.sup (fun x : ∀ i, V i => (P x).natDegree)
  refine ⟨D, ⟨⟨P, hr, ?_, ?_, ?_⟩⟩⟩
  · intro x k hk
    have hcase : k = 0 ∨ k = 1 := by omega
    rcases hcase with rfl | rfl
    · exact hzero x
    · rw [hcoeff x 1 one_ne_zero, hlinear]
  · intro x
    rw [hcoeff x 2 (by decide), hquadratic]
  · intro x
    exact Polynomial.degree_le_of_natDegree_le
      (Finset.le_sup (f := fun x : ∀ i, V i => (P x).natDegree) (Finset.mem_univ x))

theorem rational_second_order_frame {r w : ℕ}
    (u : Fin r → ∀ i, V i → Polynomial (RatFunc F)) (T : Tensor F ι V)
    (hQ : Tensor.RankAtMost
      (∑ q, Tensor.simple (fun i a => (u q i a).coeff 0)) w)
    (hlinear : ∀ x, ((∑ q, Tensor.simple (u q)) x).coeff 1 = 0)
    (hquadratic : ∀ x, ((∑ q, Tensor.simple (u q)) x).coeff 2 =
      algebraMap F (RatFunc F) (T x)) :
    Tensor.RationalBorderRankAtMost T (r + w) := by
  obtain ⟨D, ⟨A⟩⟩ := second_order_polynomial_certificate u
    (Tensor.mapCoefficients (algebraMap F (RatFunc F)) T) hQ hlinear hquadratic
  exact A.rationalBorderRankAtMost_of_ratFunc

end

end Lemmata.Centroid.BigCentroid
