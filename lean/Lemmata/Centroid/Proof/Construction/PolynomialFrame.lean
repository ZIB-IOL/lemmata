module

public import Lemmata.Centroid.Proof.Construction.SecondOrder

@[expose] public section

open scoped BigOperators
open Classical

namespace Lemmata.Centroid.Realization

noncomputable section

variable {K ι : Type*} [Field K] [Fintype ι]
variable {U L : ι → Type*} [∀ i, Fintype (U i)]

def polynomialCoreFactor (p : ∀ i, U i → Polynomial K) :
    ∀ i, Coordinates U L i → Polynomial K :=
  fun i => Sum.elim (p i) (fun _ => 0)

omit [Fintype ι] [∀ i, Fintype (U i)] in
theorem polynomialCoreFactor_coeff (p : ∀ i, U i → Polynomial K) (k : ℕ)
    (i : ι) (x : Coordinates U L i) :
    (polynomialCoreFactor p i x).coeff k = coreFactor (fun j a => (p j a).coeff k) i x := by
  cases x <;> simp [polynomialCoreFactor, coreFactor]

theorem simple_polynomialCoreFactor (p : ∀ i, U i → Polynomial K) :
    Tensor.simple (polynomialCoreFactor (L := L) p) =
      Tensor.localMap (fun i x a => Polynomial.C (coreEntry (F := K) i x a)) (Tensor.simple p) := by
  rw [Tensor.localMap_simple]
  congr 1
  funext i x
  cases x <;> simp [polynomialCoreFactor, coreEntry]

theorem polynomialCoreMap_coeff (T : Tensor (Polynomial K) ι U) (k : ℕ)
    (x : ∀ i, Coordinates U L i) :
    (Tensor.localMap (fun i x a => Polynomial.C (coreEntry (F := K) i x a)) T x).coeff k =
      coreEmbedding (fun a => (T a).coeff k) x := by
  simp only [Tensor.localMap, coreEmbedding, LinearMap.coe_mk, AddHom.coe_mk,
    Polynomial.finsetSum_coeff,
    Lemmata.TensorRank.Tensor.localMap]
  apply Finset.sum_congr rfl
  intro a ha
  rw [← map_prod, Polynomial.coeff_C_mul]

theorem polynomialCoreFactor_sum_coeff {J : Type*} [Fintype J]
    (p : J → ∀ i, U i → Polynomial K) (k : ℕ) (x : ∀ i, Coordinates U L i) :
    ((∑ j, Tensor.simple (polynomialCoreFactor (L := L) (p j))) x).coeff k =
      coreEmbedding (fun a => ((∑ j, Tensor.simple (p j)) a).coeff k) x := by
  simp_rw [simple_polynomialCoreFactor]
  rw [← Tensor.localMap_sum]
  exact polynomialCoreMap_coeff _ k x

theorem coreEmbedding_map {F : Type*} [Field F] (φ : F →+* K) (T : Tensor F ι U) :
    coreEmbedding (L := L) (Tensor.mapCoefficients φ T) =
      Tensor.mapCoefficients φ (coreEmbedding T) := by
  ext x
  simp only [coreEmbedding, LinearMap.coe_mk, AddHom.coe_mk, Tensor.localMap,
    Tensor.mapCoefficients, map_sum, map_mul, map_prod, map_coreEntry,
    Lemmata.TensorRank.Tensor.localMap]

variable {F : Type*} [Field F]
variable {V W : Fin 3 → Type*} [∀ i, Fintype (V i)] [∀ i, Fintype (W i)]

theorem rational_second_order_realization_core {J : Type*} [Fintype J] {w : ℕ}
    (P : PairFamily F V W) (τ : Tensor F (Fin 3) V)
    (p : J → ∀ i, V i → Polynomial (RatFunc F))
    (u : J → ∀ i, V i → RatFunc F)
    (hbase : ∀ j i a, (p j i a).coeff 0 = u j i a)
    (hQ : Tensor.RankAtMost (∑ j, Tensor.simple (u j)) w)
    (hs : FrameSpans (mapPairs (algebraMap F (RatFunc F)) P) u)
    (hlinear : ∀ x, ((∑ j, Tensor.simple (p j)) x).coeff 1 = 0)
    (hquadratic : ∀ x, ((∑ j, Tensor.simple (p j)) x).coeff 2 =
      algebraMap F (RatFunc F) (τ x)) :
    Tensor.RationalBorderRankAtMost (tensor P τ) (Fintype.card J + w) := by
  apply rational_second_order_realization_family P τ
    (fun j => polynomialCoreFactor (p j)) u
  · intro j i a
    rw [polynomialCoreFactor_coeff]
    congr 1
    funext i a
    exact hbase j i a
  · exact hQ
  · exact hs
  · intro x
    rw [polynomialCoreFactor_sum_coeff]
    simp only [hlinear]
    exact congrFun (map_zero (coreEmbedding (F := RatFunc F))) x
  · intro x
    rw [polynomialCoreFactor_sum_coeff]
    simp only [hquadratic]
    exact congrFun (coreEmbedding_map (algebraMap F (RatFunc F)) τ) x

end

end Lemmata.Centroid.Realization
