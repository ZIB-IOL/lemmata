module

public import Lemmata.Centroid.Proof.Construction.Frames
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

open scoped BigOperators
open Classical

namespace Lemmata.Centroid.BigCentroid

noncomputable section

variable {F : Type*} [Field F]
variable {V : Fin 3 → Type*}

theorem mul_coeff_two (p q : Polynomial F) :
    (p * q).coeff 2 = p.coeff 0 * q.coeff 2 + p.coeff 1 * q.coeff 1 + p.coeff 2 * q.coeff 0 := by
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [Finset.sum_range_succ, add_assoc]

def quadraticLift (p : ∀ i, V i → Polynomial F) (v : ∀ i, V i → F) :
    ∀ i, V i → Polynomial F := fun i a => p i a + Polynomial.X ^ 2 * Polynomial.C (v i a)

@[simp] theorem quadraticLift_coeff_zero (p : ∀ i, V i → Polynomial F)
    (v : ∀ i, V i → F) (i : Fin 3) (a : V i) :
    (quadraticLift p v i a).coeff 0 = (p i a).coeff 0 := by
  simp [quadraticLift]

@[simp] theorem quadraticLift_coeff_one (p : ∀ i, V i → Polynomial F)
    (v : ∀ i, V i → F) (i : Fin 3) (a : V i) :
    (quadraticLift p v i a).coeff 1 = (p i a).coeff 1 := by
  simp [quadraticLift]

@[simp] theorem quadraticLift_coeff_two (p : ∀ i, V i → Polynomial F)
    (v : ∀ i, V i → F) (i : Fin 3) (a : V i) :
    (quadraticLift p v i a).coeff 2 = (p i a).coeff 2 + v i a := by
  simp [quadraticLift]

theorem simple_quadraticLift_coeff_one (p : ∀ i, V i → Polynomial F)
    (v : ∀ i, V i → F) (x : ∀ i, V i) :
    (Tensor.simple (quadraticLift p v) x).coeff 1 = (Tensor.simple p x).coeff 1 := by
  simp only [Tensor.simple, Fin.prod_univ_three, Polynomial.mul_coeff_one,
    Polynomial.mul_coeff_zero, quadraticLift_coeff_zero, quadraticLift_coeff_one,
    Lemmata.TensorRank.Tensor.pure]

theorem simple_quadraticLift_coeff_two (p : ∀ i, V i → Polynomial F)
    (v : ∀ i, V i → F) (x : ∀ i, V i) :
    (Tensor.simple (quadraticLift p v) x).coeff 2 = (Tensor.simple p x).coeff 2 +
      firstVariation (fun i a => (p i a).coeff 0) v x := by
  rw [← coeff_one_simple_variation]
  simp only [Tensor.simple, Fin.prod_univ_three, mul_coeff_two,
    Polynomial.mul_coeff_one, Polynomial.mul_coeff_zero, quadraticLift_coeff_zero,
    quadraticLift_coeff_one, quadraticLift_coeff_two,
    Lemmata.TensorRank.Tensor.pure]
  simp [Polynomial.mul_coeff_one, Polynomial.mul_coeff_zero]
  ring

theorem rational_second_order_lift [∀ i, Fintype (V i)] {r w : ℕ}
    (p : Fin r → ∀ i, V i → Polynomial (RatFunc F))
    (v : Fin r → ∀ i, V i → RatFunc F) (T S : Tensor F (Fin 3) V)
    (hQ : Tensor.RankAtMost
      (∑ q, Tensor.simple (fun i a => (p q i a).coeff 0)) w)
    (hlinear : ∀ x, ((∑ q, Tensor.simple (p q)) x).coeff 1 = 0)
    (hquadratic : ∀ x, ((∑ q, Tensor.simple (p q)) x).coeff 2 =
      algebraMap F (RatFunc F) (T x))
    (hvariation : (∑ q, firstVariation (fun i a => (p q i a).coeff 0) (v q)) =
      Tensor.mapCoefficients (algebraMap F (RatFunc F)) S) :
    Tensor.RationalBorderRankAtMost (T + S) (r + w) := by
  apply rational_second_order_frame (fun q => quadraticLift (p q) (v q)) (T + S)
  · simpa only [quadraticLift_coeff_zero] using hQ
  · intro x
    simpa only [Finset.sum_apply, Polynomial.finsetSum_coeff,
      simple_quadraticLift_coeff_one] using hlinear x
  · intro x
    have hv := congrFun hvariation x
    rw [show ((∑ q, Tensor.simple (quadraticLift (p q) (v q))) x).coeff 2 =
        ((∑ q, Tensor.simple (p q)) x).coeff 2 +
          (∑ q, firstVariation (fun i a => (p q i a).coeff 0) (v q)) x from by
      simp only [Finset.sum_apply, Polynomial.finsetSum_coeff,
        simple_quadraticLift_coeff_two, Finset.sum_add_distrib]]
    rw [hquadratic x, hv]
    exact (map_add (algebraMap F (RatFunc F)) (T x) (S x)).symm

end

end Lemmata.Centroid.BigCentroid

namespace Lemmata.Centroid.Realization

noncomputable section

variable {F : Type*} [Field F]
variable {U L : Fin 3 → Type*} [∀ i, Fintype (U i)] [∀ i, Fintype (L i)]

theorem rational_second_order_realization {r w : ℕ} (P : PairFamily F U L)
    (τ : Tensor F (Fin 3) U)
    (p : Fin r → ∀ i, Coordinates U L i → Polynomial (RatFunc F))
    (u : Fin r → ∀ i, U i → RatFunc F)
    (hbase : ∀ q i a, (p q i a).coeff 0 = coreFactor (u q) i a)
    (hQ : Tensor.RankAtMost (∑ q, Tensor.simple (u q)) w)
    (hs : FrameSpans (mapPairs (algebraMap F (RatFunc F)) P) u)
    (hlinear : ∀ x, ((∑ q, Tensor.simple (p q)) x).coeff 1 = 0)
    (hquadratic : ∀ x, ((∑ q, Tensor.simple (p q)) x).coeff 2 =
      algebraMap F (RatFunc F) (coreEmbedding τ x)) :
    Tensor.RationalBorderRankAtMost (tensor P τ) (r + w) := by
  obtain ⟨l, hl⟩ := FrameSpans.exists_dualFactor _ u hs
  have hsum : coreEmbedding τ + tensor P 0 = tensor P τ := by
    simp [tensor, add_comm]
  rw [← hsum]
  apply BigCentroid.rational_second_order_lift p (fun q => dualFactor (l q))
    (coreEmbedding τ) (tensor P 0)
  · simp_rw [hbase]
    exact coreFactor_sum_rank u hQ
  · exact hlinear
  · exact hquadratic
  · simp_rw [hbase]
    rw [map_tensor, Tensor.mapCoefficients_zero]
    exact frame_variation _ u l hl

theorem rational_second_order_realization_family {J : Type*} [Fintype J] {w : ℕ}
    (P : PairFamily F U L) (τ : Tensor F (Fin 3) U)
    (p : J → ∀ i, Coordinates U L i → Polynomial (RatFunc F))
    (u : J → ∀ i, U i → RatFunc F)
    (hbase : ∀ q i a, (p q i a).coeff 0 = coreFactor (u q) i a)
    (hQ : Tensor.RankAtMost (∑ q, Tensor.simple (u q)) w)
    (hs : FrameSpans (mapPairs (algebraMap F (RatFunc F)) P) u)
    (hlinear : ∀ x, ((∑ q, Tensor.simple (p q)) x).coeff 1 = 0)
    (hquadratic : ∀ x, ((∑ q, Tensor.simple (p q)) x).coeff 2 =
      algebraMap F (RatFunc F) (coreEmbedding τ x)) :
    Tensor.RationalBorderRankAtMost (tensor P τ) (Fintype.card J + w) := by
  let e : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  have hsumP : (∑ q, Tensor.simple (p (e q))) = ∑ q, Tensor.simple (p q) :=
    e.sum_comp (fun q => Tensor.simple (p q))
  have hsumU : (∑ q, Tensor.simple (u (e q))) = ∑ q, Tensor.simple (u q) :=
    e.sum_comp (fun q => Tensor.simple (u q))
  apply rational_second_order_realization P τ (fun q => p (e q)) (fun q => u (e q))
  · intro q i a
    exact hbase (e q) i a
  · rw [hsumU]
    exact hQ
  · intro i l
    have hrange : Set.range (fun q => BigCentroid.oppositeSimple (u (e q)) i) =
        Set.range (fun q => BigCentroid.oppositeSimple (u q) i) := by
      ext v
      constructor
      · rintro ⟨q, rfl⟩
        exact ⟨e q, rfl⟩
      · rintro ⟨q, rfl⟩
        exact ⟨e.symm q, by dsimp only; rw [e.apply_symm_apply]⟩
    change _ ∈ Submodule.span (RatFunc F) (Set.range (fun q => BigCentroid.oppositeSimple (u (e q)) i))
    rw [hrange]
    exact hs i l
  · rw [hsumP]
    exact hlinear
  · rw [hsumP]
    exact hquadratic

end

end Lemmata.Centroid.Realization
