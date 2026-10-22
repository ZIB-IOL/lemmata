module

public import Lemmata.Centroid.Proof.Construction

@[expose] public section

open scoped BigOperators
open Classical

namespace Lemmata.Centroid.Tensor

noncomputable section

variable {F ι : Type*} [Field F] [Fintype ι]
variable {V : ι → Type*} [∀ i, Fintype (V i)]

def weightedFlattening (T : Tensor F ι V) (i : ι)
    (E : (∀ j, V j) → V i → F) : Matrix (V i) (V i) F :=
  fun a b => ∑ x, T (Function.update x i a) * E x b

theorem RankAtMost.weightedFlattening_rank_le {T : Tensor F ι V} {r : ℕ}
    (hT : RankAtMost T r) (i : ι) (E : (∀ j, V j) → V i → F) :
    (weightedFlattening T i E).rank ≤ r := by
  obtain ⟨u, rfl⟩ := hT
  let A : Matrix (V i) (Fin r) F := fun a q => u q i a
  let B : Matrix (Fin r) (V i) F := fun q b =>
    ∑ x, (∏ j ∈ Finset.univ.erase i, u q j (x j)) * E x b
  have hmul : weightedFlattening (∑ q, simple (u q)) i E = A * B := by
    ext a b
    simp only [weightedFlattening, Finset.sum_apply, Matrix.mul_apply]
    dsimp only [A, B]
    change (∑ x, (∑ q, simple (u q) (Function.update x i a)) * E x b) =
      ∑ q, u q i a * ∑ x, (∏ j ∈ Finset.univ.erase i, u q j (x j)) * E x b
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro q hq
    apply Finset.sum_congr rfl
    intro x hx
    rw [simple_apply, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    simp only [Function.update_self]
    rw [mul_assoc]
    congr 2
    apply Finset.prod_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
  rw [hmul]
  exact (Matrix.rank_mul_le_left _ _).trans (by simpa using Matrix.rank_le_card_width A)

theorem RationalBorderRankAtMost.card_le_of_weightedFlattening
    {T : Tensor F ι V} {r : ℕ} (hT : RationalBorderRankAtMost T r)
    (i : ι) (E : (∀ j, V j) → V i → F)
    (hdet : (weightedFlattening T i E).det ≠ 0) : Fintype.card (V i) ≤ r := by
  obtain ⟨A⟩ := hT
  let M : Matrix (V i) (V i) (RationalFunction.regularSubring F) :=
    fun a b => ∑ x,
      (⟨A.family (Function.update x i a), A.regular _⟩ : RationalFunction.regularSubring F) *
        RationalFunction.ofPolynomial (Polynomial.C (E x b))
  have hspec : RationalFunction.specialize.mapMatrix M = weightedFlattening T i E := by
    ext a b
    change RationalFunction.specialize (M a b) = _
    simp only [M, map_sum, map_mul, weightedFlattening]
    apply Finset.sum_congr rfl
    intro x hx
    change RatFunc.eval (RingHom.id F) 0 (A.family (Function.update x i a)) *
      RatFunc.eval (RingHom.id F) 0 (algebraMap (Polynomial F) (RatFunc F)
        (Polynomial.C (E x b))) = _
    simp [A.value]
  have hcoe : (Subring.subtype (RationalFunction.regularSubring F)).mapMatrix M =
      weightedFlattening A.family i (fun x b => algebraMap F (RatFunc F) (E x b)) := by
    ext a b
    change (Subring.subtype (RationalFunction.regularSubring F)) (M a b) = _
    simp [M, weightedFlattening, RationalFunction.ofPolynomial]
  have hdet' : (weightedFlattening A.family i
      (fun x b => algebraMap F (RatFunc F) (E x b))).det ≠ 0 := by
    intro hz
    have hz' : M.det = 0 := by
      apply Subtype.val_injective
      change (Subring.subtype (RationalFunction.regularSubring F)) M.det = 0
      rw [RingHom.map_det, hcoe]
      exact hz
    have hs := congrArg RationalFunction.specialize hz'
    rw [RingHom.map_det, hspec, map_zero] at hs
    exact hdet hs
  rw [← Matrix.rank_of_det_ne_zero hdet']
  exact A.rank_bound.weightedFlattening_rank_le i _

theorem Concise.rationalBorderRank_lower {T : Tensor F ι V} (hT : Concise T)
    (i : ι) {r : ℕ} (hr : RationalBorderRankAtMost T r) : Fintype.card (V i) ≤ r := by
  obtain ⟨g, hg⟩ := (contraction T i).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (hT i))
  let E : (∀ j, V j) → V i → F := fun x b => g (Pi.single x 1) b
  have hidentity : weightedFlattening T i E = 1 := by
    ext a b
    have hex : contraction T i (Pi.single a 1) =
        ∑ x, T (Function.update x i a) • Pi.single x 1 := by
      ext y
      simp [contraction_apply, Pi.single_apply, mul_ite, ite_mul, eq_comm]
    have hh := congrArg (fun L : (V i → F) →ₗ[F] (V i → F) => L (Pi.single a 1)) hg
    change g (contraction T i (Pi.single a 1)) = Pi.single a 1 at hh
    rw [hex] at hh
    have hb := congrFun hh b
    simpa [weightedFlattening, E, map_sum, map_smul, Pi.single_apply, Matrix.one_apply,
      smul_eq_mul, eq_comm] using hb
  apply hr.card_le_of_weightedFlattening i E
  rw [hidentity, Matrix.det_one]
  exact one_ne_zero

theorem Concise.le_rationalBorderRank [Nonempty ι] {T : Tensor F ι V} (hT : Concise T)
    (i : ι) : Fintype.card (V i) ≤ rationalBorderRank T :=
  hT.rationalBorderRank_lower i (rationalBorderRankAtMost_rank T)

end

end Lemmata.Centroid.Tensor
