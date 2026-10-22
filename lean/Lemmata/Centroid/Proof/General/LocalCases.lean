module

public import Lemmata.Centroid.Proof.General.HigherRadical
public import Lemmata.Centroid.Proof.General.SquareZero
public import Lemmata.Centroid.Proof.General.ResidueAlgebra
public import Lemmata.Centroid.Proof.General.MergeNumeric
public import Lemmata.Centroid.Proof.Linear.LocalAlgebra

@[expose] public section

open Classical

noncomputable section

namespace Lemmata.Centroid.General

variable {F A : Type*} [Field F] [CommRing A] [Algebra F A] [FiniteDimensional F A]

theorem residue_dimension_pos (I : Ideal A) [I.IsMaximal] :
    0 < Module.finrank F (A ⧸ I) := by
  let q := (Ideal.Quotient.mkₐ F I).toLinearMap
  let : FiniteDimensional F (A ⧸ I) := Module.Finite.of_surjective q Ideal.Quotient.mk_surjective
  let : Field (A ⧸ I) := Ideal.Quotient.field I
  exact Module.finrank_pos

include F in
theorem local_maximalIdeal_nilpotent [IsLocalRing A] :
    IsNilpotent (IsLocalRing.maximalIdeal A) := by
  let : IsArtinianRing A := isArtinian_of_tower F inferInstance
  rw [← IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal A) bot_ne_top]
  exact IsArtinianRing.isNilpotent_jacobson_bot

end Lemmata.Centroid.General

namespace Lemmata.Centroid.Tensor.BalancedAlgebra

variable {F A : Type*} [Field F] [CommRing A] [Algebra F A] [FiniteDimensional F A]
variable {V : Fin 3 → Type*} [∀ i, Fintype (V i)]
variable (T : Tensor F (Fin 3) V) (hT : Concise T)
variable (f : A →ₐ[F] centroidAlgebra T hT)

theorem split_algebra_support_bound (hf : Function.Injective f) (I : Ideal A)
    (hI : IsNilpotent I) (he : Module.finrank F (A ⧸ I) = 1) (N : ℕ)
    (hformat : ∀ i, Fintype.card (V i) ≤ N) :
    Module.finrank F A ≤ supportBound N + 1 := by
  have hsplit := General.ideal_dimension_split (F := F) I
  rw [he] at hsplit
  by_cases hzero : I * I = ⊥
  · have hz : I ^ 2 = 0 := by simpa only [pow_two, Ideal.zero_eq_bot] using hzero
    have h := square_zero_centroid_support_bound hT (idealSpace_le T hT f I)
      (idealSpace_square_zero T hT f I hz) N hformat
    rw [idealSpace_finrank T hT f hf I] at h
    omega
  · have h := higher_radical_bound T hT f hf I hI hzero N hformat
    have hG := General.generalBound_le_support_succ N
    omega

theorem split_algebra_dimension_bound (hf : Function.Injective f) (I : Ideal A)
    (hI : IsNilpotent I) (he : Module.finrank F (A ⧸ I) = 1) (N : ℕ)
    (hN : 0 < N) (hformat : ∀ i, Fintype.card (V i) = N) :
    Module.finrank F A ≤ generalBound N := by
  by_cases hzero : I * I = ⊥
  · apply square_zero_algebra_dimension_bound T hT f hf I _ he N hN hformat
    simpa only [pow_two, Ideal.zero_eq_bot] using hzero
  · have h := higher_radical_bound T hT f hf I hI hzero N (fun i => (hformat i).le)
    have hsplit := General.ideal_dimension_split (F := F) I
    rw [he] at hsplit
    have hG : 0 < generalBound N := hN.trans_le (General.le_generalBound N)
    omega

variable [IsLocalRing A]

theorem local_algebra_cost_bound (hf : Function.Injective f)
    (hformat : ∀ i, 0 < Fintype.card (V i)) :
    General.dimensionCost (Module.finrank F A) ≤
      ((Fintype.card (V 0) : ℝ) + Fintype.card (V 1) + Fintype.card (V 2)) / 3 := by
  let I := IsLocalRing.maximalIdeal A
  have hI : IsNilpotent I := General.local_maximalIdeal_nilpotent (F := F)
  have hepos := General.residue_dimension_pos (F := F) I
  by_cases he : Module.finrank F (A ⧸ I) = 1
  · exact split_algebra_cost_bound T hT f hf I hI he hformat
  · exact nonsplit_algebra_cost_bound T hT f hf I hI (by omega) hformat

theorem local_algebra_support_bound (hf : Function.Injective f) (N : ℕ)
    (hformat : ∀ i, 0 < Fintype.card (V i)) (hN : ∀ i, Fintype.card (V i) ≤ N) :
    Module.finrank F A ≤ supportBound N + 1 := by
  let I := IsLocalRing.maximalIdeal A
  have hI : IsNilpotent I := General.local_maximalIdeal_nilpotent (F := F)
  have hepos := General.residue_dimension_pos (F := F) I
  by_cases he : Module.finrank F (A ⧸ I) = 1
  · exact split_algebra_support_bound T hT f hf I hI he N hN
  · exact (nonsplit_algebra_dimension_bound T hT f hf I hI (by omega) N hformat hN).trans
      (General.generalBound_le_support_succ N)

theorem local_algebra_dimension_bound (hf : Function.Injective f) (N : ℕ)
    (hN : 0 < N) (hformat : ∀ i, Fintype.card (V i) = N) :
    Module.finrank F A ≤ generalBound N := by
  let I := IsLocalRing.maximalIdeal A
  have hI : IsNilpotent I := General.local_maximalIdeal_nilpotent (F := F)
  have hepos := General.residue_dimension_pos (F := F) I
  by_cases he : Module.finrank F (A ⧸ I) = 1
  · exact split_algebra_dimension_bound T hT f hf I hI he N hN hformat
  · exact nonsplit_algebra_dimension_bound T hT f hf I hI (by omega) N
      (fun i => (hformat i).symm ▸ hN) (fun i => (hformat i).le)

end Lemmata.Centroid.Tensor.BalancedAlgebra
