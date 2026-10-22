module

public import Lemmata.Centroid.Proof.GeneralMax
public import Lemmata.Centroid.Proof.General.BlockRepresentations
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public section

open scoped BigOperators
open Classical

noncomputable section

local instance finDecidableEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

namespace Lemmata.Centroid.Tensor.CRT

variable {F : Type*} [Field F] {V : Fin 3 → Type*} [∀ i, Fintype (V i)]
variable (T : Tensor F (Fin 3) V) (hT : Concise T)

abbrev Algebra := centroidAlgebra T hT
abbrev Spectrum := MaximalSpectrum (Algebra T hT)
abbrev Factor (m : Spectrum T hT) := Linear.LocalComponent (Algebra T hT) m

instance algebraArtinian : IsArtinianRing (Algebra T hT) := centroid_artinian T hT

instance spectrumFintype : Fintype (Spectrum T hT) := Fintype.ofFinite _

instance factorFinite (m : Spectrum T hT) : Module.Finite F (Factor T hT m) :=
  Module.Finite.of_surjective
    (Ideal.Quotient.mkₐ F (m.asIdeal ^ Linear.localExponent (Algebra T hT))).toLinearMap
    Ideal.Quotient.mk_surjective

def equivalence : Algebra T hT ≃ₐ[F] ∀ m, Factor T hT m := centroidLocalDecomposition T hT

abbrev size (m : Spectrum T hT) (i : Fin 3) : ℕ :=
  General.TensorBlocks.blockSize (equivalence T hT) (centroidRepresentation T hT) m i

def tensor (m : Spectrum T hT) : Tensor F (Fin 3) (fun i => Fin (size T hT m i)) :=
  General.TensorBlocks.blockTensor (equivalence T hT) (centroidRepresentation T hT) T m

theorem balanced (a : Algebra T hT) :
    General.TensorBlocks.algebraMatrices (centroidRepresentation T hT) a ∈ centroid T := by
  have h : General.TensorBlocks.algebraMatrices (centroidRepresentation T hT) a = a.val := by
    funext i
    change LinearMap.toMatrix' (Matrix.toLin' (a.val i)) = a.val i
    exact LinearMap.toMatrix'_toLin' _
  rw [h]
  exact a.property

theorem concise (m : Spectrum T hT) : Concise (tensor T hT m) :=
  General.TensorBlocks.blockTensor_concise (equivalence T hT)
    (centroidRepresentation T hT) hT (balanced T hT) m

theorem size_pos (m : Spectrum T hT) (i : Fin 3) : 0 < size T hT m i :=
  General.TensorBlocks.blockSize_pos (equivalence T hT) (centroidRepresentation T hT)
    (centroidRepresentation_injective hT) m i

theorem sum_size (i : Fin 3) : ∑ m, size T hT m i = Fintype.card (V i) :=
  General.TensorBlocks.sum_blockSize (equivalence T hT) (centroidRepresentation T hT) i

def action (m : Spectrum T hT) : Factor T hT m →ₐ[F] centroidAlgebra (tensor T hT m) (concise T hT m) :=
  General.TensorBlocks.localCentroidHom (equivalence T hT)
    (centroidRepresentation T hT) hT (balanced T hT) m

theorem action_injective (m : Spectrum T hT) : Function.Injective (action T hT m) :=
  General.TensorBlocks.localCentroidHom_injective (equivalence T hT)
    (centroidRepresentation T hT) hT (balanced T hT)
    (centroidRepresentation_injective hT) m

theorem radical_nilpotent (m : Spectrum T hT) :
    IsNilpotent (IsLocalRing.maximalIdeal (Factor T hT m)) := by
  let : IsArtinianRing (Factor T hT m) := isArtinian_of_tower F inferInstance
  rw [← IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal (Factor T hT m)) bot_ne_top]
  exact IsArtinianRing.isNilpotent_jacobson_bot

theorem dimension_sum : Module.finrank F (centroid T) =
    ∑ m, Module.finrank F (Factor T hT m) := by
  have h := (equivalence T hT).toLinearEquiv.finrank_eq
  rw [Module.finrank_pi_fintype] at h
  exact ((centroidAlgebra T hT).toSubmoduleEquiv.finrank_eq).trans h

theorem centroid_dimension_sum : Module.finrank F (centroid T) =
    ∑ m, Module.finrank F (centroid (tensor T hT m)) :=
  General.TensorBlocks.finrank_centroid_eq_sum (equivalence T hT)
    (centroidRepresentation T hT) T hT (balanced T hT)

theorem factor_dimension_eq (m : Spectrum T hT) :
    Module.finrank F (Factor T hT m) = Module.finrank F (centroid (tensor T hT m)) := by
  have hle : ∀ m, Module.finrank F (Factor T hT m) ≤
      Module.finrank F (centroid (tensor T hT m)) := by
    intro m
    have h := LinearMap.finrank_le_finrank_of_injective
      (f := (action T hT m).toLinearMap) (action_injective T hT m)
    rwa [← (centroidAlgebra (tensor T hT m) (concise T hT m)).toSubmoduleEquiv.finrank_eq] at h
  have hs : (∑ m, Module.finrank F (Factor T hT m)) =
      ∑ m, Module.finrank F (centroid (tensor T hT m)) :=
    (dimension_sum T hT).symm.trans (centroid_dimension_sum T hT)
  by_contra hne
  have hlt : Module.finrank F (Factor T hT m) <
      Module.finrank F (centroid (tensor T hT m)) := by have := hle m; omega
  have hsum := Finset.sum_lt_sum (fun m (_ : m ∈ Finset.univ) => hle m)
    ⟨m, Finset.mem_univ _, hlt⟩
  omega

def actionEquiv (m : Spectrum T hT) :
    Factor T hT m ≃ₐ[F] centroidAlgebra (tensor T hT m) (concise T hT m) :=
  AlgEquiv.ofBijective (action T hT m) ⟨action_injective T hT m,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := (action T hT m).toLinearMap)
      ((factor_dimension_eq T hT m).trans
        (centroidAlgebra (tensor T hT m) (concise T hT m)).toSubmoduleEquiv.finrank_eq)).mp
      (action_injective T hT m)⟩

theorem centroid_isLocalRing (m : Spectrum T hT) :
    IsLocalRing (centroidAlgebra (tensor T hT m) (concise T hT m)) :=
  (actionEquiv T hT m).toRingEquiv.isLocalRing

end Lemmata.Centroid.Tensor.CRT
