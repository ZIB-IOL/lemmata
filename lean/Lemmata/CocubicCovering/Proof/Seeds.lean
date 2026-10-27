module

public import Lemmata.CocubicCovering.Proof.RankTen
public meta import Lemmata.CocubicCovering.Proof.RankTen
public import Lemmata.CocubicCovering.Proof.Realization
public meta import Lemmata.CocubicCovering.Proof.Realization
public import Lemmata.CocubicCovering.Proof.Ambient
public meta import Lemmata.CocubicCovering.Proof.Ambient

@[expose] public section

set_option Elab.async false

namespace Lemmata.CocubicCovering.CoveringSeeds

open Covering Module CoveringCongruence CoveringCovarianceData

def HasWitness (m : ℕ) : Prop :=
  ∃ f : BooleanFunction m, ∃ e : Vector 24 →ₗ[Field] BooleanFunction m,
    f ∈ reedMuller m (m - 3) ∧
    (∀ q, e q ∈ reedMuller m 2) ∧
    (∀ q, e q * f ∈ reedMuller m (m - 2)) ∧
    (∀ h ∈ reedMuller m (m - 4),
      Function.Injective ((restrictSupport (f + h)).comp (affineFunctionLinear m))) ∧
    (∀ h ∈ reedMuller m (m - 4),
      10 ≤ finrank Field (LinearMap.range (supportGram (f + h) e)))

theorem hasWitness9 : HasWitness 9 := by
  refine ⟨eval form9, CoveringEmbedding.multiplierLinear, form9_mem,
    CoveringEmbedding.multiplierLinear_mem, CoveringEmbedding.multiplierLinear_products,
    ?_, ?_⟩
  · intro h hh
    apply affineSupport_injective (by decide) cubic9 h hh
    · exact ⟨⟨{0, 3, 6}, by decide⟩, by native_decide⟩
    · exact cubic9_contraction_injective
  · intro h hh
    obtain ⟨v, hv, hgram⟩ := CoveringRealization.exists_pointed_realization h hh
    have hr := CoveringRankTen.rank_at_least_ten v hv
    have he := congrArg (fun B : LinearMap.BilinForm Field (Vector 24) =>
      finrank Field (LinearMap.range B)) hgram
    exact hr.trans_eq he.symm

theorem hasWitness10 : HasWitness 10 := by
  refine ⟨eval form10, CoveringAmbient.multiplierLinear 0, form10_mem,
    CoveringAmbient.multiplierLinear_mem 0, CoveringAmbient.multiplierLinear_products 0,
    ?_, ?_⟩
  · intro h hh
    apply affineSupport_injective (by decide) cubic10 h hh
    · exact ⟨⟨{0, 3, 6}, by decide⟩, by native_decide⟩
    · exact cubic10_contraction_injective
  · intro h hh
    obtain ⟨v, hv, hgram⟩ := CoveringAmbient.exists_pointed_realization 0 h hh
    have hr := CoveringRankTen.rank_at_least_ten v hv
    have he := congrArg (fun B : LinearMap.BilinForm Field (Vector 24) =>
      finrank Field (LinearMap.range B)) hgram
    exact hr.trans_eq he.symm

theorem hasWitness11 : HasWitness 11 := by
  refine ⟨eval form11, CoveringAmbient.multiplierLinear 1, form11_mem,
    CoveringAmbient.multiplierLinear_mem 1, CoveringAmbient.multiplierLinear_products 1,
    ?_, ?_⟩
  · intro h hh
    apply affineSupport_injective (by decide) cubic11 h hh
    · exact ⟨⟨{0, 3, 6}, by decide⟩, by native_decide⟩
    · exact cubic11_contraction_injective
  · intro h hh
    obtain ⟨v, hv, hgram⟩ := CoveringAmbient.exists_pointed_realization 1 h hh
    have hr := CoveringRankTen.rank_at_least_ten v hv
    have he := congrArg (fun B : LinearMap.BilinForm Field (Vector 24) =>
      finrank Field (LinearMap.range B)) hgram
    exact hr.trans_eq he.symm

end Lemmata.CocubicCovering.CoveringSeeds
