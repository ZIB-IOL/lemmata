module

public import Lemmata.CocubicCovering.Proof.Seeds
public meta import Lemmata.CocubicCovering.Proof.Seeds
public import Lemmata.CocubicCovering.Proof.Extension
public meta import Lemmata.CocubicCovering.Proof.Extension

@[expose] public section

set_option Elab.async false

namespace Lemmata.CocubicCovering.CoveringGeneral

open Covering CoveringSeeds CoveringExtension Module

theorem hasWitness_add_three {m : ℕ} (hm : 4 ≤ m) (hw : HasWitness m) :
    HasWitness (m + 3) := by
  obtain ⟨f, e, hf, he, hproduct, hinjective, hrank⟩ := hw
  refine ⟨extendedFunction f, (liftLinear m).comp e, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Nat.add_sub_cancel] using extendedFunction_mem (by omega) hf
  · intro q
    exact lift_reedMuller (he q)
  · intro q
    simpa only [LinearMap.comp_apply, show m + 3 - 2 = m + 1 by omega] using
      lifted_admissibility (by omega) (he q) (hproduct q)
  · intro h hh
    rw [show m + 3 - 4 = m - 1 by omega] at hh
    exact affineSupport_injective_lift hm f hf hinjective h hh
  · intro h hh
    rw [show m + 3 - 4 = m - 1 by omega] at hh
    exact rank_bound_lift hm f e hrank h hh

theorem hasWitness_of_ge_nine : ∀ m : ℕ, 9 ≤ m → HasWitness m := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro hm
    by_cases hsmall : m < 12
    · have hcases : m = 9 ∨ m = 10 ∨ m = 11 := by omega
      rcases hcases with rfl | rfl | rfl
      · exact hasWitness9
      · exact hasWitness10
      · exact hasWitness11
    · have hprevious : HasWitness (m - 3) := ih (m - 3) (by omega) (by omega)
      have hnext := hasWitness_add_three (by omega : 4 ≤ m - 3) hprevious
      simpa only [Nat.sub_add_cancel (by omega : 3 ≤ m)] using hnext

theorem witness_weight_lower_bound {m : ℕ} (hm : 4 ≤ m) (hw : HasWitness m) :
    ∃ f ∈ reedMuller m (m - 3),
      ∀ h ∈ reedMuller m (m - 4), 2 * m + 12 ≤ weight (f + h) := by
  obtain ⟨f, e, hf, he, hproduct, hinjective, hrank⟩ := hw
  refine ⟨f, hf, ?_⟩
  intro h hh
  have hdim := affineOnSupport_finrank_of_injective (f + h) (hinjective h hh)
  have hgram := hrank h hh
  have hweight := weight_bound_of_correction hm f h hf hh e he hproduct
  omega

theorem cocubic_coset_lower_bound (m : ℕ) (hm : 9 ≤ m) :
    ∃ f ∈ reedMuller m (m - 3), 2 * m + 12 ≤ cosetMinimum (m - 4) f := by
  obtain ⟨f, hf, hweight⟩ :=
    witness_weight_lower_bound (by omega) (hasWitness_of_ge_nine m hm)
  exact ⟨f, hf, le_cosetMinimum_iff.mpr hweight⟩

theorem coveringRadius_ge_two_mul_add_twelve (m : ℕ) (hm : 9 ≤ m) :
    2 * m + 12 ≤ coveringRadius m (m - 4) (m - 3) := by
  obtain ⟨f, hf, hcoset⟩ := cocubic_coset_lower_bound m hm
  exact hcoset.trans (cosetMinimum_le_coveringRadius hf)

end Lemmata.CocubicCovering.CoveringGeneral
