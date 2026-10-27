module

public import Lemmata.CocubicCovering.Compute.CoreSearchSound
public meta import Lemmata.CocubicCovering.Compute.CoreSearchSound
public import Lemmata.CocubicCovering.Compute.SystemInputs
public meta import Lemmata.CocubicCovering.Compute.SystemInputs
public import Lemmata.CocubicCovering.Proof.SystemGeometry
public meta import Lemmata.CocubicCovering.Proof.SystemGeometry

@[expose] public section

namespace Lemmata.CocubicCovering.Compute.Terminal

open Lemmata.CocubicCovering
open Module CoveringBits CoveringWitness CoveringPackedWitness CoveringPolynomial
open CoveringLevelSixReconstruction CoveringSystemGeometryData

def SystemsInconsistent : Prop :=
  ∀ system : Fin 13, ¬ ∃ assignment : Nat → Field, ∀ row : Fin 87,
    CoveringIdeal.eval assignment (CoveringLevelSixSystems.input system row) = 0

theorem coreSpace_finrank (s : Fin 13) : finrank Field (coreSpace s) = coreCount s := by
  have independent := (familyLinear_injective_iff (combinedVector s)).mp (combined_injective s)
  have part := (linearIndependent_sum.mp independent).1
  have basisIndependent : LinearIndependent Field (coreVector s) := by
    simpa only [combinedVector, Function.comp_def, Sum.elim_inl] using part
  change finrank Field (Submodule.span Field (Set.range (coreVector s))) = coreCount s
  exact (finrank_span_eq_card basisIndependent).trans (Fintype.card_fin _)

theorem no_profile (inconsistent : SystemsInconsistent) (s : Fin 13) (v : Vector 127)
    (point : v (Fin.last 126) = 1)
    (coordinates : ∀ i : Fin 15, v ⟨111 + i.val, by omega⟩ =
      ofBool ((restriction s).testBit i.val))
    (dimension : finrank Field (CoveringLevelSixReduction.fullKernel v) = coreCount s)
    (contained : familySpan (decoded (n := 12) (core s).get) ≤
      CoveringLevelSixReduction.fullKernel v)
    (rank : finrank Field (LinearMap.range (CoveringLevelSixReduction.fullForm v)) ≤ 10) : False := by
  have inclusion : coreSpace s ≤ W ⊓ LinearMap.ker (CoveringLevelSixReduction.fullForm v) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    refine ⟨core_mem_W s i, ?_⟩
    have kernelMembership : (decodeMask (coreMask s i) : Vector 12) ∈
        CoveringLevelSixReduction.fullKernel v :=
      contained (Submodule.subset_span ⟨i, rfl⟩)
    change CoveringLevelSixReduction.fullForm v
      (CoveringLevelSixReduction.localEmbedding (decodeMask (coreMask s i))) = 0 at kernelMembership
    change CoveringLevelSixReduction.fullForm v (coreVector s i) = 0
    simpa only [embedding_mask, coreVector] using kernelMembership
  have intersectionDimension : finrank Field
      (W ⊓ LinearMap.ker (CoveringLevelSixReduction.fullForm v) : Submodule Field (Vector 27)) =
        coreCount s :=
    (CoveringLevelSixReduction.fullKernel_finrank v).trans dimension
  have intersection : W ⊓ LinearMap.ker (CoveringLevelSixReduction.fullForm v) = coreSpace s :=
    (Submodule.eq_of_le_of_finrank_eq inclusion
      ((coreSpace_finrank s).trans intersectionDimension.symm)).symm
  exact inconsistent s
    (CoveringSystemGeometry.exists_input_solution s v point coordinates intersection rank)

structure Interpretation (model : CoreSearch.Model) : Prop where
  kernel : model.kernel = CoveringLevelSixReduction.fullKernel
  coordinates : ∀ root v, model.allowed root v → ∀ i : Fin 15,
    v ⟨111 + i.val, by omega⟩ = ofBool ((model.roots root).assignment.testBit i.val)
  dimension : ∀ root v, model.allowed root v →
    finrank Field (model.kernel v) = (model.roots root).required
  rank : ∀ root v, model.allowed root v →
    finrank Field (LinearMap.range (CoveringLevelSixReduction.fullForm v)) ≤ 10
  inconsistent : ∀ root v, model.allowed root v → SystemsInconsistent

def close (model : CoreSearch.Model) (interpretation : Interpretation model)
    (state : CoreSearch.State) : Option (CoreSearch.Closed model state) := do
  for profile in List.finRange 13 do
    if assignment : (model.roots state.root).assignment = restriction profile then
      if dimension : (model.roots state.root).required = coreCount profile then
        if let some coefficients := CoreSearch.coefficients (core profile) state.core then
          if span : Certificate.CoreCertificate.listCheckSpan (core profile) state.core coefficients = true then
            return ⟨by
              rintro ⟨v, allowed, contained⟩
              have profileContained := Certificate.CoreCertificate.listCheckSpan_eq
                (core profile) state.core coefficients
              rw [profileContained] at span
              apply no_profile (interpretation.inconsistent state.root v allowed) profile v
                (model.point state.root v allowed)
              · simpa only [← assignment] using interpretation.coordinates state.root v allowed
              · rw [← interpretation.kernel, ← dimension]
                exact interpretation.dimension state.root v allowed
              · rw [← interpretation.kernel]
                exact (listCheckSpan_sound 12 _ _ _ span).trans contained
              · exact interpretation.rank state.root v allowed⟩
  return ← none

end Lemmata.CocubicCovering.Compute.Terminal
