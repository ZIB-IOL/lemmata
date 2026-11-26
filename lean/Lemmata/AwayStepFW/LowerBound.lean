module

public import Lemmata.AwayStepFW.PyramidalEq

@[expose] public section

/-!
# A lower bound on the pyramidal width from inequalities (Corollary 2.32, corrected)

For a proper face `F` and the rows `I` of an inequality system that are tight on `F`, the summed row
`Ψ = ∑_{i ∈ I} a_i` equals `∑_{i ∈ I} b_i` on `conv F` and is smaller by at least the minimal total
slack `m` on the convex hull of the other vertices. Hence the face is at distance at least `m /
‖Ψ‖`.
-/

namespace Lemmata.AwayStepFW

open Lemmata.FrankWolfe

namespace Proof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
theorem lowerBound_le_facialDistance [FiniteDimensional ℝ E] (V : Finset E) {ι : Type} [Fintype ι]
    (a : ι → StrongDual ℝ E) (b : ι → ℝ) (hprop : ∃ ψ : StrongDual ℝ E, exposedFace V ψ ≠ V)
    (hfeas : ∀ v ∈ V, ∀ i, a i v ≤ b i)
    (hcut : ∀ ψ : StrongDual ℝ E, exposedFace V ψ ≠ V → ∀ v ∈ V \ exposedFace V ψ,
      ∃ i, (∀ w ∈ exposedFace V ψ, a i w = b i) ∧ a i v < b i) :
    sInf {r : ℝ | ∃ I : Finset ι, ∃ w ∈ V, (∀ i ∈ I, a i w = b i) ∧ ∃ v ∈ V,
      0 < ∑ i ∈ I, (b i - a i v) ∧ r = (∑ i ∈ I, (b i - a i v)) / ‖∑ i ∈ I, a i‖} ≤
      facialDistance V := by
  set X := {r : ℝ | ∃ I : Finset ι, ∃ w ∈ V, (∀ i ∈ I, a i w = b i) ∧ ∃ v ∈ V,
      0 < ∑ i ∈ I, (b i - a i v) ∧ r = (∑ i ∈ I, (b i - a i v)) / ‖∑ i ∈ I, a i‖} with hX
  have hXbdd : BddBelow X :=
    ⟨0, fun r ⟨_, _, _, _, _, _, hpos, hr⟩ => hr ▸ div_nonneg hpos.le (norm_nonneg _)⟩
  obtain ⟨ψ0, hψ0⟩ := hprop
  have hV : V.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    exact hψ0 (by rw [h]; exact Finset.subset_empty.mp (h ▸ exposedFace_subset _ ψ0))
  unfold facialDistance
  obtain ⟨p0, hp0⟩ := exposedFace_nonempty hV ψ0
  obtain ⟨q0, hq0⟩ : (V \ exposedFace V ψ0).Nonempty :=
    Finset.sdiff_nonempty.mpr (fun h => hψ0 (Finset.Subset.antisymm (exposedFace_subset V ψ0) h))
  refine le_csInf ⟨_, ψ0, hψ0, p0, subset_convexHull ℝ _ (by exact_mod_cast hp0), q0,
    subset_convexHull ℝ _ (by exact_mod_cast hq0), rfl⟩ ?_
  rintro r ⟨ψ, hψ, p, hp, q, hq, rfl⟩
  set F := exposedFace V ψ with hF
  set I := Finset.univ.filter (fun i => ∀ w ∈ F, a i w = b i) with hI
  set Ψ : StrongDual ℝ E := ∑ i ∈ I, a i with hΨ
  set β := ∑ i ∈ I, b i with hβ
  have hΨapp : ∀ z : E, Ψ z = ∑ i ∈ I, a i z := fun z => by
    simp only [hΨ, FunLike.coe_sum, Finset.sum_apply]
  have hslack : ∀ v ∈ V \ F, 0 < ∑ i ∈ I, (b i - a i v) := by
    intro v hv
    obtain ⟨i, hiT, hilt⟩ := hcut ψ hψ v hv
    have hiI : i ∈ I := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hiT⟩
    exact Finset.sum_pos' (fun j _ => sub_nonneg.mpr (hfeas v (Finset.mem_sdiff.mp hv).1 j))
      ⟨i, hiI, sub_pos.mpr hilt⟩
  have hne : (V \ F).Nonempty :=
    Finset.sdiff_nonempty.mpr (fun h => hψ (Finset.Subset.antisymm (exposedFace_subset V ψ) h))
  obtain ⟨vmin, hvmin, hmin⟩ := (V \ F).exists_min_image (fun v => ∑ i ∈ I, (b i - a i v)) hne
  set m := ∑ i ∈ I, (b i - a i vmin) with hm
  have hmpos : 0 < m := hslack vmin hvmin
  have hΨp : Ψ p = β := by
    have hsub : (↑F : Set E) ⊆ {z | Ψ z = β} := fun w hw => by
      show Ψ w = β
      rw [hΨapp]
      exact Finset.sum_congr rfl (fun i hi => (Finset.mem_filter.mp hi).2 w hw)
    exact convexHull_min hsub (convex_hyperplane Ψ.toLinearMap.isLinear β) hp
  have hΨq : Ψ q ≤ β - m := by
    have hsub : (↑(V \ F) : Set E) ⊆ {z | Ψ z ≤ β - m} := fun v hv => by
      show Ψ v ≤ β - m
      have := hmin v hv
      rw [hΨapp]
      have e : ∑ i ∈ I, a i v = β - ∑ i ∈ I, (b i - a i v) := by
        rw [hβ, Finset.sum_sub_distrib]; ring
      linarith
    exact convexHull_min hsub (convex_halfSpace_le Ψ.toLinearMap.isLinear _) hq
  have hgap : m ≤ Ψ (p - q) := by rw [map_sub]; linarith
  have hop : Ψ (p - q) ≤ ‖Ψ‖ * ‖p - q‖ :=
    (le_abs_self _).trans (by rw [← Real.norm_eq_abs]; exact Ψ.le_opNorm _)
  have hΨpos : 0 < ‖Ψ‖ := by
    rcases eq_or_lt_of_le (norm_nonneg Ψ) with h | h
    · rw [← h, zero_mul] at hop; linarith
    · exact h
  obtain ⟨w0, hw0⟩ := exposedFace_nonempty hV ψ
  have hmem : m / ‖Ψ‖ ∈ X := ⟨I, w0, exposedFace_subset V ψ hw0,
    fun i hi => (Finset.mem_filter.mp hi).2 w0 hw0, vmin, (Finset.mem_sdiff.mp hvmin).1, hmpos, rfl⟩
  refine (csInf_le hXbdd hmem).trans ?_
  rw [div_le_iff₀ hΨpos]
  linarith
end Proof

end Lemmata.AwayStepFW
