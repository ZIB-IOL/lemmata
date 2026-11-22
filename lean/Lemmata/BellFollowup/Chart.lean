module

/- The finite-product reindexing in sumFour adapts the tuple equivalence from
   the Apache-2.0 SymmetricBellCrossPolytope entry by Ma and Zhang. -/

public import Lemmata.BellFollowup.Projection
public import Lemmata.BellFollowup.Facets.Main

@[expose] public section
noncomputable section
open Set BigOperators
namespace Lemmata.BellFollowup

open SymmetricBellCrossPolytope BellFollowup.Facets

/-- Expand a linear statistic on the four-setting tensor into its 64 entries. -/
private theorem sumFour (f : FourIndex → ℝ) :
    ∑ x, f x = ∑ i : Fin 4, ∑ j : Fin 4, ∑ k : Fin 4, f ![i,j,k] := by
  let e : FourIndex ≃ (Fin 4 × Fin 4 × Fin 4) := (tensorTowerTupleEquiv (Fin 4) 2).symm
  have h : ∑ x, f x = ∑ t : Fin 4 × Fin 4 × Fin 4, f ![t.1,t.2.1,t.2.2] := by
    apply Fintype.sum_equiv e
    intro x
    congr 1
    funext n
    fin_cases n <;> rfl
  rw [h, Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]

private theorem inner_expr (p : V) (r : Fin 2) :
    inner ℝ p (fourBasis r) =
      ∑ i : Fin 4, ∑ j : Fin 4, ∑ k : Fin 4, (fourCoeff r ![i,j,k] : ℝ) * p ![i,j,k] := by
  rw [PiLp.inner_apply]
  simp only [fourBasis,PiLp.toLp_apply,RCLike.inner_apply,conj_trivial]
  exact sumFour _

private theorem inner0 (p : V) : inner ℝ p (fourBasis 0) = d0 p := by
  rw [inner_expr]
  norm_num [Fin.sum_univ_four, fourCoeff, d0, block000, block011, block101, block110,
    mermin, entry_apply]
  ring

private theorem inner1 (p : V) : inner ℝ p (fourBasis 1) = d13 p := by
  rw [inner_expr]
  norm_num [Fin.sum_univ_four, fourCoeff, d13, entry_apply]
  ring

/-- The two signed sums are invariant under the archive's orthogonal projection. -/
theorem chart_project (p : V) : chart (Gamma 3 4 p) = chart p := by
  apply Prod.ext
  · exact (inner0 _).symm.trans ((four_inner_project 0 p).trans (inner0 _))
  · exact (inner1 _).symm.trans ((four_inner_project 1 p).trans (inner1 _))

/-- Reconstruct the fixed tensor from its two signed sums. -/
def reconstruct : (ℝ × ℝ) →L[ℝ] V :=
  ((1/16 : ℝ) • (ContinuousLinearMap.fst ℝ ℝ ℝ)).smulRight (fourBasis 0) +
  ((1/32 : ℝ) • (ContinuousLinearMap.snd ℝ ℝ ℝ)).smulRight (fourBasis 1)

private theorem gram : d0 (fourBasis 0) = 16 ∧ d0 (fourBasis 1) = 0 ∧
    d13 (fourBasis 0) = 0 ∧ d13 (fourBasis 1) = 32 := by
  norm_num [d0, block000, block011, block101, block110, mermin, d13, entry_apply, fourBasis, fourCoeff]

private theorem back_fixed (q : V) (hq : q ∈ symSub 3 4) :
    reconstruct (chart q) = q := by
  obtain ⟨h00,h01,h10,h11⟩ := gram
  have h := four_fixed_expansion q hq
  have u := congrArg d0 h
  have v := congrArg d13 h
  simp only [map_add, map_smul, smul_eq_mul, h00,h01,h10,h11,mul_zero,add_zero,zero_add] at u v
  change ((1/16 : ℝ) * d0 q) • fourBasis 0 + ((1/32 : ℝ) * d13 q) • fourBasis 1 = q
  rw [u,v]
  have a : (1/16:ℝ)*(q (rep 0)*16) = q (rep 0) := by ring
  have b : (1/32:ℝ)*(q (rep 1)*32) = q (rep 1) := by ring
  rw [a,b]
  exact h.symm

theorem reconstruct_chart (p : V) : reconstruct (chart p) = Gamma 3 4 p := by
  rw [← chart_project p]
  exact back_fixed _ ((symSub 3 4).starProjection_apply_mem p)

end Lemmata.BellFollowup
