module

public import Lemmata.CGBasics.Vanilla

@[expose] public section

/-!
# Iterates as combinations of the first iterate (Proposition 2.9)

The weight on `x₁` after the steps `γ₁, …, γ_{T-1}` is `P = ∏ (1 - γ_t)`; the remaining weight
`1 - P` sits on a convex combination of the atoms.
-/

namespace Lemmata.CGBasics

open Lemmata.FrankWolfe

universe u

namespace Proof

theorem fixed_step_decomposition : FixedStepDecomposition.{u} := by
  intro E _ _ C x v γ hCc hx0 hrun T hT
  have hxC := iterates_mem hCc hx0 hrun
  induction T, hT using Nat.le_induction with
  | base => exact ⟨x 1, hxC 1, by simp⟩
  | succ T hT ih =>
    obtain ⟨y, hy, hxT⟩ := ih
    set P := ∏ t ∈ Finset.Ico 1 T, (1 - γ t) with hP
    have hP' : ∏ t ∈ Finset.Ico 1 (T + 1), (1 - γ t) = P * (1 - γ T) :=
      Finset.prod_Ico_succ_top hT _
    have hP0 : 0 ≤ P := Finset.prod_nonneg (fun t _ => by linarith [(hrun t).2.1.2])
    have hP1 : P ≤ 1 := Finset.prod_le_one₀ (fun t _ => by linarith [(hrun t).2.1.2])
      (fun t _ => by linarith [(hrun t).2.1.1])
    obtain ⟨hvC, ⟨hγ0, hγ1⟩, hx'⟩ := hrun T
    rw [hP']
    set w := 1 - P * (1 - γ T) with hw
    have hwe : w = (1 - γ T) * (1 - P) + γ T := by rw [hw]; ring
    have hw0 : 0 ≤ w := by rw [hwe]; nlinarith
    rcases eq_or_lt_of_le hw0 with hwz | hwpos
    · have hγz : γ T = 0 := by nlinarith
      have hPz : P = 1 := by
        rw [hγz] at hwe
        nlinarith
      refine ⟨x 1, hxC 1, ?_⟩
      rw [hx', hγz, zero_smul, add_zero, hxT, ← hwz, hPz]
      simp
    · refine ⟨((1 - γ T) * (1 - P) / w) • y + (γ T / w) • v T,
        hCc hy hvC (by positivity) (by positivity) (by field_simp; linarith), ?_⟩
      have e1 : w * ((1 - γ T) * (1 - P) / w) = (1 - γ T) * (1 - P) :=
        mul_div_cancel₀ _ hwpos.ne'
      have e2 : w * (γ T / w) = γ T := mul_div_cancel₀ _ hwpos.ne'
      rw [smul_add, smul_smul, smul_smul, e1, e2, hx', hxT]
      module

end Proof

end Lemmata.CGBasics
