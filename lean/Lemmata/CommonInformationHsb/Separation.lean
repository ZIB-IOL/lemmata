module

public import Lemmata.CommonInformationHsb.Blocks
public import Lemmata.CommonInformationHsb.Hsb

@[expose] public section

namespace Lemmata.CommonInformationHsb

open Filter
open scoped Topology

/-- With a fixed number of singleton blocks, the entropy of their block weights
converges to zero as the side length of the large block grows. -/
theorem tendsto_block_weight_entropy (r : ℕ) :
    Tendsto (fun S : ℕ =>
      Real.negMulLog ((S : ℝ)^2 / ((S : ℝ)^2 + r)) +
        (r : ℝ) * Real.negMulLog (1 / ((S : ℝ)^2 + r))) atTop (𝓝 0) := by
  have hmass : Tendsto (fun S : ℕ => (S : ℝ)^2 + r) atTop atTop := by
    apply tendsto_atTop_mono _ tendsto_natCast_atTop_atTop
    intro S
    have hs : (S : ℝ) ≤ (S : ℝ)^2 := by
      exact_mod_cast (Nat.le_self_pow (by decide : 2 ≠ 0) S)
    exact hs.trans (le_add_of_nonneg_right (Nat.cast_nonneg r))
  have hinv := hmass.const_div_atTop 1
  have hlarge : Tendsto (fun S : ℕ => (S : ℝ)^2 / ((S : ℝ)^2 + r))
      atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ))).sub (hinv.const_mul (r : ℝ))
    have heq : (fun S : ℕ => 1 - (r : ℝ) * (1 / ((S : ℝ)^2 + r))) =ᶠ[atTop]
        (fun S : ℕ => (S : ℝ)^2 / ((S : ℝ)^2 + r)) := by
      filter_upwards [eventually_ge_atTop 1] with S hS
      have hs : 0 < (S : ℝ) := by exact_mod_cast (by omega : 0 < S)
      have hm : (S : ℝ)^2 + r ≠ 0 := ne_of_gt (by positivity)
      field_simp
      ring
    simpa using h.congr' heq
  have h := (Real.continuous_negMulLog.tendsto 1).comp hlarge
  have h' := ((Real.continuous_negMulLog.tendsto 0).comp hinv).const_mul (r : ℝ)
  simpa using h.add h'

/-- The half-heavy entropy diverges even though its HSB value remains fixed. -/
theorem tendsto_heavy_entropy :
    Tendsto (fun N : ℕ => (Real.log 2 + Real.log N / 2) / Real.log 2) atTop atTop := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  exact (tendsto_const_nhds.add_atTop (hlog.atTop_div_const (by norm_num))).atTop_div_const
    (Real.log_pos (by norm_num))

/-- The common information in bits tends to zero for a fixed number of
singleton blocks. This uses scalar entropy continuity at zero and one. -/
theorem tendsto_block_commonInformation (r : ℕ) :
    Tendsto (fun S : ℕ => commonInformation (blockMatrix S r)) atTop (𝓝 0) := by
  have h := (tendsto_block_weight_entropy r).div_const (Real.log 2)
  have heq : (fun S : ℕ =>
      (Real.negMulLog ((S : ℝ)^2 / ((S : ℝ)^2 + r)) +
        (r : ℝ) * Real.negMulLog (1 / ((S : ℝ)^2 + r))) / Real.log 2) =ᶠ[atTop]
      (fun S : ℕ => commonInformation (blockMatrix S r)) := by
    filter_upwards [eventually_ge_atTop 1] with S hS
    rw [commonInformation, commonInformationNat_blockMatrix S r hS, entropy_blockWeights]
  simpa using h.congr' heq

/-- The two exact values for the half-heavy diagonal family. -/
theorem heavyDiagonal_values (N : ℕ) (hN : 1 ≤ N) :
    commonInformationNat (heavyDiagonal N) = Real.log 2 + Real.log N / 2 ∧
      hsb (heavyDiagonal N) = 2 :=
  ⟨commonInformationNat_heavyDiagonal N hN, hsb_heavyDiagonal N hN⟩

/-- The two exact values for the large-block plus singleton family. -/
theorem blockMatrix_values (S r : ℕ) (hS : 1 ≤ S) :
    commonInformationNat (blockMatrix S r) = entropy (blockWeights S r) ∧
      hsb (blockMatrix S r) = (r : ℝ) + 1 :=
  ⟨commonInformationNat_blockMatrix S r hS, hsb_blockMatrix S r hS⟩

/-- Common information is arbitrarily large while HSB is exactly two. -/
theorem exists_heavyDiagonal_separation (L : ℝ) :
    ∃ N : ℕ, 1 ≤ N ∧ L < commonInformation (heavyDiagonal N) ∧
      hsb (heavyDiagonal N) = 2 := by
  obtain ⟨N, hN, h⟩ := ((eventually_ge_atTop 1).and
    (tendsto_heavy_entropy.eventually_gt_atTop L)).exists
  refine ⟨N, hN, ?_, hsb_heavyDiagonal N hN⟩
  rwa [commonInformation, commonInformationNat_heavyDiagonal N hN]

/-- Logarithmic HSB is arbitrarily large while common information in bits is
arbitrarily small. The number of singleton blocks is chosen before the side length. -/
theorem exists_blockMatrix_separation (L ε : ℝ) (hε : 0 < ε) :
    ∃ r S : ℕ, 1 ≤ S ∧
      L < Real.log (hsb (blockMatrix S r)) / Real.log 2 ∧
      commonInformation (blockMatrix S r) < ε := by
  have hlog : Tendsto (fun r : ℕ => Real.log ((r : ℝ) + 1) / Real.log 2) atTop atTop :=
    (Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1 : ℝ))))).atTop_div_const
        (Real.log_pos (by norm_num))
  obtain ⟨r, hr⟩ := (hlog.eventually_gt_atTop L).exists
  obtain ⟨S, hS, hs⟩ := ((eventually_ge_atTop 1).and
    ((tendsto_block_commonInformation r).eventually_lt_const hε)).exists
  exact ⟨r, S, hS, by rwa [hsb_blockMatrix S r hS], hs⟩

/-- No polynomial-growth majorant in HSB can bound common information. -/
theorem commonInformation_exceeds_polynomial_hsb (a : ℝ) (d : ℕ) :
    ∃ N : ℕ, 1 ≤ N ∧
      a * (1 + hsb (heavyDiagonal N))^d < commonInformation (heavyDiagonal N) := by
  obtain ⟨N, hN, h, hh⟩ := exists_heavyDiagonal_separation (a * 3^d)
  refine ⟨N, hN, ?_⟩
  simpa only [hh, show (1 : ℝ) + 2 = 3 by norm_num] using h

/-- The same failure holds even when the proposed argument is logarithmic HSB. -/
theorem commonInformation_exceeds_polynomial_log_hsb (a : ℝ) (d : ℕ) :
    ∃ N : ℕ, 1 ≤ N ∧
      a * (1 + Real.log (hsb (heavyDiagonal N)) / Real.log 2)^d <
        commonInformation (heavyDiagonal N) := by
  obtain ⟨N, hN, h, hh⟩ := exists_heavyDiagonal_separation (a * 2^d)
  refine ⟨N, hN, ?_⟩
  have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  simpa only [hh, div_self hlog, show (1 : ℝ) + 1 = 2 by norm_num] using h

/-- Conversely, no nonnegative polynomial-growth majorant in common information
can bound logarithmic HSB. This is a polynomial claim, not an arbitrary-function claim. -/
theorem log_hsb_exceeds_polynomial_commonInformation (a : ℝ) (ha : 0 ≤ a) (d : ℕ) :
    ∃ r S : ℕ, 1 ≤ S ∧
      a * (1 + commonInformation (blockMatrix S r))^d <
        Real.log (hsb (blockMatrix S r)) / Real.log 2 := by
  obtain ⟨r, S, hS, hlarge, hsmall⟩ := exists_blockMatrix_separation (a * 2^d) 1 (by norm_num)
  have hn := commonInformation_nonneg (blockMatrix_nonneg S r) (matrixMass_blockMatrix_pos S r hS)
  have hp : (1 + commonInformation (blockMatrix S r))^d ≤ (2 : ℝ)^d :=
    pow_le_pow_left₀ (by linarith) (by linarith) d
  exact ⟨r, S, hS, (mul_le_mul_of_nonneg_left hp ha).trans_lt hlarge⟩

end Lemmata.CommonInformationHsb
