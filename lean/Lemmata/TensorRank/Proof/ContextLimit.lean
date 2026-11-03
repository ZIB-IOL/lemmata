module

/-
Copyright (c) 2026 Kirill Khoruzhii. Licensed under Apache-2.0.
Modified for the arbitrary-field tensor-rank formalization; namespace and imports
adapted for Lemmata. See docs/tensor-rank/NOTICE.txt for upstream attribution
and modification notices, and docs/tensor-rank/LICENSE.txt for the license.
-/

public import Lemmata.TensorRank.Proof.ContextTransport
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Order.Filter.AtTopBot.Archimedean
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

@[expose] public section

set_option autoImplicit false

open Filter
open scoped Topology

namespace Lemmata.TensorRank.Tensor

variable {𝕜 : Type*} [Field 𝕜] {I : Type} [Fintype I]
variable {V W : I → Type} [∀ i, Fintype (V i)] [∀ i, Fintype (W i)]

theorem le_of_polynomial_power_bounds (a b A : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (d : ℕ) (hA : 0 < A)
    (H : ∀ q : ℕ, 0 < q → a ^ q ≤ A * ((q : ℝ) + 1) ^ d * b ^ q) :
    a ≤ b := by
  by_contra hab
  have hba : b < a := lt_of_not_ge hab
  have ha' : 0 < a := hb.trans_lt hba
  have hb' : 0 < b := by
    by_contra hb'
    have hb0 : b = 0 := le_antisymm (le_of_not_gt hb') hb
    have h1 := H 1 (by decide)
    simp only [pow_one, hb0, mul_zero] at h1
    exact ha'.not_ge h1
  have hgap : 0 < Real.log a - Real.log b := sub_pos.mpr (Real.log_lt_log hb' hba)
  have hl : Tendsto (fun q : ℕ =>
      ((d : ℝ) * Real.log ((q : ℝ) + 1) + Real.log A) / q) atTop (𝓝 0) := by
    have hnr : Tendsto (fun q : ℕ => (q : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    have hn1 := tendsto_atTop_add_const_right atTop 1 hnr
    have hlog : Tendsto (fun q : ℕ => Real.log ((q : ℝ) + 1) / q) atTop (𝓝 0) := by
      have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero).comp hn1
      simpa only [Function.comp_def, pow_one, one_mul, add_neg_cancel_right] using h
    have hconst : Tendsto (fun q : ℕ => Real.log A / (q : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hnr
    have hs : Tendsto (fun q : ℕ =>
        (d : ℝ) * (Real.log ((q : ℝ) + 1) / q) + Real.log A / q) atTop (𝓝 0) := by
      simpa using (hlog.const_mul (d : ℝ)).add hconst
    apply hs.congr
    intro q
    ring
  have hev := hl.eventually (Iio_mem_nhds hgap)
  obtain ⟨q₀, hq₀⟩ := Filter.eventually_atTop.mp hev
  let q := max q₀ 1
  have hq : 0 < q := lt_of_lt_of_le (by decide : 0 < 1) (le_max_right _ _)
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hlog := Real.log_le_log (pow_pos ha' _) (H q hq)
  rw [Real.log_mul (mul_pos hA (pow_pos (by positivity) d)).ne' (pow_pos hb' _).ne',
    Real.log_mul hA.ne' (pow_pos (by positivity) d).ne',
    Real.log_pow, Real.log_pow, Real.log_pow] at hlog
  have hlow : Real.log a - Real.log b ≤
      ((d : ℝ) * Real.log ((q : ℝ) + 1) + Real.log A) / q := by
    apply (le_div_iff₀ hqr).mpr
    nlinarith
  exact (not_lt_of_ge hlow) (hq₀ q (le_max_left _ _))

theorem ContextLE.of_polynomial_powers {S : Tensor 𝕜 I V} {T : Tensor 𝕜 I W}
    (A : ℝ) (hA : 0 < A) (d : ℕ)
    (H : ∀ q : ℕ, 0 < q → ContextLE (A * ((q : ℝ) + 1) ^ d)
      (Lemmata.TensorRank.Tensor.power S q) (Lemmata.TensorRank.Tensor.power T q)) :
    ContextLE 1 S T := by
  intro U _ Q
  rw [one_mul]
  apply le_of_polynomial_power_bounds _ _ A
    (asymptoticRank_nonneg _) (asymptoticRank_nonneg _) d hA
  intro q hq
  have hs (X : I → Type) [∀ i, Fintype (X i)] (P : Tensor 𝕜 I X) :
      asymptoticRank (Lemmata.TensorRank.Tensor.product (Lemmata.TensorRank.Tensor.power P q)
        (Lemmata.TensorRank.Tensor.power Q q)) = asymptoticRank (Lemmata.TensorRank.Tensor.product P Q) ^ q := by
    have he := asymptoticRank_reindex
      (fun i => Equiv.arrowProdEquivProdArrow (Fin q) (fun _ => X i) (fun _ => U i))
      (Lemmata.TensorRank.Tensor.product (Lemmata.TensorRank.Tensor.power P q) (Lemmata.TensorRank.Tensor.power Q q))
    rw [power_product_reindex, asymptoticRank_power] at he
    exact he.symm
  simpa only [hs] using H q hq _ (Lemmata.TensorRank.Tensor.power Q q)

end Lemmata.TensorRank.Tensor
