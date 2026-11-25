module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Topology.MetricSpace.HausdorffDistance

@[expose] public section

namespace Lemmata.FrankWolfeLDS

section

/-!
# Additions to `Mathlib.Analysis.SpecificLimits.Basic`

## Main results

* `tendsto_const_div_add_atTop_nhds_zero_nat` : `C / (n + k) → 0` for arbitrary
  `C : 𝕜` and `k : ℕ`, under `[ContinuousMul 𝕜]`

## Target file

`Mathlib.Analysis.SpecificLimits.Basic`, after `tendsto_one_div_add_atTop_nhds_zero_nat`
-/

open Set Function Filter Finset Metric Topology Nat uniformity NNReal ENNReal

theorem tendsto_const_div_add_atTop_nhds_zero_nat {𝕜 : Type*} [DivisionSemiring 𝕜] [CharZero 𝕜]
    [TopologicalSpace 𝕜] [ContinuousSMul ℚ≥0 𝕜] [ContinuousMul 𝕜] (C : 𝕜) (k : ℕ) :
    Tendsto (fun n : ℕ ↦ C / ((n : 𝕜) + k)) atTop (𝓝 0) := by
  suffices Tendsto (fun n : ℕ ↦ C / (↑(n + k) : 𝕜)) atTop (𝓝 0) by
    simpa [Nat.cast_add]
  exact (tendsto_add_atTop_iff_nat k).2 (_root_.tendsto_const_div_atTop_nhds_zero_nat C)

end

section

/-!
# Additions to `Mathlib.Analysis.SpecialFunctions.Pow.Continuity`

## Main results

* `tendsto_rpow_const_zero` : special case of `Filter.Tendsto.rpow_const`
  where the base tends to `0`

## Target file

`Mathlib.Analysis.SpecialFunctions.Pow.Continuity`, after `Filter.Tendsto.rpow_const`
-/

open Real Topology NNReal ENNReal Filter ComplexConjugate Finset Set

variable {α : Type*}

theorem tendsto_rpow_const_zero {l : Filter α} {f : α → ℝ} {p : ℝ}
    (hf : Tendsto f l (𝓝 0)) (hp : 0 < p) :
    Tendsto (fun t ↦ f t ^ p) l (𝓝 0) :=
  Real.zero_rpow hp.ne' ▸ hf.rpow_const (Or.inr hp.le)

end

section

/-!
# Additions to `Mathlib.Topology.MetricSpace.HausdorffDistance`

## Main definitions

* `nearestPoint IsCompact` : a nearest point in `M` to `x`, for compact nonempty `M`.

## Main results

* `nearestPoint_mem IsCompact` : the nearest point lies in `M`.
* `infDist_nearestPoint IsCompact` : the nearest point realises the infimum distance.
* `tendsto_dist_nearestPoint_of_tendsto_infDist IsCompact` : if `infDist (f x) M → 0`
  along a filter `l`, then `dist (f x) (nearestPoint (f x)) → 0` along `l`.

## Target file

`Mathlib.Topology.MetricSpace.HausdorffDistance`, after `IsCompact.exists_infDist_eq_dist`.

## TODO

Add `IsCompact.tendsto_dist_nearestPoint_of_tendsto_infEDist` for `[PseudoEMetricSpace α]`
using `IsCompact.exists_infEDist_eq_edist`.
-/

open Metric Set

variable {α : Type*} [PseudoMetricSpace α] {β : Type*} {M : Set α}

/-- A nearest point in `M` to `x`, for compact nonempty `M`.
Existence is guaranteed by `IsCompact.exists_infDist_eq_dist`. -/
noncomputable def nearestPoint
    (hM : IsCompact M) (hne : M.Nonempty) (x : α) : α :=
  (hM.exists_infDist_eq_dist hne x).choose

lemma nearestPoint_mem
    (hM : IsCompact M) (hne : M.Nonempty) (x : α) :
    nearestPoint hM hne x ∈ M :=
  (hM.exists_infDist_eq_dist hne x).choose_spec.1

lemma infDist_nearestPoint
    (hM : IsCompact M) (hne : M.Nonempty) (x : α) :
    infDist x M = dist x (nearestPoint hM hne x) :=
  (hM.exists_infDist_eq_dist hne x).choose_spec.2

lemma tendsto_dist_nearestPoint_of_tendsto_infDist
    (hM : IsCompact M) (hne : M.Nonempty)
    {l : Filter β} {f : β → α}
    (h : Filter.Tendsto (fun x => infDist (f x) M) l (nhds 0)) :
    Filter.Tendsto (fun x => dist (f x) (nearestPoint hM hne (f x))) l (nhds 0) := by
  simp_rw [← infDist_nearestPoint hM hne]
  exact h

end

end Lemmata.FrankWolfeLDS
