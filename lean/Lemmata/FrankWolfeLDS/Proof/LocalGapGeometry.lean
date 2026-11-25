module

public import Lemmata.FrankWolfeLDS.Proof.UniformlyConvexSet
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

@[expose] public section

namespace Lemmata.FrankWolfeLDS

open InnerProductSpace Set Filter
open scoped Topology Polynomial
local notation "inner" => inner ℝ

section LocalGapGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {C : Set E} (O : Oracle C)

/-- A local dual sharpness condition around a reference set `M`.

For points of `C` whose distance to `M` is sufficiently small, every linear
functional enjoys the same power-type lower bound that global uniform convexity
would provide everywhere on `C`. -/
def HasLocalLMOGapPowerOn
    (M : Set E) (A : ℝ) (q : ℝ) : Prop :=
  ∃ ρ > 0, ∀ x ∈ C, Metric.infDist x M < ρ →
    ∀ g : E,
      A * ‖g‖ * ‖x - LMO O g‖ ^ q ≤
        (inner g (x - LMO O g) : ℝ)

/-- A local quadratic error bound around a reference set `M`. -/
def HasLocalQuadraticErrorBoundOn
    (M : Set E) (f : E → ℝ) (fStar B : ℝ) : Prop :=
  ∃ ρ > 0, ∀ x ∈ C, Metric.infDist x M < ρ →
    (Metric.infDist x M) ^ 2 ≤ B * (f x - fStar)

/-- A local Hölder error bound of order `r` around a reference set `M`.

The quadratic error bound is the special case `r = 2`. -/
def HasLocalHolderErrorBoundOn
    (M : Set E) (f : E → ℝ) (fStar B r : ℝ) : Prop :=
  ∃ ρ > 0, ∀ x ∈ C, Metric.infDist x M < ρ →
    (Metric.infDist x M) ^ r ≤ B * (f x - fStar)

/-- Global power-type uniform convexity implies the local dual sharpness condition
around any reference set. -/
lemma hasLocalLMOGapPowerOn_of_uniformlyConvex
    {M : Set E} {α : ℝ} {q : ℝ}
    (hUC : IsUniformlyConvexPower C α q) :
    HasLocalLMOGapPowerOn O M (α / 2) q := by
  refine ⟨1, by positivity, ?_⟩
  intro x hx _ g
  simpa using
    uniformlyConvex_lmoGap_lower_bound
      (O := O)
      (C := C) (hUC := hUC) (q := q) (g := g) (x := x) hx

/-- A local dual sharpness can also be inherited from a uniformly convex
patch, provided points near `M` stay in that patch and directions whose selected
atom leaves the patch retain a uniform residual gap. -/
lemma hasLocalLMOGapPowerOn_of_uniformlyConvexPatchOrResidual
    {K M : Set E} {α β ρ : ℝ} {q : ℝ}
    (hq_nonneg : 0 ≤ q)
    (hUC : IsUniformlyConvexPower K α q)
    (hρ : 0 < ρ)
    (hnearK : ∀ x ∈ C, Metric.infDist x M < ρ → x ∈ K)
    (hcase :
      ∀ x ∈ C, Metric.infDist x M < ρ → ∀ g : E,
        let s := LMO O g;
        ((s ∈ K ∧ ∀ y ∈ K, 0 ≤ (inner g (y - s) : ℝ)) ∨
          β * ‖g‖ ≤ (inner g (x - s) : ℝ)))
    (hβ : 0 ≤ β) :
    HasLocalLMOGapPowerOn
      O M (min (α / 2) (β / max 1 ((Metric.diam C) ^ q))) q := by
  refine ⟨ρ, hρ, ?_⟩
  intro x hx hxM g
  let s := LMO O g
  have hsC : s ∈ C := LMO_mem O g
  have hxK : x ∈ K := hnearK x hx hxM
  have hcase0 :
      (s ∈ K ∧ ∀ y ∈ K, 0 ≤ (inner g (y - s) : ℝ)) ∨
        β * ‖g‖ ≤ (inner g (x - s) : ℝ) := by
    simpa [s] using hcase x hx hxM g
  rcases hcase0 with hpatch | hresid
  · rcases hpatch with ⟨hsK, hnormalK⟩
    have hpatchGap :
        (α / 2) * ‖g‖ * ‖x - s‖ ^ q ≤ (inner g (x - s) : ℝ) := by
      simpa [s] using
        uniformlyConvex_support_lower_bound
          (C := K) (hUC := hUC) (v := s) (x := x) (η := g) hsK hxK hnormalK
    have hcoef :
        min (α / 2) (β / max 1 ((Metric.diam C) ^ q)) ≤ α / 2 := by
      exact min_le_left _ _
    have hnonneg : 0 ≤ ‖g‖ * ‖x - s‖ ^ q := by positivity
    have hscaled :
        min (α / 2) (β / max 1 ((Metric.diam C) ^ q)) * ‖g‖ * ‖x - s‖ ^ q ≤
          (α / 2) * ‖g‖ * ‖x - s‖ ^ q := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        mul_le_mul_of_nonneg_right hcoef hnonneg
    exact le_trans hscaled hpatchGap
  · let DqMax : ℝ := max 1 ((Metric.diam C) ^ q)
    have hdiam :
        ‖x - s‖ ^ q ≤ DqMax := by
      have hdist : ‖x - s‖ ≤ Metric.diam C := by
        have hdist0 : dist x s ≤ Metric.diam C :=
          Metric.dist_le_diam_of_mem O.isCompact.isBounded hx hsC
        simpa [dist_eq_norm] using hdist0
      have hdiam0 : ‖x - s‖ ^ q ≤ (Metric.diam C) ^ q := by
        exact Real.rpow_le_rpow (norm_nonneg _) hdist hq_nonneg
      exact le_trans hdiam0 (le_max_right _ _)
    have hcoef :
        min (α / 2) (β / max 1 ((Metric.diam C) ^ q)) ≤ β / DqMax := by
      simp [DqMax]
    have hnonneg : 0 ≤ ‖g‖ * ‖x - s‖ ^ q := by positivity
    have hscaled0 :
        min (α / 2) (β / max 1 ((Metric.diam C) ^ q)) * ‖g‖ * ‖x - s‖ ^ q ≤
          (β / DqMax) * ‖g‖ * ‖x - s‖ ^ q := by
      simpa [DqMax, mul_assoc, mul_left_comm, mul_comm] using
        mul_le_mul_of_nonneg_right hcoef hnonneg
    have hfac_nonneg : 0 ≤ (β / DqMax) * ‖g‖ := by
      positivity
    have hscaled1 :
        (β / DqMax) * ‖g‖ * ‖x - s‖ ^ q ≤ β * ‖g‖ := by
      have hmul :
          (β / DqMax) * ‖g‖ * ‖x - s‖ ^ q ≤
            (β / DqMax) * ‖g‖ * DqMax := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          mul_le_mul_of_nonneg_left hdiam hfac_nonneg
      have hne : DqMax ≠ 0 := by positivity
      have hcancel : (β / DqMax) * ‖g‖ * DqMax = β * ‖g‖ := by
        field_simp [DqMax, hne]
      exact hmul.trans_eq hcancel
    have hfinal :
        min (α / 2) (β / max 1 ((Metric.diam C) ^ q)) * ‖g‖ * ‖x - s‖ ^ q ≤
          (inner g (x - s) : ℝ) := by
      exact le_trans hscaled0 (le_trans hscaled1 hresid)
    simpa [s] using hfinal

omit [InnerProductSpace ℝ E] in
/-- If a continuous residual gap is strictly positive on a compact product,
then it has a uniform positive lower bound. This is the compactness step used
in the planar patch examples in the paper. -/
lemma compact_positive_uniform_lower_bound₂
    {U S : Set E} {Φ : E → E → ℝ}
    (hU : IsCompact U) (hS : IsCompact S)
    (hU_nonempty : U.Nonempty) (hS_nonempty : S.Nonempty)
    (hΦ_cont : ContinuousOn (fun p : E × E => Φ p.1 p.2) (U ×ˢ S))
    (hΦ_pos : ∀ x ∈ U, ∀ u ∈ S, 0 < Φ x u) :
    ∃ β > 0, ∀ x ∈ U, ∀ u ∈ S, β ≤ Φ x u := by
  have hK : IsCompact (U ×ˢ S) := hU.prod hS
  have hK_nonempty : (U ×ˢ S).Nonempty := hU_nonempty.prod hS_nonempty
  rcases hK.exists_isMinOn hK_nonempty hΦ_cont with ⟨p, hp, hpmin⟩
  refine ⟨Φ p.1 p.2, ?_, ?_⟩
  · exact hΦ_pos p.1 hp.1 p.2 hp.2
  · intro x hx u hu
    exact isMinOn_iff.mp hpmin (x, u) ⟨hx, hu⟩

omit E [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
/-- The superflat model gap `exp (-1/u^2)` is smaller than every fixed
integer power near `0` from the right. This is the analytic core behind the
strict-convexity counterexample in the paper. -/
theorem superflat_exp_neg_inv_sq_div_power_nat_tendsto_zero (n : ℕ) :
    Tendsto
      (fun u : ℝ => Real.exp (-(u ^ 2)⁻¹) / u ^ n)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  let p : ℝ[X] := Polynomial.X ^ n
  have hsq : Tendsto (fun u : ℝ => u ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hsq_nhds : Tendsto (fun u : ℝ => u ^ 2) (𝓝 (0 : ℝ)) (𝓝 ((0 : ℝ) ^ 2)) := by
      exact (continuous_pow 2).tendsto _
    simpa using hsq_nhds.mono_left nhdsWithin_le_nhds
  have hflat :
      Tendsto
        (fun u : ℝ => p.eval ((u ^ 2)⁻¹) * expNegInvGlue (u ^ 2))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa [Function.comp_def, p] using
      (expNegInvGlue.tendsto_polynomial_inv_mul_zero p).comp hsq
  have hpow : Tendsto (fun u : ℝ => u ^ n) (𝓝[>] (0 : ℝ)) (𝓝 (0 ^ n)) := by
    have hpow_nhds : Tendsto (fun u : ℝ => u ^ n) (𝓝 (0 : ℝ)) (𝓝 ((0 : ℝ) ^ n)) := by
      exact (continuous_pow n).tendsto _
    simpa using hpow_nhds.mono_left nhdsWithin_le_nhds
  have hmul :
      Tendsto
        (fun u : ℝ => u ^ n * (p.eval ((u ^ 2)⁻¹) * expNegInvGlue (u ^ 2)))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using hpow.mul hflat
  have hcongr :
      (fun u : ℝ => u ^ n * (p.eval ((u ^ 2)⁻¹) * expNegInvGlue (u ^ 2)))
        =ᶠ[𝓝[>] (0 : ℝ)]
      (fun u : ℝ => Real.exp (-(u ^ 2)⁻¹) / u ^ n) := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    have hu_pos : 0 < u := hu
    have hu_ne : u ≠ 0 := hu_pos.ne'
    have hu2_pos : 0 < u ^ 2 := sq_pos_of_ne_zero hu_ne
    simp [p, expNegInvGlue, hu2_pos.not_ge, div_eq_mul_inv, inv_pow]
    field_simp [pow_ne_zero n hu_ne]
    ring
  exact (tendsto_congr' hcongr).mp hmul

/-- Real-exponent version of the superflat obstruction: `exp (-1/u^2)` is
`o(u^q)` from the right for every real exponent `q`. -/
theorem superflat_exp_neg_inv_sq_div_rpow_tendsto_zero (q : ℝ) :
    Tendsto
      (fun u : ℝ => Real.exp (-(u ^ 2)⁻¹) / u ^ q)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  let n : ℕ := Nat.ceil q
  have hnq : q ≤ (n : ℝ) := Nat.le_ceil q
  have hdiff : 0 ≤ (n : ℝ) - q := sub_nonneg.mpr hnq
  have hnat := superflat_exp_neg_inv_sq_div_power_nat_tendsto_zero n
  have hbase : Tendsto (fun u : ℝ => u) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hdiff_tendsto :
      Tendsto (fun u : ℝ => u ^ ((n : ℝ) - q))
        (𝓝[>] (0 : ℝ)) (𝓝 (0 ^ ((n : ℝ) - q))) :=
    hbase.rpow_const (Or.inr hdiff)
  have hprod :
      Tendsto
        (fun u : ℝ =>
          (Real.exp (-(u ^ 2)⁻¹) / u ^ n) * u ^ ((n : ℝ) - q))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using hnat.mul hdiff_tendsto
  have hcongr :
      (fun u : ℝ =>
          (Real.exp (-(u ^ 2)⁻¹) / u ^ n) * u ^ ((n : ℝ) - q))
        =ᶠ[𝓝[>] (0 : ℝ)]
      (fun u : ℝ => Real.exp (-(u ^ 2)⁻¹) / u ^ q) := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    have hu_pos : 0 < u := hu
    have hu_ne : u ≠ 0 := hu_pos.ne'
    have hrpow_ne : u ^ q ≠ 0 := (Real.rpow_pos_of_pos hu_pos q).ne'
    rw [Real.rpow_sub hu_pos (n : ℝ) q, Real.rpow_natCast]
    field_simp [pow_ne_zero n hu_ne, hrpow_ne]
  exact (tendsto_congr' hcongr).mp hprod

end LocalGapGeometry

section LocalGapBoostedConvergence

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {C : Set E} (O : Oracle C)

/-- The abstract uniformly-convex-set engine only needs the power-type geometry
from some index onward. A finite prefix does not affect the `o(1/t)` limit. -/
theorem tendsto_mul_gap_of_decrease_and_eventually_uniformGeometry
    {F g δ d : ℕ → ℝ} {L A : ℝ} {q : ℝ}
    (hq : 2 ≤ q)
    (hF_pos : ∀ t, 0 < F t)
    (hδ_pos : ∀ t, 0 < δ t)
    (hd_pos : ∀ t, 0 < d t)
    (hL : 0 < L) (hA : 0 < A)
    (hδ_zero : Tendsto δ atTop (nhds 0))
    (hgap : ∀ t, F t ≤ g t)
    (hsmooth : ∀ t, F t ≤ (L / 2) * (δ t) ^ 2)
    (hgeom_event : ∀ᶠ t in atTop, A * (F t / δ t) * (d t) ^ q ≤ g t)
    (hdec : ∀ t, F (t + 1) ≤ F t - (1 / 2) * min (g t) (g t ^ 2 / (L * (d t) ^ 2))) :
    Tendsto (fun t : ℕ => (t + 2 : ℝ) * F t) atTop (nhds 0) := by
  rcases Filter.Eventually.exists_forall_of_atTop hgeom_event with ⟨N, hNgeom⟩
  let F' : ℕ → ℝ := fun t => F (t + N)
  let g' : ℕ → ℝ := fun t => g (t + N)
  let δ' : ℕ → ℝ := fun t => δ (t + N)
  let d' : ℕ → ℝ := fun t => d (t + N)
  have hF'_pos : ∀ t, 0 < F' t := by
    intro t
    exact hF_pos (t + N)
  have hδ'_pos : ∀ t, 0 < δ' t := by
    intro t
    exact hδ_pos (t + N)
  have hd'_pos : ∀ t, 0 < d' t := by
    intro t
    exact hd_pos (t + N)
  have hδ'_zero : Tendsto δ' atTop (nhds 0) := by
    simpa [δ', Function.comp_def] using hδ_zero.comp (tendsto_add_atTop_nat N)
  have hgap' : ∀ t, F' t ≤ g' t := by
    intro t
    exact hgap (t + N)
  have hsmooth' : ∀ t, F' t ≤ (L / 2) * (δ' t) ^ 2 := by
    intro t
    exact hsmooth (t + N)
  have hgeom' : ∀ t, A * (F' t / δ' t) * (d' t) ^ q ≤ g' t := by
    intro t
    exact hNgeom (t + N) <| by
      omega
  have hdec' :
      ∀ t,
        F' (t + 1) ≤
          F' t - (1 / 2) * min (g' t) (g' t ^ 2 / (L * (d' t) ^ 2)) := by
    intro t
    simpa [F', g', d', Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hdec (t + N)
  have hcore :
      Tendsto (fun t : ℕ => (t + 2 : ℝ) * F' t) atTop (nhds 0) := by
    exact
      tendsto_mul_gap_of_decrease_and_uniformGeometry
        (hq := hq) (hF_pos := hF'_pos) (hδ_pos := hδ'_pos) (hd_pos := hd'_pos)
        (hL := hL) (hA := hA) (hδ_zero := hδ'_zero)
        (hgap := hgap') (hsmooth := hsmooth') (hgeom := hgeom') (hdec := hdec')
  have hscaled :
      Tendsto
        (fun t : ℕ => (N + 1 : ℝ) * ((t + 2 : ℝ) * F (t + N)))
        atTop (nhds 0) := by
    simpa [F', mul_assoc, mul_left_comm, mul_comm] using hcore.const_mul (N + 1 : ℝ)
  have hshift :
      Tendsto (fun t : ℕ => (((t + N : ℕ) : ℝ) + 2) * F (t + N)) atTop (nhds 0) := by
    refine squeeze_zero
      (f := fun t : ℕ => (((t + N : ℕ) : ℝ) + 2) * F (t + N))
      (g := fun t : ℕ => (N + 1 : ℝ) * ((t + 2 : ℝ) * F (t + N)))
      (fun t => mul_nonneg (by positivity) (le_of_lt (hF_pos (t + N)))) ?_ hscaled
    intro t
    have hcoef :
        (((t + N : ℕ) : ℝ) + 2) ≤ (N + 1 : ℝ) * (t + 2 : ℝ) := by
      push_cast
      nlinarith
    simpa [mul_assoc] using
      (mul_le_mul_of_nonneg_right hcoef (le_of_lt (hF_pos (t + N))))
  exact
    (tendsto_add_atTop_iff_nat N).1 <| by
      simpa [Nat.cast_add, add_assoc] using hshift

/-- An abstract eventually-valid `q = 2` Polyak step bound yields a shifted
geometric primal-gap estimate. -/
theorem gap_le_geometric_of_eventually_polyak_linear_step
    {F g d : ℕ → ℝ} {L A G : ℝ}
    (hF_nonneg : ∀ t, 0 ≤ F t)
    (hL : 0 < L) (hA : 0 < A) (hG : 0 < G)
    (hgap : ∀ t, F t ≤ g t)
    (hzero : ∀ t, d t = 0 → g t = 0)
    (hgeom_event : ∀ᶠ t in atTop, A * G * (d t) ^ 2 ≤ g t)
    (hdec : ∀ t, F (t + 1) ≤ F t - (1 / 2) * min (g t) (g t ^ 2 / (L * (d t) ^ 2))) :
    let κ : ℝ := (1 / 2) * min 1 (A * G / L)
    ∃ T : ℕ, ∀ n : ℕ, F (T + n) ≤ (1 - κ) ^ n * F T := by
  rcases Filter.Eventually.exists_forall_of_atTop hgeom_event with ⟨T, hTgeom⟩
  let F' : ℕ → ℝ := fun t => F (T + t)
  let g' : ℕ → ℝ := fun t => g (T + t)
  let d' : ℕ → ℝ := fun t => d (T + t)
  have hF'_nonneg : ∀ t, 0 ≤ F' t := by
    intro t
    exact hF_nonneg (T + t)
  have hgap' : ∀ t, F' t ≤ g' t := by
    intro t
    exact hgap (T + t)
  have hzero' : ∀ t, d' t = 0 → g' t = 0 := by
    intro t hdt
    exact hzero (T + t) hdt
  have hgeom' : ∀ t, A * G * (d' t) ^ 2 ≤ g' t := by
    intro t
    exact hTgeom (T + t) (by omega)
  have hdec' :
      ∀ t,
        F' (t + 1) ≤ F' t - (1 / 2) * min (g' t) (g' t ^ 2 / (L * (d' t) ^ 2)) := by
    intro t
    simpa [F', g', d', Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hdec (T + t)
  dsimp
  refine ⟨T, ?_⟩
  intro n
  have hcore :=
    gap_le_geometric_of_polyak_linear_step
      (F := F') (g := g') (d := d') (L := L) (A := A) (G := G)
      hF'_nonneg hL hA hG hgap' hgeom' hzero' hdec'
  simpa [F', g', d', Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcore n

/-- An abstract eventually-valid `q > 2` Polyak step bound yields a shifted
polynomial-rate estimate with exponent `q / (q - 2)`. -/
theorem gap_shifted_power_bound_of_eventually_polyak_uniformGeometry
    {F g d : ℕ → ℝ} {L A G M : ℝ} {q : ℝ}
    (hq : 2 < q)
    (hF_nonneg : ∀ t, 0 ≤ F t)
    (hstd : ∀ t, F t ≤ M / (t + 2 : ℝ))
    (hM_nonneg : 0 ≤ M)
    (hL : 0 < L) (hA : 0 < A) (hG : 0 < G)
    (hd_nonneg : ∀ t, 0 ≤ d t)
    (hgap : ∀ t, F t ≤ g t)
    (hzero : ∀ t, d t = 0 → g t = 0)
    (hgeom_event : ∀ᶠ t in atTop, A * G * (d t) ^ q ≤ g t)
    (hdec : ∀ t, F (t + 1) ≤ F t - (1 / 2) * min (g t) (g t ^ 2 / (L * (d t) ^ 2))) :
    ∃ T : ℕ, ∃ K : ℝ, 0 < K ∧
      ∀ n : ℕ, F (T + n) ≤ K / (n + 1 : ℝ) ^ (q / (q - 2 : ℝ)) := by
  rcases Filter.Eventually.exists_forall_of_atTop hgeom_event with ⟨N, hNgeom⟩
  let F' : ℕ → ℝ := fun t => F (N + t)
  let g' : ℕ → ℝ := fun t => g (N + t)
  let d' : ℕ → ℝ := fun t => d (N + t)
  have hF'_nonneg : ∀ t, 0 ≤ F' t := by
    intro t
    exact hF_nonneg (N + t)
  have hstd' : ∀ t, F' t ≤ M / (t + 2 : ℝ) := by
    intro t
    have hbase : F' t ≤ M / (((N + t : ℕ) : ℝ) + 2) := by
      simpa [F', Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hstd (N + t)
    refine hbase.trans ?_
    have hden_left : 0 < (((N + t : ℕ) : ℝ) + 2) := by positivity
    have hden_right : 0 < (t + 2 : ℝ) := by positivity
    refine (_root_.div_le_div_iff₀ hden_left hden_right).2 ?_
    have horder : (t + 2 : ℝ) ≤ (((N + t : ℕ) : ℝ) + 2) := by
      simp only [Nat.cast_add]; linarith [show (0 : ℝ) ≤ (N : ℝ) from Nat.cast_nonneg N]
    nlinarith
  have hd'_nonneg : ∀ t, 0 ≤ d' t := by
    intro t
    exact hd_nonneg (N + t)
  have hgap' : ∀ t, F' t ≤ g' t := by
    intro t
    exact hgap (N + t)
  have hzero' : ∀ t, d' t = 0 → g' t = 0 := by
    intro t hdt
    exact hzero (N + t) hdt
  have hgeom' : ∀ t, A * G * (d' t) ^ q ≤ g' t := by
    intro t
    exact hNgeom (N + t) (by omega)
  have hdec' :
      ∀ t,
        F' (t + 1) ≤ F' t - (1 / 2) * min (g' t) (g' t ^ 2 / (L * (d' t) ^ 2)) := by
    intro t
    simpa [F', g', d', Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hdec (N + t)
  obtain ⟨T, K, hK_pos, htail⟩ :=
    gap_shifted_power_bound_of_polyak_uniformGeometry
      (F := F') (g := g') (d := d') (L := L) (A := A) (G := G) (M := M) (q := q)
      hq hF'_nonneg hstd' hL hA hG hd'_nonneg hgap' hgeom' hzero' hdec'
  refine ⟨N + T, K, hK_pos, ?_⟩
  intro n
  simpa [F', Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using htail n

/-- For `u ∈ [0,1]`, the reciprocal factor `1 / (1 + u)` is bounded by the
first-order truncation `1 - u / 2`. -/
lemma one_div_add_le_one_sub_half
    {u : ℝ} (hu_nonneg : 0 ≤ u) (hu_le_one : u ≤ 1) :
    1 / (1 + u) ≤ 1 - u / 2 := by
  have hden : 0 < 1 + u := by linarith
  refine (_root_.div_le_iff₀ hden).2 ?_
  nlinarith [hu_nonneg, hu_le_one]

/-- For `u ≥ 0`, the reciprocal `1 / (1 + u)` stays above the affine lower
bound `1 - u`. -/
lemma one_sub_le_one_div_add
    {u : ℝ} (hu_nonneg : 0 ≤ u) :
    1 - u ≤ 1 / (1 + u) := by
  have hden : 0 < 1 + u := by linarith
  refine (_root_.le_div_iff₀ hden).2 ?_
  nlinarith [hu_nonneg]

/-- If the scaled open-loop gap `H` is controlled by the distance `δ`, then
a local Hölder error bound turns this into the sharp pointwise power bound. -/
lemma small_branch_scaled_gap_bound_of_localHEB
    {H δ C B r T : ℝ}
    (hr : 2 ≤ r) (hH_nonneg : 0 ≤ H) (hδ_nonneg : 0 ≤ δ)
    (hC_pos : 0 < C) (hB_pos : 0 < B) (hT_pos : 0 < T)
    (hsmall : H ≤ C * δ)
    (hheb : δ ^ r ≤ B * H / T) :
    H ≤ (C ^ r * B) ^ (1 / (r - 1)) / T ^ (1 / (r - 1)) := by
  by_cases hH0 : H = 0
  · simp [hH0]
    positivity
  have hH_pos : 0 < H := lt_of_le_of_ne hH_nonneg (by simpa [eq_comm] using hH0)
  have hr_pos : 0 < r := by linarith
  have hrm_pos : 0 < r - 1 := by linarith
  have hrm_ne : r - 1 ≠ 0 := hrm_pos.ne'
  have hC_nonneg : 0 ≤ C := le_of_lt hC_pos
  have hB_nonneg : 0 ≤ B := le_of_lt hB_pos
  have hsmall_pow : H ^ r ≤ (C * δ) ^ r :=
    Real.rpow_le_rpow hH_nonneg hsmall (le_of_lt hr_pos)
  have hmul_pow : (C * δ) ^ r = C ^ r * δ ^ r := by
    rw [Real.mul_rpow hC_nonneg hδ_nonneg]
  have hdelta_bound : C ^ r * δ ^ r ≤ C ^ r * (B * H / T) := by
    exact mul_le_mul_of_nonneg_left hheb (Real.rpow_nonneg hC_nonneg r)
  have hHpow_le : H ^ r ≤ C ^ r * (B * H / T) := by
    rw [hmul_pow] at hsmall_pow
    exact le_trans hsmall_pow hdelta_bound
  have hdivide : H ^ (r - 1) ≤ C ^ r * B / T := by
    have hHr : H ^ r = H ^ (r - 1) * H := by
      conv_lhs => rw [show r = (r - 1) + 1 by ring]
      rw [Real.rpow_add hH_pos, Real.rpow_one]
    rw [hHr] at hHpow_le
    have htmp : H ^ (r - 1) ≤ (C ^ r * (B * H / T)) / H :=
      (_root_.le_div_iff₀ hH_pos).2 hHpow_le
    have heq : (C ^ r * (B * H / T)) / H = C ^ r * B / T := by
      field_simp [hH_pos.ne', hT_pos.ne']
    simpa [heq] using htmp
  have hpow :=
    Real.rpow_le_rpow (Real.rpow_nonneg hH_nonneg (r - 1)) hdivide
      (le_of_lt (show 0 < 1 / (r - 1) by positivity))
  have hleft : (H ^ (r - 1)) ^ (1 / (r - 1)) = H := by
    calc
      (H ^ (r - 1)) ^ (1 / (r - 1)) = H ^ ((r - 1) * (1 / (r - 1))) := by
        rw [← Real.rpow_mul hH_nonneg]
      _ = H ^ (1 : ℝ) := by
        congr 1
        field_simp [hrm_ne]
      _ = H := by rw [Real.rpow_one]
  have hright :
      (C ^ r * B / T) ^ (1 / (r - 1)) =
        (C ^ r * B) ^ (1 / (r - 1)) / T ^ (1 / (r - 1)) := by
    have hnum_nonneg : 0 ≤ C ^ r * B := by positivity
    rw [show C ^ r * B / T = (C ^ r * B) / T by ring]
    rw [Real.div_rpow hnum_nonneg (le_of_lt hT_pos)]
  rwa [hleft, hright] at hpow

/-- A shifted reciprocal barrier for the borderline quadratic open-loop
recurrence. The shift absorbs the `O(1/t²)` perturbation in the coefficient. -/
lemma openLoop_qeb_shifted_coeff_bound
    {Cq : ℝ} (hCq_nonneg : 0 ≤ Cq)
    (t : ℕ) (ht : 4 * Cq + 4 ≤ (t : ℝ)) :
    ((t : ℝ) * (t + 3) / (t + 2) ^ 2 +
        Cq * (t + 3) / (t + 2) ^ 3) /
      (t + (Cq ^ 2 + Cq + 10)) ≤
        1 / (t + (Cq ^ 2 + Cq + 10) + 1) := by
  let S : ℝ := Cq ^ 2 + Cq + 10
  have hS_pos : 0 < S := by
    dsimp [S]
    nlinarith [sq_nonneg Cq]
  have ht2 : 0 < (t : ℝ) + 2 := by positivity
  have htS : 0 < (t : ℝ) + S := by positivity
  have htS1 : 0 < (t : ℝ) + S + 1 := by positivity
  change (((t : ℝ) * (t + 3) / (t + 2) ^ 2 +
      Cq * (t + 3) / (t + 2) ^ 3) / (t + S) ≤ 1 / (t + S + 1))
  field_simp [ht2.ne', htS.ne', htS1.ne']
  dsimp [S]
  ring_nf
  nlinarith [sq_nonneg Cq, sq_nonneg ((t : ℝ) - (4 * Cq + 4)),
    sq_nonneg ((t : ℝ) - Cq), sq_nonneg ((t : ℝ) - 2 * Cq),
    sq_nonneg ((t : ℝ) - 4 * Cq), sq_nonneg (Cq * ((t : ℝ) - Cq)),
    sq_nonneg (Cq * ((t : ℝ) - 4 * Cq))]

/-- In the large-gap regime `L d² ≤ g`, universal decrease already yields a
reciprocal increment lower bound of order `1 / F`. -/
lemma reciprocalIncrement_large_gap_universal_lower_bound
    {F Fnext g d L : ℝ}
    (hF_pos : 0 < F) (hFnext_pos : 0 < Fnext)
    (hd_pos : 0 < d) (hL : 0 < L)
    (hgap : F ≤ g)
    (hdec : Fnext ≤ F - (1 / 2) * min g (g ^ 2 / (L * d ^ 2)))
    (hcase : L * d ^ 2 ≤ g) :
    1 / (2 * F) ≤ Fnext⁻¹ - F⁻¹ := by
  have hg_pos : 0 < g := lt_of_lt_of_le hF_pos hgap
  have hd2_pos : 0 < d ^ 2 := sq_pos_of_pos hd_pos
  have hLd2_pos : 0 < L * d ^ 2 := mul_pos hL hd2_pos
  have hmin_eq := min_gap_eq_of_large_case hg_pos hLd2_pos hcase
  have hdec' : Fnext ≤ F - g / 2 := by
    have hdec0 : Fnext ≤ F - (1 / 2) * g := by
      simpa [hmin_eq] using hdec
    calc
      Fnext ≤ F - (1 / 2) * g := hdec0
      _ = F - g / 2 := by ring
  have hinc :
      (g / 2) / F ^ 2 ≤ Fnext⁻¹ - F⁻¹ :=
    reciprocalIncrement_ge_decrease_over_sq
      hF_pos hFnext_pos (by positivity : 0 ≤ g / 2) hdec'
  have hfront : 1 / (2 * F) ≤ (g / 2) / F ^ 2 := by
    have hEqL : 1 / (2 * F) = F / (2 * F ^ 2) := by
      field_simp [hF_pos.ne']
    have hEqR : (g / 2) / F ^ 2 = g / (2 * F ^ 2) := by
      field_simp [hF_pos.ne']
    rw [hEqL, hEqR]
    exact div_le_div_of_nonneg_right hgap (by positivity)
  exact le_trans hfront hinc

/-- In the small-gap regime `g ≤ L d²`, local dual sharpness geometry together with a
local quadratic error bound yields a reciprocal increment lower bound of order
`F^{-1/q}`. -/
lemma reciprocalIncrement_small_gap_localQEB_lower_bound
    {F Fnext g d δ L A B : ℝ} {q : ℝ}
    (hq : 2 ≤ q)
    (hF_pos : 0 < F) (hFnext_pos : 0 < Fnext)
    (hδ_pos : 0 < δ) (hd_pos : 0 < d)
    (hL : 0 < L) (hA : 0 < A) (hB : 0 < B)
    (hgap : F ≤ g)
    (hqeb : δ ^ 2 ≤ B * F)
    (hgeom : A * (F / δ) * d ^ q ≤ g)
    (hdec : Fnext ≤ F - (1 / 2) * min g (g ^ 2 / (L * d ^ 2)))
    (hcase : g ≤ L * d ^ 2) :
    A ^ ((2 : ℝ) / q) / (2 * L * B ^ ((1 : ℝ) / q)) * F ^ (-(1 / q : ℝ)) ≤
      Fnext⁻¹ - F⁻¹ := by
  let H : ℝ := Fnext⁻¹ - F⁻¹
  let u1 : ℝ := 1 / (2 * L * d ^ 2)
  let u2 : ℝ := A ^ 2 * (d ^ 2) ^ (q - 1) / (2 * L * δ ^ 2)
  have hq_pos : 0 < q := by linarith
  have hq_ne : q ≠ 0 := hq_pos.ne'
  have hq_sub_nonneg : 0 ≤ q - 1 := by linarith
  have hu1 :
      u1 ≤ H := by
    simpa [H, u1] using
      (reciprocalIncrement_small_gap_universal_lower_bound
        (F := F) (Fnext := Fnext) (g := g) (d := d) (L := L)
        hF_pos hFnext_pos hd_pos hL hgap hdec hcase)
  have hu2 :
      u2 ≤ H := by
    simpa [u2] using
      (reciprocalIncrement_small_gap_uniform_lower_bound
        (q := q) (F := F) (Fnext := Fnext) (g := g) (d := d) (δ := δ) (L := L) (A := A)
        (by linarith : 1 ≤ q)
        hF_pos hFnext_pos hδ_pos hd_pos hL hA hgap hgeom hdec hcase)
  have hH_nonneg : 0 ≤ H := by
    exact le_trans (by positivity : 0 ≤ u1) hu1
  have hH_pos : 0 < H := lt_of_lt_of_le (by positivity : 0 < u1) hu1
  have hu1pow : u1 ^ (q - 1) ≤ H ^ (q - 1) := by
    exact Real.rpow_le_rpow (by positivity) hu1 hq_sub_nonneg
  have hu12 :
      u1 ^ (q - 1) * u2 ≤ H ^ q := by
    have hq1_eq : (q - 1 : ℝ) + 1 = q := by linarith
    calc
      u1 ^ (q - 1) * u2 ≤ H ^ (q - 1) * u2 := by
            exact mul_le_mul_of_nonneg_right hu1pow (by positivity : 0 ≤ u2)
      _ ≤ H ^ (q - 1) * H := by
            exact mul_le_mul_of_nonneg_left hu2 (Real.rpow_nonneg hH_nonneg _)
      _ = H ^ q := by
            conv_rhs => rw [show (q : ℝ) = q - 1 + 1 by linarith]
            rw [Real.rpow_add hH_pos, Real.rpow_one]
  have hu12' :
      A ^ 2 / ((2 * L) ^ q * δ ^ 2) ≤ H ^ q := by
    have hEq :
        u1 ^ (q - 1) * u2 = A ^ 2 / ((2 * L) ^ q * δ ^ 2) := by
      dsimp [u1, u2]
      have h2L_pos : (0 : ℝ) < 2 * L := by positivity
      have hd2_pos : (0 : ℝ) < d ^ 2 := by positivity
      -- (1/(2Ld²))^(q-1) * (d²)^(q-1) = (1/(2L))^(q-1)
      have hmul : (1 / (2 * L * d ^ 2)) ^ (q - 1) * (d ^ 2) ^ (q - 1) =
          (2 * L) ^ (-(q - 1)) := by
        rw [← Real.mul_rpow (by positivity : 0 ≤ 1 / (2 * L * d ^ 2)) hd2_pos.le]
        rw [show (1 : ℝ) / (2 * L * d ^ 2) * d ^ 2 = (2 * L)⁻¹ by
              field_simp [hL.ne', hd_pos.ne']]
        rw [Real.inv_rpow h2L_pos.le]
        exact (Real.rpow_neg h2L_pos.le _).symm
      -- (2L)^(-(q-1)) * (2L) = (2L)^(-(q-1)+1) = (2L)^(-(q-1-1)) hmm
      -- Better: (2L)^(q-1) * (2L) = (2L)^q
      have hpow_step : (2 * L) ^ (q - 1) * (2 * L) = (2 * L) ^ q := by
        conv_rhs => rw [show (q : ℝ) = q - 1 + 1 by linarith]
        rw [Real.rpow_add h2L_pos, Real.rpow_one]
      calc
        (1 / (2 * L * d ^ 2)) ^ (q - 1) *
            (A ^ 2 * (d ^ 2) ^ (q - 1) / (2 * L * δ ^ 2))
          = A ^ 2 * ((1 / (2 * L * d ^ 2)) ^ (q - 1) * (d ^ 2) ^ (q - 1)) /
              (2 * L * δ ^ 2) := by ring
        _ = A ^ 2 * (2 * L) ^ (-(q - 1)) / (2 * L * δ ^ 2) := by
              rw [hmul]
        _ = A ^ 2 / ((2 * L) ^ (q - 1) * (2 * L) * δ ^ 2) := by
              rw [Real.rpow_neg h2L_pos.le]
              field_simp [hL.ne', hδ_pos.ne', Real.rpow_pos_of_pos h2L_pos]
        _ = A ^ 2 / ((2 * L) ^ q * δ ^ 2) := by
              rw [hpow_step]
    rw [hEq] at hu12
    exact hu12
  have hrecip : 1 / (B * F) ≤ 1 / (δ ^ 2) := by
    exact one_div_le_one_div_of_le (by positivity : 0 < δ ^ 2) hqeb
  have hu12'' :
      A ^ 2 / ((2 * L) ^ q * B * F) ≤ H ^ q := by
    have hfac_nonneg : 0 ≤ A ^ 2 / ((2 * L) ^ q) := by positivity
    have hscaled :
        (A ^ 2 / ((2 * L) ^ q)) * (1 / (B * F)) ≤
          (A ^ 2 / ((2 * L) ^ q)) * (1 / (δ ^ 2)) := by
      exact mul_le_mul_of_nonneg_left hrecip hfac_nonneg
    have hEqL :
        (A ^ 2 / ((2 * L) ^ q)) * (1 / (B * F)) =
          A ^ 2 / ((2 * L) ^ q * B * F) := by
      field_simp [hL.ne', hB.ne', hF_pos.ne']
    have hEqR :
        (A ^ 2 / ((2 * L) ^ q)) * (1 / (δ ^ 2)) =
          A ^ 2 / ((2 * L) ^ q * δ ^ 2) := by
      field_simp [hL.ne', hδ_pos.ne']
    rw [hEqL, hEqR] at hscaled
    exact le_trans hscaled hu12'
  let c : ℝ := A ^ ((2 : ℝ) / q) / (2 * L * B ^ ((1 : ℝ) / q)) * F ^ (-(1 / q : ℝ))
  have hc_nonneg : 0 ≤ c := by positivity
  have hc_pow :
      c ^ q = A ^ 2 / ((2 * L) ^ q * B * F) := by
    dsimp [c]
    have hA_nonneg : 0 ≤ A := le_of_lt hA
    have hB_nonneg : 0 ≤ B := le_of_lt hB
    have hF_nonneg : 0 ≤ F := le_of_lt hF_pos
    have h2L_pos : (0 : ℝ) < 2 * L := by positivity
    have hAq : (A ^ ((2 : ℝ) / q)) ^ q = A ^ 2 := by
      rw [← Real.rpow_mul hA_nonneg]
      simp [hq_ne]
    have hBq : (B ^ ((1 : ℝ) / q)) ^ q = B := by
      rw [← Real.rpow_mul hB_nonneg]
      simp [hq_ne]
    have hFq : (F ^ (-(1 / q : ℝ))) ^ q = F⁻¹ := by
      rw [← Real.rpow_mul hF_nonneg]
      simp [hq_ne, Real.rpow_neg_one]
    have h2Lq : (2 * L * B ^ ((1 : ℝ) / q)) ^ q = (2 * L) ^ q * B := by
      rw [Real.mul_rpow (by positivity : 0 ≤ 2 * L) (Real.rpow_nonneg hB_nonneg _)]
      rw [hBq]
    calc
      (A ^ ((2 : ℝ) / q) / (2 * L * B ^ ((1 : ℝ) / q)) * F ^ (-(1 / q : ℝ))) ^ q
        = (A ^ ((2 : ℝ) / q)) ^ q / (2 * L * B ^ ((1 : ℝ) / q)) ^ q *
            (F ^ (-(1 / q : ℝ))) ^ q := by
              rw [Real.mul_rpow (by positivity : 0 ≤ A ^ ((2:ℝ)/q) / (2*L*B^((1:ℝ)/q)))
                                (by positivity : 0 ≤ F ^ (-(1/q:ℝ)))]
              rw [Real.div_rpow (by positivity : 0 ≤ A ^ ((2:ℝ)/q)) (by positivity : 0 ≤ 2*L*B^((1:ℝ)/q))]
        _ = A ^ 2 / ((2 * L) ^ q * B) * F⁻¹ := by
              rw [hAq, hFq, h2Lq]
        _ = A ^ 2 / ((2 * L) ^ q * B * F) := by
              field_simp [hF_pos.ne']
  have hc_pow_le : c ^ q ≤ H ^ q := by
    rw [hc_pow]
    exact hu12''
  exact (Real.rpow_le_rpow_iff hc_nonneg hH_nonneg hq_pos).mp hc_pow_le

/-- If a reciprocal-increment lower bound of the form `c * F ^ (-α) ≤ Fnext⁻¹ - F⁻¹` holds
with `α + β = 1` and `F ≤ 1`, then `Fnext ≤ F - (c / 2) * F ^ (1 + β)`. -/
lemma powerDescent_of_reciprocalIncrement_lower_bound
    {F Fnext α β c : ℝ}
    (hF_pos : 0 < F) (hFnext_pos : 0 < Fnext)
    (hF_le_one : F ≤ 1)
    (hβ_nonneg : 0 ≤ β)
    (hc_pos : 0 < c) (hc_le_half : c ≤ 1 / 2)
    (hαβ : α + β = 1)
    (hH_lower : c * F ^ (-α) ≤ Fnext⁻¹ - F⁻¹) :
    Fnext ≤ F - (c / 2) * F ^ (1 + β) := by
  have hbase : Fnext ≤ F / (1 + c * F ^ β) := by
    have hden_pos : 0 < 1 + c * F ^ β := by positivity
    have hineq : (1 + c * F ^ β) / F ≤ Fnext⁻¹ := by
      have hEq : F⁻¹ + c * F ^ (-α) = (1 + c * F ^ β) / F := by
        have hpow : c * F ^ β * F⁻¹ = c * F ^ (-α) := by
          have hpow0 : F ^ β * F⁻¹ = F ^ (-α) := by
            calc
              F ^ β * F⁻¹ = F ^ β * F ^ (-1 : ℝ) := by rw [Real.rpow_neg_one]
              _ = F ^ (β + (-1 : ℝ)) := by symm; exact Real.rpow_add hF_pos β (-1)
              _ = F ^ (-α) := by congr 1; linarith
          simpa [mul_assoc, mul_left_comm, mul_comm] using congrArg (fun z => c * z) hpow0
        calc
          F⁻¹ + c * F ^ (-α) = F⁻¹ + c * F ^ β * F⁻¹ := by rw [hpow]
          _ = (1 + c * F ^ β) / F := by field_simp [hF_pos.ne']
      have hmain : F⁻¹ + c * F ^ (-α) ≤ Fnext⁻¹ := by linarith [hH_lower]
      rw [hEq] at hmain
      exact hmain
    have hdiv : 1 / Fnext⁻¹ ≤ 1 / ((1 + c * F ^ β) / F) :=
      one_div_le_one_div_of_le (by positivity) hineq
    have hEqLeft : 1 / Fnext⁻¹ = Fnext := by field_simp [hFnext_pos.ne']
    have hEqRight : 1 / ((1 + c * F ^ β) / F) = F / (1 + c * F ^ β) := by
      field_simp [hF_pos.ne', hden_pos.ne']
    rw [hEqLeft, hEqRight] at hdiv
    exact hdiv
  have hu_nonneg : 0 ≤ c * F ^ β := by positivity
  have hu_le_one : c * F ^ β ≤ 1 := by
    have hpow_le_one : F ^ β ≤ 1 :=
      Real.rpow_le_one (le_of_lt hF_pos) hF_le_one hβ_nonneg
    calc c * F ^ β ≤ c * 1 := mul_le_mul_of_nonneg_left hpow_le_one hc_pos.le
      _ ≤ 1 := by linarith
  have hfrac : F / (1 + c * F ^ β) ≤ F * (1 - c * F ^ β / 2) := by
    have hmain := one_div_add_le_one_sub_half hu_nonneg hu_le_one
    have hscaled := mul_le_mul_of_nonneg_left hmain (le_of_lt hF_pos)
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hscaled
  have hpow_eq : F * F ^ β = F ^ (1 + β) := by
    calc F * F ^ β = F ^ (1 : ℝ) * F ^ β := by rw [Real.rpow_one]
      _ = F ^ (1 + β) := by rw [← Real.rpow_add hF_pos 1 β]
  calc
    Fnext ≤ F / (1 + c * F ^ β) := hbase
    _ ≤ F * (1 - c * F ^ β / 2) := hfrac
    _ = F - (c / 2) * F ^ (1 + β) := by
          have : F * (1 - c * F ^ β / 2) = F - (c / 2) * (F * F ^ β) := by ring
          rw [this, hpow_eq]

/-- A local dual sharpness lower bound together with a local quadratic error bound yields
one-step power descent with exponent `(q - 1) / q`. -/
lemma localQEB_power_step
    {F Fnext g d δ L A B : ℝ} {q : ℝ}
    (hq : 2 ≤ q)
    (hF_pos : 0 < F) (hFnext_pos : 0 < Fnext)
    (hδ_pos : 0 < δ) (hd_nonneg : 0 ≤ d)
    (hF_le_one : F ≤ 1)
    (hL : 0 < L) (hA : 0 < A) (hB : 0 < B)
    (hgap : F ≤ g)
    (hzero : d = 0 → g = 0)
    (hqeb : δ ^ 2 ≤ B * F)
    (hgeom : A * (F / δ) * d ^ q ≤ g)
    (hdec : Fnext ≤ F - (1 / 2) * min g (g ^ 2 / (L * d ^ 2))) :
    let β : ℝ := (q - 1 : ℝ) / q
    let c : ℝ := min (1 / 2 : ℝ)
      (A ^ ((2 : ℝ) / q) / (2 * L * B ^ ((1 : ℝ) / q)))
    let η : ℝ := c / 2
    Fnext ≤ F - η * F ^ (1 + β) := by
  let β : ℝ := (q - 1 : ℝ) / q
  let c : ℝ := min (1 / 2 : ℝ)
    (A ^ ((2 : ℝ) / q) / (2 * L * B ^ ((1 : ℝ) / q)))
  let η : ℝ := c / 2
  have hq_pos : 0 < q := by linarith
  have hq_ne : q ≠ 0 := hq_pos.ne'
  have hβ_eq : β = 1 - (1 : ℝ) / q := by
    dsimp [β]
    field_simp [hq_ne]
  have hβ_nonneg : 0 ≤ β := by
    have hq_inv_le_half : ((1 : ℝ) / q) ≤ (1 / 2 : ℝ) :=
      one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hq
    rw [hβ_eq]
    nlinarith
  have hc_pos :
      0 < c := by
    dsimp [c]
    have hsmall_pos :
        0 < A ^ ((2 : ℝ) / q) / (2 * L * B ^ ((1 : ℝ) / q)) := by
      positivity
    exact lt_min (by positivity) hsmall_pos
  have hc_le_half : c ≤ 1 / 2 := by
    dsimp [c]
    exact min_le_left _ _
  have hd_pos : 0 < d := by
    by_contra hd0'
    have hd0 : d = 0 := le_antisymm (not_lt.mp hd0') hd_nonneg
    have hg0 : g = 0 := hzero hd0
    exact (not_le_of_gt hF_pos) (by simpa [hg0] using hgap)
  have hH_lower :
      c * F ^ (-(1 / q : ℝ)) ≤ Fnext⁻¹ - F⁻¹ := by
    by_cases hcase : g ≤ L * d ^ 2
    · have hsmall :
          A ^ ((2 : ℝ) / q) / (2 * L * B ^ ((1 : ℝ) / q)) * F ^ (-(1 / q : ℝ)) ≤
            Fnext⁻¹ - F⁻¹ := by
        exact
          reciprocalIncrement_small_gap_localQEB_lower_bound
            (q := q) hq hF_pos hFnext_pos hδ_pos hd_pos hL hA hB
            hgap hqeb hgeom hdec hcase
      have hc_cmp :
          c * F ^ (-(1 / q : ℝ)) ≤
            (A ^ ((2 : ℝ) / q) / (2 * L * B ^ ((1 : ℝ) / q))) * F ^ (-(1 / q : ℝ)) := by
        exact mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
      exact le_trans hc_cmp hsmall
    · have hlarge_case : L * d ^ 2 ≤ g := le_of_not_ge hcase
      have hlarge :
          1 / (2 * F) ≤ Fnext⁻¹ - F⁻¹ := by
        exact
          reciprocalIncrement_large_gap_universal_lower_bound
            hF_pos hFnext_pos hd_pos hL hgap hdec hlarge_case
      have hpow_le :
          F ^ (-(1 / q : ℝ)) ≤ F⁻¹ := by
        have hFinv_ge_one : 1 ≤ F⁻¹ := by
          exact (one_le_inv₀ hF_pos).2 hF_le_one
        have hq_inv_le_one : ((1 : ℝ) / q) ≤ 1 :=
          (div_le_one hq_pos).mpr (by linarith)
        calc
          F ^ (-(1 / q : ℝ)) = (F⁻¹) ^ ((1 : ℝ) / q) := by
                calc
                  F ^ (-(1 / q : ℝ)) = F ^ ((-1 : ℝ) * ((1 : ℝ) / q)) := by ring_nf
                  _ = (F ^ (-1 : ℝ)) ^ ((1 : ℝ) / q) := by
                        rw [Real.rpow_mul (le_of_lt hF_pos)]
                  _ = (F⁻¹) ^ ((1 : ℝ) / q) := by rw [Real.rpow_neg_one]
          _ ≤ (F⁻¹) ^ (1 : ℝ) := by
                exact Real.rpow_le_rpow_of_exponent_le hFinv_ge_one hq_inv_le_one
          _ = F⁻¹ := by rw [Real.rpow_one]
      have hhalf :
          (1 / 2 : ℝ) * F ^ (-(1 / q : ℝ)) ≤ 1 / (2 * F) := by
        have hscaled :=
          mul_le_mul_of_nonneg_left hpow_le (by positivity : 0 ≤ (1 / 2 : ℝ))
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hscaled
      have hc_cmp :
          c * F ^ (-(1 / q : ℝ)) ≤ (1 / 2 : ℝ) * F ^ (-(1 / q : ℝ)) := by
        exact mul_le_mul_of_nonneg_right hc_le_half (by positivity)
      exact le_trans hc_cmp (le_trans hhalf hlarge)
  exact powerDescent_of_reciprocalIncrement_lower_bound (α := 1 / q)
    hF_pos hFnext_pos hF_le_one hβ_nonneg hc_pos hc_le_half
    (by linarith [hβ_eq]) hH_lower

/-- A pointwise local dual sharpness bound together with a pointwise local quadratic error
bound yields a shifted polynomial tail with exponent `q / (q - 1)`. -/
theorem gap_shifted_power_bound_of_localQEBGeometry
    {F g d δ : ℕ → ℝ} {L A B M : ℝ} {q : ℝ}
    (hq : 2 ≤ q)
    (hF_pos : ∀ t, 0 < F t)
    (hδ_pos : ∀ t, 0 < δ t)
    (hd_nonneg : ∀ t, 0 ≤ d t)
    (hstd : ∀ t, F t ≤ M / (t + 2 : ℝ))
    (hL : 0 < L) (hA : 0 < A) (hB : 0 < B)
    (hgap : ∀ t, F t ≤ g t)
    (hzero : ∀ t, d t = 0 → g t = 0)
    (hqeb : ∀ t, (δ t) ^ 2 ≤ B * F t)
    (hgeom : ∀ t, A * (F t / δ t) * (d t) ^ q ≤ g t)
    (hdec : ∀ t, F (t + 1) ≤ F t - (1 / 2) * min (g t) (g t ^ 2 / (L * (d t) ^ 2))) :
    ∃ T : ℕ, ∃ K : ℝ, 0 < K ∧
      ∀ n : ℕ, F (T + n) ≤ K / (n + 1 : ℝ) ^ (q / (q - 1 : ℝ)) := by
  let β : ℝ := (q - 1 : ℝ) / q
  let c : ℝ := min (1 / 2 : ℝ)
    (A ^ ((2 : ℝ) / q) / (2 * L * B ^ ((1 : ℝ) / q)))
  let η : ℝ := c / 2
  let T : ℕ := Nat.ceil M
  have hq_pos : 0 < q := by linarith
  have hq_ne : q ≠ 0 := hq_pos.ne'
  have hq_sub_pos : 0 < (q - 1 : ℝ) := by linarith
  have hq_sub_ne : (q - 1 : ℝ) ≠ 0 := hq_sub_pos.ne'
  have hβ_eq : β = 1 - (1 : ℝ) / q := by
    dsimp [β]
    field_simp [hq_ne]
  have hβ_pos : 0 < β := by
    have hq_inv_le_half : ((1 : ℝ) / q) ≤ (1 / 2 : ℝ) :=
      one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hq
    rw [hβ_eq]
    nlinarith
  have hβ_le_one : β ≤ 1 := by
    have hq_inv_nonneg : 0 ≤ (1 : ℝ) / q := by positivity
    rw [hβ_eq]
    nlinarith
  have hη_pos : 0 < η := by
    dsimp [η, c]
    positivity
  have hη_le_one : η ≤ 1 := by
    dsimp [η, c]
    nlinarith [min_le_left (1 / 2 : ℝ) (A ^ ((2 : ℝ) / q) / (2 * L * B ^ ((1 : ℝ) / q)))]
  have hF_nonneg : ∀ t, 0 ≤ F t := fun t => (hF_pos t).le
  have hstep_pow :
      ∀ t, T ≤ t → F (t + 1) ≤ F t - η * F t ^ (1 + β) := by
    intro t ht
    have hFt_le_one : F t ≤ 1 :=
      F_le_one_of_std_and_ceil_le hstd (le_trans (Nat.le_ceil M) (by exact_mod_cast ht))
    have hpow :=
      localQEB_power_step
        (q := q) hq
        (F := F t) (Fnext := F (t + 1)) (g := g t) (d := d t) (δ := δ t)
        (L := L) (A := A) (B := B)
        (hF_pos := hF_pos t) (hFnext_pos := hF_pos (t + 1)) (hδ_pos := hδ_pos t)
        (hd_nonneg := hd_nonneg t)
        (hF_le_one := hFt_le_one) hL hA hB
        (hgap t) (hzero t) (hqeb t) (hgeom t) (hdec t)
    simpa [β, η, c] using hpow
  have hshift :=
    shifted_power_bound_of_powerDescent_from_ceil
      (F := F) (β := β) (η := η) (M := M)
      hβ_pos hβ_le_one hη_pos hη_le_one hF_nonneg hstd hstep_pow
  have hp_eq : (1 / β : ℝ) = q / (q - 1 : ℝ) := by
    dsimp [β]
    field_simp [hq_ne, hq_sub_ne]
  refine ⟨T, (max 1 (1 / (β * η))) ^ (1 / β), ?_, ?_⟩
  · positivity
  · intro n
    simpa [hp_eq, β, η, c] using hshift n

/-- A finite prefix does not affect the quantitative local-QEB tail bound. -/
theorem gap_shifted_power_bound_of_eventually_localQEBGeometry
    {F g d δ : ℕ → ℝ} {L A B M : ℝ} {q : ℝ}
    (hq : 2 ≤ q)
    (hF_pos : ∀ t, 0 < F t)
    (hδ_pos : ∀ t, 0 < δ t)
    (hd_nonneg : ∀ t, 0 ≤ d t)
    (hstd : ∀ t, F t ≤ M / (t + 2 : ℝ))
    (hM_nonneg : 0 ≤ M)
    (hL : 0 < L) (hA : 0 < A) (hB : 0 < B)
    (hgap : ∀ t, F t ≤ g t)
    (hzero : ∀ t, d t = 0 → g t = 0)
    (hqeb_event : ∀ᶠ t in atTop, (δ t) ^ 2 ≤ B * F t)
    (hgeom_event : ∀ᶠ t in atTop, A * (F t / δ t) * (d t) ^ q ≤ g t)
    (hdec : ∀ t, F (t + 1) ≤ F t - (1 / 2) * min (g t) (g t ^ 2 / (L * (d t) ^ 2))) :
    ∃ T : ℕ, ∃ K : ℝ, 0 < K ∧
      ∀ n : ℕ, F (T + n) ≤ K / (n + 1 : ℝ) ^ (q / (q - 1 : ℝ)) := by
  rcases Filter.Eventually.exists_forall_of_atTop hqeb_event with ⟨Nqeb, hNqeb⟩
  rcases Filter.Eventually.exists_forall_of_atTop hgeom_event with ⟨Ngeom, hNgeom⟩
  let N : ℕ := max Nqeb Ngeom
  let F' : ℕ → ℝ := fun t => F (N + t)
  let g' : ℕ → ℝ := fun t => g (N + t)
  let d' : ℕ → ℝ := fun t => d (N + t)
  let δ' : ℕ → ℝ := fun t => δ (N + t)
  have hF'_pos : ∀ t, 0 < F' t := by
    intro t
    exact hF_pos (N + t)
  have hδ'_pos : ∀ t, 0 < δ' t := by
    intro t
    exact hδ_pos (N + t)
  have hstd' : ∀ t, F' t ≤ M / (t + 2 : ℝ) := by
    intro t
    have hbase : F' t ≤ M / (((N + t : ℕ) : ℝ) + 2) := by
      simpa [F', Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hstd (N + t)
    refine hbase.trans ?_
    have hden_left : 0 < (((N + t : ℕ) : ℝ) + 2) := by positivity
    have hden_right : 0 < (t + 2 : ℝ) := by positivity
    refine (_root_.div_le_div_iff₀ hden_left hden_right).2 ?_
    have horder : (t + 2 : ℝ) ≤ (((N + t : ℕ) : ℝ) + 2) := by
      simp only [Nat.cast_add]; linarith [show (0 : ℝ) ≤ (N : ℝ) from Nat.cast_nonneg N]
    nlinarith
  have hgap' : ∀ t, F' t ≤ g' t := by
    intro t
    exact hgap (N + t)
  have hzero' : ∀ t, d' t = 0 → g' t = 0 := by
    intro t hdt
    exact hzero (N + t) hdt
  have hqeb' : ∀ t, (δ' t) ^ 2 ≤ B * F' t := by
    intro t
    exact hNqeb (N + t) (le_trans (le_max_left _ _) (Nat.le_add_right _ _))
  have hgeom' : ∀ t, A * (F' t / δ' t) * (d' t) ^ q ≤ g' t := by
    intro t
    exact hNgeom (N + t) (le_trans (le_max_right _ _) (Nat.le_add_right _ _))
  have hdec' :
      ∀ t,
        F' (t + 1) ≤
          F' t - (1 / 2) * min (g' t) (g' t ^ 2 / (L * (d' t) ^ 2)) := by
    intro t
    simpa [F', g', d', Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hdec (N + t)
  obtain ⟨T, K, hK_pos, htail⟩ :=
    gap_shifted_power_bound_of_localQEBGeometry
      (F := F') (g := g') (d := d') (δ := δ')
      (L := L) (A := A) (B := B) (M := M) (q := q)
      hq hF'_pos hδ'_pos (by intro t; exact hd_nonneg (N + t))
      hstd' hL hA hB hgap' hzero' hqeb' hgeom' hdec'
  refine ⟨N + T, K, hK_pos, ?_⟩
  intro n
  simpa [F', Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using htail n

/-- In the small-gap regime `g ≤ L d²`, local dual sharpness geometry together with a
local Hölder error bound of order `r` yields a reciprocal increment lower bound
of order `F^{-2/(rq)}`. -/
lemma reciprocalIncrement_small_gap_localHEB_lower_bound
    {F Fnext g d δ L A B r : ℝ} {q : ℝ}
    (hq : 2 ≤ q) (hr : 0 < r)
    (hF_pos : 0 < F) (hFnext_pos : 0 < Fnext)
    (hδ_pos : 0 < δ) (hd_pos : 0 < d)
    (hL : 0 < L) (hA : 0 < A) (hB : 0 < B)
    (hgap : F ≤ g)
    (hheb : δ ^ r ≤ B * F)
    (hgeom : A * (F / δ) * d ^ q ≤ g)
    (hdec : Fnext ≤ F - (1 / 2) * min g (g ^ 2 / (L * d ^ 2)))
    (hcase : g ≤ L * d ^ 2) :
    A ^ ((2 : ℝ) / q) / (2 * L) * (B * F) ^ (-(2 / (r * q : ℝ))) ≤
      Fnext⁻¹ - F⁻¹ := by
  let H : ℝ := Fnext⁻¹ - F⁻¹
  let u1 : ℝ := 1 / (2 * L * d ^ 2)
  let u2 : ℝ := A ^ 2 * (d ^ 2) ^ (q - 1) / (2 * L * δ ^ 2)
  have hq_pos : 0 < q := by linarith
  have hq_ne : q ≠ 0 := hq_pos.ne'
  have hq_sub_nonneg : 0 ≤ q - 1 := by linarith
  have hr_ne : r ≠ 0 := hr.ne'
  have hu1 :
      u1 ≤ H := by
    simpa [H, u1] using
      (reciprocalIncrement_small_gap_universal_lower_bound
        (F := F) (Fnext := Fnext) (g := g) (d := d) (L := L)
        hF_pos hFnext_pos hd_pos hL hgap hdec hcase)
  have hu2 :
      u2 ≤ H := by
    simpa [u2] using
      (reciprocalIncrement_small_gap_uniform_lower_bound
        (q := q) (F := F) (Fnext := Fnext) (g := g) (d := d) (δ := δ) (L := L) (A := A)
        (by linarith : 1 ≤ q)
        hF_pos hFnext_pos hδ_pos hd_pos hL hA hgap hgeom hdec hcase)
  have hH_nonneg : 0 ≤ H := by
    exact le_trans (by positivity : 0 ≤ u1) hu1
  have hH_pos : 0 < H := lt_of_lt_of_le (by positivity : 0 < u1) hu1
  have hu1pow : u1 ^ (q - 1) ≤ H ^ (q - 1) := by
    exact Real.rpow_le_rpow (by positivity) hu1 hq_sub_nonneg
  have hu12 :
      u1 ^ (q - 1) * u2 ≤ H ^ q := by
    have hq1_eq : (q - 1 : ℝ) + 1 = q := by linarith
    calc
      u1 ^ (q - 1) * u2 ≤ H ^ (q - 1) * u2 := by
            exact mul_le_mul_of_nonneg_right hu1pow (by positivity : 0 ≤ u2)
      _ ≤ H ^ (q - 1) * H := by
            exact mul_le_mul_of_nonneg_left hu2 (Real.rpow_nonneg hH_nonneg _)
      _ = H ^ q := by
            conv_rhs => rw [show (q : ℝ) = q - 1 + 1 by linarith]
            rw [Real.rpow_add hH_pos, Real.rpow_one]
  have hu12' :
      A ^ 2 / ((2 * L) ^ q * δ ^ 2) ≤ H ^ q := by
    have hEq :
        u1 ^ (q - 1) * u2 = A ^ 2 / ((2 * L) ^ q * δ ^ 2) := by
      dsimp [u1, u2]
      have h2L_pos : (0 : ℝ) < 2 * L := by positivity
      have hd2_pos : (0 : ℝ) < d ^ 2 := by positivity
      have hmul : (1 / (2 * L * d ^ 2)) ^ (q - 1) * (d ^ 2) ^ (q - 1) =
          (2 * L) ^ (-(q - 1)) := by
        rw [← Real.mul_rpow (by positivity : 0 ≤ 1 / (2 * L * d ^ 2)) hd2_pos.le]
        rw [show (1 : ℝ) / (2 * L * d ^ 2) * d ^ 2 = (2 * L)⁻¹ by
              field_simp [hL.ne', hd_pos.ne']]
        rw [Real.inv_rpow h2L_pos.le]
        exact (Real.rpow_neg h2L_pos.le _).symm
      have hpow_step : (2 * L) ^ (q - 1) * (2 * L) = (2 * L) ^ q := by
        conv_rhs => rw [show (q : ℝ) = q - 1 + 1 by linarith]
        rw [Real.rpow_add h2L_pos, Real.rpow_one]
      calc
        (1 / (2 * L * d ^ 2)) ^ (q - 1) *
            (A ^ 2 * (d ^ 2) ^ (q - 1) / (2 * L * δ ^ 2))
          = A ^ 2 * ((1 / (2 * L * d ^ 2)) ^ (q - 1) * (d ^ 2) ^ (q - 1)) /
              (2 * L * δ ^ 2) := by ring
        _ = A ^ 2 * (2 * L) ^ (-(q - 1)) / (2 * L * δ ^ 2) := by
              rw [hmul]
        _ = A ^ 2 / ((2 * L) ^ (q - 1) * (2 * L) * δ ^ 2) := by
              rw [Real.rpow_neg h2L_pos.le]
              field_simp [hL.ne', hδ_pos.ne', Real.rpow_pos_of_pos h2L_pos]
        _ = A ^ 2 / ((2 * L) ^ q * δ ^ 2) := by
              rw [hpow_step]
    rw [hEq] at hu12
    exact hu12
  have htwo_over_r_nonneg : 0 ≤ 2 / r := by positivity
  have hheb_pow :
      δ ^ 2 ≤ (B * F) ^ (2 / r) := by
    have hpow :
        (δ ^ r) ^ (2 / r) ≤ (B * F) ^ (2 / r) := by
      exact Real.rpow_le_rpow (by positivity : 0 ≤ δ ^ r) hheb htwo_over_r_nonneg
    have hleft :
        (δ ^ r) ^ (2 / r) = δ ^ 2 := by
      calc
        (δ ^ r) ^ (2 / r) = δ ^ (r * (2 / r)) := by
              rw [← Real.rpow_mul (le_of_lt hδ_pos) r (2 / r)]
        _ = δ ^ (2 : ℝ) := by
              congr 1
              field_simp [hr_ne]
        _ = δ ^ 2 := by simp
    rw [hleft] at hpow
    exact hpow
  have hrecip : 1 / ((B * F) ^ (2 / r)) ≤ 1 / (δ ^ 2) := by
    exact one_div_le_one_div_of_le (by positivity : 0 < δ ^ 2) hheb_pow
  have hu12'' :
      A ^ 2 / ((2 * L) ^ q * (B * F) ^ (2 / r)) ≤ H ^ q := by
    have hfac_nonneg : 0 ≤ A ^ 2 / ((2 * L) ^ q) := by positivity
    have hscaled :
        (A ^ 2 / ((2 * L) ^ q)) * (1 / ((B * F) ^ (2 / r))) ≤
          (A ^ 2 / ((2 * L) ^ q)) * (1 / (δ ^ 2)) := by
      exact mul_le_mul_of_nonneg_left hrecip hfac_nonneg
    have hEqL :
        (A ^ 2 / ((2 * L) ^ q)) * (1 / ((B * F) ^ (2 / r))) =
          A ^ 2 / ((2 * L) ^ q * (B * F) ^ (2 / r)) := by
      field_simp [hL.ne', hB.ne', hF_pos.ne']
    have hEqR :
        (A ^ 2 / ((2 * L) ^ q)) * (1 / (δ ^ 2)) =
          A ^ 2 / ((2 * L) ^ q * δ ^ 2) := by
      field_simp [hL.ne', hδ_pos.ne']
    rw [hEqL, hEqR] at hscaled
    exact le_trans hscaled hu12'
  let c : ℝ := A ^ ((2 : ℝ) / q) / (2 * L) * (B * F) ^ (-(2 / (r * q : ℝ)))
  have hc_nonneg : 0 ≤ c := by positivity
  have hc_pow :
      c ^ q = A ^ 2 / ((2 * L) ^ q * (B * F) ^ (2 / r)) := by
    dsimp [c]
    have hA_nonneg : 0 ≤ A := le_of_lt hA
    have hBF_nonneg : 0 ≤ B * F := by positivity
    have hAq : (A ^ ((2 : ℝ) / q)) ^ q = A ^ 2 := by
      rw [← Real.rpow_mul hA_nonneg]
      simp [hq_ne]
    have hBFq : ((B * F) ^ (-(2 / (r * q : ℝ)))) ^ q = (B * F) ^ (-(2 / r)) := by
      rw [← Real.rpow_mul hBF_nonneg]
      congr 1
      field_simp [hq_ne]
    calc
      (A ^ ((2 : ℝ) / q) / (2 * L) * (B * F) ^ (-(2 / (r * q : ℝ)))) ^ q
        = (A ^ ((2 : ℝ) / q)) ^ q / (2 * L) ^ q *
            ((B * F) ^ (-(2 / (r * q : ℝ)))) ^ q := by
              rw [Real.mul_rpow (by positivity : 0 ≤ A ^ ((2:ℝ)/q) / (2*L))
                                (by positivity : 0 ≤ (B*F) ^ (-(2/(r*q:ℝ))))]
              rw [Real.div_rpow (by positivity : 0 ≤ A ^ ((2:ℝ)/q)) (by positivity : 0 ≤ 2*L)]
        _ = A ^ 2 / (2 * L) ^ q * (B * F) ^ (-(2 / r)) := by
              rw [hAq, hBFq]
        _ = A ^ 2 / ((2 * L) ^ q * (B * F) ^ (2 / r)) := by
              rw [Real.rpow_neg hBF_nonneg]
              field_simp [hL.ne', hB.ne', hF_pos.ne']
  have hc_pow_le : c ^ q ≤ H ^ q := by
    rw [hc_pow]
    exact hu12''
  exact (Real.rpow_le_rpow_iff hc_nonneg hH_nonneg hq_pos).mp hc_pow_le

set_option maxHeartbeats 1000000 in
/-- A local dual sharpness lower bound together with a local Hölder error bound of order
`r` yields one-step power descent with exponent `1 - 2 / (rq)`. -/
lemma localHEB_power_step
    {F Fnext g d δ L A B r : ℝ} {q : ℝ}
    (hq : 2 ≤ q) (hr : 2 ≤ r)
    (hF_pos : 0 < F) (hFnext_pos : 0 < Fnext)
    (hδ_pos : 0 < δ) (hd_nonneg : 0 ≤ d)
    (hF_le_one : F ≤ 1)
    (hL : 0 < L) (hA : 0 < A) (hB : 0 < B)
    (hgap : F ≤ g)
    (hzero : d = 0 → g = 0)
    (hheb : δ ^ r ≤ B * F)
    (hgeom : A * (F / δ) * d ^ q ≤ g)
    (hdec : Fnext ≤ F - (1 / 2) * min g (g ^ 2 / (L * d ^ 2))) :
    let α : ℝ := 2 / (r * q : ℝ)
    let β : ℝ := 1 - α
    let c : ℝ := min (1 / 2 : ℝ)
      (A ^ ((2 : ℝ) / q) / (2 * L * B ^ α))
    let η : ℝ := c / 2
    Fnext ≤ F - η * F ^ (1 + β) := by
  let α : ℝ := 2 / (r * q : ℝ)
  let β : ℝ := 1 - α
  let c : ℝ := min (1 / 2 : ℝ)
    (A ^ ((2 : ℝ) / q) / (2 * L * B ^ α))
  let η : ℝ := c / 2
  have hr_ge : (2 : ℝ) ≤ r := hr
  have hq_pos : 0 < q := by linarith
  have hr_pos : 0 < r := by linarith
  have hq_ne : q ≠ 0 := hq_pos.ne'
  have hr_ne : r ≠ 0 := hr_pos.ne'
  have hrq_pos : 0 < r * q := by positivity
  have hrq_ne : (r * q : ℝ) ≠ 0 := hrq_pos.ne'
  have hα_nonneg : 0 ≤ α := by
    dsimp [α]
    positivity
  have hα_le_one : α ≤ 1 := by
    have hfour_le : (4 : ℝ) ≤ r * q := by nlinarith
    have hhalf : 2 / (r * q : ℝ) ≤ (1 / 2 : ℝ) := by
      exact (_root_.div_le_iff₀ hrq_pos).2 (by nlinarith)
    linarith
  have hβ_nonneg : 0 ≤ β := by
    dsimp [β]
    linarith
  have hc_pos :
      0 < c := by
    dsimp [c]
    have hsmall_pos :
        0 < A ^ ((2 : ℝ) / q) / (2 * L * B ^ α) := by
      positivity
    exact lt_min (by positivity) hsmall_pos
  have hc_le_half : c ≤ 1 / 2 := by
    dsimp [c]
    exact min_le_left _ _
  have hd_pos : 0 < d := by
    by_contra hd0'
    have hd0 : d = 0 := le_antisymm (not_lt.mp hd0') hd_nonneg
    have hg0 : g = 0 := hzero hd0
    exact (not_le_of_gt hF_pos) (by simpa [hg0] using hgap)
  have hH_lower :
      c * F ^ (-α) ≤ Fnext⁻¹ - F⁻¹ := by
    by_cases hcase : g ≤ L * d ^ 2
    · have hsmall_combo :
          A ^ ((2 : ℝ) / q) / (2 * L) * (B * F) ^ (-α) ≤
            Fnext⁻¹ - F⁻¹ := by
        simpa [α, mul_assoc, mul_left_comm, mul_comm] using
          reciprocalIncrement_small_gap_localHEB_lower_bound
            (q := q) (r := r) hq hr_pos hF_pos hFnext_pos hδ_pos hd_pos hL hA hB
            hgap hheb hgeom hdec hcase
      have hsmall :
          (A ^ ((2 : ℝ) / q) / (2 * L * B ^ α)) * F ^ (-α) ≤
            Fnext⁻¹ - F⁻¹ := by
        have hsplit :
            (A ^ ((2 : ℝ) / q) / (2 * L * B ^ α)) * F ^ (-α) =
              (A ^ ((2 : ℝ) / q) / (2 * L)) * (B * F) ^ (-α) := by
          have hpowBF :
              (B * F) ^ (-α) = B ^ (-α) * F ^ (-α) := by
            simpa using
              (show (B * F) ^ (-α) = B ^ (-α) * F ^ (-α) from
                Real.mul_rpow hB.le (le_of_lt hF_pos))
          have hBneg : B ^ (-α) = (B ^ α)⁻¹ := by
            rw [Real.rpow_neg hB.le]
          calc
            (A ^ ((2 : ℝ) / q) / (2 * L * B ^ α)) * F ^ (-α)
                = (A ^ ((2 : ℝ) / q) / (2 * L)) * ((B ^ α)⁻¹ * F ^ (-α)) := by
                    field_simp [hL.ne', (Real.rpow_pos_of_pos hB α).ne']
            _ = (A ^ ((2 : ℝ) / q) / (2 * L)) * (B ^ (-α) * F ^ (-α)) := by
                  rw [hBneg]
            _ = (A ^ ((2 : ℝ) / q) / (2 * L)) * (B * F) ^ (-α) := by
                  rw [← hpowBF]
        exact hsplit.le.trans hsmall_combo
      have hc_cmp :
          c * F ^ (-α) ≤
            (A ^ ((2 : ℝ) / q) / (2 * L * B ^ α)) * F ^ (-α) := by
        exact mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
      exact le_trans hc_cmp hsmall
    · have hlarge_case : L * d ^ 2 ≤ g := le_of_not_ge hcase
      have hlarge :
          1 / (2 * F) ≤ Fnext⁻¹ - F⁻¹ := by
        exact
          reciprocalIncrement_large_gap_universal_lower_bound
            hF_pos hFnext_pos hd_pos hL hgap hdec hlarge_case
      have hpow_le :
          F ^ (-α) ≤ F⁻¹ := by
        have hFinv_ge_one : 1 ≤ F⁻¹ := by
          exact (one_le_inv₀ hF_pos).2 hF_le_one
        calc
          F ^ (-α) = (F⁻¹) ^ α := by
                calc
                  F ^ (-α) = F ^ ((-1 : ℝ) * α) := by ring_nf
                  _ = (F ^ (-1 : ℝ)) ^ α := by
                        rw [Real.rpow_mul (le_of_lt hF_pos)]
                  _ = (F⁻¹) ^ α := by rw [Real.rpow_neg_one]
          _ ≤ (F⁻¹) ^ (1 : ℝ) := by
                exact Real.rpow_le_rpow_of_exponent_le hFinv_ge_one hα_le_one
          _ = F⁻¹ := by rw [Real.rpow_one]
      have hhalf :
          (1 / 2 : ℝ) * F ^ (-α) ≤ 1 / (2 * F) := by
        have hscaled :=
          mul_le_mul_of_nonneg_left hpow_le (by positivity : 0 ≤ (1 / 2 : ℝ))
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hscaled
      have hc_cmp :
          c * F ^ (-α) ≤ (1 / 2 : ℝ) * F ^ (-α) := by
        exact mul_le_mul_of_nonneg_right hc_le_half (by positivity)
      exact le_trans hc_cmp (le_trans hhalf hlarge)
  exact powerDescent_of_reciprocalIncrement_lower_bound
    hF_pos hFnext_pos hF_le_one hβ_nonneg hc_pos hc_le_half
    (by ring) hH_lower

set_option maxHeartbeats 1000000 in
/-- A pointwise local dual sharpness bound together with a pointwise local Hölder error
bound of order `r` yields a shifted polynomial tail with exponent
`rq / (rq - 2)`. -/
theorem gap_shifted_power_bound_of_localHEBGeometry
    {F g d δ : ℕ → ℝ} {L A B M r : ℝ} {q : ℝ}
    (hq : 2 ≤ q) (hr : 2 ≤ r)
    (hF_pos : ∀ t, 0 < F t)
    (hδ_pos : ∀ t, 0 < δ t)
    (hd_nonneg : ∀ t, 0 ≤ d t)
    (hstd : ∀ t, F t ≤ M / (t + 2 : ℝ))
    (hL : 0 < L) (hA : 0 < A) (hB : 0 < B)
    (hgap : ∀ t, F t ≤ g t)
    (hzero : ∀ t, d t = 0 → g t = 0)
    (hheb : ∀ t, (δ t) ^ r ≤ B * F t)
    (hgeom : ∀ t, A * (F t / δ t) * (d t) ^ q ≤ g t)
    (hdec : ∀ t, F (t + 1) ≤ F t - (1 / 2) * min (g t) (g t ^ 2 / (L * (d t) ^ 2))) :
    ∃ T : ℕ, ∃ K : ℝ, 0 < K ∧
      ∀ n : ℕ, F (T + n) ≤ K / (n + 1 : ℝ) ^ ((r * q : ℝ) / (r * q - 2)) := by
  let α : ℝ := 2 / (r * q : ℝ)
  let β : ℝ := 1 - α
  let c : ℝ := min (1 / 2 : ℝ)
    (A ^ ((2 : ℝ) / q) / (2 * L * B ^ α))
  let η : ℝ := c / 2
  let T : ℕ := Nat.ceil M
  have hr_ge : (2 : ℝ) ≤ r := hr
  have hq_pos : 0 < q := by linarith
  have hr_pos : 0 < r := by linarith
  have hrq_pos : 0 < r * q := by positivity
  have hrq_ne : (r * q : ℝ) ≠ 0 := hrq_pos.ne'
  have hα_nonneg : 0 ≤ α := by
    dsimp [α]
    positivity
  have hβ_pos : 0 < β := by
    have hfour_le : (4 : ℝ) ≤ r * q := by nlinarith
    have hhalf : 2 / (r * q : ℝ) ≤ (1 / 2 : ℝ) := by
      exact (_root_.div_le_iff₀ hrq_pos).2 (by nlinarith)
    dsimp [β, α]
    linarith
  have hβ_le_one : β ≤ 1 := by
    dsimp [β, α]
    have hnonneg : 0 ≤ 2 / (r * q : ℝ) := by positivity
    linarith
  have hη_pos : 0 < η := by
    dsimp [η, c]
    positivity
  have hη_le_one : η ≤ 1 := by
    dsimp [η, c]
    nlinarith [min_le_left (1 / 2 : ℝ) (A ^ ((2 : ℝ) / q) / (2 * L * B ^ α))]
  have hF_nonneg : ∀ t, 0 ≤ F t := fun t => (hF_pos t).le
  have hstep_pow :
      ∀ t, T ≤ t → F (t + 1) ≤ F t - η * F t ^ (1 + β) := by
    intro t ht
    have hFt_le_one : F t ≤ 1 :=
      F_le_one_of_std_and_ceil_le hstd (le_trans (Nat.le_ceil M) (by exact_mod_cast ht))
    have hpow :=
      localHEB_power_step
        (q := q) (r := r) hq hr
        (F := F t) (Fnext := F (t + 1)) (g := g t) (d := d t) (δ := δ t)
        (L := L) (A := A) (B := B)
        (hF_pos := hF_pos t) (hFnext_pos := hF_pos (t + 1)) (hδ_pos := hδ_pos t)
        (hd_nonneg := hd_nonneg t)
        (hF_le_one := hFt_le_one) hL hA hB
        (hgap t) (hzero t) (hheb t) (hgeom t) (hdec t)
    simpa [α, β, η, c] using hpow
  have hshift :=
    shifted_power_bound_of_powerDescent_from_ceil
      (F := F) (β := β) (η := η) (M := M)
      hβ_pos hβ_le_one hη_pos hη_le_one hF_nonneg hstd hstep_pow
  have hp_eq : (1 / β : ℝ) = (r * q : ℝ) / (r * q - 2) := by
    dsimp [β, α]
    field_simp [hrq_ne]
  refine ⟨T, (max 1 (1 / (β * η))) ^ (1 / β), ?_, ?_⟩
  · positivity
  · intro n
    simpa [hp_eq, α, β, η, c] using hshift n

set_option maxHeartbeats 1000000 in
/-- A finite prefix does not affect the quantitative local-Hölder tail bound. -/
theorem gap_shifted_power_bound_of_eventually_localHEBGeometry
    {F g d δ : ℕ → ℝ} {L A B M r : ℝ} {q : ℝ}
    (hq : 2 ≤ q) (hr : 2 ≤ r)
    (hF_pos : ∀ t, 0 < F t)
    (hδ_pos : ∀ t, 0 < δ t)
    (hd_nonneg : ∀ t, 0 ≤ d t)
    (hstd : ∀ t, F t ≤ M / (t + 2 : ℝ))
    (hM_nonneg : 0 ≤ M)
    (hL : 0 < L) (hA : 0 < A) (hB : 0 < B)
    (hgap : ∀ t, F t ≤ g t)
    (hzero : ∀ t, d t = 0 → g t = 0)
    (hheb_event : ∀ᶠ t in atTop, (δ t) ^ r ≤ B * F t)
    (hgeom_event : ∀ᶠ t in atTop, A * (F t / δ t) * (d t) ^ q ≤ g t)
    (hdec : ∀ t, F (t + 1) ≤ F t - (1 / 2) * min (g t) (g t ^ 2 / (L * (d t) ^ 2))) :
    ∃ T : ℕ, ∃ K : ℝ, 0 < K ∧
      ∀ n : ℕ, F (T + n) ≤ K / (n + 1 : ℝ) ^ ((r * q : ℝ) / (r * q - 2)) := by
  rcases Filter.Eventually.exists_forall_of_atTop hheb_event with ⟨Nheb, hNheb⟩
  rcases Filter.Eventually.exists_forall_of_atTop hgeom_event with ⟨Ngeom, hNgeom⟩
  let N : ℕ := max Nheb Ngeom
  let F' : ℕ → ℝ := fun t => F (N + t)
  let g' : ℕ → ℝ := fun t => g (N + t)
  let d' : ℕ → ℝ := fun t => d (N + t)
  let δ' : ℕ → ℝ := fun t => δ (N + t)
  have hF'_pos : ∀ t, 0 < F' t := by
    intro t
    exact hF_pos (N + t)
  have hδ'_pos : ∀ t, 0 < δ' t := by
    intro t
    exact hδ_pos (N + t)
  have hstd' : ∀ t, F' t ≤ M / (t + 2 : ℝ) := by
    intro t
    have hbase : F' t ≤ M / (((N + t : ℕ) : ℝ) + 2) := by
      simpa [F', Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hstd (N + t)
    refine hbase.trans ?_
    have hden_left : 0 < (((N + t : ℕ) : ℝ) + 2) := by positivity
    have hden_right : 0 < (t + 2 : ℝ) := by positivity
    refine (_root_.div_le_div_iff₀ hden_left hden_right).2 ?_
    have horder : (t + 2 : ℝ) ≤ (((N + t : ℕ) : ℝ) + 2) := by
      simp only [Nat.cast_add]; linarith [show (0 : ℝ) ≤ (N : ℝ) from Nat.cast_nonneg N]
    nlinarith
  have hgap' : ∀ t, F' t ≤ g' t := by
    intro t
    exact hgap (N + t)
  have hzero' : ∀ t, d' t = 0 → g' t = 0 := by
    intro t hdt
    exact hzero (N + t) hdt
  have hheb' : ∀ t, (δ' t) ^ r ≤ B * F' t := by
    intro t
    exact hNheb (N + t) (le_trans (le_max_left _ _) (Nat.le_add_right _ _))
  have hgeom' : ∀ t, A * (F' t / δ' t) * (d' t) ^ q ≤ g' t := by
    intro t
    exact hNgeom (N + t) (le_trans (le_max_right _ _) (Nat.le_add_right _ _))
  have hdec' :
      ∀ t,
        F' (t + 1) ≤
          F' t - (1 / 2) * min (g' t) (g' t ^ 2 / (L * (d' t) ^ 2)) := by
    intro t
    simpa [F', g', d', Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hdec (N + t)
  obtain ⟨T, K, hK_pos, htail⟩ :=
    gap_shifted_power_bound_of_localHEBGeometry
      (F := F') (g := g') (d := d') (δ := δ')
      (L := L) (A := A) (B := B) (M := M) (r := r) (q := q)
      hq hr hF'_pos hδ'_pos (by intro t; exact hd_nonneg (N + t))
      hstd' hL hA hB hgap' hzero' hheb' hgeom' hdec'
  refine ⟨N + T, K, hK_pos, ?_⟩
  intro n
  simpa [F', Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using htail n

/-- If a nonnegative one-step-decreasing sequence ever hits `0`, then it
stays identically `0` afterwards. -/
lemma zero_tail_of_nonneg_step_le
    {F : ℕ → ℝ}
    (hF_nonneg : ∀ t, 0 ≤ F t)
    (hstep : ∀ t, F (t + 1) ≤ F t)
    {T : ℕ} (hFT : F T = 0) :
    ∀ n : ℕ, F (T + n) = 0 := by
  intro n
  induction n with
  | zero =>
      simpa using hFT
  | succ n ihn =>
      have hle : F (T + n + 1) ≤ F (T + n) := by
        simpa [Nat.add_assoc] using hstep (T + n)
      have hnonneg : 0 ≤ F (T + n + 1) := hF_nonneg (T + n + 1)
      rw [ihn] at hle
      exact le_antisymm hle hnonneg

/-- A local quadratic dual-sharpness condition at a minimizer gives the same refined
one-step open-loop bound as the strongly-convex-set correction lemma. -/
lemma frankWolfeStep_gap_bound_with_localCorrection_two
    {M : Set E} {A : ℝ}
    (hLocal :
      HasLocalLMOGapPowerOn
        O M A 2)
    (f : E → ℝ) (f' : E → E) (L : NNReal)
    (hConv : IsFirstOrderConvex f f')
    (hSmooth : IsLipschitzSmoothUpperBound f L f')
    {x x_star : E} (hx_star : x_star ∈ C) (hxM : x_star ∈ M)
    {γ : ℝ} (hγ : γ ∈ Set.Icc (0 : ℝ) 1)
    (hγsmall : γ ≤ A * ‖f' x‖ / (2 * (L : ℝ))) :
    f (frankWolfeStep O f' x γ) - f x_star ≤
      (1 - γ) * (f x - f x_star) + (L : ℝ) * γ ^ 2 * ‖x - x_star‖ ^ 2 := by
  obtain ⟨ρ, hρ_pos, hρ_geom⟩ := hLocal
  have hdistM : Metric.infDist x_star M < ρ := by
    simpa [Metric.infDist_zero_of_mem hxM] using hρ_pos
  have h_corr_geom :
      A * ‖f' x‖ * ‖x_star - LMO O (f' x)‖ ^ 2 ≤
        (inner (f' x) (x_star - LMO O (f' x)) : ℝ) := by
    simpa [norm_sub_rev] using hρ_geom x_star hx_star hdistM (f' x)
  by_cases hL0 : (L : ℝ) = 0
  · -- L = 0 implies γ = 0, so both sides trivially match
    have hγ0 : γ = 0 := by
      simp [hL0] at hγsmall; linarith [hγ.1, hγsmall]
    simp only [hL0, hγ0, frankWolfeStep, zero_smul, add_zero, zero_mul]
    linarith
  · have hγsmall_kernel : γ * (L : ℝ) ≤ A * ‖f' x‖ := by
      have hL_pos : 0 < (L : ℝ) := lt_of_le_of_ne (by exact_mod_cast L.2) (Ne.symm hL0)
      have hmul := mul_le_mul_of_nonneg_left hγsmall hL_pos.le
      rw [show (L : ℝ) * (A * ‖f' x‖ / (2 * (L : ℝ))) = A * ‖f' x‖ / 2 by
            field_simp [hL0]] at hmul
      nlinarith [hγ.1, hL_pos.le, mul_nonneg hγ.1 hL_pos.le]
    exact frankWolfeStep_gap_bound_quadratic_kernel
      O f f' L hConv hSmooth hγ
      (A := A) hγsmall_kernel h_corr_geom

/-- The higher-order open-loop correction lemma only needs the power-type LMO
gap at the comparison minimizer. -/
lemma frankWolfeStep_gap_bound_with_localCorrection
    {M : Set E} {A : ℝ} {q : ℝ} (hq : 2 < q) (hA : 0 < A)
    (hLocal :
      HasLocalLMOGapPowerOn
        O M A q)
    (f : E → ℝ) (f' : E → E) (L : NNReal)
    (hConv : IsFirstOrderConvex f f')
    (hSmooth : IsLipschitzSmoothUpperBound f L f')
    {x x_star : E} (hx_star : x_star ∈ C) (hxM : x_star ∈ M)
    {γ : ℝ} (hγ : γ ∈ Set.Icc (0 : ℝ) 1) (hγ_pos : 0 < γ)
    (hF_pos : 0 < f x - f x_star) (hδ_pos : 0 < ‖x - x_star‖) :
    let δ : ℝ := ‖x - x_star‖
    let lam : ℝ := 4 * (L : ℝ) * γ * δ / (q * A * (f x - f x_star))
    f (frankWolfeStep O f' x γ) - f x_star ≤
      (1 - γ) * (f x - f x_star) +
        (L : ℝ) * γ ^ 2 * δ ^ 2 +
        ((q - 2 : ℝ) / q) * (L : ℝ) * γ ^ 2 * lam ^ ((2 : ℝ) / (q - 2 : ℝ)) := by
  obtain ⟨ρ, hρ_pos, hρ_geom⟩ := hLocal
  have hdistM : Metric.infDist x_star M < ρ := by
    simpa [Metric.infDist_zero_of_mem hxM] using hρ_pos
  exact frankWolfeStep_gap_bound_power_kernel
    O hq hA f f' L hConv hSmooth hγ hγ_pos hF_pos hδ_pos
    (A := A)
    (by simpa [norm_sub_rev] using hρ_geom x_star hx_star hdistM (f' x))

/-! ### Global short-step convergence -/

/-- Global short-step Frank-Wolfe satisfies the boosted theorem under the local
dual sharpness condition, provided the iterates approach a zero-gradient
minimizer sequence. -/
theorem globalShortStep_localGap_boosted_convergence_of_minimizerSequence_tendsto_zero
    (hC_convex : Convex ℝ C)
    {A : ℝ} {q : ℝ} (hq : 2 ≤ q) (hA : 0 < A)
    (f : E → ℝ) (f' : E → E) (L : NNReal) (hL : 0 < L)
    (hConv : IsFirstOrderConvex f f')
    (hSmooth : IsLipschitzSmoothUpperBound f L f')
    (x_star : E)
    {Mset : Set E}
    (hLocal :
      HasLocalLMOGapPowerOn
        O Mset A q)
    (xStarSeq : ℕ → E)
    (hxStarSeq : ∀ t, xStarSeq t ∈ C)
    (hxStarSeqM : ∀ t, xStarSeq t ∈ Mset)
    (hvalSeq : ∀ t, f (xStarSeq t) = f x_star)
    (hgradSeq : ∀ t, f' (xStarSeq t) = 0)
    {x0 : E} (hx0 : x0 ∈ C)
    (hgap_pos :
      ∀ t,
        0 < f (globalShortStepSequence O f' L x0 t) - f x_star)
    (hδ_zero :
      Tendsto
        (fun t => ‖globalShortStepSequence O f' L x0 t - xStarSeq t‖)
        atTop (nhds 0)) :
    Tendsto
      (fun t : ℕ =>
        (t + 2 : ℝ) *
          (f (globalShortStepSequence O f' L x0 t) - f x_star))
      atTop (nhds 0) := by
  have hL_real : 0 < (L : ℝ) := NNReal.coe_pos.mpr hL
  let xSeq : ℕ → E := globalShortStepSequence O f' L x0
  let s : ℕ → E := fun t => LMO O (f' (xSeq t))
  let F : ℕ → ℝ := fun t => f (xSeq t) - f x_star
  let g : ℕ → ℝ := fun t => inner (f' (xSeq t)) (xSeq t - s t)
  let δ : ℕ → ℝ := fun t => ‖xSeq t - xStarSeq t‖
  let d : ℕ → ℝ := fun t => ‖s t - xSeq t‖
  have hxSeq : ∀ t, xSeq t ∈ C := by
    intro t
    simpa [xSeq] using
      globalShortStepSequence_mem
        (O := O)
        hC_convex f' L hx0 t
  have hF_pos : ∀ t, 0 < F t := by
    intro t
    simpa [F, xSeq] using hgap_pos t
  have hδ_pos : ∀ t, 0 < δ t := by
    intro t
    show 0 < ‖xSeq t - xStarSeq t‖
    exact norm_sub_pos_of_primalGap_pos_of_valSeq hvalSeq hF_pos t
  have hd_pos : ∀ t, 0 < d t := by
    intro t
    have hgap_le : F t ≤ g t := by
      have hgap_le' :
          f (xSeq t) - f (xStarSeq t) ≤ g t := by
        simpa [g, xSeq, s] using
          primalGap_le_lmoGap
            (O := O)
            (C := C) (f := f) (f' := f') hConv
            (x := xSeq t) (x_star := xStarSeq t) (hxStarSeq t)
      simpa [F, hvalSeq t] using hgap_le'
    have hg_pos : 0 < g t := lt_of_lt_of_le (hF_pos t) hgap_le
    by_contra hdt
    have hd0 : d t = 0 := le_antisymm (not_lt.mp hdt) (norm_nonneg _)
    have hsx : s t = xSeq t := by
      exact sub_eq_zero.mp (norm_eq_zero.mp (by simpa [d] using hd0))
    have : g t = 0 := by simp [g, hsx]
    exact hg_pos.ne' this
  have hgap : ∀ t, F t ≤ g t := by
    intro t
    have hgap_le' :
        f (xSeq t) - f (xStarSeq t) ≤ g t := by
      simpa [g, xSeq, s] using
        primalGap_le_lmoGap
          (O := O)
          (C := C) (f := f) (f' := f') hConv
          (x := xSeq t) (x_star := xStarSeq t) (hxStarSeq t)
    simpa [F, hvalSeq t] using hgap_le'
  have hsmooth : ∀ t, F t ≤ ((L : ℝ) / 2) * (δ t) ^ 2 := by
    intro t
    have hsmooth_t :
        f (xSeq t) - f (xStarSeq t) ≤ ((L : ℝ) / 2) * (δ t) ^ 2 := by
      simpa [δ, xSeq] using
        primalGap_le_half_L_mul_sqDist
          (f := f) (f' := f') (L := L) hSmooth
          (x := xSeq t) (x_star := xStarSeq t) (hgradSeq t)
    simpa [F, hvalSeq t] using hsmooth_t
  obtain ⟨ρ, hρ_pos, hρ_geom⟩ := hLocal
  have hgeom_event : ∀ᶠ t in atTop, A * (F t / δ t) * (d t) ^ q ≤ g t := by
    have hδ_event : ∀ᶠ t : ℕ in atTop, δ t < ρ := by
      exact hδ_zero.eventually (Iio_mem_nhds hρ_pos)
    filter_upwards [hδ_event] with t hδt
    have hdistM : Metric.infDist (xSeq t) Mset < ρ := by
      have hle : Metric.infDist (xSeq t) Mset ≤ dist (xSeq t) (xStarSeq t) := by
        exact Metric.infDist_le_dist_of_mem (hxStarSeqM t)
      have hlt : dist (xSeq t) (xStarSeq t) < ρ := by
        simpa [δ, dist_eq_norm] using hδt
      exact lt_of_le_of_lt hle hlt
    have hgradbound : F t / δ t ≤ ‖f' (xSeq t)‖ := by
      have hgradbound_t :
          f (xSeq t) - f (xStarSeq t) ≤ ‖f' (xSeq t)‖ * ‖xSeq t - xStarSeq t‖ := by
        simpa [xSeq] using
          (primalGap_le_gradNorm_mul_dist
            (f := f) (f' := f') hConv
            (x := xSeq t) (x_star := xStarSeq t))
      exact (_root_.div_le_iff₀ (hδ_pos t)).2 <| by simpa [F, δ, hvalSeq t] using hgradbound_t
    let coeff : ℝ := A * (d t) ^ q
    have hcoeff_nonneg : 0 ≤ coeff := by
      dsimp [coeff]
      positivity
    have hscaled :
        coeff * (F t / δ t) ≤ coeff * ‖f' (xSeq t)‖ := by
      exact mul_le_mul_of_nonneg_left hgradbound hcoeff_nonneg
    have hlocal_t :
        A * ‖f' (xSeq t)‖ * (d t) ^ q ≤ g t := by
      simpa [g, d, xSeq, s, norm_sub_rev] using
        (hρ_geom (xSeq t) (hxSeq t) hdistM (f' (xSeq t)))
    have hscaled' :
        A * (F t / δ t) * (d t) ^ q ≤
          A * ‖f' (xSeq t)‖ * (d t) ^ q := by
      simpa [coeff, mul_assoc, mul_left_comm, mul_comm] using hscaled
    exact le_trans hscaled' hlocal_t
  have hdec :
      ∀ t,
        F (t + 1) ≤
          F t - (1 / 2) * min (g t) (g t ^ 2 / ((L : ℝ) * (d t) ^ 2)) := by
    intro t
    have hx_t : xSeq t ∈ C := hxSeq t
    have hstep :
        (1 / 2 : ℝ) * min (g t) (g t ^ 2 / ((L : ℝ) * (d t) ^ 2)) ≤
          f (xSeq t) - f (xSeq (t + 1)) := by
      simpa [xSeq, s, g, d, globalShortStepSequence] using
        (globalShortStep_decrease
          (O := O)
          (C := C) (f := f) (f' := f') (L := L) hSmooth (x := xSeq t) hx_t)
    linarith [hstep]
  have hcore :=
    tendsto_mul_gap_of_decrease_and_eventually_uniformGeometry
      (hq := hq) (hF_pos := hF_pos) (hδ_pos := hδ_pos) (hd_pos := hd_pos)
      (hL := hL_real) (hA := hA) (hδ_zero := by simpa [δ, xSeq] using hδ_zero)
      (hgap := hgap) (hsmooth := hsmooth) (hgeom_event := hgeom_event) (hdec := hdec)
  simpa [F, xSeq] using hcore

/-- Global short-step Frank-Wolfe also satisfies the boosted theorem without a
uniqueness assumption under the local dual sharpness condition. -/
theorem globalShortStep_localGap_boosted_convergence_of_zeroGradient_minimizer
    (hC_convex : Convex ℝ C)
    {A : ℝ} {q : ℝ} (hq : 2 ≤ q) (hA : 0 < A)
    (f : E → ℝ) (f' : E → E) (L : NNReal) (hL : 0 < L)
    (hConv : IsFirstOrderConvex f f')
    (hSmooth : IsLipschitzSmoothUpperBound f L f')
    {x_star : E} (hx_star : x_star ∈ C) (hgrad : f' x_star = 0)
    (hLocal :
      HasLocalLMOGapPowerOn
        O (C ∩ {y : E | f y = f x_star}) A q)
    {x0 : E} (hx0 : x0 ∈ C)
    (h0_bound : f x0 - f x_star ≤ L * (Metric.diam C) ^ 2) :
    Tendsto
      (fun t : ℕ =>
        (t + 2 : ℝ) *
          (f (globalShortStepSequence O f' L x0 t) - f x_star))
      atTop (nhds 0) := by
  let xSeq : ℕ → E := globalShortStepSequence O f' L x0
  let F : ℕ → ℝ := fun t => f (xSeq t) - f x_star
  let M : Set E := C ∩ {y : E | f y = f x_star}
  have hcont : Continuous f :=
    continuous_of_isFirstOrderConvex_isLipschitzSmoothUpperBound (f := f) (f' := f') (L := L) hConv hSmooth
  have hlevel_closed : IsClosed {y : E | f y = f x_star} :=
    isClosed_eq hcont continuous_const
  have hM_compact : IsCompact M := by
    simpa [M] using O.isCompact.inter_right hlevel_closed
  have hM_nonempty : M.Nonempty := by
    refine ⟨x_star, ?_⟩
    simp [M, hx_star]
  have hxSeq : ∀ t, xSeq t ∈ C := by
    intro t
    simpa [xSeq] using
      globalShortStepSequence_mem
        (O := O)
        hC_convex f' L hx0 t
  have hgap_zero :
      Tendsto F atTop (nhds 0) := by
    simpa [F, xSeq] using
      globalShortStep_gap_tendsto_zero
        (O := O)
        hC_convex f f' L hL hConv hSmooth hx_star hgrad hx0 h0_bound
  by_cases hzero : ∃ t, F t = 0
  · rcases hzero with ⟨t0, ht0⟩
    let y := xSeq t0
    have hyval : f y = f x_star := by
      exact sub_eq_zero.mp (by simpa [F, y] using ht0)
    have hygrad : f' y = 0 := by
      exact gradient_eq_zero_of_eq_minimizer_value
        (f := f) (f' := f') (L := L) hL hConv hSmooth hgrad hyval
    have htail : ∀ n, xSeq (t0 + n) = y := by
      intro n
      induction n with
      | zero =>
          simp [y]
      | succ n ih =>
          calc
            xSeq (t0 + (n + 1))
                = globalShortStep O f' L (xSeq (t0 + n)) := by
                    simp [xSeq, globalShortStepSequence]
            _ = globalShortStep O f' L y := by rw [ih]
            _ = y := globalShortStep_eq_self_of_zero_gradient
                (O := O)
                (f' := f') (L := L) hygrad
    have h_eventually :
        ∀ᶠ n : ℕ in atTop, (n + 2 : ℝ) * F n = 0 := by
      refine Filter.eventually_atTop.2 ⟨t0, ?_⟩
      intro n hn
      have hxn : xSeq n = y := by
        have : n = t0 + (n - t0) := by omega
        rw [this]
        exact htail (n - t0)
      simp [F, y, hxn, hyval]
    exact tendsto_nhds_of_eventually_eq h_eventually
  · have hgap_pos : ∀ t, 0 < F t := by
      intro t
      have hnonneg : 0 ≤ F t := by
        dsimp [F, xSeq]
        exact primalGap_nonneg_of_zero_gradient
          (f := f) (f' := f') hConv
          (x := globalShortStepSequence O f' L x0 t)
          (x_star := x_star) hgrad
      have hne : F t ≠ 0 := fun ht => hzero ⟨t, ht⟩
      exact lt_of_le_of_ne hnonneg (by simpa [eq_comm] using hne)
    have hdist_zero :
        Tendsto (fun t => Metric.infDist (xSeq t) M) atTop (nhds 0) := by
      simpa [xSeq, M] using
        tendsto_infDist_minimizerSet_of_gap_tendsto_zero
          O.isCompact (f := f) (f' := f') (L := L) hConv hSmooth x_star xSeq hxSeq
          (by simpa [F] using hgap_zero)
    classical
    let pSeq : ℕ → E := fun t =>
      Classical.choose (hM_compact.exists_infDist_eq_dist hM_nonempty (xSeq t))
    have hpSeq_memM : ∀ t, pSeq t ∈ M := by
      intro t
      exact (Classical.choose_spec (hM_compact.exists_infDist_eq_dist hM_nonempty (xSeq t))).1
    have hpSeq_mem : ∀ t, pSeq t ∈ C := by
      intro t
      exact (hpSeq_memM t).1
    have hpSeq_val : ∀ t, f (pSeq t) = f x_star := by
      intro t
      exact (hpSeq_memM t).2
    have hpSeq_grad : ∀ t, f' (pSeq t) = 0 := by
      intro t
      exact gradient_eq_zero_of_eq_minimizer_value
        (f := f) (f' := f') (L := L) hL hConv hSmooth hgrad (hpSeq_val t)
    have hpSeq_dist : ∀ t, Metric.infDist (xSeq t) M = dist (xSeq t) (pSeq t) := by
      intro t
      exact (Classical.choose_spec (hM_compact.exists_infDist_eq_dist hM_nonempty (xSeq t))).2
    have hδ_zero :
        Tendsto (fun t => ‖xSeq t - pSeq t‖) atTop (nhds 0) := by
      have hdist_zero' :
          Tendsto (fun t => dist (xSeq t) (pSeq t)) atTop (nhds 0) := by
        simpa [hpSeq_dist] using hdist_zero
      simpa [dist_eq_norm] using hdist_zero'
    simpa [xSeq] using
      globalShortStep_localGap_boosted_convergence_of_minimizerSequence_tendsto_zero
        (O := O)
          hC_convex hq hA f f' L hL hConv hSmooth x_star hLocal
          pSeq hpSeq_mem hpSeq_memM hpSeq_val hpSeq_grad hx0
          (by simpa [F, xSeq] using hgap_pos) hδ_zero

/-! ### Exact line-search convergence -/

/-- Exact line-search Frank-Wolfe satisfies the boosted theorem under the
local dual sharpness condition, provided the iterates approach a
zero-gradient minimizer sequence. -/
theorem exactLineSearch_localGap_boosted_convergence_of_minimizerSequence_tendsto_zero
    (hC_convex : Convex ℝ C)
    {A : ℝ} {q : ℝ} (hq : 2 ≤ q) (hA : 0 < A)
    (f : E → ℝ) (f' : E → E) (L : NNReal) (hL : 0 < L)
    (hConv : IsFirstOrderConvex f f')
    (hSmooth : IsLipschitzSmoothUpperBound f L f')
    (x_star : E)
    {Mset : Set E}
    (hLocal :
      HasLocalLMOGapPowerOn
        O Mset A q)
    (xStarSeq : ℕ → E)
    (hxStarSeq : ∀ t, xStarSeq t ∈ C)
    (hxStarSeqM : ∀ t, xStarSeq t ∈ Mset)
    (hvalSeq : ∀ t, f (xStarSeq t) = f x_star)
    (hgradSeq : ∀ t, f' (xStarSeq t) = 0)
    (hLS : LineSearch O f f')
    {x0 : E} (hx0 : x0 ∈ C)
    (hgap_pos :
      ∀ t,
        0 < f
          (exactLineSearchSequence O f f'
            hLS
            x0 t) - f x_star)
    (hδ_zero :
      Tendsto
        (fun t =>
          ‖exactLineSearchSequence O f f'
              hLS
              x0 t - xStarSeq t‖)
        atTop (nhds 0)) :
    Tendsto
      (fun t : ℕ =>
        (t + 2 : ℝ) *
          (f
            (exactLineSearchSequence O f f'
              hLS
              x0 t) - f x_star))
      atTop (nhds 0) := by
  have hL_real : 0 < (L : ℝ) := NNReal.coe_pos.mpr hL
  let hfc : Continuous f := continuous_of_isFirstOrderConvex_isLipschitzSmoothUpperBound (f := f) (f' := f') (L := L) hConv hSmooth
  let xSeq : ℕ → E := exactLineSearchSequence O f f' hLS x0
  let s : ℕ → E := fun t => LMO O (f' (xSeq t))
  let F : ℕ → ℝ := fun t => f (xSeq t) - f x_star
  let g : ℕ → ℝ := fun t => inner (f' (xSeq t)) (xSeq t - s t)
  let δ : ℕ → ℝ := fun t => ‖xSeq t - xStarSeq t‖
  let d : ℕ → ℝ := fun t => ‖s t - xSeq t‖
  have hxSeq : ∀ t, xSeq t ∈ C := by
    intro t
    simpa [xSeq] using
      exactLineSearchSequence_mem
        (O := O)
        hC_convex f f' hLS hx0 t
  have hF_pos : ∀ t, 0 < F t := by
    intro t
    simpa [F, xSeq] using hgap_pos t
  have hδ_pos : ∀ t, 0 < δ t := by
    intro t
    show 0 < ‖xSeq t - xStarSeq t‖
    exact norm_sub_pos_of_primalGap_pos_of_valSeq hvalSeq hF_pos t
  have hd_pos : ∀ t, 0 < d t := by
    intro t
    have hgap_le : F t ≤ g t := by
      have hgap_le' :
          f (xSeq t) - f (xStarSeq t) ≤ g t := by
        simpa [g, xSeq, s] using
          primalGap_le_lmoGap
            (O := O)
            (C := C) (f := f) (f' := f') hConv
            (x := xSeq t) (x_star := xStarSeq t) (hxStarSeq t)
      simpa [F, hvalSeq t] using hgap_le'
    have hg_pos : 0 < g t := lt_of_lt_of_le (hF_pos t) hgap_le
    by_contra hdt
    have hd0 : d t = 0 := le_antisymm (not_lt.mp hdt) (norm_nonneg _)
    have hsx : s t = xSeq t := by
      exact sub_eq_zero.mp (norm_eq_zero.mp (by simpa [d] using hd0))
    have : g t = 0 := by simp [g, hsx]
    exact hg_pos.ne' this
  have hgap : ∀ t, F t ≤ g t := by
    intro t
    have hgap_le' :
        f (xSeq t) - f (xStarSeq t) ≤ g t := by
      simpa [g, xSeq, s] using
        primalGap_le_lmoGap
          (O := O)
          (C := C) (f := f) (f' := f') hConv
          (x := xSeq t) (x_star := xStarSeq t) (hxStarSeq t)
    simpa [F, hvalSeq t] using hgap_le'
  have hsmooth : ∀ t, F t ≤ ((L : ℝ) / 2) * (δ t) ^ 2 := by
    intro t
    have hsmooth_t :
        f (xSeq t) - f (xStarSeq t) ≤ ((L : ℝ) / 2) * (δ t) ^ 2 := by
      simpa [δ, xSeq] using
        primalGap_le_half_L_mul_sqDist
          (f := f) (f' := f') (L := L) hSmooth
          (x := xSeq t) (x_star := xStarSeq t) (hgradSeq t)
    simpa [F, hvalSeq t] using hsmooth_t
  obtain ⟨ρ, hρ_pos, hρ_geom⟩ := hLocal
  have hgeom_event : ∀ᶠ t in atTop, A * (F t / δ t) * (d t) ^ q ≤ g t := by
    have hδ_event : ∀ᶠ t : ℕ in atTop, δ t < ρ := by
      exact hδ_zero.eventually (Iio_mem_nhds hρ_pos)
    filter_upwards [hδ_event] with t hδt
    have hdistM : Metric.infDist (xSeq t) Mset < ρ := by
      have hle : Metric.infDist (xSeq t) Mset ≤ dist (xSeq t) (xStarSeq t) := by
        exact Metric.infDist_le_dist_of_mem (hxStarSeqM t)
      have hlt : dist (xSeq t) (xStarSeq t) < ρ := by
        simpa [δ, dist_eq_norm] using hδt
      exact lt_of_le_of_lt hle hlt
    have hgradbound : F t / δ t ≤ ‖f' (xSeq t)‖ := by
      have hgradbound_t :
          f (xSeq t) - f (xStarSeq t) ≤ ‖f' (xSeq t)‖ * ‖xSeq t - xStarSeq t‖ := by
        simpa [xSeq] using
          (primalGap_le_gradNorm_mul_dist
            (f := f) (f' := f') hConv
            (x := xSeq t) (x_star := xStarSeq t))
      exact (_root_.div_le_iff₀ (hδ_pos t)).2 <| by simpa [F, δ, hvalSeq t] using hgradbound_t
    let coeff : ℝ := A * (d t) ^ q
    have hcoeff_nonneg : 0 ≤ coeff := by
      dsimp [coeff]
      positivity
    have hscaled :
        coeff * (F t / δ t) ≤ coeff * ‖f' (xSeq t)‖ := by
      exact mul_le_mul_of_nonneg_left hgradbound hcoeff_nonneg
    have hlocal_t :
        A * ‖f' (xSeq t)‖ * (d t) ^ q ≤ g t := by
      simpa [g, d, xSeq, s, norm_sub_rev] using
        (hρ_geom (xSeq t) (hxSeq t) hdistM (f' (xSeq t)))
    have hscaled' :
        A * (F t / δ t) * (d t) ^ q ≤
          A * ‖f' (xSeq t)‖ * (d t) ^ q := by
      simpa [coeff, mul_assoc, mul_left_comm, mul_comm] using hscaled
    exact le_trans hscaled' hlocal_t
  have hdec :
      ∀ t,
        F (t + 1) ≤
          F t - (1 / 2) * min (g t) (g t ^ 2 / ((L : ℝ) * (d t) ^ 2)) := by
    intro t
    have hx_t : xSeq t ∈ C := hxSeq t
    have hstep :
        (1 / 2 : ℝ) * min (g t) (g t ^ 2 / ((L : ℝ) * (d t) ^ 2)) ≤
          f (xSeq t) - f (xSeq (t + 1)) := by
      simpa [xSeq, s, g, d, exactLineSearchSequence] using
        (exactLineSearch_decrease
          (O := O)
          (f := f) (f' := f') (L := L) hLS hSmooth (x := xSeq t) hx_t)
    linarith [hstep]
  have hcore :=
    tendsto_mul_gap_of_decrease_and_eventually_uniformGeometry
      (hq := hq) (hF_pos := hF_pos) (hδ_pos := hδ_pos) (hd_pos := hd_pos)
      (hL := hL_real) (hA := hA) (hδ_zero := by simpa [δ, xSeq] using hδ_zero)
      (hgap := hgap) (hsmooth := hsmooth) (hgeom_event := hgeom_event) (hdec := hdec)
  simpa [F, xSeq] using hcore

/-- Exact line-search Frank-Wolfe also satisfies the boosted theorem without a
uniqueness assumption under the local dual sharpness condition. -/
theorem exactLineSearch_localGap_boosted_convergence_of_zeroGradient_minimizer
    (hC_convex : Convex ℝ C)
    {A : ℝ} {q : ℝ} (hq : 2 ≤ q) (hA : 0 < A)
    (f : E → ℝ) (f' : E → E) (L : NNReal) (hL : 0 < L)
    (hConv : IsFirstOrderConvex f f')
    (hSmooth : IsLipschitzSmoothUpperBound f L f')
    {x_star : E} (hx_star : x_star ∈ C) (hgrad : f' x_star = 0)
    (hLocal :
      HasLocalLMOGapPowerOn
        O (C ∩ {y : E | f y = f x_star}) A q)
    (hLS : LineSearch O f f')
    {x0 : E} (hx0 : x0 ∈ C)
    (h0_bound : f x0 - f x_star ≤ L * (Metric.diam C) ^ 2) :
    Tendsto
      (fun t : ℕ =>
        (t + 2 : ℝ) *
          (f
            (exactLineSearchSequence O f f'
              hLS
              x0 t) - f x_star))
      atTop (nhds 0) := by
  let hfc : Continuous f := continuous_of_isFirstOrderConvex_isLipschitzSmoothUpperBound (f := f) (f' := f') (L := L) hConv hSmooth
  let xSeq : ℕ → E := exactLineSearchSequence O f f' hLS x0
  let F : ℕ → ℝ := fun t => f (xSeq t) - f x_star
  let M : Set E := C ∩ {y : E | f y = f x_star}
  have hlevel_closed : IsClosed {y : E | f y = f x_star} :=
    isClosed_eq hfc continuous_const
  have hM_compact : IsCompact M := by
    simpa [M] using O.isCompact.inter_right hlevel_closed
  have hM_nonempty : M.Nonempty := by
    refine ⟨x_star, ?_⟩
    simp [M, hx_star]
  have hxSeq : ∀ t, xSeq t ∈ C := by
    intro t
    simpa [xSeq] using
      exactLineSearchSequence_mem
        (O := O)
        hC_convex f f' hLS hx0 t
  have hgap_zero :
      Tendsto F atTop (nhds 0) := by
    simpa [F, xSeq] using
      exactLineSearch_gap_tendsto_zero
        (O := O)
        hC_convex f f' hLS L hConv hSmooth hx_star hgrad hx0 h0_bound
  by_cases hzero : ∃ t, F t = 0
  · rcases hzero with ⟨t0, ht0⟩
    have htail_val : ∀ n, f (xSeq (t0 + n)) = f x_star := by
      intro n
      induction n with
      | zero =>
          exact sub_eq_zero.mp (by simpa [F, xSeq] using ht0)
      | succ n ih =>
          simpa [xSeq, exactLineSearchSequence, Nat.add_assoc] using
            (exactLineSearch_value_eq_of_eq_minimizer_value
              (O := O)
              (f := f) (f' := f') hLS hConv
              (x := xSeq (t0 + n)) (x_star := x_star) hgrad ih)
    have h_eventually :
        ∀ᶠ n : ℕ in atTop, (n + 2 : ℝ) * F n = 0 := by
      refine Filter.eventually_atTop.2 ⟨t0, ?_⟩
      intro n hn
      have hfn : f (xSeq n) = f x_star := by
        have : n = t0 + (n - t0) := by omega
        rw [this]
        exact htail_val (n - t0)
      simp [F, hfn]
    exact tendsto_nhds_of_eventually_eq h_eventually
  · have hgap_pos : ∀ t, 0 < F t := by
      intro t
      have hnonneg : 0 ≤ F t := by
        dsimp [F, xSeq]
        exact primalGap_nonneg_of_zero_gradient
          (f := f) (f' := f') hConv
          (x := exactLineSearchSequence O f f' hLS x0 t)
          (x_star := x_star) hgrad
      have hne : F t ≠ 0 := fun ht => hzero ⟨t, ht⟩
      exact lt_of_le_of_ne hnonneg (by simpa [eq_comm] using hne)
    have hdist_zero :
        Tendsto (fun t => Metric.infDist (xSeq t) M) atTop (nhds 0) := by
      simpa [xSeq, M] using
        tendsto_infDist_minimizerSet_of_gap_tendsto_zero
          O.isCompact (f := f) (f' := f') (L := L) hConv hSmooth x_star xSeq hxSeq
          (by simpa [F] using hgap_zero)
    classical
    let pSeq : ℕ → E := fun t =>
      Classical.choose (hM_compact.exists_infDist_eq_dist hM_nonempty (xSeq t))
    have hpSeq_memM : ∀ t, pSeq t ∈ M := by
      intro t
      exact (Classical.choose_spec (hM_compact.exists_infDist_eq_dist hM_nonempty (xSeq t))).1
    have hpSeq_mem : ∀ t, pSeq t ∈ C := by
      intro t
      exact (hpSeq_memM t).1
    have hpSeq_val : ∀ t, f (pSeq t) = f x_star := by
      intro t
      exact (hpSeq_memM t).2
    have hpSeq_grad : ∀ t, f' (pSeq t) = 0 := by
      intro t
      exact gradient_eq_zero_of_eq_minimizer_value
        (f := f) (f' := f') (L := L) hL hConv hSmooth hgrad (hpSeq_val t)
    have hpSeq_dist : ∀ t, Metric.infDist (xSeq t) M = dist (xSeq t) (pSeq t) := by
      intro t
      exact (Classical.choose_spec (hM_compact.exists_infDist_eq_dist hM_nonempty (xSeq t))).2
    have hδ_zero :
        Tendsto (fun t => ‖xSeq t - pSeq t‖) atTop (nhds 0) := by
      have hdist_zero' :
          Tendsto (fun t => dist (xSeq t) (pSeq t)) atTop (nhds 0) := by
        simpa [hpSeq_dist] using hdist_zero
      simpa [dist_eq_norm] using hdist_zero'
    simpa [xSeq] using
      exactLineSearch_localGap_boosted_convergence_of_minimizerSequence_tendsto_zero
        (O := O)
          hC_convex hq hA f f' L hL hConv hSmooth x_star hLocal
          pSeq hpSeq_mem hpSeq_memM hpSeq_val hpSeq_grad hLS hx0
          (by simpa [F, xSeq] using hgap_pos) hδ_zero

/-- [FW-POLYAK-LOCAL-SS] Under a local dual sharpness condition near the
optimal level set, the global short-step rule satisfies the Polyak-type
`o(1/t)` conclusion whenever the gradient norm is bounded away from zero on the
whole feasible set. -/
theorem globalShortStep_localGap_polyak_convergence
    (hC_convex : Convex ℝ C)
    {A : ℝ} {q : ℝ} (hq : 2 ≤ q) (hA : 0 < A)
    (f : E → ℝ) (f' : E → E) (L : NNReal) (hL : 0 < L)
    (hConv : IsFirstOrderConvex f f')
    (hSmooth : IsLipschitzSmoothUpperBound f L f')
    {x_star : E} (hx_star : x_star ∈ C)
    (hLocal :
      HasLocalLMOGapPowerOn
        O (C ∩ {y : E | f y = f x_star}) A q)
    (G : ℝ) (hG : 0 < G)
    (hgrad_lb : ∀ x ∈ C, G ≤ ‖f' x‖)
    (hmin : ∀ y ∈ C, f x_star ≤ f y)
    {x0 : E} (hx0 : x0 ∈ C) :
    Tendsto
      (fun t : ℕ =>
        (t + 2 : ℝ) *
          (f (globalShortStepSequence O f' L x0 t) - f x_star))
      atTop (nhds 0) := by
  have hL_real : 0 < (L : ℝ) := NNReal.coe_pos.mpr hL
  let xSeq : ℕ → E := globalShortStepSequence O f' L x0
  let s : ℕ → E := fun t => LMO O (f' (xSeq t))
  let F : ℕ → ℝ := fun t => f (xSeq t) - f x_star
  let g : ℕ → ℝ := fun t => inner (f' (xSeq t)) (xSeq t - s t)
  let δ : ℕ → ℝ := fun t => max (Real.sqrt (2 * F t / (L : ℝ))) (F t / G)
  let d : ℕ → ℝ := fun t => ‖s t - xSeq t‖
  let M : Set E := C ∩ {y : E | f y = f x_star}
  have hxSeq : ∀ t, xSeq t ∈ C := by
    intro t
    simpa [xSeq] using
      globalShortStepSequence_mem
        (O := O)
        hC_convex f' L hx0 t
  have hgap_zero :
      Tendsto F atTop (nhds 0) := by
    simpa [F, xSeq] using
      globalShortStep_gap_tendsto_zero_of_isMinOn
        (O := O)
        hC_convex f f' L hL hConv hSmooth hx_star hmin hx0
  by_cases hzero : ∃ t, F t = 0
  · rcases hzero with ⟨t0, ht0⟩
    let y : E := xSeq t0
    have hy : y ∈ C := by
      simpa [y] using hxSeq t0
    have hyval : f y = f x_star := by
      exact sub_eq_zero.mp (by simpa [F, y] using ht0)
    have hymin : ∀ z ∈ C, f y ≤ f z := by
      intro z hz
      linarith [hmin z hz, hyval]
    have htail : ∀ n, xSeq (t0 + n) = y := by
      intro n
      induction n with
      | zero =>
          simp [y]
      | succ n ih =>
          calc
            xSeq (t0 + (n + 1))
                = globalShortStep O f' L (xSeq (t0 + n)) := by
                    simp [xSeq, globalShortStepSequence]
            _ = globalShortStep O f' L y := by rw [ih]
            _ = y := by
                  exact
                    globalShortStep_eq_self_of_isMinOn
                      (O := O)
                      (C := C) hC_convex f f' L hL hSmooth hy hymin
    have h_eventually :
        ∀ᶠ n : ℕ in atTop, (n + 2 : ℝ) * F n = 0 := by
      refine Filter.eventually_atTop.2 ⟨t0, ?_⟩
      intro n hn
      have hxn : xSeq n = y := by
        have : n = t0 + (n - t0) := by omega
        rw [this]
        exact htail (n - t0)
      simp [F, y, hxn, hyval]
    exact tendsto_nhds_of_eventually_eq h_eventually
  · have hF_pos : ∀ t, 0 < F t := by
      intro t
      have hnonneg : 0 ≤ F t := by
        exact primalGap_nonneg_of_isMinOn (C := C) (f := f) (hxSeq t) hmin
      have hne : F t ≠ 0 := fun ht => hzero ⟨t, ht⟩
      exact lt_of_le_of_ne hnonneg (by simpa [eq_comm] using hne)
    have hδ_pos : ∀ t, 0 < δ t := by
      intro t
      dsimp [δ]
      exact lt_max_of_lt_right (div_pos (hF_pos t) hG)
    have hd_pos : ∀ t, 0 < d t := by
      intro t
      have hgap_le : F t ≤ g t := by
        have hgap_le' :
            f (xSeq t) - f x_star ≤ g t := by
          simpa [g, xSeq, s] using
            primalGap_le_lmoGap
              (O := O)
              (C := C) (f := f) (f' := f') hConv
              (x := xSeq t) (x_star := x_star) hx_star
        simpa [F] using hgap_le'
      have hg_pos : 0 < g t := lt_of_lt_of_le (hF_pos t) hgap_le
      by_contra hdt
      have hd0 : d t = 0 := le_antisymm (not_lt.mp hdt) (norm_nonneg _)
      have hsx : s t = xSeq t := by
        exact sub_eq_zero.mp (norm_eq_zero.mp (by simpa [d] using hd0))
      have : g t = 0 := by simp [g, hsx]
      exact hg_pos.ne' this
    have hδ_zero :
        Tendsto δ atTop (nhds 0) := by
      simpa [δ] using
        tendsto_polyakScale_zero (F := F) (L := (L : ℝ)) (G := G) hgap_zero
    have hgap : ∀ t, F t ≤ g t := by
      intro t
      have hgap_le' :
          f (xSeq t) - f x_star ≤ g t := by
        simpa [g, xSeq, s] using
          primalGap_le_lmoGap
            (O := O)
            (C := C) (f := f) (f' := f') hConv
            (x := xSeq t) (x_star := x_star) hx_star
      simpa [F] using hgap_le'
    have hsmooth : ∀ t, F t ≤ ((L : ℝ) / 2) * (δ t) ^ 2 := by
      intro t
      have hsqrt_nonneg : 0 ≤ 2 * F t / (L : ℝ) := by
        have hnum_nonneg : 0 ≤ 2 * F t := by
          exact mul_nonneg (by positivity : 0 ≤ (2 : ℝ)) (le_of_lt (hF_pos t))
        exact div_nonneg hnum_nonneg hL_real.le
      have hsqrt_le : Real.sqrt (2 * F t / (L : ℝ)) ≤ δ t := by
        dsimp [δ]
        exact le_max_left _ _
      have hsqrt_sq_le :
          (Real.sqrt (2 * F t / (L : ℝ))) ^ 2 ≤ (δ t) ^ 2 := by
        exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqrt_le 2
      have hrewrite : ((L : ℝ) / 2) * (2 * F t / (L : ℝ)) = F t := by
        field_simp [hL_real.ne']
      calc
        F t = ((L : ℝ) / 2) * (2 * F t / (L : ℝ)) := by rw [hrewrite]
        _ = ((L : ℝ) / 2) * (Real.sqrt (2 * F t / (L : ℝ))) ^ 2 := by
              rw [Real.sq_sqrt hsqrt_nonneg]
        _ ≤ ((L : ℝ) / 2) * (δ t) ^ 2 := by
              gcongr
    have hdist_zero :
        Tendsto (fun t => Metric.infDist (xSeq t) M) atTop (nhds 0) := by
      simpa [xSeq, M] using
        tendsto_infDist_minimizerSet_of_gap_tendsto_zero
          O.isCompact (f := f) (f' := f') (L := L) hConv hSmooth x_star xSeq hxSeq
          (by simpa [F] using hgap_zero)
    obtain ⟨ρ, hρ_pos, hρ_geom⟩ := hLocal
    have hgeom_event : ∀ᶠ t in atTop, A * (F t / δ t) * (d t) ^ q ≤ g t := by
      have hdist_event : ∀ᶠ t : ℕ in atTop, Metric.infDist (xSeq t) M < ρ := by
        exact hdist_zero.eventually (Iio_mem_nhds hρ_pos)
      filter_upwards [hdist_event] with t hdist_t
      have hgap_grad : F t / δ t ≤ G := by
        have hδ_ge : F t / G ≤ δ t := by
          dsimp [δ]
          exact le_max_right _ _
        have hprod : F t ≤ δ t * G := by
          exact (_root_.div_le_iff₀ hG).1 hδ_ge
        exact (_root_.div_le_iff₀ (hδ_pos t)).2 <| by
          simpa [mul_comm, mul_left_comm, mul_assoc] using hprod
      have hgradbound : F t / δ t ≤ ‖f' (xSeq t)‖ := by
        exact le_trans hgap_grad (hgrad_lb (xSeq t) (hxSeq t))
      let coeff : ℝ := A * (d t) ^ q
      have hcoeff_nonneg : 0 ≤ coeff := by
        dsimp [coeff]
        positivity
      have hscaled :
          coeff * (F t / δ t) ≤ coeff * ‖f' (xSeq t)‖ := by
        exact mul_le_mul_of_nonneg_left hgradbound hcoeff_nonneg
      have hlocal_t :
          A * ‖f' (xSeq t)‖ * (d t) ^ q ≤ g t := by
        simpa [M, g, d, xSeq, s, norm_sub_rev] using
          (hρ_geom (xSeq t) (hxSeq t) hdist_t (f' (xSeq t)))
      have hscaled' :
          A * (F t / δ t) * (d t) ^ q ≤
            A * ‖f' (xSeq t)‖ * (d t) ^ q := by
        simpa [coeff, mul_assoc, mul_left_comm, mul_comm] using hscaled
      exact le_trans hscaled' hlocal_t
    have hdec :
        ∀ t,
          F (t + 1) ≤
            F t - (1 / 2) * min (g t) (g t ^ 2 / ((L : ℝ) * (d t) ^ 2)) := by
      intro t
      have hstep :
          (1 / 2 : ℝ) * min (g t) (g t ^ 2 / ((L : ℝ) * (d t) ^ 2)) ≤
            f (xSeq t) - f (xSeq (t + 1)) := by
        simpa [xSeq, s, g, d, globalShortStepSequence] using
          (globalShortStep_decrease
            (O := O)
            (C := C) (f := f) (f' := f') (L := L) hSmooth (x := xSeq t) (hxSeq t))
      linarith [hstep]
    have hcore :=
      tendsto_mul_gap_of_decrease_and_eventually_uniformGeometry
        (hq := hq) (hF_pos := hF_pos) (hδ_pos := hδ_pos) (hd_pos := hd_pos)
        (hL := hL_real) (hA := hA) (hδ_zero := hδ_zero)
        (hgap := hgap) (hsmooth := hsmooth) (hgeom_event := hgeom_event) (hdec := hdec)
    simpa [F, xSeq] using hcore

/-- [FW-POLYAK-LOCAL-LS] Under a local dual sharpness condition near the
optimal level set, exact line search satisfies the same Polyak-type `o(1/t)`
conclusion whenever the gradient norm is bounded away from zero on the whole
feasible set. -/
theorem exactLineSearch_localGap_polyak_convergence
    (hC_convex : Convex ℝ C)
    {A : ℝ} {q : ℝ} (hq : 2 ≤ q) (hA : 0 < A)
    (f : E → ℝ) (f' : E → E) (L : NNReal) (hL : 0 < L)
    (hConv : IsFirstOrderConvex f f')
    (hSmooth : IsLipschitzSmoothUpperBound f L f')
    {x_star : E} (hx_star : x_star ∈ C)
    (hLocal :
      HasLocalLMOGapPowerOn
        O (C ∩ {y : E | f y = f x_star}) A q)
    (G : ℝ) (hG : 0 < G)
    (hgrad_lb : ∀ x ∈ C, G ≤ ‖f' x‖)
    (hmin : ∀ y ∈ C, f x_star ≤ f y)
    (hLS : LineSearch O f f')
    {x0 : E} (hx0 : x0 ∈ C) :
    Tendsto
      (fun t : ℕ =>
        (t + 2 : ℝ) *
          (f
            (exactLineSearchSequence O f f'
              hLS
              x0 t) - f x_star))
      atTop (nhds 0) := by
  have hL_real : 0 < (L : ℝ) := NNReal.coe_pos.mpr hL
  let hfc : Continuous f := continuous_of_isFirstOrderConvex_isLipschitzSmoothUpperBound (f := f) (f' := f') (L := L) hConv hSmooth
  let xSeq : ℕ → E := exactLineSearchSequence O f f' hLS x0
  let s : ℕ → E := fun t => LMO O (f' (xSeq t))
  let F : ℕ → ℝ := fun t => f (xSeq t) - f x_star
  let g : ℕ → ℝ := fun t => inner (f' (xSeq t)) (xSeq t - s t)
  let δ : ℕ → ℝ := fun t => max (Real.sqrt (2 * F t / (L : ℝ))) (F t / G)
  let d : ℕ → ℝ := fun t => ‖s t - xSeq t‖
  let M : Set E := C ∩ {y : E | f y = f x_star}
  have hxSeq : ∀ t, xSeq t ∈ C := by
    intro t
    simpa [xSeq] using
      exactLineSearchSequence_mem
        (O := O)
        hC_convex f f' hLS hx0 t
  have hgap_zero :
      Tendsto F atTop (nhds 0) := by
    simpa [F, xSeq] using
      exactLineSearch_gap_tendsto_zero_of_isMinOn
        (O := O)
        hC_convex f f' hLS L hConv hSmooth hx_star hmin hx0
  by_cases hzero : ∃ t, F t = 0
  · rcases hzero with ⟨t0, ht0⟩
    let y : E := xSeq t0
    have hyval : f y = f x_star := by
      exact sub_eq_zero.mp (by simpa [F, y] using ht0)
    have htail_val : ∀ n, f (xSeq (t0 + n)) = f x_star := by
      intro n
      induction n with
      | zero =>
          exact hyval
      | succ n ih =>
          have hmin_n : ∀ z ∈ C, f (xSeq (t0 + n)) ≤ f z := by
            intro z hz
            linarith [hmin z hz, ih]
          have hstep_val :
              f (xSeq (t0 + (n + 1))) = f (xSeq (t0 + n)) := by
            simpa [xSeq, exactLineSearchSequence, Nat.add_assoc] using
              (exactLineSearch_value_eq_of_isMinOn
                (O := O)
                (C := C) hC_convex (f := f) (f' := f') hLS
                (hx := hxSeq (t0 + n)) hmin_n)
          exact hstep_val.trans ih
    have h_eventually :
        ∀ᶠ n : ℕ in atTop, (n + 2 : ℝ) * F n = 0 := by
      refine Filter.eventually_atTop.2 ⟨t0, ?_⟩
      intro n hn
      have hfn : f (xSeq n) = f x_star := by
        have : n = t0 + (n - t0) := by omega
        rw [this]
        exact htail_val (n - t0)
      simp [F, hfn]
    exact tendsto_nhds_of_eventually_eq h_eventually
  · have hF_pos : ∀ t, 0 < F t := by
      intro t
      have hnonneg : 0 ≤ F t := by
        exact primalGap_nonneg_of_isMinOn (C := C) (f := f) (hxSeq t) hmin
      have hne : F t ≠ 0 := fun ht => hzero ⟨t, ht⟩
      exact lt_of_le_of_ne hnonneg (by simpa [eq_comm] using hne)
    have hδ_pos : ∀ t, 0 < δ t := by
      intro t
      dsimp [δ]
      exact lt_max_of_lt_right (div_pos (hF_pos t) hG)
    have hd_pos : ∀ t, 0 < d t := by
      intro t
      have hgap_le : F t ≤ g t := by
        have hgap_le' :
            f (xSeq t) - f x_star ≤ g t := by
          simpa [g, xSeq, s] using
            primalGap_le_lmoGap
              (O := O)
              (C := C) (f := f) (f' := f') hConv
              (x := xSeq t) (x_star := x_star) hx_star
        simpa [F] using hgap_le'
      have hg_pos : 0 < g t := lt_of_lt_of_le (hF_pos t) hgap_le
      by_contra hdt
      have hd0 : d t = 0 := le_antisymm (not_lt.mp hdt) (norm_nonneg _)
      have hsx : s t = xSeq t := by
        exact sub_eq_zero.mp (norm_eq_zero.mp (by simpa [d] using hd0))
      have : g t = 0 := by simp [g, hsx]
      exact hg_pos.ne' this
    have hδ_zero :
        Tendsto δ atTop (nhds 0) := by
      simpa [δ] using
        tendsto_polyakScale_zero (F := F) (L := (L : ℝ)) (G := G) hgap_zero
    have hgap : ∀ t, F t ≤ g t := by
      intro t
      have hgap_le' :
          f (xSeq t) - f x_star ≤ g t := by
        simpa [g, xSeq, s] using
          primalGap_le_lmoGap
            (O := O)
            (C := C) (f := f) (f' := f') hConv
            (x := xSeq t) (x_star := x_star) hx_star
      simpa [F] using hgap_le'
    have hsmooth : ∀ t, F t ≤ ((L : ℝ) / 2) * (δ t) ^ 2 := by
      intro t
      have hsqrt_nonneg : 0 ≤ 2 * F t / (L : ℝ) := by
        have hnum_nonneg : 0 ≤ 2 * F t := by
          exact mul_nonneg (by positivity : 0 ≤ (2 : ℝ)) (le_of_lt (hF_pos t))
        exact div_nonneg hnum_nonneg hL_real.le
      have hsqrt_le : Real.sqrt (2 * F t / (L : ℝ)) ≤ δ t := by
        dsimp [δ]
        exact le_max_left _ _
      have hsqrt_sq_le :
          (Real.sqrt (2 * F t / (L : ℝ))) ^ 2 ≤ (δ t) ^ 2 := by
        exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqrt_le 2
      have hrewrite : ((L : ℝ) / 2) * (2 * F t / (L : ℝ)) = F t := by
        field_simp [hL_real.ne']
      calc
        F t = ((L : ℝ) / 2) * (2 * F t / (L : ℝ)) := by rw [hrewrite]
        _ = ((L : ℝ) / 2) * (Real.sqrt (2 * F t / (L : ℝ))) ^ 2 := by
              rw [Real.sq_sqrt hsqrt_nonneg]
        _ ≤ ((L : ℝ) / 2) * (δ t) ^ 2 := by
              gcongr
    have hdist_zero :
        Tendsto (fun t => Metric.infDist (xSeq t) M) atTop (nhds 0) := by
      simpa [xSeq, M] using
        tendsto_infDist_minimizerSet_of_gap_tendsto_zero
          O.isCompact (f := f) (f' := f') (L := L) hConv hSmooth x_star xSeq hxSeq
          (by simpa [F] using hgap_zero)
    obtain ⟨ρ, hρ_pos, hρ_geom⟩ := hLocal
    have hgeom_event : ∀ᶠ t in atTop, A * (F t / δ t) * (d t) ^ q ≤ g t := by
      have hdist_event : ∀ᶠ t : ℕ in atTop, Metric.infDist (xSeq t) M < ρ := by
        exact hdist_zero.eventually (Iio_mem_nhds hρ_pos)
      filter_upwards [hdist_event] with t hdist_t
      have hgap_grad : F t / δ t ≤ G := by
        have hδ_ge : F t / G ≤ δ t := by
          dsimp [δ]
          exact le_max_right _ _
        have hprod : F t ≤ δ t * G := by
          exact (_root_.div_le_iff₀ hG).1 hδ_ge
        exact (_root_.div_le_iff₀ (hδ_pos t)).2 <| by
          simpa [mul_comm, mul_left_comm, mul_assoc] using hprod
      have hgradbound : F t / δ t ≤ ‖f' (xSeq t)‖ := by
        exact le_trans hgap_grad (hgrad_lb (xSeq t) (hxSeq t))
      let coeff : ℝ := A * (d t) ^ q
      have hcoeff_nonneg : 0 ≤ coeff := by
        dsimp [coeff]
        positivity
      have hscaled :
          coeff * (F t / δ t) ≤ coeff * ‖f' (xSeq t)‖ := by
        exact mul_le_mul_of_nonneg_left hgradbound hcoeff_nonneg
      have hlocal_t :
          A * ‖f' (xSeq t)‖ * (d t) ^ q ≤ g t := by
        simpa [M, g, d, xSeq, s, norm_sub_rev] using
          (hρ_geom (xSeq t) (hxSeq t) hdist_t (f' (xSeq t)))
      have hscaled' :
          A * (F t / δ t) * (d t) ^ q ≤
            A * ‖f' (xSeq t)‖ * (d t) ^ q := by
        simpa [coeff, mul_assoc, mul_left_comm, mul_comm] using hscaled
      exact le_trans hscaled' hlocal_t
    have hdec :
        ∀ t,
          F (t + 1) ≤
            F t - (1 / 2) * min (g t) (g t ^ 2 / ((L : ℝ) * (d t) ^ 2)) := by
      intro t
      have hstep :
          (1 / 2 : ℝ) * min (g t) (g t ^ 2 / ((L : ℝ) * (d t) ^ 2)) ≤
            f (xSeq t) - f (xSeq (t + 1)) := by
        simpa [xSeq, s, g, d, exactLineSearchSequence] using
          (exactLineSearch_decrease
            (O := O)
            (f := f) (f' := f') (L := L) hLS hSmooth (x := xSeq t) (hxSeq t))
      linarith [hstep]
    have hcore :=
      tendsto_mul_gap_of_decrease_and_eventually_uniformGeometry
        (hq := hq) (hF_pos := hF_pos) (hδ_pos := hδ_pos) (hd_pos := hd_pos)
        (hL := hL_real) (hA := hA) (hδ_zero := hδ_zero)
        (hgap := hgap) (hsmooth := hsmooth) (hgeom_event := hgeom_event) (hdec := hdec)
    simpa [F, xSeq] using hcore

/-- [FW-POLYAK-LOCAL-SS-LIN] In the local dual sharpness Polyak regime with `q = 2`,
global short step satisfies an explicit geometric tail bound. -/
theorem globalShortStep_localGap_polyak_linear_rate
    (hC_convex : Convex ℝ C)
    {A : ℝ} (hA : 0 < A)
    (f : E → ℝ) (f' : E → E) (L : NNReal) (hL : 0 < L)
    (hConv : IsFirstOrderConvex f f')
    (hSmooth : IsLipschitzSmoothUpperBound f L f')
    (x_star : E) (hx_star : x_star ∈ C)
    (hLocal :
      HasLocalLMOGapPowerOn
        O (C ∩ {y : E | f y = f x_star}) A 2)
    (G : ℝ) (hG : 0 < G)
    (hgrad_lb : ∀ x ∈ C, G ≤ ‖f' x‖)
    (hmin : ∀ y ∈ C, f x_star ≤ f y)
    (x0 : E) (hx0 : x0 ∈ C) :
    let κ : ℝ := (1 / 2) * min 1 (A * G / (L : ℝ))
    ∃ T : ℕ,
      ∀ n : ℕ,
        f (globalShortStepSequence O f' L x0 (T + n)) - f x_star ≤
          (1 - κ) ^ n *
            (f (globalShortStepSequence O f' L x0 T) - f x_star) := by
  have hL_real : 0 < (L : ℝ) := NNReal.coe_pos.mpr hL
  let xSeq : ℕ → E := globalShortStepSequence O f' L x0
  let s : ℕ → E := fun t => LMO O (f' (xSeq t))
  let F : ℕ → ℝ := fun t => f (xSeq t) - f x_star
  let g : ℕ → ℝ := fun t => inner (f' (xSeq t)) (xSeq t - s t)
  let d : ℕ → ℝ := fun t => ‖s t - xSeq t‖
  let M : Set E := C ∩ {y : E | f y = f x_star}
  have hxSeq : ∀ t, xSeq t ∈ C := by
    intro t
    simpa [xSeq] using
      globalShortStepSequence_mem
        (O := O)
        hC_convex f' L hx0 t
  have hF_nonneg : ∀ t, 0 ≤ F t := by
    intro t
    exact primalGap_nonneg_of_isMinOn (C := C) (f := f) (hxSeq t) hmin
  have hgap_zero :
      Tendsto F atTop (nhds 0) := by
    simpa [F, xSeq] using
      globalShortStep_gap_tendsto_zero_of_isMinOn
        (O := O)
        hC_convex f f' L hL hConv hSmooth hx_star hmin hx0
  have hgap : ∀ t, F t ≤ g t := by
    intro t
    have hgap_le' :
        f (xSeq t) - f x_star ≤ g t := by
      simpa [g, xSeq, s] using
        primalGap_le_lmoGap
          (O := O)
          (C := C) (f := f) (f' := f') hConv
          (x := xSeq t) (x_star := x_star) hx_star
    simpa [F] using hgap_le'
  have hdist_zero :
      Tendsto (fun t => Metric.infDist (xSeq t) M) atTop (nhds 0) := by
    simpa [xSeq, M] using
      tendsto_infDist_minimizerSet_of_gap_tendsto_zero
        O.isCompact (f := f) (f' := f') (L := L) hConv hSmooth x_star xSeq hxSeq hgap_zero
  obtain ⟨ρ, hρ_pos, hρ_geom⟩ := hLocal
  have hgeom_event : ∀ᶠ t in atTop, A * G * (d t) ^ 2 ≤ g t := by
    have hdist_event : ∀ᶠ t : ℕ in atTop, Metric.infDist (xSeq t) M < ρ := by
      exact hdist_zero.eventually (Iio_mem_nhds hρ_pos)
    filter_upwards [hdist_event] with t hdist_t
    let coeff : ℝ := A * (d t) ^ 2
    have hcoeff_nonneg : 0 ≤ coeff := by
      dsimp [coeff]
      positivity
    have hscaled : coeff * G ≤ coeff * ‖f' (xSeq t)‖ := by
      exact mul_le_mul_of_nonneg_left (hgrad_lb (xSeq t) (hxSeq t)) hcoeff_nonneg
    have hlocal_t :
        A * ‖f' (xSeq t)‖ * (d t) ^ 2 ≤ g t := by
      simpa [M, g, d, xSeq, s, norm_sub_rev] using
        (hρ_geom (xSeq t) (hxSeq t) hdist_t (f' (xSeq t)))
    have hscaled' :
        A * G * (d t) ^ 2 ≤ A * ‖f' (xSeq t)‖ * (d t) ^ 2 := by
      simpa [coeff, mul_assoc, mul_left_comm, mul_comm] using hscaled
    exact le_trans hscaled' hlocal_t
  have hzero : ∀ t, d t = 0 → g t = 0 := by
    intro t hd0
    have hsx : s t = xSeq t := by
      exact sub_eq_zero.mp (norm_eq_zero.mp (by simpa [d] using hd0))
    simp [g, hsx]
  have hdec :
      ∀ t,
        F (t + 1) ≤
          F t - (1 / 2) * min (g t) (g t ^ 2 / ((L : ℝ) * (d t) ^ 2)) := by
    intro t
    have hstep :
        (1 / 2 : ℝ) * min (g t) (g t ^ 2 / ((L : ℝ) * (d t) ^ 2)) ≤
          f (xSeq t) - f (xSeq (t + 1)) := by
      simpa [xSeq, s, g, d, globalShortStepSequence] using
        (globalShortStep_decrease
          (O := O)
          (C := C) (f := f) (f' := f') (L := L) hSmooth (x := xSeq t) (hxSeq t))
    linarith [hstep]
  dsimp
  have hcore :=
    gap_le_geometric_of_eventually_polyak_linear_step
      (F := F) (g := g) (d := d) (L := (L : ℝ)) (A := A) (G := G)
      hF_nonneg hL_real hA hG hgap hzero hgeom_event hdec
  simpa [F, xSeq] using hcore

set_option maxHeartbeats 2000000 in
private lemma localGap_polyak_power_rate_kernel
    {A : ℝ} {q : ℝ} (hq : 2 < q) (hA : 0 < A)
    {f : E → ℝ} {f' : E → E} {L : NNReal} (hL_real : 0 < (L : ℝ))
    (hConv : IsFirstOrderConvex f f')
    (hSmooth : IsLipschitzSmoothUpperBound f L f')
    {x_star : E} (hx_star : x_star ∈ C)
    (hLocal :
      HasLocalLMOGapPowerOn
        O (C ∩ {y : E | f y = f x_star}) A q)
    (G : ℝ) (hG : 0 < G)
    (hgrad_lb : ∀ x ∈ C, G ≤ ‖f' x‖)
    (hmin : ∀ y ∈ C, f x_star ≤ f y)
    {xSeq : ℕ → E} (hxSeq : ∀ t, xSeq t ∈ C)
    {Bstd : ℝ} (hBstd_nonneg : 0 ≤ Bstd)
    (hstd : ∀ t, f (xSeq t) - f x_star ≤ (2 * Bstd) / (t + 2 : ℝ))
    (hgap_zero : Tendsto (fun t => f (xSeq t) - f x_star) atTop (nhds 0))
    (hdec : ∀ t,
        f (xSeq (t + 1)) - f x_star ≤
          f (xSeq t) - f x_star -
          (1 / 2) * min
              (inner (f' (xSeq t)) (xSeq t - LMO O (f' (xSeq t))))
              ((inner (f' (xSeq t)) (xSeq t - LMO O (f' (xSeq t)))) ^ 2 /
               ((L : ℝ) * ‖LMO O (f' (xSeq t)) - xSeq t‖ ^ 2))) :
    ∃ T : ℕ, ∃ K : ℝ, 0 < K ∧
      ∀ n : ℕ, f (xSeq (T + n)) - f x_star ≤ K / (n + 1 : ℝ) ^ (q / (q - 2 : ℝ)) := by
  let s : ℕ → E := fun t => LMO O (f' (xSeq t))
  let F : ℕ → ℝ := fun t => f (xSeq t) - f x_star
  let g : ℕ → ℝ := fun t => inner (f' (xSeq t)) (xSeq t - s t)
  let d : ℕ → ℝ := fun t => ‖s t - xSeq t‖
  let Mset : Set E := C ∩ {y : E | f y = f x_star}
  have hF_nonneg : ∀ t, 0 ≤ F t := fun t =>
    primalGap_nonneg_of_isMinOn (C := C) (f := f) (hxSeq t) hmin
  have hd_nonneg : ∀ t, 0 ≤ d t := fun t => by dsimp [d]; positivity
  have hgap : ∀ t, F t ≤ g t := by
    intro t
    have hgap_le' :
        f (xSeq t) - f x_star ≤ g t := by
      simpa [g, s] using
        primalGap_le_lmoGap
          (O := O)
          (C := C) (f := f) (f' := f') hConv
          (x := xSeq t) (x_star := x_star) hx_star
    simpa [F] using hgap_le'
  have hdist_zero :
      Tendsto (fun t => Metric.infDist (xSeq t) Mset) atTop (nhds 0) := by
    simpa [Mset] using
      tendsto_infDist_minimizerSet_of_gap_tendsto_zero
        O.isCompact (f := f) (f' := f') (L := L) hConv hSmooth x_star xSeq hxSeq hgap_zero
  obtain ⟨ρ, hρ_pos, hρ_geom⟩ := hLocal
  have hgeom_event : ∀ᶠ t in atTop, A * G * (d t) ^ q ≤ g t := by
    have hdist_event : ∀ᶠ t : ℕ in atTop, Metric.infDist (xSeq t) Mset < ρ :=
      hdist_zero.eventually (Iio_mem_nhds hρ_pos)
    filter_upwards [hdist_event] with t hdist_t
    let coeff : ℝ := A * (d t) ^ q
    have hcoeff_nonneg : 0 ≤ coeff := by dsimp [coeff]; positivity
    have hscaled : coeff * G ≤ coeff * ‖f' (xSeq t)‖ :=
      mul_le_mul_of_nonneg_left (hgrad_lb (xSeq t) (hxSeq t)) hcoeff_nonneg
    have hlocal_t :
        A * ‖f' (xSeq t)‖ * (d t) ^ q ≤ g t := by
      simpa [Mset, g, d, s, norm_sub_rev] using
        hρ_geom (xSeq t) (hxSeq t) hdist_t (f' (xSeq t))
    have hscaled' :
        A * G * (d t) ^ q ≤ A * ‖f' (xSeq t)‖ * (d t) ^ q := by
      simpa [coeff, mul_assoc, mul_left_comm, mul_comm] using hscaled
    exact le_trans hscaled' hlocal_t
  have hzero : ∀ t, d t = 0 → g t = 0 := by
    intro t hd0
    have hsx : s t = xSeq t :=
      sub_eq_zero.mp (norm_eq_zero.mp (by simpa [d] using hd0))
    simp [g, hsx]
  have hdec' : ∀ t,
      F (t + 1) ≤ F t - (1 / 2) * min (g t) (g t ^ 2 / ((L : ℝ) * (d t) ^ 2)) :=
    fun t => by simpa [F, g, d, s] using hdec t
  have hcore :=
    gap_shifted_power_bound_of_eventually_polyak_uniformGeometry
      (F := F) (g := g) (d := d) (L := (L : ℝ)) (A := A) (G := G) (M := 2 * Bstd) (q := q)
      hq hF_nonneg hstd (by positivity) hL_real hA hG hd_nonneg hgap hzero hgeom_event hdec'
  simpa [F] using hcore

/-- [FW-POLYAK-LOCAL-SS-POW] In the local dual sharpness Polyak regime with `q > 2`,
global short step satisfies a shifted polynomial tail bound with exponent
`q / (q - 2)`. -/
theorem globalShortStep_localGap_polyak_power_rate
    (hC_convex : Convex ℝ C)
    {A : ℝ} {q : ℝ} (hq : 2 < q) (hA : 0 < A)
    (f : E → ℝ) (f' : E → E) (L : NNReal) (hL : 0 < L)
    (hConv : IsFirstOrderConvex f f')
    (hSmooth : IsLipschitzSmoothUpperBound f L f')
    (x_star : E) (hx_star : x_star ∈ C)
    (hLocal :
      HasLocalLMOGapPowerOn
        O (C ∩ {y : E | f y = f x_star}) A q)
    (G : ℝ) (hG : 0 < G)
    (hgrad_lb : ∀ x ∈ C, G ≤ ‖f' x‖)
    (hmin : ∀ y ∈ C, f x_star ≤ f y)
    (x0 : E) (hx0 : x0 ∈ C) :
    ∃ T : ℕ, ∃ K : ℝ, 0 < K ∧
      ∀ n : ℕ,
        f (globalShortStepSequence O f' L x0 (T + n)) - f x_star ≤
          K / (n + 1 : ℝ) ^ ((q : ℝ) / (q - 2 : ℝ)) := by
  have hL_real : 0 < (L : ℝ) := NNReal.coe_pos.mpr hL
  let xSeq : ℕ → E := globalShortStepSequence O f' L x0
  let Dsq : ℝ := (Metric.diam C) ^ 2
  let Bstd : ℝ := max (f x0 - f x_star) ((L : ℝ) * Dsq)
  have hBstd_nonneg : 0 ≤ Bstd :=
    le_trans (primalGap_nonneg_of_isMinOn (C := C) (f := f) hx0 hmin) (le_max_left _ _)
  have hxSeq : ∀ t, xSeq t ∈ C := fun t => by
    simpa [xSeq] using
      globalShortStepSequence_mem
        (O := O)
        hC_convex f' L hx0 t
  have hstd : ∀ t, f (xSeq t) - f x_star ≤ (2 * Bstd) / (t + 2 : ℝ) := fun t => by
    simpa [xSeq, Bstd, Dsq] using
      global_short_step_convergence_of_initialGap_le
        (O := O)
        hC_convex f f' L hL hSmooth hConv hx_star hx0
        (B := Bstd) hBstd_nonneg (le_max_left _ _) (le_max_right _ _) t
  have hgap_zero : Tendsto (fun t => f (xSeq t) - f x_star) atTop (nhds 0) := by
    simpa [xSeq] using
      globalShortStep_gap_tendsto_zero_of_isMinOn
        (O := O)
        hC_convex f f' L hL hConv hSmooth hx_star hmin hx0
  have hdec : ∀ t,
      f (xSeq (t + 1)) - f x_star ≤
        f (xSeq t) - f x_star -
        (1 / 2) * min
            (inner (f' (xSeq t)) (xSeq t - LMO O (f' (xSeq t))))
            ((inner (f' (xSeq t)) (xSeq t - LMO O (f' (xSeq t)))) ^ 2 /
             ((L : ℝ) * ‖LMO O (f' (xSeq t)) - xSeq t‖ ^ 2)) := fun t => by
    have hstep :=
      globalShortStep_decrease (O := O)
        (C := C) f f' L hSmooth (hx := hxSeq t)
    have heq : xSeq (t + 1) = globalShortStep O f' L (xSeq t) := rfl
    rw [heq]; linarith
  simpa [xSeq] using
    localGap_polyak_power_rate_kernel O
      hq hA hL_real hConv hSmooth hx_star hLocal G hG hgrad_lb hmin
      hxSeq hBstd_nonneg hstd hgap_zero hdec

/-- [FW-POLYAK-LOCAL-LS-LIN] In the local dual sharpness Polyak regime with `q = 2`,
exact line search satisfies an explicit geometric tail bound. -/
theorem exactLineSearch_localGap_polyak_linear_rate
    (hC_convex : Convex ℝ C)
    {A : ℝ} (hA : 0 < A)
    (f : E → ℝ) (f' : E → E) (L : NNReal) (hL : 0 < L)
    (hConv : IsFirstOrderConvex f f')
    (hSmooth : IsLipschitzSmoothUpperBound f L f')
    (x_star : E) (hx_star : x_star ∈ C)
    (hLocal :
      HasLocalLMOGapPowerOn
        O (C ∩ {y : E | f y = f x_star}) A 2)
    (G : ℝ) (hG : 0 < G)
    (hgrad_lb : ∀ x ∈ C, G ≤ ‖f' x‖)
    (hmin : ∀ y ∈ C, f x_star ≤ f y)
    (hLS : LineSearch O f f')
    (x0 : E) (hx0 : x0 ∈ C) :
    let κ : ℝ := (1 / 2) * min 1 (A * G / (L : ℝ))
    ∃ T : ℕ,
      ∀ n : ℕ,
        f
          (exactLineSearchSequence O f f'
            hLS
            x0 (T + n)) - f x_star ≤
          (1 - κ) ^ n *
            (f
              (exactLineSearchSequence O f f'
                hLS
                x0 T) - f x_star) := by
  have hL_real : 0 < (L : ℝ) := NNReal.coe_pos.mpr hL
  let hfc : Continuous f := continuous_of_isFirstOrderConvex_isLipschitzSmoothUpperBound (f := f) (f' := f') (L := L) hConv hSmooth
  let xSeq : ℕ → E := exactLineSearchSequence O f f' hLS x0
  let s : ℕ → E := fun t => LMO O (f' (xSeq t))
  let F : ℕ → ℝ := fun t => f (xSeq t) - f x_star
  let g : ℕ → ℝ := fun t => inner (f' (xSeq t)) (xSeq t - s t)
  let d : ℕ → ℝ := fun t => ‖s t - xSeq t‖
  let M : Set E := C ∩ {y : E | f y = f x_star}
  have hxSeq : ∀ t, xSeq t ∈ C := by
    intro t
    simpa [xSeq] using
      exactLineSearchSequence_mem
        (O := O)
        hC_convex f f' hLS hx0 t
  have hF_nonneg : ∀ t, 0 ≤ F t := by
    intro t
    exact primalGap_nonneg_of_isMinOn (C := C) (f := f) (hxSeq t) hmin
  have hgap_zero :
      Tendsto F atTop (nhds 0) := by
    simpa [F, xSeq] using
      exactLineSearch_gap_tendsto_zero_of_isMinOn
        (O := O)
        hC_convex f f' hLS L hConv hSmooth hx_star hmin hx0
  have hgap : ∀ t, F t ≤ g t := by
    intro t
    have hgap_le' :
        f (xSeq t) - f x_star ≤ g t := by
      simpa [g, xSeq, s] using
        primalGap_le_lmoGap
          (O := O)
          (C := C) (f := f) (f' := f') hConv
          (x := xSeq t) (x_star := x_star) hx_star
    simpa [F] using hgap_le'
  have hdist_zero :
      Tendsto (fun t => Metric.infDist (xSeq t) M) atTop (nhds 0) := by
    simpa [xSeq, M] using
      tendsto_infDist_minimizerSet_of_gap_tendsto_zero
        O.isCompact (f := f) (f' := f') (L := L) hConv hSmooth x_star xSeq hxSeq hgap_zero
  obtain ⟨ρ, hρ_pos, hρ_geom⟩ := hLocal
  have hgeom_event : ∀ᶠ t in atTop, A * G * (d t) ^ 2 ≤ g t := by
    have hdist_event : ∀ᶠ t : ℕ in atTop, Metric.infDist (xSeq t) M < ρ := by
      exact hdist_zero.eventually (Iio_mem_nhds hρ_pos)
    filter_upwards [hdist_event] with t hdist_t
    let coeff : ℝ := A * (d t) ^ 2
    have hcoeff_nonneg : 0 ≤ coeff := by
      dsimp [coeff]
      positivity
    have hscaled : coeff * G ≤ coeff * ‖f' (xSeq t)‖ := by
      exact mul_le_mul_of_nonneg_left (hgrad_lb (xSeq t) (hxSeq t)) hcoeff_nonneg
    have hlocal_t :
        A * ‖f' (xSeq t)‖ * (d t) ^ 2 ≤ g t := by
      simpa [M, g, d, xSeq, s, norm_sub_rev] using
        (hρ_geom (xSeq t) (hxSeq t) hdist_t (f' (xSeq t)))
    have hscaled' :
        A * G * (d t) ^ 2 ≤ A * ‖f' (xSeq t)‖ * (d t) ^ 2 := by
      simpa [coeff, mul_assoc, mul_left_comm, mul_comm] using hscaled
    exact le_trans hscaled' hlocal_t
  have hzero : ∀ t, d t = 0 → g t = 0 := by
    intro t hd0
    have hsx : s t = xSeq t := by
      exact sub_eq_zero.mp (norm_eq_zero.mp (by simpa [d] using hd0))
    simp [g, hsx]
  have hdec :
      ∀ t,
        F (t + 1) ≤
          F t - (1 / 2) * min (g t) (g t ^ 2 / ((L : ℝ) * (d t) ^ 2)) := by
    intro t
    have hstep :
        (1 / 2 : ℝ) * min (g t) (g t ^ 2 / ((L : ℝ) * (d t) ^ 2)) ≤
          f (xSeq t) - f (xSeq (t + 1)) := by
      simpa [xSeq, s, g, d, exactLineSearchSequence] using
        (exactLineSearch_decrease
          (O := O)
          (f := f) (f' := f') (L := L) hLS hSmooth (x := xSeq t) (hxSeq t))
    linarith [hstep]
  dsimp
  have hcore :=
    gap_le_geometric_of_eventually_polyak_linear_step
      (F := F) (g := g) (d := d) (L := (L : ℝ)) (A := A) (G := G)
      hF_nonneg hL_real hA hG hgap hzero hgeom_event hdec
  simpa [F, xSeq] using hcore

/-- [FW-POLYAK-LOCAL-LS-POW] In the local dual sharpness Polyak regime with `q > 2`,
exact line search satisfies a shifted polynomial tail bound with exponent
`q / (q - 2)`. -/
theorem exactLineSearch_localGap_polyak_power_rate
    (hC_convex : Convex ℝ C)
    {A : ℝ} {q : ℝ} (hq : 2 < q) (hA : 0 < A)
    (f : E → ℝ) (f' : E → E) (L : NNReal) (hL : 0 < L)
    (hConv : IsFirstOrderConvex f f')
    (hSmooth : IsLipschitzSmoothUpperBound f L f')
    (x_star : E) (hx_star : x_star ∈ C)
    (hLocal :
      HasLocalLMOGapPowerOn
        O (C ∩ {y : E | f y = f x_star}) A q)
    (G : ℝ) (hG : 0 < G)
    (hgrad_lb : ∀ x ∈ C, G ≤ ‖f' x‖)
    (hmin : ∀ y ∈ C, f x_star ≤ f y)
    (hLS : LineSearch O f f')
    (x0 : E) (hx0 : x0 ∈ C) :
    ∃ T : ℕ, ∃ K : ℝ, 0 < K ∧
      ∀ n : ℕ,
        f
          (exactLineSearchSequence O f f'
            hLS
            x0 (T + n)) - f x_star ≤
          K / (n + 1 : ℝ) ^ ((q : ℝ) / (q - 2 : ℝ)) := by
  have hL_real : 0 < (L : ℝ) := NNReal.coe_pos.mpr hL
  let hfc : Continuous f :=
    continuous_of_isFirstOrderConvex_isLipschitzSmoothUpperBound
      (f := f) (f' := f') (L := L) hConv hSmooth
  let xSeq : ℕ → E := exactLineSearchSequence O f f' hLS x0
  let Dsq : ℝ := (Metric.diam C) ^ 2
  let Bstd : ℝ := max (f x0 - f x_star) ((L : ℝ) * Dsq)
  have hBstd_nonneg : 0 ≤ Bstd :=
    le_trans (primalGap_nonneg_of_isMinOn (C := C) (f := f) hx0 hmin) (le_max_left _ _)
  have hxSeq : ∀ t, xSeq t ∈ C := fun t => by
    simpa [xSeq] using
      exactLineSearchSequence_mem
        (O := O)
        hC_convex f f' hLS hx0 t
  have hstd : ∀ t, f (xSeq t) - f x_star ≤ (2 * Bstd) / (t + 2 : ℝ) := fun t => by
    simpa [xSeq, Bstd, Dsq] using
      exact_line_search_convergence_of_initialGap_le
        (O := O)
        hC_convex f f' hLS L hSmooth hConv hx_star hx0
        (B := Bstd) hBstd_nonneg (le_max_left _ _) (le_max_right _ _) t
  have hgap_zero : Tendsto (fun t => f (xSeq t) - f x_star) atTop (nhds 0) := by
    simpa [xSeq] using
      exactLineSearch_gap_tendsto_zero_of_isMinOn
        (O := O)
        hC_convex f f' hLS L hConv hSmooth hx_star hmin hx0
  have hdec : ∀ t,
      f (xSeq (t + 1)) - f x_star ≤
        f (xSeq t) - f x_star -
        (1 / 2) * min
            (inner (f' (xSeq t)) (xSeq t - LMO O (f' (xSeq t))))
            ((inner (f' (xSeq t)) (xSeq t - LMO O (f' (xSeq t)))) ^ 2 /
             ((L : ℝ) * ‖LMO O (f' (xSeq t)) - xSeq t‖ ^ 2)) := fun t => by
    have hstep :=
      exactLineSearch_decrease (O := O)
        f f' L hLS hSmooth (hx := hxSeq t)
    have heq : xSeq (t + 1) = exactLineSearch O f f' hLS (xSeq t) := rfl
    rw [heq]; linarith
  simpa [xSeq] using
    localGap_polyak_power_rate_kernel O
      hq hA hL_real hConv hSmooth hx_star hLocal G hG hgrad_lb hmin
      hxSeq hBstd_nonneg hstd hgap_zero hdec

set_option maxHeartbeats 2000000 in
private lemma localGap_qeb_power_rate_kernel
    {A B : ℝ} {q : ℝ} (hq : 2 ≤ q) (hA : 0 < A) (hB : 0 < B)
    {f : E → ℝ} {f' : E → E} {L : NNReal} (hL_real : 0 < (L : ℝ))
    (hConv : IsFirstOrderConvex f f')
    (hSmooth : IsLipschitzSmoothUpperBound f L f')
    {x_star : E} (hx_star : x_star ∈ C)
    (hLocal :
      HasLocalLMOGapPowerOn
        O (C ∩ {y : E | f y = f x_star}) A q)
    (hQEB :
      HasLocalQuadraticErrorBoundOn
        (C := C) (C ∩ {y : E | f y = f x_star}) f (f x_star) B)
    (hmin : ∀ y ∈ C, f x_star ≤ f y)
    {xSeq : ℕ → E} (hxSeq : ∀ t, xSeq t ∈ C)
    {Bstd : ℝ} (hBstd_nonneg : 0 ≤ Bstd)
    (hstd : ∀ t, f (xSeq t) - f x_star ≤ (2 * Bstd) / (t + 2 : ℝ))
    (hgap_zero : Tendsto (fun t => f (xSeq t) - f x_star) atTop (nhds 0))
    (hdec : ∀ t,
        f (xSeq (t + 1)) - f x_star ≤
          f (xSeq t) - f x_star
          - (1 / 2) * min
              (inner (f' (xSeq t)) (xSeq t - LMO O (f' (xSeq t))))
              ((inner (f' (xSeq t)) (xSeq t - LMO O (f' (xSeq t)))) ^ 2
               / ((L : ℝ) * ‖LMO O (f' (xSeq t)) - xSeq t‖ ^ 2))) :
    ∃ T : ℕ, ∃ K : ℝ, 0 < K ∧
      ∀ n : ℕ, f (xSeq (T + n)) - f x_star ≤ K / (n + 1 : ℝ) ^ (q / (q - 1 : ℝ)) := by
  let s : ℕ → E := fun t => LMO O (f' (xSeq t))
  let F : ℕ → ℝ := fun t => f (xSeq t) - f x_star
  let g : ℕ → ℝ := fun t => inner (f' (xSeq t)) (xSeq t - s t)
  let d : ℕ → ℝ := fun t => ‖s t - xSeq t‖
  let Mset : Set E := C ∩ {y : E | f y = f x_star}
  have hcont : Continuous f :=
    continuous_of_isFirstOrderConvex_isLipschitzSmoothUpperBound (f := f) (f' := f') (L := L) hConv hSmooth
  have hlevel_closed : IsClosed {y : E | f y = f x_star} :=
    isClosed_eq hcont continuous_const
  have hMset_compact : IsCompact Mset := by
    simpa [Mset] using O.isCompact.inter_right hlevel_closed
  have hMset_nonempty : Mset.Nonempty := by
    refine ⟨x_star, ?_⟩
    simp [Mset, hx_star]
  have hF_nonneg : ∀ t, 0 ≤ F t :=
    fun t => primalGap_nonneg_of_isMinOn (C := C) (f := f) (hxSeq t) hmin
  have hd_nonneg : ∀ t, 0 ≤ d t := fun t => by dsimp [d]; positivity
  have hgap : ∀ t, F t ≤ g t := by
    intro t
    simpa [F, g, s] using
      primalGap_le_lmoGap
        (O := O)
        (C := C) (f := f) (f' := f') hConv (x := xSeq t) (x_star := x_star) hx_star
  have hdist_zero :
      Tendsto (fun t => Metric.infDist (xSeq t) Mset) atTop (nhds 0) := by
    simpa [Mset] using
      tendsto_infDist_minimizerSet_of_gap_tendsto_zero
        O.isCompact (f := f) (f' := f') (L := L) hConv hSmooth x_star xSeq hxSeq hgap_zero
  let pSeq : ℕ → E := nearestPoint hMset_compact hMset_nonempty ∘ xSeq
  have hpSeq_memM : ∀ t, pSeq t ∈ Mset :=
      fun t => nearestPoint_mem hMset_compact hMset_nonempty (xSeq t)
  have hpSeq_dist : ∀ t, Metric.infDist (xSeq t) Mset = dist (xSeq t) (pSeq t) :=
      fun t => infDist_nearestPoint hMset_compact hMset_nonempty (xSeq t)
  have hδ_zero' : Filter.Tendsto (fun t => dist (xSeq t) (pSeq t)) Filter.atTop (nhds 0) :=
      tendsto_dist_nearestPoint_of_tendsto_infDist hMset_compact hMset_nonempty hdist_zero
  have hpSeq_val : ∀ t, f (pSeq t) = f x_star := fun t => (hpSeq_memM t).2
  let δ : ℕ → ℝ := fun t => ‖xSeq t - pSeq t‖
  have hδ_zero : Tendsto δ atTop (nhds 0) := hδ_zero'.congr (fun t => dist_eq_norm _ _)
  have hstep_mono : ∀ t, F (t + 1) ≤ F t := by
    intro t
    have hg_nonneg : 0 ≤ g t := le_trans (hF_nonneg t) (hgap t)
    have hdrop_nonneg : 0 ≤ (1 / 2 : ℝ) * min (g t) (g t ^ 2 / ((L : ℝ) * (d t) ^ 2)) :=
      mul_nonneg (by norm_num) (le_min hg_nonneg (by positivity))
    exact le_trans (hdec t) (sub_le_self _ hdrop_nonneg)
  by_cases hzero_hit : ∃ T0, F T0 = 0
  · rcases hzero_hit with ⟨T0, hT0⟩
    refine ⟨T0, 1, by positivity, ?_⟩
    intro n
    have htail0 : F (T0 + n) = 0 :=
      zero_tail_of_nonneg_step_le hF_nonneg hstep_mono hT0 n
    calc
      f (xSeq (T0 + n)) - f x_star = F (T0 + n) := rfl
      _ = 0 := htail0
      _ ≤ (1 : ℝ) / (n + 1 : ℝ) ^ (q / (q - 1 : ℝ)) := by positivity
  · have hF_pos : ∀ t, 0 < F t := by
      intro t
      exact lt_of_le_of_ne (hF_nonneg t) (Ne.symm (fun h => hzero_hit ⟨t, h⟩))
    have hδ_pos : ∀ t, 0 < δ t := by
      intro t
      dsimp [δ]
      exact norm_pos_iff.mpr (sub_ne_zero.mpr
        (fun hEq => hzero_hit ⟨t, by simp [F, hEq, hpSeq_val t]⟩))
    obtain ⟨ρqeb, hρqeb_pos, hqeb_local⟩ := hQEB
    have hqeb_event : ∀ᶠ t in atTop, (δ t) ^ 2 ≤ B * F t := by
      filter_upwards [hδ_zero.eventually (Iio_mem_nhds hρqeb_pos)] with t hδt
      have hdist_t : Metric.infDist (xSeq t) Mset < ρqeb := by
        rw [hpSeq_dist t]; simpa [δ, dist_eq_norm] using hδt
      have hqeb_t :
          Metric.infDist (xSeq t) Mset ^ 2 ≤ B * (f (xSeq t) - f x_star) := by
        simpa [Mset] using hqeb_local (xSeq t) (hxSeq t) hdist_t
      rw [hpSeq_dist t, dist_eq_norm] at hqeb_t
      simpa [δ, F] using hqeb_t
    obtain ⟨ρloc, hρloc_pos, hρloc_geom⟩ := hLocal
    have hgeom_event : ∀ᶠ t in atTop, A * (F t / δ t) * (d t) ^ q ≤ g t := by
      filter_upwards [hδ_zero.eventually (Iio_mem_nhds hρloc_pos)] with t hδt
      have hdist_t : Metric.infDist (xSeq t) Mset < ρloc := by
        rw [hpSeq_dist t]; simpa [δ, dist_eq_norm] using hδt
      have hgradbound : F t / δ t ≤ ‖f' (xSeq t)‖ :=
        (_root_.div_le_iff₀ (hδ_pos t)).2 <| by
          simpa [F, δ, hpSeq_val t] using
            primalGap_le_gradNorm_mul_dist (f := f) (f' := f') hConv
              (x := xSeq t) (x_star := pSeq t)
      have hscaled :
          A * (F t / δ t) * (d t) ^ q ≤ A * ‖f' (xSeq t)‖ * (d t) ^ q :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hgradbound (by positivity)) (by positivity)
      exact le_trans hscaled (by
        simpa [Mset, g, d, s, norm_sub_rev] using
          hρloc_geom (xSeq t) (hxSeq t) hdist_t (f' (xSeq t)))
    have hzero : ∀ t, d t = 0 → g t = 0 := by
      intro t hd0
      simp [g, sub_eq_zero.mp (norm_eq_zero.mp (by simpa [d] using hd0))]
    have hcore :=
      gap_shifted_power_bound_of_eventually_localQEBGeometry
        (F := F) (g := g) (d := d) (δ := δ)
        (L := (L : ℝ)) (A := A) (B := B) (M := 2 * Bstd) (q := q)
        hq hF_pos hδ_pos hd_nonneg hstd (by positivity) hL_real hA hB
        hgap hzero hqeb_event hgeom_event hdec
    simpa [F] using hcore

set_option maxHeartbeats 2000000 in
/-- [FW-LOCAL-QEB-SS] Under a local dual sharpness condition and a local
quadratic error bound around the minimizer set, global short step satisfies
the shifted `q / (q - 1)` tail. -/
theorem globalShortStep_localGap_qeb_power_rate
    (hC_convex : Convex ℝ C)
    {A B : ℝ} {q : ℝ} (hq : 2 ≤ q) (hA : 0 < A) (hB : 0 < B)
    (f : E → ℝ) (f' : E → E) (L : NNReal) (hL : 0 < L)
    (hConv : IsFirstOrderConvex f f')
    (hSmooth : IsLipschitzSmoothUpperBound f L f')
    (x_star : E) (hx_star : x_star ∈ C)
    (hLocal :
      HasLocalLMOGapPowerOn
        O (C ∩ {y : E | f y = f x_star}) A q)
    (hQEB :
      HasLocalQuadraticErrorBoundOn
        (C := C) (C ∩ {y : E | f y = f x_star}) f (f x_star) B)
    (hmin : ∀ y ∈ C, f x_star ≤ f y)
    (x0 : E) (hx0 : x0 ∈ C) :
    ∃ T : ℕ, ∃ K : ℝ, 0 < K ∧
      ∀ n : ℕ,
        f (globalShortStepSequence O f' L x0 (T + n)) - f x_star ≤
          K / (n + 1 : ℝ) ^ ((q : ℝ) / (q - 1 : ℝ)) := by
  have hL_real : 0 < (L : ℝ) := NNReal.coe_pos.mpr hL
  let xSeq : ℕ → E := globalShortStepSequence O f' L x0
  let Dsq : ℝ := (Metric.diam C) ^ 2
  let Bstd : ℝ := max (f x0 - f x_star) ((L : ℝ) * Dsq)
  have hBstd_nonneg : 0 ≤ Bstd :=
    le_trans (primalGap_nonneg_of_isMinOn (C := C) (f := f) hx0 hmin) (le_max_left _ _)
  have hxSeq : ∀ t, xSeq t ∈ C := fun t => by
    simpa [xSeq] using
      globalShortStepSequence_mem (O := O)
        hC_convex f' L hx0 t
  have hstd : ∀ t, f (xSeq t) - f x_star ≤ (2 * Bstd) / (t + 2 : ℝ) := fun t => by
    simpa [xSeq, Bstd, Dsq] using
      global_short_step_convergence_of_initialGap_le
        (O := O)
        hC_convex f f' L hL hSmooth hConv hx_star hx0
        (B := Bstd) hBstd_nonneg (le_max_left _ _) (le_max_right _ _) t
  have hgap_zero : Tendsto (fun t => f (xSeq t) - f x_star) atTop (nhds 0) := by
    simpa [xSeq] using
      globalShortStep_gap_tendsto_zero_of_isMinOn
        (O := O)
        hC_convex f f' L hL hConv hSmooth hx_star hmin hx0
  have hdec : ∀ t,
      f (xSeq (t + 1)) - f x_star ≤
        f (xSeq t) - f x_star
        - (1 / 2) * min
            (inner (f' (xSeq t)) (xSeq t - LMO O (f' (xSeq t))))
            ((inner (f' (xSeq t)) (xSeq t - LMO O (f' (xSeq t)))) ^ 2
             / ((L : ℝ) * ‖LMO O (f' (xSeq t)) - xSeq t‖ ^ 2)) := fun t => by
    have hstep :=
      globalShortStep_decrease (O := O)
        (C := C) f f' L hSmooth (hx := hxSeq t)
    have heq : xSeq (t + 1) = globalShortStep O f' L (xSeq t) := rfl
    rw [heq]; linarith
  simpa [xSeq] using
    localGap_qeb_power_rate_kernel O hq hA hB hL_real hConv hSmooth
      hx_star hLocal hQEB hmin hxSeq hBstd_nonneg hstd hgap_zero hdec

set_option maxHeartbeats 2000000 in
/-- [FW-LOCAL-QEB-LS] Under a local dual sharpness condition and a local
quadratic error bound around the minimizer set, exact line search satisfies
the shifted `q / (q - 1)` tail. -/
theorem exactLineSearch_localGap_qeb_power_rate
    (hC_convex : Convex ℝ C)
    {A B : ℝ} {q : ℝ} (hq : 2 ≤ q) (hA : 0 < A) (hB : 0 < B)
    (f : E → ℝ) (f' : E → E) (L : NNReal) (hL : 0 < L)
    (hConv : IsFirstOrderConvex f f')
    (hSmooth : IsLipschitzSmoothUpperBound f L f')
    (x_star : E) (hx_star : x_star ∈ C)
    (hLocal :
      HasLocalLMOGapPowerOn
        O (C ∩ {y : E | f y = f x_star}) A q)
    (hQEB :
      HasLocalQuadraticErrorBoundOn
        (C := C) (C ∩ {y : E | f y = f x_star}) f (f x_star) B)
    (hmin : ∀ y ∈ C, f x_star ≤ f y)
    (hLS : LineSearch O f f')
    (x0 : E) (hx0 : x0 ∈ C) :
    ∃ T : ℕ, ∃ K : ℝ, 0 < K ∧
      ∀ n : ℕ,
        f
          (exactLineSearchSequence O f f'
            hLS
            x0 (T + n)) - f x_star ≤
          K / (n + 1 : ℝ) ^ ((q : ℝ) / (q - 1 : ℝ)) := by
  have hL_real : 0 < (L : ℝ) := NNReal.coe_pos.mpr hL
  let hfc : Continuous f :=
    continuous_of_isFirstOrderConvex_isLipschitzSmoothUpperBound (f := f) (f' := f') (L := L) hConv hSmooth
  let xSeq : ℕ → E := exactLineSearchSequence O f f' hLS x0
  let Dsq : ℝ := (Metric.diam C) ^ 2
  let Bstd : ℝ := max (f x0 - f x_star) ((L : ℝ) * Dsq)
  have hBstd_nonneg : 0 ≤ Bstd :=
    le_trans (primalGap_nonneg_of_isMinOn (C := C) (f := f) hx0 hmin) (le_max_left _ _)
  have hxSeq : ∀ t, xSeq t ∈ C := fun t => by
    simpa [xSeq] using
      exactLineSearchSequence_mem (O := O)
        hC_convex f f' hLS hx0 t
  have hstd : ∀ t, f (xSeq t) - f x_star ≤ (2 * Bstd) / (t + 2 : ℝ) := fun t => by
    simpa [xSeq, Bstd, Dsq] using
      exact_line_search_convergence_of_initialGap_le
        (O := O)
        hC_convex f f' hLS L hSmooth hConv hx_star hx0
        (B := Bstd) hBstd_nonneg (le_max_left _ _) (le_max_right _ _) t
  have hgap_zero : Tendsto (fun t => f (xSeq t) - f x_star) atTop (nhds 0) := by
    simpa [xSeq] using
      exactLineSearch_gap_tendsto_zero_of_isMinOn
        (O := O)
        hC_convex f f' hLS L hConv hSmooth hx_star hmin hx0
  have hdec : ∀ t,
      f (xSeq (t + 1)) - f x_star ≤
        f (xSeq t) - f x_star
        - (1 / 2) * min
            (inner (f' (xSeq t)) (xSeq t - LMO O (f' (xSeq t))))
            ((inner (f' (xSeq t)) (xSeq t - LMO O (f' (xSeq t)))) ^ 2
             / ((L : ℝ) * ‖LMO O (f' (xSeq t)) - xSeq t‖ ^ 2)) := fun t => by
    have hstep :=
      exactLineSearch_decrease (O := O)
        f f' L hLS hSmooth (hx := hxSeq t)
    have heq : xSeq (t + 1) = exactLineSearch O f f' hLS (xSeq t) := rfl
    rw [heq]; linarith
  simpa [xSeq] using
    localGap_qeb_power_rate_kernel O hq hA hB hL_real hConv hSmooth
      hx_star hLocal hQEB hmin hxSeq hBstd_nonneg hstd hgap_zero hdec

set_option maxHeartbeats 2000000 in
private lemma localGap_heb_power_rate_kernel
    {A B r : ℝ} {q : ℝ} (hq : 2 ≤ q) (hr : 2 ≤ r) (hA : 0 < A) (hB : 0 < B)
    {f : E → ℝ} {f' : E → E} {L : NNReal} (hL_real : 0 < (L : ℝ))
    (hConv : IsFirstOrderConvex f f')
    (hSmooth : IsLipschitzSmoothUpperBound f L f')
    {x_star : E} (hx_star : x_star ∈ C)
    (hLocal :
      HasLocalLMOGapPowerOn
        O (C ∩ {y : E | f y = f x_star}) A q)
    (hHEB :
      HasLocalHolderErrorBoundOn
        (C := C) (C ∩ {y : E | f y = f x_star}) f (f x_star) B r)
    (hmin : ∀ y ∈ C, f x_star ≤ f y)
    {xSeq : ℕ → E} (hxSeq : ∀ t, xSeq t ∈ C)
    {Bstd : ℝ} (hBstd_nonneg : 0 ≤ Bstd)
    (hstd : ∀ t, f (xSeq t) - f x_star ≤ (2 * Bstd) / (t + 2 : ℝ))
    (hgap_zero : Tendsto (fun t => f (xSeq t) - f x_star) atTop (nhds 0))
    (hdec : ∀ t,
        f (xSeq (t + 1)) - f x_star ≤
          f (xSeq t) - f x_star
          - (1 / 2) * min
              (inner (f' (xSeq t)) (xSeq t - LMO O (f' (xSeq t))))
              ((inner (f' (xSeq t)) (xSeq t - LMO O (f' (xSeq t)))) ^ 2
               / ((L : ℝ) * ‖LMO O (f' (xSeq t)) - xSeq t‖ ^ 2))) :
    ∃ T : ℕ, ∃ K : ℝ, 0 < K ∧
      ∀ n : ℕ, f (xSeq (T + n)) - f x_star ≤ K / (n + 1 : ℝ) ^ ((r * q : ℝ) / (r * q - 2)) := by
  let s : ℕ → E := fun t => LMO O (f' (xSeq t))
  let F : ℕ → ℝ := fun t => f (xSeq t) - f x_star
  let g : ℕ → ℝ := fun t => inner (f' (xSeq t)) (xSeq t - s t)
  let d : ℕ → ℝ := fun t => ‖s t - xSeq t‖
  let Mset : Set E := C ∩ {y : E | f y = f x_star}
  have hcont : Continuous f :=
    continuous_of_isFirstOrderConvex_isLipschitzSmoothUpperBound (f := f) (f' := f') (L := L) hConv hSmooth
  have hlevel_closed : IsClosed {y : E | f y = f x_star} :=
    isClosed_eq hcont continuous_const
  have hMset_compact : IsCompact Mset := by
    simpa [Mset] using O.isCompact.inter_right hlevel_closed
  have hMset_nonempty : Mset.Nonempty := by
    refine ⟨x_star, ?_⟩
    simp [Mset, hx_star]
  have hF_nonneg : ∀ t, 0 ≤ F t :=
    fun t => primalGap_nonneg_of_isMinOn (C := C) (f := f) (hxSeq t) hmin
  have hd_nonneg : ∀ t, 0 ≤ d t := fun t => by dsimp [d]; positivity
  have hgap : ∀ t, F t ≤ g t := by
    intro t
    simpa [F, g, s] using
      primalGap_le_lmoGap
        (O := O)
        (C := C) (f := f) (f' := f') hConv (x := xSeq t) (x_star := x_star) hx_star
  have hdist_zero :
      Tendsto (fun t => Metric.infDist (xSeq t) Mset) atTop (nhds 0) := by
    simpa [Mset] using
      tendsto_infDist_minimizerSet_of_gap_tendsto_zero
        O.isCompact (f := f) (f' := f') (L := L) hConv hSmooth x_star xSeq hxSeq hgap_zero
  let pSeq : ℕ → E := nearestPoint hMset_compact hMset_nonempty ∘ xSeq
  have hpSeq_memM : ∀ t, pSeq t ∈ Mset :=
      fun t => nearestPoint_mem hMset_compact hMset_nonempty (xSeq t)
  have hpSeq_dist : ∀ t, Metric.infDist (xSeq t) Mset = dist (xSeq t) (pSeq t) :=
      fun t => infDist_nearestPoint hMset_compact hMset_nonempty (xSeq t)
  have hδ_zero' : Filter.Tendsto (fun t => dist (xSeq t) (pSeq t)) Filter.atTop (nhds 0) :=
      tendsto_dist_nearestPoint_of_tendsto_infDist hMset_compact hMset_nonempty hdist_zero
  have hpSeq_val : ∀ t, f (pSeq t) = f x_star := fun t => (hpSeq_memM t).2
  let δ : ℕ → ℝ := fun t => ‖xSeq t - pSeq t‖
  have hδ_zero : Tendsto δ atTop (nhds 0) := hδ_zero'.congr (fun t => dist_eq_norm _ _)
  have hstep_mono : ∀ t, F (t + 1) ≤ F t := by
    intro t
    have hg_nonneg : 0 ≤ g t := le_trans (hF_nonneg t) (hgap t)
    have hdrop_nonneg : 0 ≤ (1 / 2 : ℝ) * min (g t) (g t ^ 2 / ((L : ℝ) * (d t) ^ 2)) :=
      mul_nonneg (by norm_num) (le_min hg_nonneg (by positivity))
    exact le_trans (hdec t) (sub_le_self _ hdrop_nonneg)
  by_cases hzero_hit : ∃ T0, F T0 = 0
  · rcases hzero_hit with ⟨T0, hT0⟩
    refine ⟨T0, 1, by positivity, ?_⟩
    intro n
    have htail0 : F (T0 + n) = 0 :=
      zero_tail_of_nonneg_step_le hF_nonneg hstep_mono hT0 n
    calc
      f (xSeq (T0 + n)) - f x_star = F (T0 + n) := rfl
      _ = 0 := htail0
      _ ≤ (1 : ℝ) / (n + 1 : ℝ) ^ ((r * q : ℝ) / (r * q - 2)) := by positivity
  · have hF_pos : ∀ t, 0 < F t := by
      intro t
      exact lt_of_le_of_ne (hF_nonneg t) (Ne.symm (fun h => hzero_hit ⟨t, h⟩))
    have hδ_pos : ∀ t, 0 < δ t := by
      intro t
      dsimp [δ]
      exact norm_pos_iff.mpr (sub_ne_zero.mpr
        (fun hEq => hzero_hit ⟨t, by simp [F, hEq, hpSeq_val t]⟩))
    obtain ⟨ρheb, hρheb_pos, hheb_local⟩ := hHEB
    have hheb_event : ∀ᶠ t in atTop, (δ t) ^ r ≤ B * F t := by
      filter_upwards [hδ_zero.eventually (Iio_mem_nhds hρheb_pos)] with t hδt
      have hdist_t : Metric.infDist (xSeq t) Mset < ρheb := by
        rw [hpSeq_dist t]; simpa [δ, dist_eq_norm] using hδt
      have hheb_t :
          Metric.infDist (xSeq t) Mset ^ r ≤ B * (f (xSeq t) - f x_star) := by
        simpa [Mset] using hheb_local (xSeq t) (hxSeq t) hdist_t
      rw [hpSeq_dist t, dist_eq_norm] at hheb_t
      simpa [δ, F] using hheb_t
    obtain ⟨ρloc, hρloc_pos, hρloc_geom⟩ := hLocal
    have hgeom_event : ∀ᶠ t in atTop, A * (F t / δ t) * (d t) ^ q ≤ g t := by
      filter_upwards [hδ_zero.eventually (Iio_mem_nhds hρloc_pos)] with t hδt
      have hdist_t : Metric.infDist (xSeq t) Mset < ρloc := by
        rw [hpSeq_dist t]; simpa [δ, dist_eq_norm] using hδt
      have hgradbound : F t / δ t ≤ ‖f' (xSeq t)‖ :=
        (_root_.div_le_iff₀ (hδ_pos t)).2 <| by
          simpa [F, δ, hpSeq_val t] using
            primalGap_le_gradNorm_mul_dist (f := f) (f' := f') hConv
              (x := xSeq t) (x_star := pSeq t)
      have hscaled :
          A * (F t / δ t) * (d t) ^ q ≤ A * ‖f' (xSeq t)‖ * (d t) ^ q :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hgradbound (by positivity)) (by positivity)
      exact le_trans hscaled (by
        simpa [Mset, g, d, s, norm_sub_rev] using
          hρloc_geom (xSeq t) (hxSeq t) hdist_t (f' (xSeq t)))
    have hzero : ∀ t, d t = 0 → g t = 0 := by
      intro t hd0
      simp [g, sub_eq_zero.mp (norm_eq_zero.mp (by simpa [d] using hd0))]
    have hcore :=
      gap_shifted_power_bound_of_eventually_localHEBGeometry
        (F := F) (g := g) (d := d) (δ := δ)
        (L := (L : ℝ)) (A := A) (B := B) (M := 2 * Bstd) (r := r) (q := q)
        hq hr hF_pos hδ_pos hd_nonneg hstd (by positivity) hL_real hA hB
        hgap hzero hheb_event hgeom_event hdec
    simpa [F] using hcore

set_option maxHeartbeats 2000000 in
/-- [FW-LOCAL-HEB-SS] Under a local dual sharpness condition and a local
Hölder error bound of order `r ≥ 2` around the minimizer set, global short
step satisfies the shifted `rq / (rq - 2)` tail. -/
theorem globalShortStep_localGap_heb_power_rate
    (hC_convex : Convex ℝ C)
    {A B r : ℝ} {q : ℝ} (hq : 2 ≤ q) (hr : 2 ≤ r) (hA : 0 < A) (hB : 0 < B)
    (f : E → ℝ) (f' : E → E) (L : NNReal) (hL : 0 < L)
    (hConv : IsFirstOrderConvex f f')
    (hSmooth : IsLipschitzSmoothUpperBound f L f')
    (x_star : E) (hx_star : x_star ∈ C)
    (hLocal :
      HasLocalLMOGapPowerOn
        O (C ∩ {y : E | f y = f x_star}) A q)
    (hHEB :
      HasLocalHolderErrorBoundOn
        (C := C) (C ∩ {y : E | f y = f x_star}) f (f x_star) B r)
    (hmin : ∀ y ∈ C, f x_star ≤ f y)
    (x0 : E) (hx0 : x0 ∈ C) :
    ∃ T : ℕ, ∃ K : ℝ, 0 < K ∧
      ∀ n : ℕ,
        f (globalShortStepSequence O f' L x0 (T + n)) - f x_star ≤
          K / (n + 1 : ℝ) ^ ((r * q : ℝ) / (r * q - 2)) := by
  have hL_real : 0 < (L : ℝ) := NNReal.coe_pos.mpr hL
  let xSeq : ℕ → E := globalShortStepSequence O f' L x0
  let Dsq : ℝ := (Metric.diam C) ^ 2
  let Bstd : ℝ := max (f x0 - f x_star) ((L : ℝ) * Dsq)
  have hBstd_nonneg : 0 ≤ Bstd :=
    le_trans (primalGap_nonneg_of_isMinOn (C := C) (f := f) hx0 hmin) (le_max_left _ _)
  have hxSeq : ∀ t, xSeq t ∈ C := fun t => by
    simpa [xSeq] using
      globalShortStepSequence_mem (O := O)
        hC_convex f' L hx0 t
  have hstd : ∀ t, f (xSeq t) - f x_star ≤ (2 * Bstd) / (t + 2 : ℝ) := fun t => by
    simpa [xSeq, Bstd, Dsq] using
      global_short_step_convergence_of_initialGap_le
        (O := O)
        hC_convex f f' L hL hSmooth hConv hx_star hx0
        (B := Bstd) hBstd_nonneg (le_max_left _ _) (le_max_right _ _) t
  have hgap_zero : Tendsto (fun t => f (xSeq t) - f x_star) atTop (nhds 0) := by
    simpa [xSeq] using
      globalShortStep_gap_tendsto_zero_of_isMinOn
        (O := O)
        hC_convex f f' L hL hConv hSmooth hx_star hmin hx0
  have hdec : ∀ t,
      f (xSeq (t + 1)) - f x_star ≤
        f (xSeq t) - f x_star
        - (1 / 2) * min
            (inner (f' (xSeq t)) (xSeq t - LMO O (f' (xSeq t))))
            ((inner (f' (xSeq t)) (xSeq t - LMO O (f' (xSeq t)))) ^ 2
             / ((L : ℝ) * ‖LMO O (f' (xSeq t)) - xSeq t‖ ^ 2)) := fun t => by
    have hstep :=
      globalShortStep_decrease (O := O)
        (C := C) f f' L hSmooth (hx := hxSeq t)
    have heq : xSeq (t + 1) = globalShortStep O f' L (xSeq t) := rfl
    rw [heq]; linarith
  simpa [xSeq] using
    localGap_heb_power_rate_kernel O hq hr hA hB hL_real hConv hSmooth
      hx_star hLocal hHEB hmin hxSeq hBstd_nonneg hstd hgap_zero hdec

set_option maxHeartbeats 2000000 in
/-- [FW-LOCAL-HEB-LS] Under a local dual sharpness condition and a local
Hölder error bound of order `r ≥ 2` around the minimizer set, exact line
search satisfies the shifted `rq / (rq - 2)` tail. -/
theorem exactLineSearch_localGap_heb_power_rate
    (hC_convex : Convex ℝ C)
    {A B r : ℝ} {q : ℝ} (hq : 2 ≤ q) (hr : 2 ≤ r) (hA : 0 < A) (hB : 0 < B)
    (f : E → ℝ) (f' : E → E) (L : NNReal) (hL : 0 < L)
    (hConv : IsFirstOrderConvex f f')
    (hSmooth : IsLipschitzSmoothUpperBound f L f')
    (x_star : E) (hx_star : x_star ∈ C)
    (hLocal :
      HasLocalLMOGapPowerOn
        O (C ∩ {y : E | f y = f x_star}) A q)
    (hHEB :
      HasLocalHolderErrorBoundOn
        (C := C) (C ∩ {y : E | f y = f x_star}) f (f x_star) B r)
    (hmin : ∀ y ∈ C, f x_star ≤ f y)
    (hLS : LineSearch O f f')
    (x0 : E) (hx0 : x0 ∈ C) :
    ∃ T : ℕ, ∃ K : ℝ, 0 < K ∧
      ∀ n : ℕ,
        f
          (exactLineSearchSequence O f f'
            hLS
            x0 (T + n)) - f x_star ≤
          K / (n + 1 : ℝ) ^ ((r * q : ℝ) / (r * q - 2)) := by
  have hL_real : 0 < (L : ℝ) := NNReal.coe_pos.mpr hL
  let hfc : Continuous f :=
    continuous_of_isFirstOrderConvex_isLipschitzSmoothUpperBound (f := f) (f' := f') (L := L) hConv hSmooth
  let xSeq : ℕ → E := exactLineSearchSequence O f f' hLS x0
  let Dsq : ℝ := (Metric.diam C) ^ 2
  let Bstd : ℝ := max (f x0 - f x_star) ((L : ℝ) * Dsq)
  have hBstd_nonneg : 0 ≤ Bstd :=
    le_trans (primalGap_nonneg_of_isMinOn (C := C) (f := f) hx0 hmin) (le_max_left _ _)
  have hxSeq : ∀ t, xSeq t ∈ C := fun t => by
    simpa [xSeq] using
      exactLineSearchSequence_mem (O := O)
        hC_convex f f' hLS hx0 t
  have hstd : ∀ t, f (xSeq t) - f x_star ≤ (2 * Bstd) / (t + 2 : ℝ) := fun t => by
    simpa [xSeq, Bstd, Dsq] using
      exact_line_search_convergence_of_initialGap_le
        (O := O)
        hC_convex f f' hLS L hSmooth hConv hx_star hx0
        (B := Bstd) hBstd_nonneg (le_max_left _ _) (le_max_right _ _) t
  have hgap_zero : Tendsto (fun t => f (xSeq t) - f x_star) atTop (nhds 0) := by
    simpa [xSeq] using
      exactLineSearch_gap_tendsto_zero_of_isMinOn
        (O := O)
        hC_convex f f' hLS L hConv hSmooth hx_star hmin hx0
  have hdec : ∀ t,
      f (xSeq (t + 1)) - f x_star ≤
        f (xSeq t) - f x_star
        - (1 / 2) * min
            (inner (f' (xSeq t)) (xSeq t - LMO O (f' (xSeq t))))
            ((inner (f' (xSeq t)) (xSeq t - LMO O (f' (xSeq t)))) ^ 2
             / ((L : ℝ) * ‖LMO O (f' (xSeq t)) - xSeq t‖ ^ 2)) := fun t => by
    have hstep :=
      exactLineSearch_decrease (O := O)
        f f' L hLS hSmooth (hx := hxSeq t)
    have heq : xSeq (t + 1) = exactLineSearch O f f' hLS (xSeq t) := rfl
    rw [heq]; linarith
  simpa [xSeq] using
    localGap_heb_power_rate_kernel O hq hr hA hB hL_real hConv hSmooth
      hx_star hLocal hHEB hmin hxSeq hBstd_nonneg hstd hgap_zero hdec

/-! ### Open-loop convergence (canonical γ_t = 2 / (t + 2)) -/

set_option maxHeartbeats 7000000 in
/-- [FW-LOCAL-HEB-OL] Under a local dual sharpness condition and a local
Hölder error bound of order `r ≥ 2` around the minimizer set, the canonical
open-loop rule `γ_t = 2 / (t + 2)` satisfies the shifted `rq / (rq - 2)` tail
for exponents `q > 2`. -/
theorem frankWolfe_localGap_heb_power_rate
    (hC_convex : Convex ℝ C)
    {A B r : ℝ} {q : ℝ} (hq : 2 < q) (hr : 2 ≤ r) (hA : 0 < A) (hB : 0 < B)
    (f : E → ℝ) (f' : E → E) (L : NNReal) (hL : 0 < L)
    (hConv : IsFirstOrderConvex f f')
    (hSmooth : IsLipschitzSmoothUpperBound f L f')
    (x_star : E) (hx_star : x_star ∈ C)
    (hLocal :
      HasLocalLMOGapPowerOn
        O (C ∩ {y : E | f y = f x_star}) A q)
    (hHEB :
      HasLocalHolderErrorBoundOn
        (C := C) (C ∩ {y : E | f y = f x_star}) f (f x_star) B r)
    (hmin : ∀ y ∈ C, f x_star ≤ f y)
    (x0 : E) (hx0 : x0 ∈ C) :
    ∃ T : ℕ, ∃ K : ℝ, 0 < K ∧
      ∀ n : ℕ,
        f (frankWolfeSequence O f' x0 (T + n)) - f x_star ≤
          K / (n + 1 : ℝ) ^ ((r * q : ℝ) / (r * q - 2)) := by
  let xSeq : ℕ → E := frankWolfeSequence O f' x0
  let s : ℕ → E := fun t => LMO O (f' (xSeq t))
  let F : ℕ → ℝ := fun t => f (xSeq t) - f x_star
  let d : ℕ → ℝ := fun t => ‖s t - xSeq t‖
  let Mset : Set E := C ∩ {y : E | f y = f x_star}
  let Dsq : ℝ := (Metric.diam C) ^ 2
  let Bstd : ℝ := max (f x0 - f x_star) ((L : ℝ) * Dsq)
  let H : ℕ → ℝ := fun t => (t + 2 : ℝ) * F t
  have hq_pos : 0 < q := by linarith
  have hr_pos : 0 < r := by linarith
  have hr_nonneg : 0 ≤ r := hr_pos.le
  have hr_ne : r ≠ 0 := hr_pos.ne'
  have hq_sub_pos : 0 < (q - 2 : ℝ) := by
    linarith
  have hq_sub_ne : (q - 2 : ℝ) ≠ 0 := hq_sub_pos.ne'
  have hq_one_pos : 0 < (q - 1 : ℝ) := by
    linarith
  have hq_one_ne : (q - 1 : ℝ) ≠ 0 := hq_one_pos.ne'
  have hrq_sub_pos : 0 < r * q - 2 := by
    nlinarith
  have hrq_sub_ne : r * q - 2 ≠ 0 := hrq_sub_pos.ne'
  let σ : ℝ := 2 / (r * q - 2)
  let theta : ℝ := 2 / (r * (q - 2 : ℝ))
  let betaExp : ℝ := 2 / (q - 2 : ℝ)
  let τ : ℝ := 2 * (q - 1 : ℝ) / (r * q - 2)
  have hσ_pos : 0 < σ := by
    dsimp [σ]
    positivity
  have hσ_nonneg : 0 ≤ σ := hσ_pos.le
  have hσ_lt_one : σ < 1 := by
    dsimp [σ]
    exact (_root_.div_lt_iff₀ hrq_sub_pos).2 (by nlinarith)
  have hσ_le_one : σ ≤ 1 := by linarith
  have hone_sub_sigma_pos : 0 < 1 - σ := by linarith
  have hone_sub_sigma_nonneg : 0 ≤ 1 - σ := hone_sub_sigma_pos.le
  have htheta_pos : 0 < theta := by
    dsimp [theta]
    positivity
  have htheta_nonneg : 0 ≤ theta := htheta_pos.le
  have hbetaEq : betaExp = r * theta := by
    dsimp [betaExp, theta]
    field_simp [hq_sub_ne, hr_ne]
  have htheta_sigma : theta * (1 - (r - 1) * σ) = σ := by
    dsimp [theta, σ]
    field_simp [hq_sub_ne, hr_ne, hrq_sub_ne]
    ring
  have hτ_pos : 0 < τ := by
    dsimp [τ]
    positivity
  have hpow_two_lt_one : (2 : ℝ) ^ (σ - 1) < 1 := by
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hpow_two_nonneg : 0 ≤ (2 : ℝ) ^ (σ - 1) := by positivity
  have hpow_two_margin_pos : 0 < 1 - (2 : ℝ) ^ (σ - 1) := by
    linarith
  have hxSeq : ∀ t, xSeq t ∈ C := by
    intro t
    simpa [xSeq] using
      frankWolfeSequence_mem
        (O := O)
        hC_convex f' hx0 t
  have hF_nonneg : ∀ t, 0 ≤ F t := by
    intro t
    exact primalGap_nonneg_of_isMinOn (C := C) (f := f) (hxSeq t) hmin
  have hBstd_nonneg : 0 ≤ Bstd := by
    have hgap0_nonneg : 0 ≤ f x0 - f x_star := by
      exact primalGap_nonneg_of_isMinOn (C := C) (f := f) hx0 hmin
    exact le_trans hgap0_nonneg (le_max_left _ _)
  have hstd :
      ∀ t, F t ≤ (2 * Bstd) / (t + 2 : ℝ) := by
    intro t
    have hfw :=
      frank_wolfe_convergence_of_initialGap_le
        (O := O)
        hC_convex f f' L hSmooth hConv hx_star hx0
        (B := Bstd) hBstd_nonneg (le_max_left _ _) (le_max_right _ _) t
    simpa [F, xSeq, Bstd, Dsq] using hfw
  have hH_bounded :
      ∀ t, H t ≤ 2 * Bstd := by
    intro t
    calc
      H t = (t + 2 : ℝ) * F t := by rfl
      _ ≤ (t + 2 : ℝ) * ((2 * Bstd) / (t + 2 : ℝ)) := by
            gcongr
            exact hstd t
      _ = 2 * Bstd := by
            field_simp [show (t + 2 : ℝ) ≠ 0 by positivity]
  have hH_nonneg : ∀ t, 0 ≤ H t := by
    intro t
    dsimp [H]
    exact mul_nonneg (by positivity) (hF_nonneg t)
  have hgap_zero :
      Tendsto F atTop (nhds 0) := by
    simpa [F, xSeq] using
      frankWolfe_gap_tendsto_zero_of_isMinOn
        (O := O)
        hC_convex f f' L hConv hSmooth hx_star hmin hx0
  have hcont : Continuous f :=
    continuous_of_isFirstOrderConvex_isLipschitzSmoothUpperBound (f := f) (f' := f') (L := L) hConv hSmooth
  have hlevel_closed : IsClosed {y : E | f y = f x_star} :=
    isClosed_eq hcont continuous_const
  have hMset_compact : IsCompact Mset := by
    simpa [Mset] using O.isCompact.inter_right hlevel_closed
  have hMset_nonempty : Mset.Nonempty := by
    refine ⟨x_star, ?_⟩
    simp [Mset, hx_star]
  have hdist_zero :
      Tendsto (fun t => Metric.infDist (xSeq t) Mset) atTop (nhds 0) := by
    simpa [xSeq, Mset] using
      tendsto_infDist_minimizerSet_of_gap_tendsto_zero
        O.isCompact (f := f) (f' := f') (L := L) hConv hSmooth x_star xSeq hxSeq hgap_zero
  classical
  let pSeq : ℕ → E := fun t =>
    Classical.choose (hMset_compact.exists_infDist_eq_dist hMset_nonempty (xSeq t))
  have hpSeq_memM : ∀ t, pSeq t ∈ Mset := by
    intro t
    exact (Classical.choose_spec (hMset_compact.exists_infDist_eq_dist hMset_nonempty (xSeq t))).1
  have hpSeq_val : ∀ t, f (pSeq t) = f x_star := by
    intro t
    exact (hpSeq_memM t).2
  have hpSeq_dist : ∀ t, Metric.infDist (xSeq t) Mset = dist (xSeq t) (pSeq t) := by
    intro t
    exact (Classical.choose_spec (hMset_compact.exists_infDist_eq_dist hMset_nonempty (xSeq t))).2
  let δ : ℕ → ℝ := fun t => ‖xSeq t - pSeq t‖
  have hδ_zero :
      Tendsto δ atTop (nhds 0) := by
    have hdist_zero' :
        Tendsto (fun t => dist (xSeq t) (pSeq t)) atTop (nhds 0) := by
      simpa [hpSeq_dist] using hdist_zero
    simpa [δ, dist_eq_norm] using hdist_zero'
  obtain ⟨ρheb, hρheb_pos, hheb_local⟩ := hHEB
  have hheb_event : ∀ᶠ t : ℕ in atTop, (δ t) ^ r ≤ B * F t := by
    have hδ_event : ∀ᶠ t : ℕ in atTop, δ t < ρheb := by
      exact hδ_zero.eventually (Iio_mem_nhds hρheb_pos)
    filter_upwards [hδ_event] with t hδt
    have hdist_t : Metric.infDist (xSeq t) Mset < ρheb := by
      rw [hpSeq_dist t]
      simpa [δ, dist_eq_norm] using hδt
    have hheb_t :
        Metric.infDist (xSeq t) Mset ^ r ≤ B * (f (xSeq t) - f x_star) := by
      simpa using hheb_local (xSeq t) (hxSeq t) hdist_t
    rw [hpSeq_dist t, dist_eq_norm] at hheb_t
    simpa [δ, F] using hheb_t
  have hstd_step :
      ∀ t,
        F (t + 1) ≤
          (1 - 2 / (t + 2 : ℝ)) * F t +
            ((L : ℝ) / 2) * (2 / (t + 2 : ℝ)) ^ 2 * Dsq := by
    intro t
    have href :
        f (frankWolfeStep O f' (xSeq t) (2 / (t + 2 : ℝ))) -
            f (pSeq t) ≤
          (1 - 2 / (t + 2 : ℝ)) * (f (xSeq t) - f (pSeq t)) +
            ((L : ℝ) / 2) * (2 / (t + 2 : ℝ)) ^ 2 * Dsq := by
      simpa [xSeq, Dsq] using
        (frankWolfeStep_gap_bound
          (O := O)
          (C := C) (f := f) (f' := f') (L := L) hSmooth hConv
          (x := xSeq t) (x_star := pSeq t)
          (hxSeq t) ((hpSeq_memM t).1)
          (γ := 2 / (t + 2 : ℝ)) (standardStepSize_mem_Icc t))
    simpa [F, xSeq, frankWolfeSequence, hpSeq_val t, frankWolfeOpenLoopSequence, openLoopStepSize] using href
  rcases Filter.Eventually.exists_forall_of_atTop hheb_event with ⟨Theb, hTheb⟩
  have hterm1_zero :
      Tendsto (fun t : ℕ => 8 * (L : ℝ) * B ^ (2 / r) / (t + 2 : ℝ) ^ τ) atTop (nhds 0) := by
    have hpowNat :
        Tendsto (fun t : ℕ => (t : ℝ) + 2) atTop atTop := by
      exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    have hpow :
        Tendsto (fun t : ℕ => (t + 2 : ℝ) ^ τ) atTop atTop := by
      exact (tendsto_rpow_atTop hτ_pos).comp hpowNat
    exact tendsto_const_nhds.div_atTop hpow
  have hterm1_event :
      ∀ᶠ t : ℕ in atTop, 8 * (L : ℝ) * B ^ (2 / r) / (t + 2 : ℝ) ^ τ < (1 - σ) / 4 := by
    exact hterm1_zero.eventually (Iio_mem_nhds (by positivity : 0 < (1 - σ) / 4))
  rcases Filter.Eventually.exists_forall_of_atTop hterm1_event with ⟨Tterm, hTterm⟩
  let Cres : ℝ :=
    8 * (((q - 2 : ℝ) / q) * (L : ℝ) *
      (16 * (L : ℝ) / (q * A)) ^ betaExp * B ^ theta)
  let K0 : ℝ := max 1 (4 * Cres / (1 - σ))
  have hCres_nonneg : 0 ≤ Cres := by
    dsimp [Cres]
    positivity
  have hK0_ge_one : 1 ≤ K0 := by
    dsimp [K0]
    exact le_max_left _ _
  have hK0_pos : 0 < K0 := lt_of_lt_of_le zero_lt_one hK0_ge_one
  have hK0_nonneg : 0 ≤ K0 := hK0_pos.le
  have hCres_le :
      Cres ≤ ((1 - σ) / 4) * K0 := by
    have hbase : 4 * Cres / (1 - σ) ≤ K0 := by
      dsimp [K0]
      exact le_max_right _ _
    have hscaled :
        ((1 - σ) / 4) * (4 * Cres / (1 - σ)) ≤ ((1 - σ) / 4) * K0 := by
      exact mul_le_mul_of_nonneg_left hbase (by positivity : 0 ≤ (1 - σ) / 4)
    have hcancel : ((1 - σ) / 4) * (4 * Cres / (1 - σ)) = Cres := by
      field_simp [hone_sub_sigma_pos.ne']
    rw [hcancel] at hscaled
    exact hscaled
  have hstdtail_zero :
      Tendsto
        (fun t : ℕ => 8 * (L : ℝ) * Dsq / (t + 3 : ℝ) ^ (1 - σ))
        atTop (nhds 0) := by
    have hpowNat :
        Tendsto (fun t : ℕ => (t : ℝ) + 3) atTop atTop := by
      exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    have hpow :
        Tendsto (fun t : ℕ => (t + 3 : ℝ) ^ (1 - σ)) atTop atTop := by
      exact (tendsto_rpow_atTop hone_sub_sigma_pos).comp hpowNat
    exact tendsto_const_nhds.div_atTop hpow
  have hstd_event :
      ∀ᶠ t : ℕ in atTop,
        8 * (L : ℝ) * Dsq / (t + 3 : ℝ) ^ (1 - σ) <
          (1 - (2 : ℝ) ^ (σ - 1)) * K0 := by
    exact hstdtail_zero.eventually (Iio_mem_nhds (by
      have : 0 < 1 - (2 : ℝ) ^ (σ - 1) := hpow_two_margin_pos
      positivity))
  rcases Filter.Eventually.exists_forall_of_atTop hstd_event with ⟨Tstd, hTstd⟩
  let T : ℕ := max Theb (max Tterm Tstd)
  let K : ℝ := max K0 ((2 * Bstd) * (T + 2 : ℝ) ^ σ)
  let ε : ℕ → ℝ := fun t => K / (t + 2 : ℝ) ^ σ
  let a : ℕ → ℝ := fun t => (t : ℝ) * (t + 3 : ℝ) / (t + 2 : ℝ) ^ 2
  let c : ℕ → ℝ := fun t => (t + 3 : ℝ) / (t + 2 : ℝ) ^ 2
  let stdConst : ℕ → ℝ :=
    fun t => 2 * (L : ℝ) * Dsq * (t + 3 : ℝ) / (t + 2 : ℝ) ^ 2
  let Csmall : ℕ → ℝ :=
    fun t => 16 * (L : ℝ) * (t + 2 : ℝ) ^ σ / (q * A * K)
  let Rtail : ℕ → ℝ :=
    fun t => ((q - 2 : ℝ) / q) * (L : ℝ) * (Csmall t) ^ betaExp
  have hK_ge_K0 : K0 ≤ K := by
    dsimp [K]
    exact le_max_left _ _
  have hK_pos : 0 < K := lt_of_lt_of_le hK0_pos hK_ge_K0
  have hK_nonneg : 0 ≤ K := hK_pos.le
  have hK_ge_one : 1 ≤ K := le_trans hK0_ge_one hK_ge_K0
  have hT_ge_heb : Theb ≤ T := by
    dsimp [T]
    exact le_max_left _ _
  have hT_ge_term : Tterm ≤ T := by
    dsimp [T]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hT_ge_std : Tstd ≤ T := by
    dsimp [T]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hε_pos : ∀ t, 0 < ε t := by
    intro t
    dsimp [ε]
    positivity
  have hsmall_or_refined :
      ∀ t,
        H t ≤ ε t / 2 ∨
          H (t + 1) ≤
            a t * H t +
              c t * (4 * (L : ℝ) * (δ t) ^ 2 + 4 * Rtail t * (δ t) ^ betaExp) := by
    intro t
    by_cases hFt0 : F t = 0
    · left
      have hnonneg : 0 ≤ ε t / 2 := by positivity
      simpa [H, hFt0] using hnonneg
    · have hF_pos_t : 0 < F t := lt_of_le_of_ne (hF_nonneg t) (by simpa [eq_comm] using hFt0)
      have hδ_pos_t : 0 < δ t := by
        by_contra hδt
        have hδ0 : δ t = 0 := le_antisymm (not_lt.mp hδt) (norm_nonneg _)
        have hxeq : xSeq t = pSeq t := by
          exact sub_eq_zero.mp (norm_eq_zero.mp (by simpa [δ] using hδ0))
        have : F t = 0 := by simp [F, hxeq, hpSeq_val t]
        exact hFt0 this
      let γt : ℝ := 2 / (t + 2 : ℝ)
      let lamT : ℝ := 4 * (L : ℝ) * γt * δ t / (q * A * F t)
      have hγ_mem : γt ∈ Set.Icc (0 : ℝ) 1 := standardStepSize_mem_Icc t
      have hγ_pos : 0 < γt := by
        dsimp [γt]
        positivity
      by_cases hcase : lamT ≤ Csmall t * δ t
      · right
        have hF_seq_pos : 0 < f (xSeq t) - f (pSeq t) := by
          simpa [F, hpSeq_val t] using hF_pos_t
        have href :
            f (frankWolfeStep O f' (xSeq t) γt) - f (pSeq t) ≤
              (1 - γt) * (f (xSeq t) - f (pSeq t)) +
                (L : ℝ) * γt ^ 2 * ‖xSeq t - pSeq t‖ ^ 2 +
                ((q - 2 : ℝ) / q) * (L : ℝ) * γt ^ 2 *
                  lamT ^ ((2 : ℝ) / (q - 2 : ℝ)) := by
          simpa [xSeq, γt, δ, F, lamT, hpSeq_val t] using
            (frankWolfeStep_gap_bound_with_localCorrection
              (O := O)
              (hq := hq) hA hLocal
              f f' L hConv hSmooth
              (x := xSeq t) (x_star := pSeq t)
              ((hpSeq_memM t).1) (hpSeq_memM t)
              hγ_mem hγ_pos hF_seq_pos hδ_pos_t)
        have hlam_pow :
            lamT ^ betaExp ≤ (Csmall t * δ t) ^ betaExp := by
          have hbeta_nonneg : 0 ≤ betaExp := by
            dsimp [betaExp]
            positivity
          exact Real.rpow_le_rpow (by positivity) hcase hbeta_nonneg
        have hlam_pow' :
            lamT ^ betaExp ≤ (Csmall t) ^ betaExp * (δ t) ^ betaExp := by
          calc
            lamT ^ betaExp ≤ (Csmall t * δ t) ^ betaExp := hlam_pow
            _ = (Csmall t) ^ betaExp * (δ t) ^ betaExp := by
                  exact Real.mul_rpow (by positivity) (by positivity)
        have hres_le :
            ((q - 2 : ℝ) / q) * (L : ℝ) * γt ^ 2 * lamT ^ betaExp ≤
              Rtail t * γt ^ 2 * (δ t) ^ betaExp := by
          calc
            ((q - 2 : ℝ) / q) * (L : ℝ) * γt ^ 2 * lamT ^ betaExp
                ≤ ((q - 2 : ℝ) / q) * (L : ℝ) * γt ^ 2 *
                    ((Csmall t) ^ betaExp * (δ t) ^ betaExp) := by
                      exact mul_le_mul_of_nonneg_left hlam_pow'
                        (by positivity :
                          0 ≤ ((q - 2 : ℝ) / q) * (L : ℝ) * γt ^ 2)
            _ = Rtail t * γt ^ 2 * (δ t) ^ betaExp := by
                  dsimp [Rtail]
                  ring
        have href' :
            F (t + 1) ≤
              (1 - 2 / (t + 2 : ℝ)) * F t +
                (L : ℝ) * (2 / (t + 2 : ℝ)) ^ 2 * (δ t) ^ 2 +
                Rtail t * γt ^ 2 * (δ t) ^ betaExp := by
          have href0 :
              F (t + 1) ≤
                (1 - 2 / (t + 2 : ℝ)) * F t +
                  (L : ℝ) * (2 / (t + 2 : ℝ)) ^ 2 * (δ t) ^ 2 +
                  ((q - 2 : ℝ) / q) * (L : ℝ) * γt ^ 2 * lamT ^ betaExp := by
            simpa [F, xSeq, frankWolfeSequence, γt, δ, hpSeq_val t, betaExp, frankWolfeOpenLoopSequence, openLoopStepSize] using href
          have hsum :
              (1 - 2 / (t + 2 : ℝ)) * F t +
                  (L : ℝ) * (2 / (t + 2 : ℝ)) ^ 2 * (δ t) ^ 2 +
                  ((q - 2 : ℝ) / q) * (L : ℝ) * γt ^ 2 * lamT ^ betaExp
                ≤
                  (1 - 2 / (t + 2 : ℝ)) * F t +
                    (L : ℝ) * (2 / (t + 2 : ℝ)) ^ 2 * (δ t) ^ 2 +
                    Rtail t * γt ^ 2 * (δ t) ^ betaExp := by
            linarith [hres_le]
          exact le_trans href0 hsum
        have hh_succ : H (t + 1) = (t + 3 : ℝ) * F (t + 1) := by
          change ((((t + 1 : ℕ) : ℝ) + 2) * F (t + 1) = (t + 3 : ℝ) * F (t + 1))
          have hcast : (((t + 1 : ℕ) : ℝ) + 2) = (t + 3 : ℝ) := by
            exact_mod_cast (show t + 1 + 2 = t + 3 by omega)
          rw [hcast]
        have hmul := mul_le_mul_of_nonneg_left href' (by positivity : 0 ≤ (t + 3 : ℝ))
        calc
          H (t + 1) = (t + 3 : ℝ) * F (t + 1) := hh_succ
          _ ≤ (t + 3 : ℝ) *
                ((1 - 2 / (t + 2 : ℝ)) * F t +
                  (L : ℝ) * (2 / (t + 2 : ℝ)) ^ 2 * (δ t) ^ 2 +
                  Rtail t * γt ^ 2 * (δ t) ^ betaExp) := hmul
          _ = a t * H t + c t * (4 * (L : ℝ) * (δ t) ^ 2 + 4 * Rtail t * (δ t) ^ betaExp) := by
                dsimp [a, H, c, γt]
                field_simp [show (t + 2 : ℝ) ≠ 0 by positivity]
                ring
      · left
        have hcase' : Csmall t * δ t < lamT := lt_of_not_ge hcase
        have hlam_repr :
            lamT = (4 * (L : ℝ) * γt / (q * A * F t)) * δ t := by
          dsimp [lamT]
          field_simp [hF_pos_t.ne']
        rw [hlam_repr] at hcase'
        have hdiv :
            Csmall t < 4 * (L : ℝ) * γt / (q * A * F t) := by
          exact lt_of_mul_lt_mul_right hcase' hδ_pos_t.le
        have hF_bound :
            F t < 4 * (L : ℝ) * γt / (q * A * Csmall t) := by
          have hden_pos : 0 < q * A * Csmall t := by
            dsimp [Csmall]
            positivity
          have hmul : F t * (q * A * Csmall t) < 4 * (L : ℝ) * γt := by
            have hmul' : Csmall t * (q * A * F t) < 4 * (L : ℝ) * γt := by
              exact (_root_.lt_div_iff₀ (show 0 < q * A * F t by positivity)).1 hdiv
            simpa [mul_assoc, mul_left_comm, mul_comm] using hmul'
          exact (_root_.lt_div_iff₀ hden_pos).2 hmul
        have hEq :
            4 * (L : ℝ) * γt / (q * A * Csmall t) = ε t / (2 * (t + 2 : ℝ)) := by
          dsimp [γt, Csmall, ε]
          field_simp [hK_pos.ne', hA.ne', hq_pos.ne', hq_one_ne]
          ring
        have htmp : F t < ε t / (2 * (t + 2 : ℝ)) := by
          simpa [hEq] using hF_bound
        have hmul := mul_lt_mul_of_pos_left htmp (by positivity : 0 < (t + 2 : ℝ))
        have hcalc :
            (t + 2 : ℝ) * (ε t / (2 * (t + 2 : ℝ))) = ε t / 2 := by
          field_simp [show (t + 2 : ℝ) ≠ 0 by positivity]
        have hh_small : H t < ε t / 2 := by
          simpa [H, hcalc] using hmul
        exact le_of_lt hh_small
  have hbase :
      H T ≤ ε T := by
    have hbound : H T ≤ 2 * Bstd := hH_bounded T
    have hK_base : (2 * Bstd) * (T + 2 : ℝ) ^ σ ≤ K := by
      dsimp [K]
      exact le_max_right _ _
    have hdiv :
        2 * Bstd ≤ K / (T + 2 : ℝ) ^ σ := by
      have hden_pos : 0 < (T + 2 : ℝ) ^ σ := by positivity
      exact (_root_.le_div_iff₀ hden_pos).2 <| by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hK_base
    simpa [ε] using hbound.trans hdiv
  have hstd_small :
      ∀ t ≥ T,
        stdConst t ≤ (1 - (2 : ℝ) ^ (σ - 1)) * ε (t + 1) := by
    intro t ht
    have htail :
        8 * (L : ℝ) * Dsq / (t + 3 : ℝ) ^ (1 - σ) <
          (1 - (2 : ℝ) ^ (σ - 1)) * K0 := by
      exact hTstd t (le_trans hT_ge_std ht)
    have hstd_bound1 : stdConst t ≤ 4 * (L : ℝ) * Dsq / (t + 2 : ℝ) := by
      have hB_nonneg : 0 ≤ (L : ℝ) * Dsq := by positivity
      simpa [stdConst, mul_assoc, mul_left_comm, mul_comm] using
        (frankWolfe_openLoop_stdConst_bound (B := (L : ℝ) * Dsq) hB_nonneg t)
    have hstd_bound2 : 4 * (L : ℝ) * Dsq / (t + 2 : ℝ) ≤ 8 * (L : ℝ) * Dsq / (t + 3 : ℝ) := by
      have hfrac : (1 : ℝ) / (t + 2 : ℝ) ≤ (2 : ℝ) / (t + 3 : ℝ) := by
        have harg : (t + 3 : ℝ) ≤ 2 * (t + 2 : ℝ) := by
          exact_mod_cast (show t + 3 ≤ 2 * (t + 2) by omega)
        have hdiv :
            1 / (2 * (t + 2 : ℝ)) ≤ 1 / (t + 3 : ℝ) := by
          exact one_div_le_one_div_of_le (by positivity : 0 < (t + 3 : ℝ)) harg
        have hscaled := mul_le_mul_of_nonneg_left hdiv (by positivity : 0 ≤ (2 : ℝ))
        have hEqL : (2 : ℝ) * (1 / (2 * (t + 2 : ℝ))) = (1 : ℝ) / (t + 2 : ℝ) := by
          field_simp [show (t + 2 : ℝ) ≠ 0 by positivity]
        have hEqR : (2 : ℝ) * (1 / (t + 3 : ℝ)) = (2 : ℝ) / (t + 3 : ℝ) := by
          ring
        simpa [hEqL, hEqR, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hscaled
      have hcoef_nonneg : 0 ≤ 4 * (L : ℝ) * Dsq := by positivity
      have hmul :
          (4 * (L : ℝ) * Dsq) * ((1 : ℝ) / (t + 2 : ℝ)) ≤
            (4 * (L : ℝ) * Dsq) * ((2 : ℝ) / (t + 3 : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hfrac hcoef_nonneg
      calc
        4 * (L : ℝ) * Dsq / (t + 2 : ℝ)
            = (4 * (L : ℝ) * Dsq) * ((1 : ℝ) / (t + 2 : ℝ)) := by ring
        _ ≤ (4 * (L : ℝ) * Dsq) * ((2 : ℝ) / (t + 3 : ℝ)) := hmul
        _ = 8 * (L : ℝ) * Dsq / (t + 3 : ℝ) := by ring
    have hsplit :
        8 * (L : ℝ) * Dsq / (t + 3 : ℝ) =
          (8 * (L : ℝ) * Dsq / (t + 3 : ℝ) ^ (1 - σ)) / (t + 3 : ℝ) ^ σ := by
      have hbase_nonneg : 0 ≤ (t + 3 : ℝ) := by positivity
      have hbase_pos : 0 < (t + 3 : ℝ) := by positivity
      let a : ℝ := (t + 3 : ℝ) ^ (1 - σ)
      let b : ℝ := (t + 3 : ℝ) ^ σ
      have ha_ne : a ≠ 0 := by
        dsimp [a]
        positivity
      have hb_ne : b ≠ 0 := by
        dsimp [b]
        positivity
      have hpow : a * b = (t + 3 : ℝ) := by
        dsimp [a, b]
        calc
          (t + 3 : ℝ) ^ (1 - σ) * (t + 3 : ℝ) ^ σ = (t + 3 : ℝ) ^ ((1 - σ) + σ) := by
                rw [← Real.rpow_add hbase_pos (1 - σ) σ]
          _ = (t + 3 : ℝ) ^ (1 : ℝ) := by ring_nf
          _ = (t + 3 : ℝ) := by rw [Real.rpow_one]
      have hdiv_eq :
          (8 * (L : ℝ) * Dsq / a) / b = 8 * (L : ℝ) * Dsq / (a * b) := by
        field_simp [ha_ne, hb_ne]
      calc
        8 * (L : ℝ) * Dsq / (t + 3 : ℝ) = 8 * (L : ℝ) * Dsq / (a * b) := by
              rw [hpow]
        _ = (8 * (L : ℝ) * Dsq / a) / b := by
              exact hdiv_eq.symm
        _ = (8 * (L : ℝ) * Dsq / (t + 3 : ℝ) ^ (1 - σ)) / (t + 3 : ℝ) ^ σ := by
              rfl
        _ = (8 * (L : ℝ) * Dsq / (t + 3 : ℝ) ^ (1 - σ)) / (t + 3 : ℝ) ^ σ := by
              rfl
    have hscaled :
        (8 * (L : ℝ) * Dsq / (t + 3 : ℝ) ^ (1 - σ)) / (t + 3 : ℝ) ^ σ ≤
          ((1 - (2 : ℝ) ^ (σ - 1)) * K0) / (t + 3 : ℝ) ^ σ := by
      exact (_root_.div_le_div_of_nonneg_right (le_of_lt htail) (by positivity))
    have hKscaled :
        ((1 - (2 : ℝ) ^ (σ - 1)) * K0) / (t + 3 : ℝ) ^ σ ≤
          ((1 - (2 : ℝ) ^ (σ - 1)) * K) / (t + 3 : ℝ) ^ σ := by
      exact (_root_.div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hK_ge_K0 hpow_two_margin_pos.le) (by positivity))
    calc
      stdConst t ≤ 4 * (L : ℝ) * Dsq / (t + 2 : ℝ) := hstd_bound1
      _ ≤ 8 * (L : ℝ) * Dsq / (t + 3 : ℝ) := hstd_bound2
      _ = (8 * (L : ℝ) * Dsq / (t + 3 : ℝ) ^ (1 - σ)) / (t + 3 : ℝ) ^ σ := hsplit
      _ ≤ ((1 - (2 : ℝ) ^ (σ - 1)) * K0) / (t + 3 : ℝ) ^ σ := hscaled
      _ ≤ ((1 - (2 : ℝ) ^ (σ - 1)) * K) / (t + 3 : ℝ) ^ σ := hKscaled
      _ = (1 - (2 : ℝ) ^ (σ - 1)) * ε (t + 1) := by
            have hcast : (((t + 1 : ℕ) : ℝ) + 2) = (t + 3 : ℝ) := by
              exact_mod_cast (show t + 1 + 2 = t + 3 by omega)
            dsimp [ε]
            rw [hcast]
            ring
  have hgap_step :
      ∀ t : ℕ, (1 - σ) * K / (t + 2 : ℝ) ^ (1 + σ) ≤ ε (t + 1) - a t * ε t := by
    intro t
    let u : ℝ := 1 / (t + 2 : ℝ)
    have hu_nonneg : 0 ≤ u := by
      dsimp [u]
      positivity
    have hpow_le : (1 + u) ^ σ ≤ 1 + σ * u := by
      simpa [u, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using
        (rpow_one_add_le_one_add_mul_self (by linarith : -1 ≤ u) hσ_nonneg hσ_le_one)
    have hlin : 1 - σ * u ≤ 1 / (1 + σ * u) := by
      exact one_sub_le_one_div_add (by positivity : 0 ≤ σ * u)
    have hrecip :
        1 / (1 + σ * u) ≤ 1 / ((1 + u) ^ σ) := by
      exact one_div_le_one_div_of_le (by positivity : 0 < (1 + u) ^ σ) hpow_le
    have hlower0 :
        1 - σ * u ≤ 1 / ((1 + u) ^ σ) := by
      exact le_trans hlin hrecip
    have hfactor :
        ε t * (1 - σ * u) ≤ ε (t + 1) := by
      have hmul :
          ε t * (1 - σ * u) ≤ ε t * (1 / ((1 + u) ^ σ)) := by
        exact mul_le_mul_of_nonneg_left hlower0 (hε_pos t).le
      have hsplit :
          ε t * (1 / ((1 + u) ^ σ)) = ε (t + 1) := by
        have hpos : 0 ≤ (t + 2 : ℝ) := by positivity
        have hEq :
            (t + 3 : ℝ) = (t + 2 : ℝ) * (1 + u) := by
          dsimp [u]
          field_simp [show (t + 2 : ℝ) ≠ 0 by positivity]
          ring
        calc
          ε t * (1 / ((1 + u) ^ σ))
              = K / ((t + 2 : ℝ) ^ σ * (1 + u) ^ σ) := by
                    dsimp [ε]
                    field_simp [show (t + 2 : ℝ) ^ σ ≠ 0 by positivity]
          _ = K / (((t + 2 : ℝ) * (1 + u)) ^ σ) := by
                have hmulrpow :
                    ((t + 2 : ℝ) * (1 + u)) ^ σ =
                      (t + 2 : ℝ) ^ σ * (1 + u) ^ σ := by
                    exact Real.mul_rpow hpos (by positivity)
                rw [hmulrpow]
          _ = K / (t + 3 : ℝ) ^ σ := by rw [hEq]
          _ = ε (t + 1) := by
                have hcast : (((t + 1 : ℕ) : ℝ) + 2) = (t + 3 : ℝ) := by
                  exact_mod_cast (show t + 1 + 2 = t + 3 by omega)
                dsimp [ε]
                rw [hcast]
      exact hmul.trans_eq hsplit
    have ha_le :
        a t * ε t ≤ (1 - 1 / (t + 2 : ℝ)) * ε t := by
      have hcoeff : a t ≤ 1 - 1 / (t + 2 : ℝ) := by
        dsimp [a]
        have hden : 0 < (t + 2 : ℝ) ^ 2 := by positivity
        have hEq :
            (1 - 1 / (t + 2 : ℝ)) * (t + 2 : ℝ) ^ 2 = (t + 1 : ℝ) * (t + 2 : ℝ) := by
          field_simp [show (t + 2 : ℝ) ≠ 0 by positivity]
          ring
        have hpoly : (t : ℝ) * (t + 3 : ℝ) ≤ (t + 1 : ℝ) * (t + 2 : ℝ) := by
          have hgap : (t + 1 : ℝ) * (t + 2 : ℝ) = (t : ℝ) * (t + 3 : ℝ) + 2 := by
            ring
          calc
            (t : ℝ) * (t + 3 : ℝ) ≤ (t : ℝ) * (t + 3 : ℝ) + 2 := by linarith
            _ = (t + 1 : ℝ) * (t + 2 : ℝ) := by simp [hgap]
        refine (_root_.div_le_iff₀ hden).2 ?_
        rw [hEq]
        exact hpoly
      exact mul_le_mul_of_nonneg_right hcoeff (hε_pos t).le
    have hEq :
        (1 - 1 / (t + 2 : ℝ)) * ε t =
          ε t - K / (t + 2 : ℝ) ^ (1 + σ) := by
      dsimp [ε]
      have hpow :
          (t + 2 : ℝ) ^ (1 + σ) = (t + 2 : ℝ) * (t + 2 : ℝ) ^ σ := by
        calc
          (t + 2 : ℝ) ^ (1 + σ) = (t + 2 : ℝ) ^ (1 : ℝ) * (t + 2 : ℝ) ^ σ := by
                rw [Real.rpow_add (by positivity : 0 < (t + 2 : ℝ)) 1 σ]
          _ = (t + 2 : ℝ) * (t + 2 : ℝ) ^ σ := by rw [Real.rpow_one]
      calc
        (1 - 1 / (t + 2 : ℝ)) * (K / (t + 2 : ℝ) ^ σ)
            = K / (t + 2 : ℝ) ^ σ - K / ((t + 2 : ℝ) * (t + 2 : ℝ) ^ σ) := by
                field_simp [show (t + 2 : ℝ) ^ σ ≠ 0 by positivity,
                  show (t + 2 : ℝ) ≠ 0 by positivity]
        _ = K / (t + 2 : ℝ) ^ σ - K / (t + 2 : ℝ) ^ (1 + σ) := by
              rw [← hpow]
        _ = ε t - K / (t + 2 : ℝ) ^ (1 + σ) := by rfl
    have hfactor' :
        (1 - σ * u) * ε t = ε t - σ * K / (t + 2 : ℝ) ^ (1 + σ) := by
      dsimp [u, ε]
      have hpow :
          (t + 2 : ℝ) ^ (1 + σ) = (t + 2 : ℝ) * (t + 2 : ℝ) ^ σ := by
        calc
          (t + 2 : ℝ) ^ (1 + σ) = (t + 2 : ℝ) ^ (1 : ℝ) * (t + 2 : ℝ) ^ σ := by
                rw [Real.rpow_add (by positivity : 0 < (t + 2 : ℝ)) 1 σ]
          _ = (t + 2 : ℝ) * (t + 2 : ℝ) ^ σ := by rw [Real.rpow_one]
      calc
        (1 - σ * (1 / (t + 2 : ℝ))) * (K / (t + 2 : ℝ) ^ σ)
            = K / (t + 2 : ℝ) ^ σ - σ * K / ((t + 2 : ℝ) * (t + 2 : ℝ) ^ σ) := by
                field_simp [show (t + 2 : ℝ) ^ σ ≠ 0 by positivity,
                  show (t + 2 : ℝ) ≠ 0 by positivity]
        _ = K / (t + 2 : ℝ) ^ σ - σ * K / (t + 2 : ℝ) ^ (1 + σ) := by
              rw [← hpow]
        _ = ε t - σ * K / (t + 2 : ℝ) ^ (1 + σ) := by rfl
    have hstep1 :
        ε t - σ * K / (t + 2 : ℝ) ^ (1 + σ) ≤ ε (t + 1) := by
      have hfactor'' :
          ε t * (1 - σ * u) = ε t - σ * K / (t + 2 : ℝ) ^ (1 + σ) := by
        simpa [mul_comm] using hfactor'
      rw [hfactor''] at hfactor
      exact hfactor
    have hstep2 :
        a t * ε t ≤ ε t - K / (t + 2 : ℝ) ^ (1 + σ) := by
      rw [hEq] at ha_le
      exact ha_le
    have hstep1' :
        ε t - σ * K / (t + 2 : ℝ) ^ (1 + σ) - a t * ε t ≤
          ε (t + 1) - a t * ε t := by
      exact sub_le_sub_right hstep1 (a t * ε t)
    have hstep2' :
        K / (t + 2 : ℝ) ^ (1 + σ) ≤ ε t - a t * ε t := by
      linarith [hstep2]
    have hcomb :
        (1 - σ) * K / (t + 2 : ℝ) ^ (1 + σ) ≤
          ε t - σ * K / (t + 2 : ℝ) ^ (1 + σ) - a t * ε t := by
      have hcomb0 :
          K / (t + 2 : ℝ) ^ (1 + σ) - σ * K / (t + 2 : ℝ) ^ (1 + σ) ≤
            ε t - a t * ε t - σ * K / (t + 2 : ℝ) ^ (1 + σ) := by
        exact sub_le_sub_right hstep2' (σ * K / (t + 2 : ℝ) ^ (1 + σ))
      have hleft0 :
          K / (t + 2 : ℝ) ^ (1 + σ) - σ * K / (t + 2 : ℝ) ^ (1 + σ) =
            (1 - σ) * K / (t + 2 : ℝ) ^ (1 + σ) := by
        ring
      have hright0 :
          ε t - a t * ε t - σ * K / (t + 2 : ℝ) ^ (1 + σ) =
            ε t - σ * K / (t + 2 : ℝ) ^ (1 + σ) - a t * ε t := by
        ring
      simpa [hleft0, hright0] using hcomb0
    exact le_trans hcomb hstep1'
  have hsmall_ratio :
      ∀ t : ℕ, ε t / 2 ≤ (2 : ℝ) ^ (σ - 1) * ε (t + 1) := by
    intro t
    have harg : (t + 3 : ℝ) ≤ 2 * (t + 2 : ℝ) := by
      exact_mod_cast (show t + 3 ≤ 2 * (t + 2) by omega)
    have hpow :
        (t + 3 : ℝ) ^ σ ≤ (2 * (t + 2 : ℝ)) ^ σ := by
      exact Real.rpow_le_rpow (by positivity : 0 ≤ (t + 3 : ℝ)) harg hσ_nonneg
    have hmulrpow :
        (2 * (t + 2 : ℝ)) ^ σ = (2 : ℝ) ^ σ * (t + 2 : ℝ) ^ σ := by
      rw [Real.mul_rpow (by positivity : 0 ≤ (2 : ℝ)) (by positivity : 0 ≤ (t + 2 : ℝ))]
    have hpow' :
        (t + 3 : ℝ) ^ σ ≤ (2 : ℝ) ^ σ * (t + 2 : ℝ) ^ σ := by
      simpa [hmulrpow] using hpow
    have htwo :
        2 * (2 : ℝ) ^ (σ - 1) = (2 : ℝ) ^ σ := by
      calc
        2 * (2 : ℝ) ^ (σ - 1) = (2 : ℝ) ^ (1 : ℝ) * (2 : ℝ) ^ (σ - 1) := by
              simp [Real.rpow_one]
        _ = (2 : ℝ) ^ (1 + (σ - 1)) := by
              symm
              exact Real.rpow_add (by positivity : 0 < (2 : ℝ)) 1 (σ - 1)
        _ = (2 : ℝ) ^ σ := by
              congr 1
              ring
    have hden1 : 0 < 2 * (t + 2 : ℝ) ^ σ := by
      exact mul_pos (by norm_num) (Real.rpow_pos_of_pos (by positivity : 0 < (t + 2 : ℝ)) σ)
    have hden2 : 0 < (t + 3 : ℝ) ^ σ := by
      exact Real.rpow_pos_of_pos (by positivity : 0 < (t + 3 : ℝ)) σ
    have hcross :
        K * (t + 3 : ℝ) ^ σ ≤ ((2 : ℝ) ^ (σ - 1) * K) * (2 * (t + 2 : ℝ) ^ σ) := by
      have hcross0 :
          (t + 3 : ℝ) ^ σ ≤ (2 : ℝ) ^ (σ - 1) * (2 * (t + 2 : ℝ) ^ σ) := by
        calc
          (t + 3 : ℝ) ^ σ ≤ (2 : ℝ) ^ σ * (t + 2 : ℝ) ^ σ := hpow'
          _ = (2 : ℝ) ^ (σ - 1) * (2 * (t + 2 : ℝ) ^ σ) := by
                rw [← htwo]
                ring
      calc
        K * (t + 3 : ℝ) ^ σ ≤ K * ((2 : ℝ) ^ (σ - 1) * (2 * (t + 2 : ℝ) ^ σ)) := by
              exact mul_le_mul_of_nonneg_left hcross0 hK_nonneg
        _ = ((2 : ℝ) ^ (σ - 1) * K) * (2 * (t + 2 : ℝ) ^ σ) := by ring
    have hscaled :
        K / (2 * (t + 2 : ℝ) ^ σ) ≤ ((2 : ℝ) ^ (σ - 1) * K) / (t + 3 : ℝ) ^ σ := by
      exact (div_le_div_iff₀ hden1 hden2).2 hcross
    have hleft :
        ε t / 2 = K / (2 * (t + 2 : ℝ) ^ σ) := by
      calc
        ε t / 2 = K / ((t + 2 : ℝ) ^ σ * 2) := by
              dsimp [ε]
              field_simp [show (t + 2 : ℝ) ^ σ ≠ 0 by
                exact (Real.rpow_pos_of_pos (by positivity : 0 < (t + 2 : ℝ)) σ).ne']
        _ = K / (2 * (t + 2 : ℝ) ^ σ) := by ring
    have hright :
        ((2 : ℝ) ^ (σ - 1) * K) / (t + 3 : ℝ) ^ σ =
          (2 : ℝ) ^ (σ - 1) * ε (t + 1) := by
      dsimp [ε]
      have hcast : (((t + 1 : ℕ) : ℝ) + 2) = (t + 3 : ℝ) := by
        exact_mod_cast (show t + 1 + 2 = t + 3 by omega)
      rw [hcast]
      ring
    rw [hleft]
    calc
      K / (2 * (t + 2 : ℝ) ^ σ) ≤ ((2 : ℝ) ^ (σ - 1) * K) / (t + 3 : ℝ) ^ σ := hscaled
      _ = (2 : ℝ) ^ (σ - 1) * ε (t + 1) := hright
  have hMain :
      ∀ n : ℕ, H (T + n) ≤ ε (T + n) := by
    intro n
    induction n with
    | zero =>
        simpa using hbase
    | succ n ihn =>
        let t : ℕ := T + n
        have ht : T ≤ t := by
          dsimp [t]
          exact Nat.le_add_right _ _
        have hprev : H t ≤ ε t := by
          simpa [t, Nat.add_assoc] using ihn
        rcases hsmall_or_refined t with hsmall | href
        · have hstep : H (t + 1) ≤ a t * H t + stdConst t := by
            have hh_succ : H (t + 1) = (t + 3 : ℝ) * F (t + 1) := by
              change ((((t + 1 : ℕ) : ℝ) + 2) * F (t + 1) = (t + 3 : ℝ) * F (t + 1))
              have hcast : (((t + 1 : ℕ) : ℝ) + 2) = (t + 3 : ℝ) := by
                exact_mod_cast (show t + 1 + 2 = t + 3 by omega)
              rw [hcast]
            have hmul := mul_le_mul_of_nonneg_left (hstd_step t) (by positivity : 0 ≤ (t + 3 : ℝ))
            calc
              H (t + 1) = (t + 3 : ℝ) * F (t + 1) := hh_succ
              _ ≤ (t + 3 : ℝ) *
                    ((1 - 2 / (t + 2 : ℝ)) * F t +
                      ((L : ℝ) / 2) * (2 / (t + 2 : ℝ)) ^ 2 * Dsq) := hmul
              _ = a t * H t + stdConst t := by
                    dsimp [a, H, stdConst]
                    exact
                      frankWolfe_openLoop_scaled_standard_eq
                        (F := F) (Dsq := Dsq) (L := (L : ℝ)) t
          have ha_le_one : a t ≤ 1 := by
            dsimp [a]
            exact frankWolfe_openLoop_coeff_le_one t
          have hmain :
              H (t + 1) ≤ ε t / 2 + stdConst t := by
            have ha_nonneg : 0 ≤ a t := by
              dsimp [a]
              exact div_nonneg (by positivity) (by positivity)
            have hsmall' : a t * H t ≤ a t * (ε t / 2) := by
              exact mul_le_mul_of_nonneg_left hsmall ha_nonneg
            have hsmall'' : a t * (ε t / 2) ≤ ε t / 2 := by
              simpa using mul_le_mul_of_nonneg_right ha_le_one (by positivity : 0 ≤ ε t / 2)
            calc
              H (t + 1) ≤ a t * H t + stdConst t := hstep
              _ ≤ a t * (ε t / 2) + stdConst t := by
                    linarith [hsmall']
              _ ≤ ε t / 2 + stdConst t := by
                    linarith [hsmall'']
          have htail := hstd_small t ht
          have hratio := hsmall_ratio t
          have hnext :
              H (t + 1) ≤ ε (t + 1) := by
            calc
              H (t + 1) ≤ ε t / 2 + stdConst t := hmain
              _ ≤ ε t / 2 + (1 - (2 : ℝ) ^ (σ - 1)) * ε (t + 1) := by
                    linarith [htail]
              _ ≤ (2 : ℝ) ^ (σ - 1) * ε (t + 1) +
                    (1 - (2 : ℝ) ^ (σ - 1)) * ε (t + 1) := by
                      linarith [hratio]
              _ = ε (t + 1) := by ring
          simpa [t, Nat.add_assoc] using hnext
        · have hheb_t : (δ t) ^ r ≤ B * F t := by
            exact hTheb t (le_trans hT_ge_heb ht)
          have hheb_eps :
              (δ t) ^ r ≤ B * ε t / (t + 2 : ℝ) := by
            have hFt : F t ≤ ε t / (t + 2 : ℝ) := by
              have hprev' : F t * (t + 2 : ℝ) ≤ ε t := by
                simpa [H, mul_comm, mul_left_comm, mul_assoc] using hprev
              exact (_root_.le_div_iff₀ (by positivity : 0 < (t + 2 : ℝ))).2 hprev'
            calc
              (δ t) ^ r ≤ B * F t := hheb_t
              _ ≤ B * (ε t / (t + 2 : ℝ)) := by
                    exact mul_le_mul_of_nonneg_left hFt hB.le
              _ = B * ε t / (t + 2 : ℝ) := by ring
          have hc_bound :
              c t ≤ 2 / (t + 2 : ℝ) := by
            dsimp [c]
            have hden : 0 < (t + 2 : ℝ) ^ 2 := by positivity
            have hEq :
                (2 / (t + 2 : ℝ)) * (t + 2 : ℝ) ^ 2 = 2 * (t + 2 : ℝ) := by
              field_simp [show (t + 2 : ℝ) ≠ 0 by positivity]
            have harg : (t + 3 : ℝ) ≤ 2 * (t + 2 : ℝ) := by
              exact_mod_cast (show t + 3 ≤ 2 * (t + 2) by omega)
            refine (_root_.div_le_iff₀ hden).2 ?_
            rw [hEq]
            exact harg
          have hδr_nonneg : 0 ≤ (δ t) ^ r := by positivity
          have hδtwo_bound :
              (δ t) ^ 2 ≤ (B * ε t / (t + 2 : ℝ)) ^ (2 / r) := by
            have hpow :
                ((δ t) ^ r) ^ (2 / r) ≤ (B * ε t / (t + 2 : ℝ)) ^ (2 / r) := by
              exact Real.rpow_le_rpow hδr_nonneg hheb_eps (by positivity : 0 ≤ 2 / r)
            have hleft :
                ((δ t) ^ r) ^ (2 / r) = (δ t) ^ 2 := by
              calc
                ((δ t) ^ r) ^ (2 / r) = (δ t) ^ (r * (2 / r)) := by
                      rw [← Real.rpow_mul (by positivity : 0 ≤ δ t) r (2 / r)]
                _ = (δ t) ^ (2 : ℝ) := by
                      congr 1
                      field_simp [hr_ne]
                _ = (δ t) ^ 2 := by simp
            rw [hleft] at hpow
            exact hpow
          have htwo_over_r_le_one : 2 / r ≤ 1 := by
            exact (_root_.div_le_iff₀ hr_pos).2 (by simpa [one_mul] using hr)
          have hKpow_two_le : K ^ (2 / r) ≤ K := by
            calc
              K ^ (2 / r) ≤ K ^ (1 : ℝ) := by
                    exact Real.rpow_le_rpow_of_exponent_le hK_ge_one htwo_over_r_le_one
              _ = K := by rw [Real.rpow_one]
          have hpow_eps (e : ℝ) :
              (B * ε t / (t + 2 : ℝ)) ^ e =
                B ^ e * K ^ e / (t + 2 : ℝ) ^ ((1 + σ) * e) := by
            dsimp [ε]
            have hfirst :
                B * (K / (t + 2 : ℝ) ^ σ) / (t + 2 : ℝ) =
                  B * K * (t + 2 : ℝ) ^ (-(1 + σ)) := by
              have hpow :
                  (t + 2 : ℝ) ^ (1 + σ) = (t + 2 : ℝ) * (t + 2 : ℝ) ^ σ := by
                calc
                  (t + 2 : ℝ) ^ (1 + σ) = (t + 2 : ℝ) ^ (1 : ℝ) * (t + 2 : ℝ) ^ σ := by
                        rw [Real.rpow_add (by positivity : 0 < (t + 2 : ℝ)) 1 σ]
                  _ = (t + 2 : ℝ) * (t + 2 : ℝ) ^ σ := by rw [Real.rpow_one]
              calc
                B * (K / (t + 2 : ℝ) ^ σ) / (t + 2 : ℝ)
                    = B * K / ((t + 2 : ℝ) ^ σ * (t + 2 : ℝ)) := by
                          field_simp [show (t + 2 : ℝ) ^ σ ≠ 0 by positivity]
                _ = B * K / (t + 2 : ℝ) ^ (1 + σ) := by
                      have hpow' : (t + 2 : ℝ) ^ σ * (t + 2 : ℝ) = (t + 2 : ℝ) ^ (1 + σ) := by
                        rw [mul_comm, ← hpow]
                      rw [hpow']
                _ = B * K * (t + 2 : ℝ) ^ (-(1 + σ)) := by
                      rw [div_eq_mul_inv, Real.rpow_neg (by positivity : 0 ≤ (t + 2 : ℝ))]
            rw [hfirst]
            have hBK_nonneg : 0 ≤ B * K := by positivity
            calc
              (B * K * (t + 2 : ℝ) ^ (-(1 + σ))) ^ e
                  = (B * K) ^ e * ((t + 2 : ℝ) ^ (-(1 + σ))) ^ e := by
                        rw [Real.mul_rpow hBK_nonneg (by positivity)]
              _ = (B * K) ^ e * (t + 2 : ℝ) ^ ((-(1 + σ)) * e) := by
                    rw [← Real.rpow_mul (by positivity : 0 ≤ (t + 2 : ℝ)) (-(1 + σ)) e]
              _ = (B ^ e * K ^ e) * (t + 2 : ℝ) ^ (-((1 + σ) * e)) := by
                    rw [Real.mul_rpow hB.le hK_nonneg]
                    congr 2
                    ring
              _ = B ^ e * K ^ e / (t + 2 : ℝ) ^ ((1 + σ) * e) := by
                    rw [div_eq_mul_inv, Real.rpow_neg (by positivity : 0 ≤ (t + 2 : ℝ))]
          have hσ_tau : (1 + σ) * (2 / r) = σ + τ := by
            dsimp [σ, τ]
            field_simp [hr_ne, hrq_sub_ne]
            ring
          have hterm1_t :
              8 * (L : ℝ) * B ^ (2 / r) / (t + 2 : ℝ) ^ τ ≤ (1 - σ) / 4 := by
            exact le_of_lt (hTterm t (le_trans hT_ge_term ht))
          have hterm1 :
              c t * (4 * (L : ℝ) * (δ t) ^ 2) ≤
                ((1 - σ) / 4) * K / (t + 2 : ℝ) ^ (1 + σ) := by
            have hδtwo_step :
                4 * (L : ℝ) * (δ t) ^ 2 ≤ 4 * (L : ℝ) * (B * ε t / (t + 2 : ℝ)) ^ (2 / r) := by
              exact mul_le_mul_of_nonneg_left hδtwo_bound (by positivity : 0 ≤ 4 * (L : ℝ))
            have hEqExp1 : 1 + (1 + σ) * (2 / r) = 1 + σ + τ := by
              rw [hσ_tau]
              ring
            have hpow_split1 :
                (t + 2 : ℝ) * (t + 2 : ℝ) ^ ((1 + σ) * (2 / r)) =
                  (t + 2 : ℝ) ^ (1 + σ + τ) := by
              have hbase_pos : 0 < (t + 2 : ℝ) := by positivity
              calc
                (t + 2 : ℝ) * (t + 2 : ℝ) ^ ((1 + σ) * (2 / r))
                    = (t + 2 : ℝ) ^ (1 : ℝ) * (t + 2 : ℝ) ^ ((1 + σ) * (2 / r)) := by
                          rw [Real.rpow_one]
                _ = (t + 2 : ℝ) ^ (1 + (1 + σ) * (2 / r)) := by
                      symm
                      exact Real.rpow_add hbase_pos 1 ((1 + σ) * (2 / r))
                _ = (t + 2 : ℝ) ^ (1 + σ + τ) := by rw [hEqExp1]
            have hterm1_eq :
                (2 / (t + 2 : ℝ)) * (4 * (L : ℝ) * (B * ε t / (t + 2 : ℝ)) ^ (2 / r)) =
                  8 * (L : ℝ) * B ^ (2 / r) * K ^ (2 / r) /
                    (t + 2 : ℝ) ^ (1 + σ + τ) := by
              rw [hpow_eps (2 / r)]
              calc
                (2 / (t + 2 : ℝ)) *
                    (4 * (L : ℝ) * (B ^ (2 / r) * K ^ (2 / r) /
                      (t + 2 : ℝ) ^ ((1 + σ) * (2 / r))))
                    =
                  8 * (L : ℝ) * B ^ (2 / r) * K ^ (2 / r) /
                    ((t + 2 : ℝ) * (t + 2 : ℝ) ^ ((1 + σ) * (2 / r))) := by
                      field_simp [show (t + 2 : ℝ) ≠ 0 by positivity,
                        show (t + 2 : ℝ) ^ ((1 + σ) * (2 / r)) ≠ 0 by positivity]
                      ring
                _ = 8 * (L : ℝ) * B ^ (2 / r) * K ^ (2 / r) /
                      (t + 2 : ℝ) ^ (1 + σ + τ) := by rw [hpow_split1]
            have hterm1_K :
                8 * (L : ℝ) * B ^ (2 / r) * K ^ (2 / r) / (t + 2 : ℝ) ^ (1 + σ + τ) ≤
                  8 * (L : ℝ) * B ^ (2 / r) * K / (t + 2 : ℝ) ^ (1 + σ + τ) := by
              exact div_le_div_of_nonneg_right
                (mul_le_mul_of_nonneg_left hKpow_two_le (by positivity : 0 ≤ 8 * (L : ℝ) * B ^ (2 / r)))
                (by positivity)
            have hpow_split2 :
                (t + 2 : ℝ) ^ (1 + σ + τ) =
                  (t + 2 : ℝ) ^ τ * (t + 2 : ℝ) ^ (1 + σ) := by
              have hbase_pos : 0 < (t + 2 : ℝ) := by positivity
              calc
                (t + 2 : ℝ) ^ (1 + σ + τ) = (t + 2 : ℝ) ^ (τ + (1 + σ)) := by ring_nf
                _ = (t + 2 : ℝ) ^ τ * (t + 2 : ℝ) ^ (1 + σ) := by
                      rw [Real.rpow_add hbase_pos τ (1 + σ)]
            have hterm1_split :
                8 * (L : ℝ) * B ^ (2 / r) * K / (t + 2 : ℝ) ^ (1 + σ + τ) =
                  (8 * (L : ℝ) * B ^ (2 / r) / (t + 2 : ℝ) ^ τ) *
                    (K / (t + 2 : ℝ) ^ (1 + σ)) := by
              rw [hpow_split2]
              field_simp [show (t + 2 : ℝ) ^ τ ≠ 0 by positivity,
                show (t + 2 : ℝ) ^ (1 + σ) ≠ 0 by positivity]
            calc
              c t * (4 * (L : ℝ) * (δ t) ^ 2)
                  ≤ (2 / (t + 2 : ℝ)) * (4 * (L : ℝ) * (δ t) ^ 2) := by
                        exact mul_le_mul_of_nonneg_right hc_bound (by positivity)
              _ ≤ (2 / (t + 2 : ℝ)) * (4 * (L : ℝ) * (B * ε t / (t + 2 : ℝ)) ^ (2 / r)) := by
                        exact mul_le_mul_of_nonneg_left hδtwo_step (by positivity)
              _ = 8 * (L : ℝ) * B ^ (2 / r) * K ^ (2 / r) /
                    (t + 2 : ℝ) ^ (1 + σ + τ) := hterm1_eq
              _ ≤ 8 * (L : ℝ) * B ^ (2 / r) * K / (t + 2 : ℝ) ^ (1 + σ + τ) := hterm1_K
              _ = (8 * (L : ℝ) * B ^ (2 / r) / (t + 2 : ℝ) ^ τ) *
                    (K / (t + 2 : ℝ) ^ (1 + σ)) := hterm1_split
              _ ≤ ((1 - σ) / 4) * (K / (t + 2 : ℝ) ^ (1 + σ)) := by
                    exact mul_le_mul_of_nonneg_right hterm1_t (by positivity)
              _ = ((1 - σ) / 4) * K / (t + 2 : ℝ) ^ (1 + σ) := by ring
          have hδpow :
              (δ t) ^ betaExp = ((δ t) ^ r) ^ theta := by
            rw [hbetaEq]
            simpa using (Real.rpow_mul (by positivity : 0 ≤ δ t) r theta)
          have hheb_theta :
              ((δ t) ^ r) ^ theta ≤ (B * ε t / (t + 2 : ℝ)) ^ theta := by
            exact Real.rpow_le_rpow hδr_nonneg hheb_eps htheta_nonneg
          have hdelta_bound :
              (δ t) ^ betaExp ≤ (B * ε t / (t + 2 : ℝ)) ^ theta := by
            rw [hδpow]
            exact hheb_theta
          have hone_le_r : (1 : ℝ) ≤ r := by linarith
          have htheta_le_beta : theta ≤ betaExp := by
            rw [hbetaEq]
            calc
              theta = theta * 1 := by ring
              _ ≤ theta * r := by
                    exact mul_le_mul_of_nonneg_left hone_le_r htheta_nonneg
              _ = r * theta := by ring
          have htheta_sub_beta_nonpos : theta - betaExp ≤ 0 := by
            linarith
          have hKpow_tail_le_one : K ^ (theta - betaExp) ≤ 1 := by
            exact Real.rpow_le_one_of_one_le_of_nonpos hK_ge_one htheta_sub_beta_nonpos
          have hpow_Csmall :
              (Csmall t) ^ betaExp =
                (16 * (L : ℝ) / (q * A)) ^ betaExp *
                  (t + 2 : ℝ) ^ (σ * betaExp) * K ^ (-betaExp) := by
            have hfirst :
                16 * (L : ℝ) * (t + 2 : ℝ) ^ σ / (q * A * K) =
                  ((16 * (L : ℝ) / (q * A)) * (t + 2 : ℝ) ^ σ) * K⁻¹ := by
              field_simp [hK_pos.ne', hA.ne', hq_pos.ne']
            dsimp [Csmall]
            rw [hfirst]
            have hbase_nonneg : 0 ≤ 16 * (L : ℝ) / (q * A) := by positivity
            have hpow_nonneg : 0 ≤ (t + 2 : ℝ) ^ σ := by positivity
            calc
              (((16 * (L : ℝ) / (q * A)) * (t + 2 : ℝ) ^ σ) * K⁻¹) ^ betaExp
                  = (((16 * (L : ℝ) / (q * A)) * (t + 2 : ℝ) ^ σ) ^ betaExp) *
                      (K⁻¹) ^ betaExp := by
                        rw [Real.mul_rpow (mul_nonneg hbase_nonneg hpow_nonneg)
                          (inv_nonneg.2 hK_nonneg)]
              _ = (((16 * (L : ℝ) / (q * A)) ^ betaExp) *
                    (((t + 2 : ℝ) ^ σ) ^ betaExp)) *
                    (K⁻¹) ^ betaExp := by
                      rw [Real.mul_rpow hbase_nonneg hpow_nonneg]
              _ = (((16 * (L : ℝ) / (q * A)) ^ betaExp) *
                    ((t + 2 : ℝ) ^ (σ * betaExp))) *
                    (K⁻¹) ^ betaExp := by
                      rw [← Real.rpow_mul (by positivity : 0 ≤ (t + 2 : ℝ)) σ betaExp]
              _ = (((16 * (L : ℝ) / (q * A)) ^ betaExp) *
                    ((t + 2 : ℝ) ^ (σ * betaExp))) *
                    K ^ (-betaExp) := by
                      rw [Real.inv_rpow hK_nonneg]
                      rw [← Real.rpow_neg (le_of_lt hK_pos) betaExp]
              _ = (16 * (L : ℝ) / (q * A)) ^ betaExp *
                    (t + 2 : ℝ) ^ (σ * betaExp) * K ^ (-betaExp) := by
                      ring
          have hterm2 :
              c t * (4 * Rtail t * (δ t) ^ betaExp) ≤
                ((1 - σ) / 4) * K / (t + 2 : ℝ) ^ (1 + σ) := by
            let tailMid : ℝ :=
              (2 / (t + 2 : ℝ)) * (4 * Rtail t * (δ t) ^ betaExp)
            let tailUpper : ℝ :=
              (2 / (t + 2 : ℝ)) * (4 * Rtail t * (B * ε t / (t + 2 : ℝ)) ^ theta)
            let tailBound : ℝ := Cres * K ^ (theta - betaExp) / (t + 2 : ℝ) ^ (1 + σ)
            have hR_nonneg : 0 ≤ Rtail t := by
              dsimp [Rtail]
              positivity
            have htail_step1 :
                c t * (4 * Rtail t * (δ t) ^ betaExp) ≤ tailMid := by
              dsimp [tailMid]
              exact mul_le_mul_of_nonneg_right hc_bound (by positivity)
            have htail_step2 :
                tailMid ≤ tailUpper := by
              dsimp [tailMid, tailUpper]
              exact mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hdelta_bound (by positivity : 0 ≤ 4 * Rtail t))
                (by positivity : 0 ≤ 2 / (t + 2 : ℝ))
            have hpow_split3 :
                (t + 2 : ℝ) * (t + 2 : ℝ) ^ ((1 + σ) * theta) =
                  (t + 2 : ℝ) ^ (1 + (1 + σ) * theta) := by
              have hbase_pos : 0 < (t + 2 : ℝ) := by positivity
              calc
                (t + 2 : ℝ) * (t + 2 : ℝ) ^ ((1 + σ) * theta)
                    = (t + 2 : ℝ) ^ (1 : ℝ) * (t + 2 : ℝ) ^ ((1 + σ) * theta) := by
                          rw [Real.rpow_one]
                _ = (t + 2 : ℝ) ^ (1 + (1 + σ) * theta) := by
                      symm
                      exact Real.rpow_add hbase_pos 1 ((1 + σ) * theta)
            have hKexp :
                K ^ (-betaExp) * K ^ theta = K ^ (theta - betaExp) := by
              calc
                K ^ (-betaExp) * K ^ theta = K ^ ((-betaExp) + theta) := by
                      symm
                      exact Real.rpow_add hK_pos (-betaExp) theta
                _ = K ^ (theta - betaExp) := by
                      congr 1
                      ring
            have htheta_sigma_neg :
                theta * (σ * (r - 1) - 1) = -σ := by
              calc
                theta * (σ * (r - 1) - 1) = -(theta * (1 - (r - 1) * σ)) := by
                      ring
                _ = -σ := by rw [htheta_sigma]
            have hEqExp2 :
                σ * betaExp - (1 + (1 + σ) * theta) = -(1 + σ) := by
              calc
                σ * betaExp - (1 + (1 + σ) * theta)
                    = theta * (σ * (r - 1) - 1) - 1 := by
                          rw [hbetaEq]
                          ring
                _ = -σ - 1 := by rw [htheta_sigma_neg]
                _ = -(1 + σ) := by ring
            have hpowt :
                (t + 2 : ℝ) ^ (σ * betaExp) /
                    (t + 2 : ℝ) ^ (1 + (1 + σ) * theta) =
                  1 / (t + 2 : ℝ) ^ (1 + σ) := by
              have hbase_pos : 0 < (t + 2 : ℝ) := by positivity
              calc
                (t + 2 : ℝ) ^ (σ * betaExp) /
                    (t + 2 : ℝ) ^ (1 + (1 + σ) * theta)
                    =
                  (t + 2 : ℝ) ^ (σ * betaExp) *
                    (t + 2 : ℝ) ^ (-(1 + (1 + σ) * theta)) := by
                        rw [div_eq_mul_inv, Real.rpow_neg (by positivity : 0 ≤ (t + 2 : ℝ))]
                _ = (t + 2 : ℝ) ^ (σ * betaExp + (-(1 + (1 + σ) * theta))) := by
                      rw [← Real.rpow_add hbase_pos (σ * betaExp) (-(1 + (1 + σ) * theta))]
                _ = (t + 2 : ℝ) ^ (σ * betaExp - (1 + (1 + σ) * theta)) := by
                      rfl
                _ = (t + 2 : ℝ) ^ (-(1 + σ)) := by rw [hEqExp2]
                _ = ((t + 2 : ℝ) ^ (1 + σ))⁻¹ := by
                      rw [Real.rpow_neg (by positivity : 0 ≤ (t + 2 : ℝ))]
                _ = 1 / (t + 2 : ℝ) ^ (1 + σ) := by rw [one_div]
            have htail_step3 :
                tailUpper = tailBound := by
              dsimp [tailUpper, Rtail]
              rw [hpow_Csmall, hpow_eps theta]
              have hCres_eq :
                  Cres =
                    8 * (((q - 2 : ℝ) / q) * (L : ℝ) *
                      (16 * (L : ℝ) / (q * A)) ^ betaExp * B ^ theta) := by
                rfl
              calc
                (2 / (t + 2 : ℝ)) *
                    ((4 *
                        (((q - 2 : ℝ) / q) * (L : ℝ) *
                          ((16 * (L : ℝ) / (q * A)) ^ betaExp *
                            (t + 2 : ℝ) ^ (σ * betaExp) * K ^ (-betaExp)))) *
                      (B ^ theta * K ^ theta /
                        (t + 2 : ℝ) ^ ((1 + σ) * theta)))
                    =
                  (8 * (((q - 2 : ℝ) / q) * (L : ℝ) *
                      (16 * (L : ℝ) / (q * A)) ^ betaExp * B ^ theta)) *
                    (K ^ (-betaExp) * K ^ theta) *
                    ((t + 2 : ℝ) ^ (σ * betaExp) /
                      ((t + 2 : ℝ) * (t + 2 : ℝ) ^ ((1 + σ) * theta))) := by
                        field_simp [show (t + 2 : ℝ) ≠ 0 by positivity,
                          show (t + 2 : ℝ) ^ ((1 + σ) * theta) ≠ 0 by positivity]
                        ring_nf
                _ = Cres * (K ^ (-betaExp) * K ^ theta) *
                    ((t + 2 : ℝ) ^ (σ * betaExp) /
                      ((t + 2 : ℝ) * (t + 2 : ℝ) ^ ((1 + σ) * theta))) := by
                        rw [hCres_eq]
                _ = Cres * (K ^ (-betaExp) * K ^ theta) *
                    ((t + 2 : ℝ) ^ (σ * betaExp) /
                      (t + 2 : ℝ) ^ (1 + (1 + σ) * theta)) := by
                        rw [hpow_split3]
                _ = Cres * K ^ (theta - betaExp) *
                    ((t + 2 : ℝ) ^ (σ * betaExp) /
                      (t + 2 : ℝ) ^ (1 + (1 + σ) * theta)) := by
                        rw [hKexp]
                _ = Cres * K ^ (theta - betaExp) *
                    (1 / (t + 2 : ℝ) ^ (1 + σ)) := by rw [hpowt]
                _ = Cres * K ^ (theta - betaExp) / (t + 2 : ℝ) ^ (1 + σ) := by
                      ring
                _ = tailBound := by rfl
            calc
              c t * (4 * Rtail t * (δ t) ^ betaExp) ≤ tailMid := htail_step1
              _ ≤ tailUpper := htail_step2
              _ = tailBound := htail_step3
              _ ≤ Cres / (t + 2 : ℝ) ^ (1 + σ) := by
                    have hmul : Cres * K ^ (theta - betaExp) ≤ Cres := by
                      have htmp : Cres * K ^ (theta - betaExp) ≤ Cres * 1 := by
                        exact mul_le_mul_of_nonneg_left hKpow_tail_le_one hCres_nonneg
                      simpa using htmp
                    exact div_le_div_of_nonneg_right hmul (by positivity)
              _ ≤ (((1 - σ) / 4) * K) / (t + 2 : ℝ) ^ (1 + σ) := by
                    exact div_le_div_of_nonneg_right
                      (le_trans hCres_le (mul_le_mul_of_nonneg_left hK_ge_K0
                        (by positivity : 0 ≤ (1 - σ) / 4))) (by positivity)
              _ = ((1 - σ) / 4) * K / (t + 2 : ℝ) ^ (1 + σ) := by ring
          let sumTerms : ℝ :=
            c t * (4 * (L : ℝ) * (δ t) ^ 2 + 4 * Rtail t * (δ t) ^ betaExp)
          let nextBound : ℝ :=
            a t * ε t + ((1 - σ) / 2) * K / (t + 2 : ℝ) ^ (1 + σ)
          have href' :
              H (t + 1) ≤ nextBound := by
            have ha_nonneg : 0 ≤ a t := by
              dsimp [a]
              positivity
            have hmain : a t * H t ≤ a t * ε t := by
              exact mul_le_mul_of_nonneg_left hprev ha_nonneg
            have hsum :
                sumTerms ≤ ((1 - σ) / 2) * K / (t + 2 : ℝ) ^ (1 + σ) := by
              calc
                sumTerms = c t * (4 * (L : ℝ) * (δ t) ^ 2) + c t * (4 * Rtail t * (δ t) ^ betaExp) := by
                      dsimp [sumTerms]
                      ring
                _ ≤ ((1 - σ) / 4) * K / (t + 2 : ℝ) ^ (1 + σ) +
                      (((1 - σ) / 4) * K / (t + 2 : ℝ) ^ (1 + σ)) := by
                        exact add_le_add hterm1 hterm2
                _ = ((1 - σ) / 2) * K / (t + 2 : ℝ) ^ (1 + σ) := by ring
            calc
              H (t + 1) ≤ a t * H t + sumTerms := by
                    simpa [sumTerms] using href
              _ ≤ a t * ε t + sumTerms := by
                    linarith [hmain]
              _ ≤ a t * ε t + (((1 - σ) / 2) * K / (t + 2 : ℝ) ^ (1 + σ)) := by
                    linarith [hsum]
              _ = nextBound := by
                    dsimp [nextBound]
          have hnext :
              H (t + 1) ≤ ε (t + 1) := by
            have hgap := hgap_step t
            have hhalf_le :
                ((1 - σ) / 2) * K / (t + 2 : ℝ) ^ (1 + σ) ≤
                  (1 - σ) * K / (t + 2 : ℝ) ^ (1 + σ) := by
              have hnonneg : 0 ≤ (1 - σ) * K / (t + 2 : ℝ) ^ (1 + σ) := by positivity
              calc
                ((1 - σ) / 2) * K / (t + 2 : ℝ) ^ (1 + σ)
                    = (1 / 2 : ℝ) * ((1 - σ) * K / (t + 2 : ℝ) ^ (1 + σ)) := by ring
                _ ≤ 1 * ((1 - σ) * K / (t + 2 : ℝ) ^ (1 + σ)) := by
                      gcongr
                      norm_num
                _ = (1 - σ) * K / (t + 2 : ℝ) ^ (1 + σ) := by ring
            calc
              H (t + 1) ≤ nextBound := href'
              _ = a t * ε t + ((1 - σ) / 2) * K / (t + 2 : ℝ) ^ (1 + σ) := by
                    dsimp [nextBound]
              _ ≤ a t * ε t + (1 - σ) * K / (t + 2 : ℝ) ^ (1 + σ) := by
                    linarith [hhalf_le]
              _ ≤ a t * ε t + (ε (t + 1) - a t * ε t) := by
                    linarith [hgap]
              _ = ε (t + 1) := by ring
          have hnext' : H (T + (n + 1)) ≤ ε (T + (n + 1)) := by
            simpa [t, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hnext
          exact hnext'
  refine ⟨T, K, hK_pos, ?_⟩
  intro n
  have hbound := hMain n
  have hp_eq : 1 + σ = (r * q : ℝ) / (r * q - 2) := by
    dsimp [σ]
    field_simp [hrq_sub_ne]
    nlinarith
  have hdiv :
      F (T + n) ≤ K / (T + n + 2 : ℝ) ^ (1 + σ) := by
    have htmp :
        F (T + n) ≤ ε (T + n) / (T + n + 2 : ℝ) := by
      have hbound' : F (T + n) * (T + n + 2 : ℝ) ≤ ε (T + n) := by
        simpa [H, mul_comm, mul_left_comm, mul_assoc] using hbound
      exact (_root_.le_div_iff₀ (by positivity : 0 < (T + n + 2 : ℝ))).2 hbound'
    have hpow :
        (T + n + 2 : ℝ) ^ (1 + σ) =
          (T + n + 2 : ℝ) * (T + n + 2 : ℝ) ^ σ := by
      calc
        (T + n + 2 : ℝ) ^ (1 + σ)
            = (T + n + 2 : ℝ) ^ (1 : ℝ) * (T + n + 2 : ℝ) ^ σ := by
                rw [Real.rpow_add (by positivity : 0 < (T + n + 2 : ℝ)) 1 σ]
        _ = (T + n + 2 : ℝ) * (T + n + 2 : ℝ) ^ σ := by
              rw [Real.rpow_one]
    simpa [ε, hpow, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using htmp
  have hmono :
      K / (T + n + 2 : ℝ) ^ (1 + σ) ≤ K / (n + 1 : ℝ) ^ (1 + σ) := by
    have hbase :
        (n + 1 : ℝ) ^ (1 + σ) ≤ (T + n + 2 : ℝ) ^ (1 + σ) := by
      have harg : (n + 1 : ℝ) ≤ T + n + 2 := by
        exact_mod_cast (show n + 1 ≤ T + n + 2 by omega)
      exact Real.rpow_le_rpow (by positivity : 0 ≤ (n + 1 : ℝ)) harg (by positivity : 0 ≤ 1 + σ)
    have hrecip :
        1 / (T + n + 2 : ℝ) ^ (1 + σ) ≤ 1 / (n + 1 : ℝ) ^ (1 + σ) := by
      exact one_div_le_one_div_of_le (by positivity : 0 < (n + 1 : ℝ) ^ (1 + σ)) hbase
    calc
      K / (T + n + 2 : ℝ) ^ (1 + σ) = K * (1 / (T + n + 2 : ℝ) ^ (1 + σ)) := by ring
      _ ≤ K * (1 / (n + 1 : ℝ) ^ (1 + σ)) := by
            exact mul_le_mul_of_nonneg_left hrecip hK_nonneg
      _ = K / (n + 1 : ℝ) ^ (1 + σ) := by ring
  have hresult :
      F (T + n) ≤ K / (n + 1 : ℝ) ^ (1 + σ) := by
    exact hdiv.trans hmono
  simpa [F, xSeq, Nat.add_assoc, hp_eq] using hresult

set_option maxHeartbeats 1000000 in
/-- [FW-LOCAL-QEB-OL] The canonical open-loop rule `γ_t = 2/(t+2)` satisfies
the quadratic slice of the local Hölder theorem when `r = 2`. -/
theorem frankWolfe_localGap_qeb_power_rate
    (hC_convex : Convex ℝ C)
    {A B : ℝ} {q : ℝ} (hq : 2 < q) (hA : 0 < A) (hB : 0 < B)
    (f : E → ℝ) (f' : E → E) (L : NNReal) (hL : 0 < L)
    (hConv : IsFirstOrderConvex f f')
    (hSmooth : IsLipschitzSmoothUpperBound f L f')
    (x_star : E) (hx_star : x_star ∈ C)
    (hLocal :
      HasLocalLMOGapPowerOn
        O (C ∩ {y : E | f y = f x_star}) A q)
    (hQEB :
      HasLocalQuadraticErrorBoundOn
        (C := C) (C ∩ {y : E | f y = f x_star}) f (f x_star) B)
    (hmin : ∀ y ∈ C, f x_star ≤ f y)
    (x0 : E) (hx0 : x0 ∈ C) :
    ∃ T : ℕ, ∃ K : ℝ, 0 < K ∧
      ∀ n : ℕ,
        f (frankWolfeSequence O f' x0 (T + n)) - f x_star ≤
          K / (n + 1 : ℝ) ^ ((q : ℝ) / (q - 1 : ℝ)) := by
  have hHEB :
      HasLocalHolderErrorBoundOn
        (C := C) (C ∩ {y : E | f y = f x_star}) f (f x_star) B 2 := by
    simpa [HasLocalHolderErrorBoundOn, HasLocalQuadraticErrorBoundOn] using hQEB
  have hcore :=
    frankWolfe_localGap_heb_power_rate
      (O := O)
      hC_convex (q := q) (r := 2) hq (by norm_num : (2 : ℝ) ≤ 2)
      hA hB f f' L hL hConv hSmooth x_star hx_star hLocal hHEB hmin x0 hx0
  have hq_one_pos : 0 < (q - 1 : ℝ) := by
    linarith
  have hpow : ((2 : ℝ) * q) / ((2 : ℝ) * q - 2) = (q : ℝ) / (q - 1 : ℝ) := by
    have hden_eq : ((2 : ℝ) * q - 2) = 2 * (q - 1 : ℝ) := by
      ring
    rw [hden_eq]
    field_simp [hq_one_pos.ne']
  simpa [hpow] using hcore

set_option maxHeartbeats 3000000 in
/-- [FW-LOCAL-HEB-OL-Q2-SHARP-RGT2] For the quadratic local dual-sharpness
case and a local Hölder error bound of order `r > 2`, the canonical open-loop
rule has the sharp shifted `r / (r - 1)` tail. -/
theorem frankWolfe_localGap_two_heb_power_rate_of_two_lt
    (hC_convex : Convex ℝ C)
    {A B r : ℝ} (hr : 2 < r) (hA : 0 < A) (hB : 0 < B)
    (f : E → ℝ) (f' : E → E) (L : NNReal) (hL : 0 < L)
    (hConv : IsFirstOrderConvex f f')
    (hSmooth : IsLipschitzSmoothUpperBound f L f')
    (x_star : E) (hx_star : x_star ∈ C)
    (hLocal :
      HasLocalLMOGapPowerOn
        O (C ∩ {y : E | f y = f x_star}) A 2)
    (hHEB :
      HasLocalHolderErrorBoundOn
        (C := C) (C ∩ {y : E | f y = f x_star}) f (f x_star) B r)
    (hmin : ∀ y ∈ C, f x_star ≤ f y)
    (x0 : E) (hx0 : x0 ∈ C) :
    ∃ T : ℕ, ∃ K : ℝ, 0 < K ∧
      ∀ n : ℕ,
        f (frankWolfeSequence O f' x0 (T + n)) - f x_star ≤
          K / (n + 1 : ℝ) ^ (r / (r - 1 : ℝ)) := by
  let xSeq : ℕ → E := frankWolfeSequence O f' x0
  let F : ℕ → ℝ := fun t => f (xSeq t) - f x_star
  let Mset : Set E := C ∩ {y : E | f y = f x_star}
  let Dsq : ℝ := (Metric.diam C) ^ 2
  let Bstd : ℝ := max (f x0 - f x_star) ((L : ℝ) * Dsq)
  let H : ℕ → ℝ := fun t => (t + 2 : ℝ) * F t
  let Ksmall : ℝ := 4 * (L : ℝ) / A
  have hr_ge : (2 : ℝ) ≤ r := le_of_lt hr
  have hr_pos : 0 < r := by linarith
  have hr_nonneg : 0 ≤ r := hr_pos.le
  have hr_ne : r ≠ 0 := hr_pos.ne'
  have hrm_pos : 0 < r - 1 := by linarith
  have hrm_ne : r - 1 ≠ 0 := hrm_pos.ne'
  let σ : ℝ := 1 / (r - 1 : ℝ)
  have hσ_pos : 0 < σ := by
    dsimp [σ]
    positivity
  have hσ_nonneg : 0 ≤ σ := hσ_pos.le
  have hσ_lt_one : σ < 1 := by
    dsimp [σ]
    simpa [one_div] using inv_lt_one_of_one_lt₀ (by linarith : (1 : ℝ) < r - 1)
  have hσ_le_one : σ ≤ 1 := by linarith
  have hone_sub_sigma_pos : 0 < 1 - σ := by linarith
  have hpow_two_lt_one : (2 : ℝ) ^ (σ - 1) < 1 := by
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hpow_two_margin_pos : 0 < 1 - (2 : ℝ) ^ (σ - 1) := by
    linarith
  have hKsmall_pos : 0 < Ksmall := by
    dsimp [Ksmall]
    positivity
  have hxSeq : ∀ t, xSeq t ∈ C := by
    intro t
    simpa [xSeq] using
      frankWolfeSequence_mem
        (O := O)
        hC_convex f' hx0 t
  have hF_nonneg : ∀ t, 0 ≤ F t := by
    intro t
    exact primalGap_nonneg_of_isMinOn (C := C) (f := f) (hxSeq t) hmin
  have hH_nonneg : ∀ t, 0 ≤ H t := by
    intro t
    dsimp [H]
    exact mul_nonneg (by positivity) (hF_nonneg t)
  have hBstd_nonneg : 0 ≤ Bstd := by
    have hgap0_nonneg : 0 ≤ f x0 - f x_star := by
      exact primalGap_nonneg_of_isMinOn (C := C) (f := f) hx0 hmin
    exact le_trans hgap0_nonneg (le_max_left _ _)
  have hstd :
      ∀ t, F t ≤ (2 * Bstd) / (t + 2 : ℝ) := by
    intro t
    have hfw :=
      frank_wolfe_convergence_of_initialGap_le
        (O := O)
        hC_convex f f' L hSmooth hConv hx_star hx0
        (B := Bstd) hBstd_nonneg (le_max_left _ _) (le_max_right _ _) t
    simpa [F, xSeq, Bstd, Dsq] using hfw
  have hH_bounded :
      ∀ t, H t ≤ 2 * Bstd := by
    intro t
    calc
      H t = (t + 2 : ℝ) * F t := by rfl
      _ ≤ (t + 2 : ℝ) * ((2 * Bstd) / (t + 2 : ℝ)) := by
            gcongr
            exact hstd t
      _ = 2 * Bstd := by
            field_simp [show (t + 2 : ℝ) ≠ 0 by positivity]
  have hgap_zero :
      Tendsto F atTop (nhds 0) := by
    simpa [F, xSeq] using
      frankWolfe_gap_tendsto_zero_of_isMinOn
        (O := O)
        hC_convex f f' L hConv hSmooth hx_star hmin hx0
  have hcont : Continuous f :=
    continuous_of_isFirstOrderConvex_isLipschitzSmoothUpperBound
      (f := f) (f' := f') (L := L) hConv hSmooth
  have hlevel_closed : IsClosed {y : E | f y = f x_star} :=
    isClosed_eq hcont continuous_const
  have hMset_compact : IsCompact Mset := by
    simpa [Mset] using O.isCompact.inter_right hlevel_closed
  have hMset_nonempty : Mset.Nonempty := by
    refine ⟨x_star, ?_⟩
    simp [Mset, hx_star]
  have hdist_zero :
      Tendsto (fun t => Metric.infDist (xSeq t) Mset) atTop (nhds 0) := by
    simpa [xSeq, Mset] using
      tendsto_infDist_minimizerSet_of_gap_tendsto_zero
        O.isCompact (f := f) (f' := f') (L := L) hConv hSmooth x_star xSeq hxSeq hgap_zero
  classical
  let pSeq : ℕ → E := fun t =>
    Classical.choose (hMset_compact.exists_infDist_eq_dist hMset_nonempty (xSeq t))
  have hpSeq_memM : ∀ t, pSeq t ∈ Mset := by
    intro t
    exact (Classical.choose_spec
      (hMset_compact.exists_infDist_eq_dist hMset_nonempty (xSeq t))).1
  have hpSeq_val : ∀ t, f (pSeq t) = f x_star := by
    intro t
    exact (hpSeq_memM t).2
  have hpSeq_dist : ∀ t, Metric.infDist (xSeq t) Mset = dist (xSeq t) (pSeq t) := by
    intro t
    exact (Classical.choose_spec
      (hMset_compact.exists_infDist_eq_dist hMset_nonempty (xSeq t))).2
  let δ : ℕ → ℝ := fun t => ‖xSeq t - pSeq t‖
  have hδ_zero :
      Tendsto δ atTop (nhds 0) := by
    have hdist_zero' :
        Tendsto (fun t => dist (xSeq t) (pSeq t)) atTop (nhds 0) := by
      simpa [hpSeq_dist] using hdist_zero
    simpa [δ, dist_eq_norm] using hdist_zero'
  obtain ⟨ρheb, hρheb_pos, hheb_local⟩ := hHEB
  have hheb_event : ∀ᶠ t : ℕ in atTop, (δ t) ^ r ≤ B * F t := by
    have hδ_event : ∀ᶠ t : ℕ in atTop, δ t < ρheb := by
      exact hδ_zero.eventually (Iio_mem_nhds hρheb_pos)
    filter_upwards [hδ_event] with t hδt
    have hdist_t : Metric.infDist (xSeq t) Mset < ρheb := by
      rw [hpSeq_dist t]
      simpa [δ, dist_eq_norm] using hδt
    have hheb_t :
        Metric.infDist (xSeq t) Mset ^ r ≤ B * (f (xSeq t) - f x_star) := by
      simpa using hheb_local (xSeq t) (hxSeq t) hdist_t
    rw [hpSeq_dist t, dist_eq_norm] at hheb_t
    simpa [δ, F] using hheb_t
  rcases Filter.Eventually.exists_forall_of_atTop hheb_event with ⟨Theb, hTheb⟩
  have hstd_step :
      ∀ t,
        F (t + 1) ≤
          (1 - 2 / (t + 2 : ℝ)) * F t +
            ((L : ℝ) / 2) * (2 / (t + 2 : ℝ)) ^ 2 * Dsq := by
    intro t
    have href :
        f (frankWolfeStep O f' (xSeq t) (2 / (t + 2 : ℝ))) -
            f (pSeq t) ≤
          (1 - 2 / (t + 2 : ℝ)) * (f (xSeq t) - f (pSeq t)) +
            ((L : ℝ) / 2) * (2 / (t + 2 : ℝ)) ^ 2 * Dsq := by
      simpa [xSeq, Dsq] using
        (frankWolfeStep_gap_bound
          (O := O)
          (C := C) (f := f) (f' := f') (L := L) hSmooth hConv
          (x := xSeq t) (x_star := pSeq t)
          (hxSeq t) ((hpSeq_memM t).1)
          (γ := 2 / (t + 2 : ℝ)) (standardStepSize_mem_Icc t))
    simpa [F, xSeq, frankWolfeSequence, hpSeq_val t, frankWolfeOpenLoopSequence, openLoopStepSize] using href
  let a : ℕ → ℝ := fun t => (t : ℝ) * (t + 3 : ℝ) / (t + 2 : ℝ) ^ 2
  let c : ℕ → ℝ := fun t => (t + 3 : ℝ) / (t + 2 : ℝ) ^ 2
  let stdConst : ℕ → ℝ :=
    fun t => 2 * (L : ℝ) * Dsq * (t + 3 : ℝ) / (t + 2 : ℝ) ^ 2
  have hstd_scaled :
      ∀ t, H (t + 1) ≤ a t * H t + stdConst t := by
    intro t
    have hh_succ : H (t + 1) = (t + 3 : ℝ) * F (t + 1) := by
      change ((((t + 1 : ℕ) : ℝ) + 2) * F (t + 1) = (t + 3 : ℝ) * F (t + 1))
      have hcast : (((t + 1 : ℕ) : ℝ) + 2) = (t + 3 : ℝ) := by
        exact_mod_cast (show t + 1 + 2 = t + 3 by omega)
      rw [hcast]
    have hmul := mul_le_mul_of_nonneg_left (hstd_step t) (by positivity : 0 ≤ (t + 3 : ℝ))
    calc
      H (t + 1) = (t + 3 : ℝ) * F (t + 1) := hh_succ
      _ ≤ (t + 3 : ℝ) *
            ((1 - 2 / (t + 2 : ℝ)) * F t +
              ((L : ℝ) / 2) * (2 / (t + 2 : ℝ)) ^ 2 * Dsq) := hmul
      _ = a t * H t + stdConst t := by
            simpa [a, H, stdConst, mul_assoc, mul_left_comm, mul_comm] using
              (frankWolfe_openLoop_scaled_standard_eq
                (F := F) (Dsq := Dsq) (L := (L : ℝ)) t)
  have hraw_small_or_refined :
      ∀ t,
        H t ≤ Ksmall * δ t ∨
          F (t + 1) ≤
            (1 - 2 / (t + 2 : ℝ)) * F t +
              (L : ℝ) * (2 / (t + 2 : ℝ)) ^ 2 * (δ t) ^ 2 := by
    intro t
    by_cases hFt0 : F t = 0
    · left
      have hKsmall_nonneg : 0 ≤ Ksmall := le_of_lt hKsmall_pos
      have hδ_nonneg : 0 ≤ δ t := by
        dsimp [δ]
        positivity
      simpa [H, hFt0] using (mul_nonneg hKsmall_nonneg hδ_nonneg)
    · by_cases hcase : 2 / (t + 2 : ℝ) ≤ A * ‖f' (xSeq t)‖ / (2 * (L : ℝ))
      · right
        have hxStarSeqM : pSeq t ∈ Mset := hpSeq_memM t
        have href :
            f (frankWolfeStep O f' (xSeq t) (2 / (t + 2 : ℝ))) -
                f (pSeq t) ≤
              (1 - 2 / (t + 2 : ℝ)) * (f (xSeq t) - f (pSeq t)) +
                (L : ℝ) * (2 / (t + 2 : ℝ)) ^ 2 * ‖xSeq t - pSeq t‖ ^ 2 := by
          simpa [xSeq, δ] using
            (frankWolfeStep_gap_bound_with_localCorrection_two
              (O := O)
              hLocal
              f f' L hConv hSmooth
              (x := xSeq t) (x_star := pSeq t) ((hpSeq_memM t).1) hxStarSeqM
              (γ := 2 / (t + 2 : ℝ)) (standardStepSize_mem_Icc t) hcase)
        simpa [F, xSeq, frankWolfeSequence, hpSeq_val t, frankWolfeOpenLoopSequence, openLoopStepSize] using href
      · left
        have hF_pos_t : 0 < F t := lt_of_le_of_ne (hF_nonneg t) (by simpa [eq_comm] using hFt0)
        have hδ_pos_t : 0 < δ t := by
          by_contra hδt
          have hδ0 : δ t = 0 := le_antisymm (not_lt.mp hδt) (norm_nonneg _)
          have hxeq : xSeq t = pSeq t := by
            exact sub_eq_zero.mp (norm_eq_zero.mp (by simpa [δ] using hδ0))
          have : F t = 0 := by simp [F, hxeq, hpSeq_val t]
          exact hFt0 this
        have hgap_grad :
            F t ≤ ‖f' (xSeq t)‖ * δ t := by
          have hgap_t :
              f (xSeq t) - f (pSeq t) ≤ ‖f' (xSeq t)‖ * ‖xSeq t - pSeq t‖ := by
            simpa [xSeq] using
              (primalGap_le_gradNorm_mul_dist
                (f := f) (f' := f') hConv
                (x := xSeq t) (x_star := pSeq t))
          simpa [F, δ, hpSeq_val t] using hgap_t
        have hcase' :
            A * ‖f' (xSeq t)‖ / (2 * (L : ℝ)) < 2 / (t + 2 : ℝ) := lt_of_not_ge hcase
        have hmul :
            A * ‖f' (xSeq t)‖ < (2 / (t + 2 : ℝ)) * (2 * (L : ℝ)) := by
          exact (_root_.div_lt_iff₀ (show 0 < 2 * (L : ℝ) by positivity)).1 hcase'
        have hgrad_lt :
            ‖f' (xSeq t)‖ < ((2 / (t + 2 : ℝ)) * (2 * (L : ℝ))) / A := by
          have : ‖f' (xSeq t)‖ * A < (2 / (t + 2 : ℝ)) * (2 * (L : ℝ)) := by
            simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
          exact (_root_.lt_div_iff₀ hA).2 this
        have hsmall' :
            F t < (((2 / (t + 2 : ℝ)) * (2 * (L : ℝ))) / A) * δ t := by
          exact lt_of_le_of_lt hgap_grad <|
            mul_lt_mul_of_pos_right hgrad_lt hδ_pos_t
        have hscaled :
            H t < Ksmall * δ t := by
          dsimp [H, Ksmall]
          have hEq :
              (t + 2 : ℝ) * ((((2 / (t + 2 : ℝ)) * (2 * (L : ℝ))) / A) * δ t) =
                (4 * (L : ℝ) / A) * δ t := by
            field_simp [hA.ne', (show (t + 2 : ℝ) ≠ 0 by positivity)]
            ring
          have hmul' :
              (t + 2 : ℝ) * F t <
                (t + 2 : ℝ) *
                  ((((2 / (t + 2 : ℝ)) * (2 * (L : ℝ))) / A) * δ t) := by
            exact mul_lt_mul_of_pos_left hsmall' (by positivity)
          simpa [hEq] using hmul'
        exact le_of_lt hscaled
  have hterm_zero :
      Tendsto (fun t : ℕ => 8 * (L : ℝ) * B ^ (2 / r) / (t + 2 : ℝ) ^ σ)
        atTop (nhds 0) := by
    have hpowNat :
        Tendsto (fun t : ℕ => (t : ℝ) + 2) atTop atTop := by
      exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    have hpow :
        Tendsto (fun t : ℕ => (t + 2 : ℝ) ^ σ) atTop atTop := by
      exact (tendsto_rpow_atTop hσ_pos).comp hpowNat
    exact tendsto_const_nhds.div_atTop hpow
  have hterm_event :
      ∀ᶠ t : ℕ in atTop,
        8 * (L : ℝ) * B ^ (2 / r) / (t + 2 : ℝ) ^ σ < (1 - σ) := by
    exact hterm_zero.eventually (Iio_mem_nhds hone_sub_sigma_pos)
  rcases Filter.Eventually.exists_forall_of_atTop hterm_event with ⟨Tterm, hTterm⟩
  let Ssmall : ℝ := (Ksmall ^ r * B) ^ σ
  let K0 : ℝ := max 1 (2 * Ssmall)
  have hSsmall_nonneg : 0 ≤ Ssmall := by
    dsimp [Ssmall]
    positivity
  have hK0_ge_one : 1 ≤ K0 := by
    dsimp [K0]
    exact le_max_left _ _
  have hK0_pos : 0 < K0 := lt_of_lt_of_le zero_lt_one hK0_ge_one
  have hSsmall_le_half_K0 : Ssmall ≤ K0 / 2 := by
    have hbase : 2 * Ssmall ≤ K0 := by
      dsimp [K0]
      exact le_max_right _ _
    nlinarith
  have hstdtail_zero :
      Tendsto
        (fun t : ℕ => 8 * (L : ℝ) * Dsq / (t + 3 : ℝ) ^ (1 - σ))
        atTop (nhds 0) := by
    have hpowNat :
        Tendsto (fun t : ℕ => (t : ℝ) + 3) atTop atTop := by
      exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    have hpow :
        Tendsto (fun t : ℕ => (t + 3 : ℝ) ^ (1 - σ)) atTop atTop := by
      exact (tendsto_rpow_atTop hone_sub_sigma_pos).comp hpowNat
    exact tendsto_const_nhds.div_atTop hpow
  have hstd_event :
      ∀ᶠ t : ℕ in atTop,
        8 * (L : ℝ) * Dsq / (t + 3 : ℝ) ^ (1 - σ) <
          (1 - (2 : ℝ) ^ (σ - 1)) * K0 := by
    exact hstdtail_zero.eventually (Iio_mem_nhds (by
      have : 0 < 1 - (2 : ℝ) ^ (σ - 1) := hpow_two_margin_pos
      positivity))
  rcases Filter.Eventually.exists_forall_of_atTop hstd_event with ⟨Tstd, hTstd⟩
  let T : ℕ := max Theb (max Tterm Tstd)
  let K : ℝ := max K0 ((2 * Bstd) * (T + 2 : ℝ) ^ σ)
  let ε : ℕ → ℝ := fun t => K / (t + 2 : ℝ) ^ σ
  have hK_ge_K0 : K0 ≤ K := by
    dsimp [K]
    exact le_max_left _ _
  have hK_pos : 0 < K := lt_of_lt_of_le hK0_pos hK_ge_K0
  have hK_nonneg : 0 ≤ K := hK_pos.le
  have hK_ge_one : 1 ≤ K := le_trans hK0_ge_one hK_ge_K0
  have hSsmall_le_half_K : Ssmall ≤ K / 2 := by
    linarith [hSsmall_le_half_K0, hK_ge_K0]
  have hT_ge_heb : Theb ≤ T := by
    dsimp [T]
    exact le_max_left _ _
  have hT_ge_term : Tterm ≤ T := by
    dsimp [T]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hT_ge_std : Tstd ≤ T := by
    dsimp [T]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hε_pos : ∀ t, 0 < ε t := by
    intro t
    dsimp [ε]
    positivity
  have hbase :
      H T ≤ ε T := by
    have hbound : H T ≤ 2 * Bstd := hH_bounded T
    have hK_base : (2 * Bstd) * (T + 2 : ℝ) ^ σ ≤ K := by
      dsimp [K]
      exact le_max_right _ _
    have hdiv :
        2 * Bstd ≤ K / (T + 2 : ℝ) ^ σ := by
      have hden_pos : 0 < (T + 2 : ℝ) ^ σ := by positivity
      exact (_root_.le_div_iff₀ hden_pos).2 <| by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hK_base
    simpa [ε] using hbound.trans hdiv
  have hstd_small :
      ∀ t ≥ T,
        stdConst t ≤ (1 - (2 : ℝ) ^ (σ - 1)) * ε (t + 1) := by
    intro t ht
    have htail :
        8 * (L : ℝ) * Dsq / (t + 3 : ℝ) ^ (1 - σ) <
          (1 - (2 : ℝ) ^ (σ - 1)) * K0 := by
      exact hTstd t (le_trans hT_ge_std ht)
    have hstd_bound1 : stdConst t ≤ 4 * (L : ℝ) * Dsq / (t + 2 : ℝ) := by
      have hB_nonneg : 0 ≤ (L : ℝ) * Dsq := by positivity
      simpa [stdConst, mul_assoc, mul_left_comm, mul_comm] using
        (frankWolfe_openLoop_stdConst_bound (B := (L : ℝ) * Dsq) hB_nonneg t)
    have hstd_bound2 : 4 * (L : ℝ) * Dsq / (t + 2 : ℝ) ≤
        8 * (L : ℝ) * Dsq / (t + 3 : ℝ) := by
      have hfrac : (1 : ℝ) / (t + 2 : ℝ) ≤ (2 : ℝ) / (t + 3 : ℝ) := by
        have harg : (t + 3 : ℝ) ≤ 2 * (t + 2 : ℝ) := by
          exact_mod_cast (show t + 3 ≤ 2 * (t + 2) by omega)
        have hdiv :
            1 / (2 * (t + 2 : ℝ)) ≤ 1 / (t + 3 : ℝ) := by
          exact one_div_le_one_div_of_le (by positivity : 0 < (t + 3 : ℝ)) harg
        have hscaled := mul_le_mul_of_nonneg_left hdiv (by positivity : 0 ≤ (2 : ℝ))
        have hEqL : (2 : ℝ) * (1 / (2 * (t + 2 : ℝ))) = (1 : ℝ) / (t + 2 : ℝ) := by
          field_simp [show (t + 2 : ℝ) ≠ 0 by positivity]
        have hEqR : (2 : ℝ) * (1 / (t + 3 : ℝ)) = (2 : ℝ) / (t + 3 : ℝ) := by
          ring
        simpa [hEqL, hEqR, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hscaled
      have hcoef_nonneg : 0 ≤ 4 * (L : ℝ) * Dsq := by positivity
      have hmul :
          (4 * (L : ℝ) * Dsq) * ((1 : ℝ) / (t + 2 : ℝ)) ≤
            (4 * (L : ℝ) * Dsq) * ((2 : ℝ) / (t + 3 : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hfrac hcoef_nonneg
      calc
        4 * (L : ℝ) * Dsq / (t + 2 : ℝ)
            = (4 * (L : ℝ) * Dsq) * ((1 : ℝ) / (t + 2 : ℝ)) := by ring
        _ ≤ (4 * (L : ℝ) * Dsq) * ((2 : ℝ) / (t + 3 : ℝ)) := hmul
        _ = 8 * (L : ℝ) * Dsq / (t + 3 : ℝ) := by ring
    have hsplit :
        8 * (L : ℝ) * Dsq / (t + 3 : ℝ) =
          (8 * (L : ℝ) * Dsq / (t + 3 : ℝ) ^ (1 - σ)) /
            (t + 3 : ℝ) ^ σ := by
      let aa : ℝ := (t + 3 : ℝ) ^ (1 - σ)
      let bb : ℝ := (t + 3 : ℝ) ^ σ
      have haa_ne : aa ≠ 0 := by dsimp [aa]; positivity
      have hbb_ne : bb ≠ 0 := by dsimp [bb]; positivity
      have hpow : aa * bb = (t + 3 : ℝ) := by
        dsimp [aa, bb]
        calc
          (t + 3 : ℝ) ^ (1 - σ) * (t + 3 : ℝ) ^ σ =
              (t + 3 : ℝ) ^ ((1 - σ) + σ) := by
                rw [← Real.rpow_add (by positivity : 0 < (t + 3 : ℝ)) (1 - σ) σ]
          _ = (t + 3 : ℝ) ^ (1 : ℝ) := by ring_nf
          _ = (t + 3 : ℝ) := by rw [Real.rpow_one]
      have hdiv_eq :
          (8 * (L : ℝ) * Dsq / aa) / bb = 8 * (L : ℝ) * Dsq / (aa * bb) := by
        field_simp [haa_ne, hbb_ne]
      calc
        8 * (L : ℝ) * Dsq / (t + 3 : ℝ) = 8 * (L : ℝ) * Dsq / (aa * bb) := by
              rw [hpow]
        _ = (8 * (L : ℝ) * Dsq / aa) / bb := by
              exact hdiv_eq.symm
        _ = (8 * (L : ℝ) * Dsq / (t + 3 : ℝ) ^ (1 - σ)) /
              (t + 3 : ℝ) ^ σ := by
              rfl
    have hscaled :
        (8 * (L : ℝ) * Dsq / (t + 3 : ℝ) ^ (1 - σ)) /
            (t + 3 : ℝ) ^ σ ≤
          ((1 - (2 : ℝ) ^ (σ - 1)) * K0) / (t + 3 : ℝ) ^ σ := by
      exact (_root_.div_le_div_of_nonneg_right (le_of_lt htail) (by positivity))
    have hKscaled :
        ((1 - (2 : ℝ) ^ (σ - 1)) * K0) / (t + 3 : ℝ) ^ σ ≤
          ((1 - (2 : ℝ) ^ (σ - 1)) * K) / (t + 3 : ℝ) ^ σ := by
      exact (_root_.div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hK_ge_K0 hpow_two_margin_pos.le) (by positivity))
    calc
      stdConst t ≤ 4 * (L : ℝ) * Dsq / (t + 2 : ℝ) := hstd_bound1
      _ ≤ 8 * (L : ℝ) * Dsq / (t + 3 : ℝ) := hstd_bound2
      _ = (8 * (L : ℝ) * Dsq / (t + 3 : ℝ) ^ (1 - σ)) /
            (t + 3 : ℝ) ^ σ := hsplit
      _ ≤ ((1 - (2 : ℝ) ^ (σ - 1)) * K0) / (t + 3 : ℝ) ^ σ := hscaled
      _ ≤ ((1 - (2 : ℝ) ^ (σ - 1)) * K) / (t + 3 : ℝ) ^ σ := hKscaled
      _ = (1 - (2 : ℝ) ^ (σ - 1)) * ε (t + 1) := by
            have hcast : (((t + 1 : ℕ) : ℝ) + 2) = (t + 3 : ℝ) := by
              exact_mod_cast (show t + 1 + 2 = t + 3 by omega)
            dsimp [ε]
            rw [hcast]
            ring
  have hgap_step :
      ∀ t : ℕ, (1 - σ) * K / (t + 2 : ℝ) ^ (1 + σ) ≤ ε (t + 1) - a t * ε t := by
    intro t
    let u : ℝ := 1 / (t + 2 : ℝ)
    have hu_nonneg : 0 ≤ u := by dsimp [u]; positivity
    have hpow_le : (1 + u) ^ σ ≤ 1 + σ * u := by
      simpa [u, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using
        (rpow_one_add_le_one_add_mul_self (by linarith : -1 ≤ u) hσ_nonneg hσ_le_one)
    have hlin : 1 - σ * u ≤ 1 / (1 + σ * u) := by
      exact one_sub_le_one_div_add (by positivity : 0 ≤ σ * u)
    have hrecip : 1 / (1 + σ * u) ≤ 1 / ((1 + u) ^ σ) := by
      exact one_div_le_one_div_of_le (by positivity : 0 < (1 + u) ^ σ) hpow_le
    have hlower0 : 1 - σ * u ≤ 1 / ((1 + u) ^ σ) := le_trans hlin hrecip
    have hfactor : ε t * (1 - σ * u) ≤ ε (t + 1) := by
      have hmul : ε t * (1 - σ * u) ≤ ε t * (1 / ((1 + u) ^ σ)) := by
        exact mul_le_mul_of_nonneg_left hlower0 (hε_pos t).le
      have hsplit :
          ε t * (1 / ((1 + u) ^ σ)) = ε (t + 1) := by
        have hEq : (t + 3 : ℝ) = (t + 2 : ℝ) * (1 + u) := by
          dsimp [u]
          field_simp [show (t + 2 : ℝ) ≠ 0 by positivity]
          ring
        calc
          ε t * (1 / ((1 + u) ^ σ))
              = K / ((t + 2 : ℝ) ^ σ * (1 + u) ^ σ) := by
                    dsimp [ε]
                    field_simp [show (t + 2 : ℝ) ^ σ ≠ 0 by positivity]
          _ = K / (((t + 2 : ℝ) * (1 + u)) ^ σ) := by
                have hmulrpow :
                    ((t + 2 : ℝ) * (1 + u)) ^ σ =
                      (t + 2 : ℝ) ^ σ * (1 + u) ^ σ := by
                    exact Real.mul_rpow (by positivity) (by positivity)
                rw [hmulrpow]
          _ = K / (t + 3 : ℝ) ^ σ := by rw [hEq]
          _ = ε (t + 1) := by
                have hcast : (((t + 1 : ℕ) : ℝ) + 2) = (t + 3 : ℝ) := by
                  exact_mod_cast (show t + 1 + 2 = t + 3 by omega)
                dsimp [ε]
                rw [hcast]
      exact hmul.trans_eq hsplit
    have ha_le :
        a t * ε t ≤ (1 - 1 / (t + 2 : ℝ)) * ε t := by
      have hcoeff : a t ≤ 1 - 1 / (t + 2 : ℝ) := by
        dsimp [a]
        have hden : 0 < (t + 2 : ℝ) ^ 2 := by positivity
        have hEq :
            (1 - 1 / (t + 2 : ℝ)) * (t + 2 : ℝ) ^ 2 =
              (t + 1 : ℝ) * (t + 2 : ℝ) := by
          field_simp [show (t + 2 : ℝ) ≠ 0 by positivity]
          ring
        have hpoly : (t : ℝ) * (t + 3 : ℝ) ≤ (t + 1 : ℝ) * (t + 2 : ℝ) := by
          have hgap : (t + 1 : ℝ) * (t + 2 : ℝ) =
              (t : ℝ) * (t + 3 : ℝ) + 2 := by ring
          calc
            (t : ℝ) * (t + 3 : ℝ) ≤ (t : ℝ) * (t + 3 : ℝ) + 2 := by linarith
            _ = (t + 1 : ℝ) * (t + 2 : ℝ) := by simp [hgap]
        refine (_root_.div_le_iff₀ hden).2 ?_
        rw [hEq]
        exact hpoly
      exact mul_le_mul_of_nonneg_right hcoeff (hε_pos t).le
    have hEq :
        (1 - 1 / (t + 2 : ℝ)) * ε t =
          ε t - K / (t + 2 : ℝ) ^ (1 + σ) := by
      dsimp [ε]
      have hpow :
          (t + 2 : ℝ) ^ (1 + σ) = (t + 2 : ℝ) * (t + 2 : ℝ) ^ σ := by
        calc
          (t + 2 : ℝ) ^ (1 + σ) = (t + 2 : ℝ) ^ (1 : ℝ) * (t + 2 : ℝ) ^ σ := by
                rw [Real.rpow_add (by positivity : 0 < (t + 2 : ℝ)) 1 σ]
          _ = (t + 2 : ℝ) * (t + 2 : ℝ) ^ σ := by rw [Real.rpow_one]
      calc
        (1 - 1 / (t + 2 : ℝ)) * (K / (t + 2 : ℝ) ^ σ)
            = K / (t + 2 : ℝ) ^ σ - K / ((t + 2 : ℝ) * (t + 2 : ℝ) ^ σ) := by
                field_simp [show (t + 2 : ℝ) ^ σ ≠ 0 by positivity,
                  show (t + 2 : ℝ) ≠ 0 by positivity]
        _ = K / (t + 2 : ℝ) ^ σ - K / (t + 2 : ℝ) ^ (1 + σ) := by rw [← hpow]
        _ = ε t - K / (t + 2 : ℝ) ^ (1 + σ) := by rfl
    have hfactor' :
        (1 - σ * u) * ε t = ε t - σ * K / (t + 2 : ℝ) ^ (1 + σ) := by
      dsimp [u, ε]
      have hpow :
          (t + 2 : ℝ) ^ (1 + σ) = (t + 2 : ℝ) * (t + 2 : ℝ) ^ σ := by
        calc
          (t + 2 : ℝ) ^ (1 + σ) = (t + 2 : ℝ) ^ (1 : ℝ) * (t + 2 : ℝ) ^ σ := by
                rw [Real.rpow_add (by positivity : 0 < (t + 2 : ℝ)) 1 σ]
          _ = (t + 2 : ℝ) * (t + 2 : ℝ) ^ σ := by rw [Real.rpow_one]
      calc
        (1 - σ * (1 / (t + 2 : ℝ))) * (K / (t + 2 : ℝ) ^ σ)
            = K / (t + 2 : ℝ) ^ σ - σ * K / ((t + 2 : ℝ) * (t + 2 : ℝ) ^ σ) := by
                field_simp [show (t + 2 : ℝ) ^ σ ≠ 0 by positivity,
                  show (t + 2 : ℝ) ≠ 0 by positivity]
        _ = K / (t + 2 : ℝ) ^ σ - σ * K / (t + 2 : ℝ) ^ (1 + σ) := by rw [← hpow]
        _ = ε t - σ * K / (t + 2 : ℝ) ^ (1 + σ) := by rfl
    have hstep1 :
        ε t - σ * K / (t + 2 : ℝ) ^ (1 + σ) ≤ ε (t + 1) := by
      have hfactor'' :
          ε t * (1 - σ * u) = ε t - σ * K / (t + 2 : ℝ) ^ (1 + σ) := by
        simpa [mul_comm] using hfactor'
      rw [hfactor''] at hfactor
      exact hfactor
    have hstep2 :
        a t * ε t ≤ ε t - K / (t + 2 : ℝ) ^ (1 + σ) := by
      rw [hEq] at ha_le
      exact ha_le
    have hstep1' :
        ε t - σ * K / (t + 2 : ℝ) ^ (1 + σ) - a t * ε t ≤
          ε (t + 1) - a t * ε t := by
      exact sub_le_sub_right hstep1 (a t * ε t)
    have hstep2' :
        K / (t + 2 : ℝ) ^ (1 + σ) ≤ ε t - a t * ε t := by
      linarith [hstep2]
    have hcomb :
        (1 - σ) * K / (t + 2 : ℝ) ^ (1 + σ) ≤
          ε t - σ * K / (t + 2 : ℝ) ^ (1 + σ) - a t * ε t := by
      have hcomb0 :
          K / (t + 2 : ℝ) ^ (1 + σ) - σ * K / (t + 2 : ℝ) ^ (1 + σ) ≤
            ε t - a t * ε t - σ * K / (t + 2 : ℝ) ^ (1 + σ) := by
        exact sub_le_sub_right hstep2' (σ * K / (t + 2 : ℝ) ^ (1 + σ))
      have hleft0 :
          K / (t + 2 : ℝ) ^ (1 + σ) - σ * K / (t + 2 : ℝ) ^ (1 + σ) =
            (1 - σ) * K / (t + 2 : ℝ) ^ (1 + σ) := by ring
      have hright0 :
          ε t - a t * ε t - σ * K / (t + 2 : ℝ) ^ (1 + σ) =
            ε t - σ * K / (t + 2 : ℝ) ^ (1 + σ) - a t * ε t := by ring
      simpa [hleft0, hright0] using hcomb0
    exact le_trans hcomb hstep1'
  have hsmall_ratio :
      ∀ t : ℕ, ε t / 2 ≤ (2 : ℝ) ^ (σ - 1) * ε (t + 1) := by
    intro t
    have harg : (t + 3 : ℝ) ≤ 2 * (t + 2 : ℝ) := by
      exact_mod_cast (show t + 3 ≤ 2 * (t + 2) by omega)
    have hpow :
        (t + 3 : ℝ) ^ σ ≤ (2 * (t + 2 : ℝ)) ^ σ := by
      exact Real.rpow_le_rpow (by positivity : 0 ≤ (t + 3 : ℝ)) harg hσ_nonneg
    have hmulrpow :
        (2 * (t + 2 : ℝ)) ^ σ = (2 : ℝ) ^ σ * (t + 2 : ℝ) ^ σ := by
      rw [Real.mul_rpow (by positivity : 0 ≤ (2 : ℝ)) (by positivity : 0 ≤ (t + 2 : ℝ))]
    have hpow' :
        (t + 3 : ℝ) ^ σ ≤ (2 : ℝ) ^ σ * (t + 2 : ℝ) ^ σ := by
      simpa [hmulrpow] using hpow
    have htwo :
        2 * (2 : ℝ) ^ (σ - 1) = (2 : ℝ) ^ σ := by
      calc
        2 * (2 : ℝ) ^ (σ - 1) = (2 : ℝ) ^ (1 : ℝ) * (2 : ℝ) ^ (σ - 1) := by
              simp [Real.rpow_one]
        _ = (2 : ℝ) ^ (1 + (σ - 1)) := by
              symm
              exact Real.rpow_add (by positivity : 0 < (2 : ℝ)) 1 (σ - 1)
        _ = (2 : ℝ) ^ σ := by
              congr 1
              ring
    have hden1 : 0 < 2 * (t + 2 : ℝ) ^ σ := by positivity
    have hden2 : 0 < (t + 3 : ℝ) ^ σ := by positivity
    have hcross :
        K * (t + 3 : ℝ) ^ σ ≤ ((2 : ℝ) ^ (σ - 1) * K) *
          (2 * (t + 2 : ℝ) ^ σ) := by
      have hcross0 :
          (t + 3 : ℝ) ^ σ ≤ (2 : ℝ) ^ (σ - 1) * (2 * (t + 2 : ℝ) ^ σ) := by
        calc
          (t + 3 : ℝ) ^ σ ≤ (2 : ℝ) ^ σ * (t + 2 : ℝ) ^ σ := hpow'
          _ = (2 : ℝ) ^ (σ - 1) * (2 * (t + 2 : ℝ) ^ σ) := by
                rw [← htwo]
                ring
      calc
        K * (t + 3 : ℝ) ^ σ ≤ K * ((2 : ℝ) ^ (σ - 1) *
            (2 * (t + 2 : ℝ) ^ σ)) := by
              exact mul_le_mul_of_nonneg_left hcross0 hK_nonneg
        _ = ((2 : ℝ) ^ (σ - 1) * K) * (2 * (t + 2 : ℝ) ^ σ) := by ring
    have hscaled :
        K / (2 * (t + 2 : ℝ) ^ σ) ≤
          ((2 : ℝ) ^ (σ - 1) * K) / (t + 3 : ℝ) ^ σ := by
      exact (div_le_div_iff₀ hden1 hden2).2 hcross
    have hleft :
        ε t / 2 = K / (2 * (t + 2 : ℝ) ^ σ) := by
      dsimp [ε]
      field_simp [show (t + 2 : ℝ) ^ σ ≠ 0 by positivity]
    have hright :
        ((2 : ℝ) ^ (σ - 1) * K) / (t + 3 : ℝ) ^ σ =
          (2 : ℝ) ^ (σ - 1) * ε (t + 1) := by
      dsimp [ε]
      have hcast : (((t + 1 : ℕ) : ℝ) + 2) = (t + 3 : ℝ) := by
        exact_mod_cast (show t + 1 + 2 = t + 3 by omega)
      rw [hcast]
      ring
    rw [hleft]
    calc
      K / (2 * (t + 2 : ℝ) ^ σ) ≤
          ((2 : ℝ) ^ (σ - 1) * K) / (t + 3 : ℝ) ^ σ := hscaled
      _ = (2 : ℝ) ^ (σ - 1) * ε (t + 1) := hright
  have hMain :
      ∀ n : ℕ, H (T + n) ≤ ε (T + n) := by
    intro n
    induction n with
    | zero =>
        simpa using hbase
    | succ n ihn =>
        let t : ℕ := T + n
        have ht : T ≤ t := by
          dsimp [t]
          exact Nat.le_add_right _ _
        have hprev : H t ≤ ε t := by
          simpa [t, Nat.add_assoc] using ihn
        rcases hraw_small_or_refined t with hsmallRaw | hrefRaw
        · have hsmallPoint : H t ≤ ε t / 2 := by
            have hheb_t : (δ t) ^ r ≤ B * F t := by
              exact hTheb t (le_trans hT_ge_heb ht)
            have hheb_H : (δ t) ^ r ≤ B * H t / (t + 2 : ℝ) := by
              calc
                (δ t) ^ r ≤ B * F t := hheb_t
                _ = B * H t / (t + 2 : ℝ) := by
                      dsimp [H]
                      field_simp [show (t + 2 : ℝ) ≠ 0 by positivity]
            have hpoint :
                H t ≤ Ssmall / (t + 2 : ℝ) ^ σ := by
              simpa [Ssmall, σ] using
                (small_branch_scaled_gap_bound_of_localHEB
                  (H := H t) (δ := δ t) (C := Ksmall) (B := B) (r := r)
                  (T := (t + 2 : ℝ)) hr_ge (hH_nonneg t)
                  (by dsimp [δ]; positivity) hKsmall_pos hB
                  (by positivity) hsmallRaw hheb_H)
            have hhalf :
                Ssmall / (t + 2 : ℝ) ^ σ ≤ (K / 2) / (t + 2 : ℝ) ^ σ := by
              exact div_le_div_of_nonneg_right hSsmall_le_half_K (by positivity)
            calc
              H t ≤ Ssmall / (t + 2 : ℝ) ^ σ := hpoint
              _ ≤ (K / 2) / (t + 2 : ℝ) ^ σ := hhalf
              _ = ε t / 2 := by
                    dsimp [ε]
                    ring
          have hstep : H (t + 1) ≤ a t * H t + stdConst t := hstd_scaled t
          have ha_le_one : a t ≤ 1 := by
            simpa [a] using frankWolfe_openLoop_coeff_le_one t
          have hmain : H (t + 1) ≤ ε t / 2 + stdConst t := by
            have ha_nonneg : 0 ≤ a t := by dsimp [a]; positivity
            have hsmall' : a t * H t ≤ a t * (ε t / 2) :=
              mul_le_mul_of_nonneg_left hsmallPoint ha_nonneg
            have hsmall'' : a t * (ε t / 2) ≤ ε t / 2 :=
              by
                simpa using
                  mul_le_mul_of_nonneg_right ha_le_one (by positivity : 0 ≤ ε t / 2)
            calc
              H (t + 1) ≤ a t * H t + stdConst t := hstep
              _ ≤ a t * (ε t / 2) + stdConst t := by linarith [hsmall']
              _ ≤ ε t / 2 + stdConst t := by linarith [hsmall'']
          have htail := hstd_small t ht
          have hratio := hsmall_ratio t
          have hnext : H (t + 1) ≤ ε (t + 1) := by
            calc
              H (t + 1) ≤ ε t / 2 + stdConst t := hmain
              _ ≤ ε t / 2 + (1 - (2 : ℝ) ^ (σ - 1)) * ε (t + 1) := by
                    linarith [htail]
              _ ≤ (2 : ℝ) ^ (σ - 1) * ε (t + 1) +
                    (1 - (2 : ℝ) ^ (σ - 1)) * ε (t + 1) := by
                      linarith [hratio]
              _ = ε (t + 1) := by ring
          simpa [t, Nat.add_assoc] using hnext
        · have href : H (t + 1) ≤ a t * H t + c t * (4 * (L : ℝ) * (δ t) ^ 2) := by
            have hh_succ : H (t + 1) = (t + 3 : ℝ) * F (t + 1) := by
              change ((((t + 1 : ℕ) : ℝ) + 2) * F (t + 1) = (t + 3 : ℝ) * F (t + 1))
              have hcast : (((t + 1 : ℕ) : ℝ) + 2) = (t + 3 : ℝ) := by
                exact_mod_cast (show t + 1 + 2 = t + 3 by omega)
              rw [hcast]
            have hmul := mul_le_mul_of_nonneg_left hrefRaw (by positivity : 0 ≤ (t + 3 : ℝ))
            calc
              H (t + 1) = (t + 3 : ℝ) * F (t + 1) := hh_succ
              _ ≤ (t + 3 : ℝ) *
                    ((1 - 2 / (t + 2 : ℝ)) * F t +
                      (L : ℝ) * (2 / (t + 2 : ℝ)) ^ 2 * (δ t) ^ 2) := hmul
              _ = a t * H t + (L : ℝ) * ((t + 3 : ℝ) * (4 * (δ t) ^ 2)) /
                    (t + 2 : ℝ) ^ 2 := by
                    simpa [a, H, c, mul_assoc, mul_left_comm, mul_comm] using
                      (frankWolfe_openLoop_scaled_refined_eq
                        (F := F) (δ := δ) (L := (L : ℝ)) t)
              _ = a t * H t + c t * (4 * (L : ℝ) * (δ t) ^ 2) := by
                    dsimp [c]
                    ring
          have hheb_t : (δ t) ^ r ≤ B * F t := by
            exact hTheb t (le_trans hT_ge_heb ht)
          have hheb_eps :
              (δ t) ^ r ≤ B * ε t / (t + 2 : ℝ) := by
            have hFt : F t ≤ ε t / (t + 2 : ℝ) := by
              have hprev' : F t * (t + 2 : ℝ) ≤ ε t := by
                simpa [H, mul_comm, mul_left_comm, mul_assoc] using hprev
              exact (_root_.le_div_iff₀ (by positivity : 0 < (t + 2 : ℝ))).2 hprev'
            calc
              (δ t) ^ r ≤ B * F t := hheb_t
              _ ≤ B * (ε t / (t + 2 : ℝ)) := by
                    exact mul_le_mul_of_nonneg_left hFt hB.le
              _ = B * ε t / (t + 2 : ℝ) := by ring
          have hδr_nonneg : 0 ≤ (δ t) ^ r := by positivity
          have hδtwo_bound :
              (δ t) ^ 2 ≤ (B * ε t / (t + 2 : ℝ)) ^ (2 / r) := by
            have hpow :
                ((δ t) ^ r) ^ (2 / r) ≤ (B * ε t / (t + 2 : ℝ)) ^ (2 / r) := by
              exact Real.rpow_le_rpow hδr_nonneg hheb_eps (by positivity : 0 ≤ 2 / r)
            have hleft :
                ((δ t) ^ r) ^ (2 / r) = (δ t) ^ 2 := by
              calc
                ((δ t) ^ r) ^ (2 / r) = (δ t) ^ (r * (2 / r)) := by
                      rw [← Real.rpow_mul (by positivity : 0 ≤ δ t) r (2 / r)]
                _ = (δ t) ^ (2 : ℝ) := by
                      congr 1
                      field_simp [hr_ne]
                _ = (δ t) ^ 2 := by simp
            rw [hleft] at hpow
            exact hpow
          have htwo_over_r_le_one : 2 / r ≤ 1 := by
            exact (_root_.div_le_iff₀ hr_pos).2 (by simpa [one_mul] using hr_ge)
          have hKpow_two_le : K ^ (2 / r) ≤ K := by
            calc
              K ^ (2 / r) ≤ K ^ (1 : ℝ) := by
                    exact Real.rpow_le_rpow_of_exponent_le hK_ge_one htwo_over_r_le_one
              _ = K := by rw [Real.rpow_one]
          have hpow_eps :
              (B * ε t / (t + 2 : ℝ)) ^ (2 / r) =
                B ^ (2 / r) * K ^ (2 / r) / (t + 2 : ℝ) ^ (2 * σ) := by
            dsimp [ε, σ]
            have hfirst :
                B * (K / (t + 2 : ℝ) ^ (1 / (r - 1))) / (t + 2 : ℝ) =
                  B * K * (t + 2 : ℝ) ^ (-(r / (r - 1))) := by
              have hpow :
                  (t + 2 : ℝ) ^ (r / (r - 1)) =
                    (t + 2 : ℝ) * (t + 2 : ℝ) ^ (1 / (r - 1)) := by
                calc
                  (t + 2 : ℝ) ^ (r / (r - 1)) =
                      (t + 2 : ℝ) ^ (1 + 1 / (r - 1)) := by
                        congr 1
                        field_simp [hrm_ne]
                        ring
                  _ = (t + 2 : ℝ) ^ (1 : ℝ) * (t + 2 : ℝ) ^ (1 / (r - 1)) := by
                        rw [Real.rpow_add (by positivity : 0 < (t + 2 : ℝ)) 1 (1 / (r - 1))]
                  _ = (t + 2 : ℝ) * (t + 2 : ℝ) ^ (1 / (r - 1)) := by rw [Real.rpow_one]
              calc
                B * (K / (t + 2 : ℝ) ^ (1 / (r - 1))) / (t + 2 : ℝ)
                    = B * K / ((t + 2 : ℝ) ^ (1 / (r - 1)) * (t + 2 : ℝ)) := by
                          field_simp [show (t + 2 : ℝ) ^ (1 / (r - 1)) ≠ 0 by positivity]
                _ = B * K / (t + 2 : ℝ) ^ (r / (r - 1)) := by
                      have hpow' : (t + 2 : ℝ) ^ (1 / (r - 1)) * (t + 2 : ℝ) =
                          (t + 2 : ℝ) ^ (r / (r - 1)) := by
                        rw [mul_comm, ← hpow]
                      rw [hpow']
                _ = B * K * (t + 2 : ℝ) ^ (-(r / (r - 1))) := by
                      rw [div_eq_mul_inv, Real.rpow_neg (by positivity : 0 ≤ (t + 2 : ℝ))]
            rw [hfirst]
            have hBK_nonneg : 0 ≤ B * K := by positivity
            calc
              (B * K * (t + 2 : ℝ) ^ (-(r / (r - 1)))) ^ (2 / r)
                  = (B * K) ^ (2 / r) * ((t + 2 : ℝ) ^ (-(r / (r - 1)))) ^ (2 / r) := by
                        rw [Real.mul_rpow hBK_nonneg (by positivity)]
              _ = (B * K) ^ (2 / r) * (t + 2 : ℝ) ^ ((-(r / (r - 1))) * (2 / r)) := by
                    rw [← Real.rpow_mul (by positivity : 0 ≤ (t + 2 : ℝ)) (-(r / (r - 1))) (2 / r)]
              _ = (B ^ (2 / r) * K ^ (2 / r)) * (t + 2 : ℝ) ^ (-(2 * (1 / (r - 1)))) := by
                    rw [Real.mul_rpow hB.le hK_nonneg]
                    congr 2
                    field_simp [hr_ne, hrm_ne]
              _ = (B ^ (2 / r) * K ^ (2 / r)) *
                    ((t + 2 : ℝ) ^ (2 * (1 / (r - 1))))⁻¹ := by
                    rw [Real.rpow_neg (by positivity : 0 ≤ (t + 2 : ℝ))]
              _ = B ^ (2 / r) * K ^ (2 / r) /
                    (t + 2 : ℝ) ^ (2 * (1 / (r - 1))) := by
                    ring
          have hterm :
              c t * (4 * (L : ℝ) * (δ t) ^ 2) ≤
                (1 - σ) * K / (t + 2 : ℝ) ^ (1 + σ) := by
            have hc_bound : c t ≤ 2 / (t + 2 : ℝ) := by
              dsimp [c]
              have hden : 0 < (t + 2 : ℝ) ^ 2 := by positivity
              have hEq :
                  (2 / (t + 2 : ℝ)) * (t + 2 : ℝ) ^ 2 =
                    2 * (t + 2 : ℝ) := by
                field_simp [show (t + 2 : ℝ) ≠ 0 by positivity]
              have harg : (t + 3 : ℝ) ≤ 2 * (t + 2 : ℝ) := by
                exact_mod_cast (show t + 3 ≤ 2 * (t + 2) by omega)
              refine (_root_.div_le_iff₀ hden).2 ?_
              rw [hEq]
              exact harg
            have hδtwo_step :
                4 * (L : ℝ) * (δ t) ^ 2 ≤
                  4 * (L : ℝ) * (B * ε t / (t + 2 : ℝ)) ^ (2 / r) := by
              exact mul_le_mul_of_nonneg_left hδtwo_bound (by positivity : 0 ≤ 4 * (L : ℝ))
            have hterm_eq :
                (2 / (t + 2 : ℝ)) *
                    (4 * (L : ℝ) * (B * ε t / (t + 2 : ℝ)) ^ (2 / r)) =
                  8 * (L : ℝ) * B ^ (2 / r) * K ^ (2 / r) /
                    (t + 2 : ℝ) ^ (1 + 2 * σ) := by
              rw [hpow_eps]
              calc
                (2 / (t + 2 : ℝ)) *
                    (4 * (L : ℝ) * (B ^ (2 / r) * K ^ (2 / r) /
                      (t + 2 : ℝ) ^ (2 * σ)))
                    =
                  8 * (L : ℝ) * B ^ (2 / r) * K ^ (2 / r) /
                    ((t + 2 : ℝ) * (t + 2 : ℝ) ^ (2 * σ)) := by
                      field_simp [show (t + 2 : ℝ) ≠ 0 by positivity,
                        show (t + 2 : ℝ) ^ (2 * σ) ≠ 0 by positivity]
                      ring
                _ = 8 * (L : ℝ) * B ^ (2 / r) * K ^ (2 / r) /
                      (t + 2 : ℝ) ^ (1 + 2 * σ) := by
                      have hpow_split :
                          (t + 2 : ℝ) * (t + 2 : ℝ) ^ (2 * σ) =
                            (t + 2 : ℝ) ^ (1 + 2 * σ) := by
                        calc
                          (t + 2 : ℝ) * (t + 2 : ℝ) ^ (2 * σ) =
                              (t + 2 : ℝ) ^ (1 : ℝ) * (t + 2 : ℝ) ^ (2 * σ) := by
                                rw [Real.rpow_one]
                          _ = (t + 2 : ℝ) ^ (1 + 2 * σ) := by
                                symm
                                exact Real.rpow_add (by positivity : 0 < (t + 2 : ℝ)) 1 (2 * σ)
                      rw [hpow_split]
            have hKterm :
                8 * (L : ℝ) * B ^ (2 / r) * K ^ (2 / r) /
                    (t + 2 : ℝ) ^ (1 + 2 * σ) ≤
                  8 * (L : ℝ) * B ^ (2 / r) * K /
                    (t + 2 : ℝ) ^ (1 + 2 * σ) := by
              exact div_le_div_of_nonneg_right
                (mul_le_mul_of_nonneg_left hKpow_two_le
                  (by positivity : 0 ≤ 8 * (L : ℝ) * B ^ (2 / r))) (by positivity)
            have hpow_split :
                (t + 2 : ℝ) ^ (1 + 2 * σ) =
                  (t + 2 : ℝ) ^ σ * (t + 2 : ℝ) ^ (1 + σ) := by
              calc
                (t + 2 : ℝ) ^ (1 + 2 * σ) =
                    (t + 2 : ℝ) ^ (σ + (1 + σ)) := by ring_nf
                _ = (t + 2 : ℝ) ^ σ * (t + 2 : ℝ) ^ (1 + σ) := by
                      rw [Real.rpow_add (by positivity : 0 < (t + 2 : ℝ)) σ (1 + σ)]
            have hsplit :
                8 * (L : ℝ) * B ^ (2 / r) * K / (t + 2 : ℝ) ^ (1 + 2 * σ) =
                  (8 * (L : ℝ) * B ^ (2 / r) / (t + 2 : ℝ) ^ σ) *
                    (K / (t + 2 : ℝ) ^ (1 + σ)) := by
              rw [hpow_split]
              field_simp [show (t + 2 : ℝ) ^ σ ≠ 0 by positivity,
                show (t + 2 : ℝ) ^ (1 + σ) ≠ 0 by positivity]
            have hterm_t :
                8 * (L : ℝ) * B ^ (2 / r) / (t + 2 : ℝ) ^ σ ≤ 1 - σ := by
              exact le_of_lt (hTterm t (le_trans hT_ge_term ht))
            calc
              c t * (4 * (L : ℝ) * (δ t) ^ 2)
                  ≤ (2 / (t + 2 : ℝ)) * (4 * (L : ℝ) * (δ t) ^ 2) := by
                        exact mul_le_mul_of_nonneg_right hc_bound (by positivity)
              _ ≤ (2 / (t + 2 : ℝ)) *
                    (4 * (L : ℝ) * (B * ε t / (t + 2 : ℝ)) ^ (2 / r)) := by
                        exact mul_le_mul_of_nonneg_left hδtwo_step (by positivity)
              _ = 8 * (L : ℝ) * B ^ (2 / r) * K ^ (2 / r) /
                    (t + 2 : ℝ) ^ (1 + 2 * σ) := hterm_eq
              _ ≤ 8 * (L : ℝ) * B ^ (2 / r) * K /
                    (t + 2 : ℝ) ^ (1 + 2 * σ) := hKterm
              _ = (8 * (L : ℝ) * B ^ (2 / r) / (t + 2 : ℝ) ^ σ) *
                    (K / (t + 2 : ℝ) ^ (1 + σ)) := hsplit
              _ ≤ (1 - σ) * (K / (t + 2 : ℝ) ^ (1 + σ)) := by
                    exact mul_le_mul_of_nonneg_right hterm_t (by positivity)
              _ = (1 - σ) * K / (t + 2 : ℝ) ^ (1 + σ) := by ring
          have hnext : H (t + 1) ≤ ε (t + 1) := by
            have ha_nonneg : 0 ≤ a t := by dsimp [a]; positivity
            have hmain : a t * H t ≤ a t * ε t :=
              mul_le_mul_of_nonneg_left hprev ha_nonneg
            calc
              H (t + 1) ≤ a t * H t + c t * (4 * (L : ℝ) * (δ t) ^ 2) := href
              _ ≤ a t * ε t + c t * (4 * (L : ℝ) * (δ t) ^ 2) := by
                    linarith [hmain]
              _ ≤ a t * ε t + (1 - σ) * K / (t + 2 : ℝ) ^ (1 + σ) := by
                    linarith [hterm]
              _ ≤ a t * ε t + (ε (t + 1) - a t * ε t) := by
                    linarith [hgap_step t]
              _ = ε (t + 1) := by ring
          simpa [t, Nat.add_assoc] using hnext
  refine ⟨T, K, hK_pos, ?_⟩
  intro n
  have hbound := hMain n
  have hp_eq : 1 + σ = r / (r - 1 : ℝ) := by
    dsimp [σ]
    field_simp [hrm_ne]
    ring
  have hdiv :
      F (T + n) ≤ K / (T + n + 2 : ℝ) ^ (1 + σ) := by
    have htmp :
        F (T + n) ≤ ε (T + n) / (T + n + 2 : ℝ) := by
      have hbound' : F (T + n) * (T + n + 2 : ℝ) ≤ ε (T + n) := by
        simpa [H, mul_comm, mul_left_comm, mul_assoc] using hbound
      exact (_root_.le_div_iff₀ (by positivity : 0 < (T + n + 2 : ℝ))).2 hbound'
    have hpow :
        (T + n + 2 : ℝ) ^ (1 + σ) =
          (T + n + 2 : ℝ) * (T + n + 2 : ℝ) ^ σ := by
      calc
        (T + n + 2 : ℝ) ^ (1 + σ) =
            (T + n + 2 : ℝ) ^ (1 : ℝ) * (T + n + 2 : ℝ) ^ σ := by
                rw [Real.rpow_add (by positivity : 0 < (T + n + 2 : ℝ)) 1 σ]
        _ = (T + n + 2 : ℝ) * (T + n + 2 : ℝ) ^ σ := by
              rw [Real.rpow_one]
    simpa [ε, hpow, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using htmp
  have hmono :
      K / (T + n + 2 : ℝ) ^ (1 + σ) ≤ K / (n + 1 : ℝ) ^ (1 + σ) := by
    have hbase :
        (n + 1 : ℝ) ^ (1 + σ) ≤ (T + n + 2 : ℝ) ^ (1 + σ) := by
      have harg : (n + 1 : ℝ) ≤ T + n + 2 := by
        exact_mod_cast (show n + 1 ≤ T + n + 2 by omega)
      exact Real.rpow_le_rpow (by positivity : 0 ≤ (n + 1 : ℝ)) harg (by positivity)
    have hrecip :
        1 / (T + n + 2 : ℝ) ^ (1 + σ) ≤ 1 / (n + 1 : ℝ) ^ (1 + σ) := by
      exact one_div_le_one_div_of_le (by positivity : 0 < (n + 1 : ℝ) ^ (1 + σ)) hbase
    calc
      K / (T + n + 2 : ℝ) ^ (1 + σ) =
          K * (1 / (T + n + 2 : ℝ) ^ (1 + σ)) := by ring
      _ ≤ K * (1 / (n + 1 : ℝ) ^ (1 + σ)) := by
            exact mul_le_mul_of_nonneg_left hrecip hK_nonneg
      _ = K / (n + 1 : ℝ) ^ (1 + σ) := by ring
  have hresult :
      F (T + n) ≤ K / (n + 1 : ℝ) ^ (1 + σ) := hdiv.trans hmono
  simpa [F, xSeq, Nat.add_assoc, hp_eq] using hresult

set_option maxHeartbeats 2500000 in
/-- [FW-LOCAL-HEB-OL-Q2-SHARP-R2] Borderline quadratic local dual sharpness
plus a local quadratic error bound gives the sharp shifted `O(t^{-2})` tail for
the canonical open-loop rule. -/
theorem frankWolfe_localGap_two_heb_two_power_rate
    (hC_convex : Convex ℝ C)
    {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (f : E → ℝ) (f' : E → E) (L : NNReal) (hL : 0 < L)
    (hConv : IsFirstOrderConvex f f')
    (hSmooth : IsLipschitzSmoothUpperBound f L f')
    (x_star : E) (hx_star : x_star ∈ C)
    (hLocal :
      HasLocalLMOGapPowerOn
        O (C ∩ {y : E | f y = f x_star}) A 2)
    (hHEB :
      HasLocalHolderErrorBoundOn
        (C := C) (C ∩ {y : E | f y = f x_star}) f (f x_star) B 2)
    (hmin : ∀ y ∈ C, f x_star ≤ f y)
    (x0 : E) (hx0 : x0 ∈ C) :
    ∃ T : ℕ, ∃ K : ℝ, 0 < K ∧
      ∀ n : ℕ,
        f (frankWolfeSequence O f' x0 (T + n)) - f x_star ≤
          K / (n + 1 : ℝ) ^ (2 : ℝ) := by
  let xSeq : ℕ → E := frankWolfeSequence O f' x0
  let F : ℕ → ℝ := fun t => f (xSeq t) - f x_star
  let Mset : Set E := C ∩ {y : E | f y = f x_star}
  let Dsq : ℝ := (Metric.diam C) ^ 2
  let Bstd : ℝ := max (f x0 - f x_star) ((L : ℝ) * Dsq)
  let H : ℕ → ℝ := fun t => (t + 2 : ℝ) * F t
  let Ksmall : ℝ := 4 * (L : ℝ) / A
  let Cq : ℝ := 4 * (L : ℝ) * B
  let S : ℝ := Cq ^ 2 + Cq + 10
  have hKsmall_pos : 0 < Ksmall := by
    dsimp [Ksmall]
    positivity
  have hCq_nonneg : 0 ≤ Cq := by
    dsimp [Cq]
    positivity
  have hS_pos : 0 < S := by
    dsimp [S]
    nlinarith [sq_nonneg Cq]
  have hS_nonneg : 0 ≤ S := hS_pos.le
  have hS_ge_one : 1 ≤ S := by
    dsimp [S]
    nlinarith [sq_nonneg Cq, hCq_nonneg]
  have hxSeq : ∀ t, xSeq t ∈ C := by
    intro t
    simpa [xSeq] using
      frankWolfeSequence_mem
        (O := O)
        hC_convex f' hx0 t
  have hF_nonneg : ∀ t, 0 ≤ F t := by
    intro t
    exact primalGap_nonneg_of_isMinOn (C := C) (f := f) (hxSeq t) hmin
  have hH_nonneg : ∀ t, 0 ≤ H t := by
    intro t
    dsimp [H]
    exact mul_nonneg (by positivity) (hF_nonneg t)
  have hBstd_nonneg : 0 ≤ Bstd := by
    have hgap0_nonneg : 0 ≤ f x0 - f x_star := by
      exact primalGap_nonneg_of_isMinOn (C := C) (f := f) hx0 hmin
    exact le_trans hgap0_nonneg (le_max_left _ _)
  have hstd :
      ∀ t, F t ≤ (2 * Bstd) / (t + 2 : ℝ) := by
    intro t
    have hfw :=
      frank_wolfe_convergence_of_initialGap_le
        (O := O)
        hC_convex f f' L hSmooth hConv hx_star hx0
        (B := Bstd) hBstd_nonneg (le_max_left _ _) (le_max_right _ _) t
    simpa [F, xSeq, Bstd, Dsq] using hfw
  have hH_bounded : ∀ t, H t ≤ 2 * Bstd := by
    intro t
    calc
      H t = (t + 2 : ℝ) * F t := by rfl
      _ ≤ (t + 2 : ℝ) * ((2 * Bstd) / (t + 2 : ℝ)) := by
            gcongr
            exact hstd t
      _ = 2 * Bstd := by
            field_simp [show (t + 2 : ℝ) ≠ 0 by positivity]
  have hgap_zero : Tendsto F atTop (nhds 0) := by
    simpa [F, xSeq] using
      frankWolfe_gap_tendsto_zero_of_isMinOn
        (O := O)
        hC_convex f f' L hConv hSmooth hx_star hmin hx0
  have hcont : Continuous f :=
    continuous_of_isFirstOrderConvex_isLipschitzSmoothUpperBound
      (f := f) (f' := f') (L := L) hConv hSmooth
  have hlevel_closed : IsClosed {y : E | f y = f x_star} :=
    isClosed_eq hcont continuous_const
  have hMset_compact : IsCompact Mset := by
    simpa [Mset] using O.isCompact.inter_right hlevel_closed
  have hMset_nonempty : Mset.Nonempty := by
    refine ⟨x_star, ?_⟩
    simp [Mset, hx_star]
  have hdist_zero :
      Tendsto (fun t => Metric.infDist (xSeq t) Mset) atTop (nhds 0) := by
    simpa [xSeq, Mset] using
      tendsto_infDist_minimizerSet_of_gap_tendsto_zero
        O.isCompact (f := f) (f' := f') (L := L) hConv hSmooth x_star xSeq hxSeq hgap_zero
  classical
  let pSeq : ℕ → E := fun t =>
    Classical.choose (hMset_compact.exists_infDist_eq_dist hMset_nonempty (xSeq t))
  have hpSeq_memM : ∀ t, pSeq t ∈ Mset := by
    intro t
    exact (Classical.choose_spec
      (hMset_compact.exists_infDist_eq_dist hMset_nonempty (xSeq t))).1
  have hpSeq_val : ∀ t, f (pSeq t) = f x_star := by
    intro t
    exact (hpSeq_memM t).2
  have hpSeq_dist : ∀ t, Metric.infDist (xSeq t) Mset = dist (xSeq t) (pSeq t) := by
    intro t
    exact (Classical.choose_spec
      (hMset_compact.exists_infDist_eq_dist hMset_nonempty (xSeq t))).2
  let δ : ℕ → ℝ := fun t => ‖xSeq t - pSeq t‖
  have hδ_zero : Tendsto δ atTop (nhds 0) := by
    have hdist_zero' :
        Tendsto (fun t => dist (xSeq t) (pSeq t)) atTop (nhds 0) := by
      simpa [hpSeq_dist] using hdist_zero
    simpa [δ, dist_eq_norm] using hdist_zero'
  obtain ⟨ρheb, hρheb_pos, hheb_local⟩ := hHEB
  have hheb_event : ∀ᶠ t : ℕ in atTop, (δ t) ^ (2 : ℝ) ≤ B * F t := by
    have hδ_event : ∀ᶠ t : ℕ in atTop, δ t < ρheb := by
      exact hδ_zero.eventually (Iio_mem_nhds hρheb_pos)
    filter_upwards [hδ_event] with t hδt
    have hdist_t : Metric.infDist (xSeq t) Mset < ρheb := by
      rw [hpSeq_dist t]
      simpa [δ, dist_eq_norm] using hδt
    have hheb_t :
        Metric.infDist (xSeq t) Mset ^ (2 : ℝ) ≤ B * (f (xSeq t) - f x_star) := by
      simpa using hheb_local (xSeq t) (hxSeq t) hdist_t
    rw [hpSeq_dist t, dist_eq_norm] at hheb_t
    simpa [δ, F] using hheb_t
  rcases Filter.Eventually.exists_forall_of_atTop hheb_event with ⟨Theb, hTheb⟩
  let Tcoeff : ℕ := Nat.ceil (4 * Cq + 4)
  let T : ℕ := max Theb Tcoeff
  have hT_ge_heb : Theb ≤ T := by
    dsimp [T]
    exact le_max_left _ _
  have hT_ge_coeff : Tcoeff ≤ T := by
    dsimp [T]
    exact le_max_right _ _
  have hstd_step :
      ∀ t,
        F (t + 1) ≤
          (1 - 2 / (t + 2 : ℝ)) * F t +
            ((L : ℝ) / 2) * (2 / (t + 2 : ℝ)) ^ 2 * Dsq := by
    intro t
    have href :
        f (frankWolfeStep O f' (xSeq t) (2 / (t + 2 : ℝ))) -
            f (pSeq t) ≤
          (1 - 2 / (t + 2 : ℝ)) * (f (xSeq t) - f (pSeq t)) +
            ((L : ℝ) / 2) * (2 / (t + 2 : ℝ)) ^ 2 * Dsq := by
      simpa [xSeq, Dsq] using
        (frankWolfeStep_gap_bound
          (O := O)
          (C := C) (f := f) (f' := f') (L := L) hSmooth hConv
          (x := xSeq t) (x_star := pSeq t)
          (hxSeq t) ((hpSeq_memM t).1)
          (γ := 2 / (t + 2 : ℝ)) (standardStepSize_mem_Icc t))
    simpa [F, xSeq, frankWolfeSequence, hpSeq_val t, frankWolfeOpenLoopSequence, openLoopStepSize] using href
  let a : ℕ → ℝ := fun t => (t : ℝ) * (t + 3 : ℝ) / (t + 2 : ℝ) ^ 2
  let c : ℕ → ℝ := fun t => (t + 3 : ℝ) / (t + 2 : ℝ) ^ 2
  let stdConst : ℕ → ℝ :=
    fun t => 2 * (L : ℝ) * Dsq * (t + 3 : ℝ) / (t + 2 : ℝ) ^ 2
  have hstd_scaled :
      ∀ t, H (t + 1) ≤ a t * H t + stdConst t := by
    intro t
    have hh_succ : H (t + 1) = (t + 3 : ℝ) * F (t + 1) := by
      change ((((t + 1 : ℕ) : ℝ) + 2) * F (t + 1) = (t + 3 : ℝ) * F (t + 1))
      have hcast : (((t + 1 : ℕ) : ℝ) + 2) = (t + 3 : ℝ) := by
        exact_mod_cast (show t + 1 + 2 = t + 3 by omega)
      rw [hcast]
    have hmul := mul_le_mul_of_nonneg_left (hstd_step t) (by positivity : 0 ≤ (t + 3 : ℝ))
    calc
      H (t + 1) = (t + 3 : ℝ) * F (t + 1) := hh_succ
      _ ≤ (t + 3 : ℝ) *
            ((1 - 2 / (t + 2 : ℝ)) * F t +
              ((L : ℝ) / 2) * (2 / (t + 2 : ℝ)) ^ 2 * Dsq) := hmul
      _ = a t * H t + stdConst t := by
            simpa [a, H, stdConst, mul_assoc, mul_left_comm, mul_comm] using
              (frankWolfe_openLoop_scaled_standard_eq
                (F := F) (Dsq := Dsq) (L := (L : ℝ)) t)
  have hraw_small_or_refined :
      ∀ t,
        H t ≤ Ksmall * δ t ∨
          F (t + 1) ≤
            (1 - 2 / (t + 2 : ℝ)) * F t +
              (L : ℝ) * (2 / (t + 2 : ℝ)) ^ 2 * (δ t) ^ 2 := by
    intro t
    by_cases hFt0 : F t = 0
    · left
      have hKsmall_nonneg : 0 ≤ Ksmall := le_of_lt hKsmall_pos
      have hδ_nonneg : 0 ≤ δ t := by dsimp [δ]; positivity
      simpa [H, hFt0] using (mul_nonneg hKsmall_nonneg hδ_nonneg)
    · by_cases hcase : 2 / (t + 2 : ℝ) ≤ A * ‖f' (xSeq t)‖ / (2 * (L : ℝ))
      · right
        have href :
            f (frankWolfeStep O f' (xSeq t) (2 / (t + 2 : ℝ))) -
                f (pSeq t) ≤
              (1 - 2 / (t + 2 : ℝ)) * (f (xSeq t) - f (pSeq t)) +
                (L : ℝ) * (2 / (t + 2 : ℝ)) ^ 2 * ‖xSeq t - pSeq t‖ ^ 2 := by
          simpa [xSeq, δ] using
            (frankWolfeStep_gap_bound_with_localCorrection_two
              (O := O)
              hLocal f f' L hConv hSmooth
              (x := xSeq t) (x_star := pSeq t) ((hpSeq_memM t).1) (hpSeq_memM t)
              (γ := 2 / (t + 2 : ℝ)) (standardStepSize_mem_Icc t) hcase)
        simpa [F, xSeq, frankWolfeSequence, hpSeq_val t, frankWolfeOpenLoopSequence, openLoopStepSize] using href
      · left
        have hδ_pos_t : 0 < δ t := by
          by_contra hδt
          have hδ0 : δ t = 0 := le_antisymm (not_lt.mp hδt) (norm_nonneg _)
          have hxeq : xSeq t = pSeq t := by
            exact sub_eq_zero.mp (norm_eq_zero.mp (by simpa [δ] using hδ0))
          have : F t = 0 := by simp [F, hxeq, hpSeq_val t]
          exact hFt0 this
        have hgap_grad : F t ≤ ‖f' (xSeq t)‖ * δ t := by
          have hgap_t :
              f (xSeq t) - f (pSeq t) ≤ ‖f' (xSeq t)‖ * ‖xSeq t - pSeq t‖ := by
            simpa [xSeq] using
              (primalGap_le_gradNorm_mul_dist
                (f := f) (f' := f') hConv
                (x := xSeq t) (x_star := pSeq t))
          simpa [F, δ, hpSeq_val t] using hgap_t
        have hcase' :
            A * ‖f' (xSeq t)‖ / (2 * (L : ℝ)) < 2 / (t + 2 : ℝ) := lt_of_not_ge hcase
        have hmul :
            A * ‖f' (xSeq t)‖ < (2 / (t + 2 : ℝ)) * (2 * (L : ℝ)) := by
          exact (_root_.div_lt_iff₀ (show 0 < 2 * (L : ℝ) by positivity)).1 hcase'
        have hgrad_lt :
            ‖f' (xSeq t)‖ < ((2 / (t + 2 : ℝ)) * (2 * (L : ℝ))) / A := by
          have : ‖f' (xSeq t)‖ * A < (2 / (t + 2 : ℝ)) * (2 * (L : ℝ)) := by
            simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
          exact (_root_.lt_div_iff₀ hA).2 this
        have hsmall' :
            F t < (((2 / (t + 2 : ℝ)) * (2 * (L : ℝ))) / A) * δ t := by
          exact lt_of_le_of_lt hgap_grad <|
            mul_lt_mul_of_pos_right hgrad_lt hδ_pos_t
        have hscaled : H t < Ksmall * δ t := by
          dsimp [H, Ksmall]
          have hEq :
              (t + 2 : ℝ) * ((((2 / (t + 2 : ℝ)) * (2 * (L : ℝ))) / A) * δ t) =
                (4 * (L : ℝ) / A) * δ t := by
            field_simp [hA.ne', (show (t + 2 : ℝ) ≠ 0 by positivity)]
            ring
          have hmul' :
              (t + 2 : ℝ) * F t <
                (t + 2 : ℝ) *
                  ((((2 / (t + 2 : ℝ)) * (2 * (L : ℝ))) / A) * δ t) := by
            exact mul_lt_mul_of_pos_left hsmall' (by positivity)
          simpa [hEq] using hmul'
        exact le_of_lt hscaled
  let Ksmall2 : ℝ := Ksmall ^ 2 * B
  let KsmallBarrier : ℝ := 4 * Ksmall2 * S
  let Kstd : ℝ := 8 * (L : ℝ) * Dsq * (S + 1)
  let K0 : ℝ := max 1 (max KsmallBarrier Kstd)
  let K : ℝ := max K0 ((2 * Bstd) * (T + S))
  let ε : ℕ → ℝ := fun t => K / (t + S)
  have hKsmall2_nonneg : 0 ≤ Ksmall2 := by dsimp [Ksmall2]; positivity
  have hK0_ge_one : 1 ≤ K0 := by dsimp [K0]; exact le_max_left _ _
  have hK0_pos : 0 < K0 := lt_of_lt_of_le zero_lt_one hK0_ge_one
  have hK_ge_K0 : K0 ≤ K := by dsimp [K]; exact le_max_left _ _
  have hK_pos : 0 < K := lt_of_lt_of_le hK0_pos hK_ge_K0
  have hK_nonneg : 0 ≤ K := hK_pos.le
  have hK_ge_small : KsmallBarrier ≤ K := by
    exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hK_ge_K0
  have hK_ge_std : Kstd ≤ K := by
    exact le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hK_ge_K0
  have hε_pos : ∀ t, 0 < ε t := by
    intro t
    dsimp [ε]
    positivity
  have hbase : H T ≤ ε T := by
    have hbound : H T ≤ 2 * Bstd := hH_bounded T
    have hK_base : (2 * Bstd) * (T + S) ≤ K := by
      dsimp [K]
      exact le_max_right _ _
    have hdiv : 2 * Bstd ≤ K / (T + S) := by
      exact (_root_.le_div_iff₀ (by positivity : 0 < (T : ℝ) + S)).2 hK_base
    simpa [ε] using hbound.trans hdiv
  have hstd_small :
      ∀ t, stdConst t ≤ ε (t + 1) / 2 := by
    intro t
    have hstd_bound : stdConst t ≤ 4 * (L : ℝ) * Dsq / (t + 2 : ℝ) := by
      have hB_nonneg : 0 ≤ (L : ℝ) * Dsq := by positivity
      simpa [stdConst, mul_assoc, mul_left_comm, mul_comm] using
        (frankWolfe_openLoop_stdConst_bound (B := (L : ℝ) * Dsq) hB_nonneg t)
    have hratio :
        (t + 1 + S : ℝ) / (t + 2 : ℝ) ≤ S + 1 := by
      have hden : 0 < (t + 2 : ℝ) := by positivity
      refine (_root_.div_le_iff₀ hden).2 ?_
      nlinarith [hS_ge_one, show (0 : ℝ) ≤ t from Nat.cast_nonneg t]
    have hcoef :
        8 * (L : ℝ) * Dsq * ((t + 1 + S : ℝ) / (t + 2 : ℝ)) ≤ K := by
      have hmul :
          8 * (L : ℝ) * Dsq * ((t + 1 + S : ℝ) / (t + 2 : ℝ)) ≤
            8 * (L : ℝ) * Dsq * (S + 1) := by
        exact mul_le_mul_of_nonneg_left hratio (by positivity)
      exact le_trans hmul hK_ge_std
    have htarget :
        4 * (L : ℝ) * Dsq / (t + 2 : ℝ) ≤ K / (2 * (t + 1 + S : ℝ)) := by
      have hden1 : 0 < (t + 2 : ℝ) := by positivity
      have hden2 : 0 < 2 * (t + 1 + S : ℝ) := by positivity
      refine (_root_.div_le_div_iff₀ hden1 hden2).2 ?_
      have htmp :
          (4 * (L : ℝ) * Dsq) * (2 * (t + 1 + S : ℝ)) ≤ K * (t + 2 : ℝ) := by
        have htmp0 :
            8 * (L : ℝ) * Dsq * (t + 1 + S : ℝ) ≤ K * (t + 2 : ℝ) := by
          have hcoef' :
              (8 * (L : ℝ) * Dsq * (t + 1 + S : ℝ)) / (t + 2 : ℝ) ≤ K := by
            simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hcoef
          exact (_root_.div_le_iff₀ (by positivity : 0 < (t + 2 : ℝ))).1 hcoef'
        nlinarith
      simpa [mul_assoc, mul_left_comm, mul_comm] using htmp
    calc
      stdConst t ≤ 4 * (L : ℝ) * Dsq / (t + 2 : ℝ) := hstd_bound
      _ ≤ K / (2 * (t + 1 + S : ℝ)) := htarget
      _ = ε (t + 1) / 2 := by
            dsimp [ε]
            have hcast : (((t + 1 : ℕ) : ℝ) + S) = (t + 1 + S : ℝ) := by
              push_cast
              ring
            rw [hcast]
            field_simp [show (t + 1 + S : ℝ) ≠ 0 by positivity]
  have hsmall_ratio :
      ∀ t, ε t / 4 ≤ ε (t + 1) / 2 := by
    intro t
    have hden1 : 0 < 4 * (t + S : ℝ) := by positivity
    have hden2 : 0 < 2 * (t + 1 + S : ℝ) := by positivity
    dsimp [ε]
    have hcmp : 2 * (t + 1 + S : ℝ) ≤ 4 * (t + S : ℝ) := by
      nlinarith [hS_nonneg, show (0 : ℝ) ≤ t from Nat.cast_nonneg t]
    have hcmp' : 2 * (((t + 1 : ℕ) : ℝ) + S) ≤ 4 * (t + S : ℝ) := by
      push_cast
      exact hcmp
    field_simp [show (t + S : ℝ) ≠ 0 by positivity,
      show (t + 1 + S : ℝ) ≠ 0 by positivity, hK_pos.ne']
    nlinarith [hcmp', hK_pos.le]
  have hMain : ∀ n : ℕ, H (T + n) ≤ ε (T + n) := by
    intro n
    induction n with
    | zero =>
        simpa using hbase
    | succ n ihn =>
        let t : ℕ := T + n
        have ht : T ≤ t := by dsimp [t]; exact Nat.le_add_right _ _
        have ht_heb : Theb ≤ t := le_trans hT_ge_heb ht
        have ht_coeff_nat : Tcoeff ≤ t := le_trans hT_ge_coeff ht
        have ht_coeff : 4 * Cq + 4 ≤ (t : ℝ) := by
          exact le_trans (Nat.le_ceil _) (by exact_mod_cast ht_coeff_nat)
        have hprev : H t ≤ ε t := by
          simpa [t, Nat.add_assoc] using ihn
        rcases hraw_small_or_refined t with hsmallRaw | hrefRaw
        · have hsmallPoint : H t ≤ ε t / 4 := by
            have hheb_t : (δ t) ^ (2 : ℝ) ≤ B * F t := hTheb t ht_heb
            have hheb_H : (δ t) ^ (2 : ℝ) ≤ B * H t / (t + 2 : ℝ) := by
              calc
                (δ t) ^ (2 : ℝ) ≤ B * F t := hheb_t
                _ = B * H t / (t + 2 : ℝ) := by
                      dsimp [H]
                      field_simp [show (t + 2 : ℝ) ≠ 0 by positivity]
            have hpoint : H t ≤ Ksmall2 / (t + 2 : ℝ) := by
              have hraw :=
                small_branch_scaled_gap_bound_of_localHEB
                  (H := H t) (δ := δ t) (C := Ksmall) (B := B) (r := (2 : ℝ))
                  (T := (t + 2 : ℝ)) (by norm_num : (2 : ℝ) ≤ 2) (hH_nonneg t)
                  (by dsimp [δ]; positivity) hKsmall_pos hB (by positivity)
                  hsmallRaw hheb_H
              norm_num at hraw
              simpa [Ksmall2] using hraw
            have hratio :
                (t + S : ℝ) / (t + 2 : ℝ) ≤ S := by
              have hden : 0 < (t + 2 : ℝ) := by positivity
              refine (_root_.div_le_iff₀ hden).2 ?_
              nlinarith [hS_ge_one, show (0 : ℝ) ≤ t from Nat.cast_nonneg t]
            have hcoef : 4 * Ksmall2 * ((t + S : ℝ) / (t + 2 : ℝ)) ≤ K := by
              have hmul :
                  4 * Ksmall2 * ((t + S : ℝ) / (t + 2 : ℝ)) ≤ 4 * Ksmall2 * S := by
                exact mul_le_mul_of_nonneg_left hratio (by positivity)
              exact le_trans hmul hK_ge_small
            have htarget : Ksmall2 / (t + 2 : ℝ) ≤ (K / 4) / (t + S : ℝ) := by
              have hden1 : 0 < (t + 2 : ℝ) := by positivity
              have hden2 : 0 < (t + S : ℝ) := by positivity
              refine (_root_.div_le_div_iff₀ hden1 hden2).2 ?_
              have htmp0 : 4 * Ksmall2 * (t + S : ℝ) ≤ K * (t + 2 : ℝ) := by
                have hcoef' : (4 * Ksmall2 * (t + S : ℝ)) / (t + 2 : ℝ) ≤ K := by
                  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hcoef
                exact (_root_.div_le_iff₀ hden1).1 hcoef'
              nlinarith
            calc
              H t ≤ Ksmall2 / (t + 2 : ℝ) := hpoint
              _ ≤ (K / 4) / (t + S : ℝ) := htarget
              _ = ε t / 4 := by
                    dsimp [ε]
                    ring
          have hstep := hstd_scaled t
          have ha_le_one : a t ≤ 1 := by simpa [a] using frankWolfe_openLoop_coeff_le_one t
          have hnext : H (t + 1) ≤ ε (t + 1) := by
            have ha_nonneg : 0 ≤ a t := by dsimp [a]; positivity
            have hsmall' : a t * H t ≤ a t * (ε t / 4) :=
              mul_le_mul_of_nonneg_left hsmallPoint ha_nonneg
            have hsmall'' : a t * (ε t / 4) ≤ ε t / 4 := by
              simpa using mul_le_mul_of_nonneg_right ha_le_one (by positivity : 0 ≤ ε t / 4)
            have hstd' := hstd_small t
            have hratio := hsmall_ratio t
            calc
              H (t + 1) ≤ a t * H t + stdConst t := hstep
              _ ≤ ε t / 4 + stdConst t := by linarith [hsmall', hsmall'']
              _ ≤ ε t / 4 + ε (t + 1) / 2 := by linarith [hstd']
              _ ≤ ε (t + 1) / 2 + ε (t + 1) / 2 := by linarith [hratio]
              _ = ε (t + 1) := by ring
          simpa [t, Nat.add_assoc] using hnext
        · have href : H (t + 1) ≤ a t * H t + c t * (4 * (L : ℝ) * (δ t) ^ 2) := by
            have hh_succ : H (t + 1) = (t + 3 : ℝ) * F (t + 1) := by
              change ((((t + 1 : ℕ) : ℝ) + 2) * F (t + 1) = (t + 3 : ℝ) * F (t + 1))
              have hcast : (((t + 1 : ℕ) : ℝ) + 2) = (t + 3 : ℝ) := by
                exact_mod_cast (show t + 1 + 2 = t + 3 by omega)
              rw [hcast]
            have hmul := mul_le_mul_of_nonneg_left hrefRaw (by positivity : 0 ≤ (t + 3 : ℝ))
            calc
              H (t + 1) = (t + 3 : ℝ) * F (t + 1) := hh_succ
              _ ≤ (t + 3 : ℝ) *
                    ((1 - 2 / (t + 2 : ℝ)) * F t +
                      (L : ℝ) * (2 / (t + 2 : ℝ)) ^ 2 * (δ t) ^ 2) := hmul
              _ = a t * H t + (L : ℝ) * ((t + 3 : ℝ) * (4 * (δ t) ^ 2)) /
                    (t + 2 : ℝ) ^ 2 := by
                    simpa [a, H, c, mul_assoc, mul_left_comm, mul_comm] using
                      (frankWolfe_openLoop_scaled_refined_eq
                        (F := F) (δ := δ) (L := (L : ℝ)) t)
              _ = a t * H t + c t * (4 * (L : ℝ) * (δ t) ^ 2) := by
                    dsimp [c]
                    ring
          have hheb_t : (δ t) ^ (2 : ℝ) ≤ B * F t := hTheb t ht_heb
          have hδ2 : (δ t) ^ 2 ≤ B * H t / (t + 2 : ℝ) := by
            have htmp : (δ t) ^ 2 = (δ t) ^ (2 : ℝ) := by norm_num
            rw [htmp]
            calc
              (δ t) ^ (2 : ℝ) ≤ B * F t := hheb_t
              _ = B * H t / (t + 2 : ℝ) := by
                    dsimp [H]
                    field_simp [show (t + 2 : ℝ) ≠ 0 by positivity]
          have hδ2eps : (δ t) ^ 2 ≤ B * ε t / (t + 2 : ℝ) := by
            calc
              (δ t) ^ 2 ≤ B * H t / (t + 2 : ℝ) := hδ2
              _ ≤ B * ε t / (t + 2 : ℝ) := by
                    exact div_le_div_of_nonneg_right
                      (mul_le_mul_of_nonneg_left hprev hB.le) (by positivity)
          have hstep_eps :
              H (t + 1) ≤
                K * (((t : ℝ) * (t + 3) / (t + 2) ^ 2 +
                    Cq * (t + 3) / (t + 2) ^ 3) / (t + S)) := by
            have ha_nonneg : 0 ≤ a t := by dsimp [a]; positivity
            have hmain : a t * H t ≤ a t * ε t :=
              mul_le_mul_of_nonneg_left hprev ha_nonneg
            have hdelta_term :
                c t * (4 * (L : ℝ) * (δ t) ^ 2) ≤
                  c t * (4 * (L : ℝ) * (B * ε t / (t + 2 : ℝ))) := by
              exact mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hδ2eps (by positivity : 0 ≤ 4 * (L : ℝ)))
                (by dsimp [c]; positivity)
            calc
              H (t + 1) ≤ a t * H t + c t * (4 * (L : ℝ) * (δ t) ^ 2) := href
              _ ≤ a t * ε t + c t * (4 * (L : ℝ) * (B * ε t / (t + 2 : ℝ))) := by
                    linarith [hmain, hdelta_term]
              _ = K * (((t : ℝ) * (t + 3) / (t + 2) ^ 2 +
                    Cq * (t + 3) / (t + 2) ^ 3) / (t + S)) := by
                    dsimp [a, c, ε, Cq]
                    field_simp [show (t + 2 : ℝ) ≠ 0 by positivity,
                      show (t + S : ℝ) ≠ 0 by positivity]
          have hcoeff :=
            openLoop_qeb_shifted_coeff_bound (Cq := Cq) hCq_nonneg t ht_coeff
          have hnext : H (t + 1) ≤ ε (t + 1) := by
            have hscaled := mul_le_mul_of_nonneg_left hcoeff hK_nonneg
            calc
              H (t + 1) ≤ K * (((t : ℝ) * (t + 3) / (t + 2) ^ 2 +
                    Cq * (t + 3) / (t + 2) ^ 3) / (t + S)) := hstep_eps
              _ ≤ K * (1 / (t + S + 1)) := hscaled
              _ = ε (t + 1) := by
                    dsimp [ε]
                    have hcast : (((t + 1 : ℕ) : ℝ) + S) = (t + S + 1 : ℝ) := by
                      push_cast
                      ring
                    rw [hcast]
                    ring
          simpa [t, Nat.add_assoc] using hnext
  refine ⟨T, K, hK_pos, ?_⟩
  intro n
  have hbound := hMain n
  have hdiv : F (T + n) ≤ K / ((T + n + 2 : ℝ) * (T + n + S : ℝ)) := by
    have htmp : F (T + n) ≤ ε (T + n) / (T + n + 2 : ℝ) := by
      have hbound' : F (T + n) * (T + n + 2 : ℝ) ≤ ε (T + n) := by
        simpa [H, mul_comm, mul_left_comm, mul_assoc] using hbound
      exact (_root_.le_div_iff₀ (by positivity : 0 < (T + n + 2 : ℝ))).2 hbound'
    simpa [ε, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using htmp
  have hden :
      (n + 1 : ℝ) ^ (2 : ℝ) ≤ (T + n + 2 : ℝ) * (T + n + S : ℝ) := by
    have hleft : (n + 1 : ℝ) ≤ T + n + 2 := by
      exact_mod_cast (show n + 1 ≤ T + n + 2 by omega)
    have hright : (n + 1 : ℝ) ≤ T + n + S := by
      have hS1 : (1 : ℝ) ≤ S := hS_ge_one
      nlinarith [hS1, show (0 : ℝ) ≤ T from Nat.cast_nonneg T,
        show (0 : ℝ) ≤ n from Nat.cast_nonneg n]
    have hprod := mul_le_mul hleft hright (by positivity : 0 ≤ (n + 1 : ℝ))
      (by positivity : 0 ≤ (T + n + 2 : ℝ))
    rw [Real.rpow_two]
    simpa [pow_two] using hprod
  have hmono :
      K / ((T + n + 2 : ℝ) * (T + n + S : ℝ)) ≤ K / (n + 1 : ℝ) ^ (2 : ℝ) := by
    have hrecip :
        1 / ((T + n + 2 : ℝ) * (T + n + S : ℝ)) ≤
          1 / (n + 1 : ℝ) ^ (2 : ℝ) := by
      exact one_div_le_one_div_of_le (by positivity : 0 < (n + 1 : ℝ) ^ (2 : ℝ)) hden
    calc
      K / ((T + n + 2 : ℝ) * (T + n + S : ℝ)) =
          K * (1 / ((T + n + 2 : ℝ) * (T + n + S : ℝ))) := by ring
      _ ≤ K * (1 / (n + 1 : ℝ) ^ (2 : ℝ)) := by
            exact mul_le_mul_of_nonneg_left hrecip hK_nonneg
      _ = K / (n + 1 : ℝ) ^ (2 : ℝ) := by ring
  exact hdiv.trans hmono

set_option maxHeartbeats 1000000 in
/-- [FW-LOCAL-HEB-OL-Q2-SHARP] In the quadratic local dual-sharpness case,
the canonical open-loop rule has the sharp shifted `r / (r - 1)` tail under a
local Hölder error bound of any order `r ≥ 2`. -/
theorem frankWolfe_localGap_two_heb_power_rate
    (hC_convex : Convex ℝ C)
    {A B r : ℝ} (hr : 2 ≤ r) (hA : 0 < A) (hB : 0 < B)
    (f : E → ℝ) (f' : E → E) (L : NNReal) (hL : 0 < L)
    (hConv : IsFirstOrderConvex f f')
    (hSmooth : IsLipschitzSmoothUpperBound f L f')
    (x_star : E) (hx_star : x_star ∈ C)
    (hLocal :
      HasLocalLMOGapPowerOn
        O (C ∩ {y : E | f y = f x_star}) A 2)
    (hHEB :
      HasLocalHolderErrorBoundOn
        (C := C) (C ∩ {y : E | f y = f x_star}) f (f x_star) B r)
    (hmin : ∀ y ∈ C, f x_star ≤ f y)
    (x0 : E) (hx0 : x0 ∈ C) :
    ∃ T : ℕ, ∃ K : ℝ, 0 < K ∧
      ∀ n : ℕ,
        f (frankWolfeSequence O f' x0 (T + n)) - f x_star ≤
          K / (n + 1 : ℝ) ^ (r / (r - 1 : ℝ)) := by
  rcases lt_or_eq_of_le hr with hr_gt | hreq
  · exact
      frankWolfe_localGap_two_heb_power_rate_of_two_lt
        (O := O)
        hC_convex hr_gt hA hB f f' L hL hConv hSmooth
        x_star hx_star hLocal hHEB hmin x0 hx0
  · subst r
    have hHEB2 :
        HasLocalHolderErrorBoundOn
          (C := C) (C ∩ {y : E | f y = f x_star}) f (f x_star) B 2 := by
      simpa using hHEB
    have hcore :=
      frankWolfe_localGap_two_heb_two_power_rate
        (O := O)
        hC_convex hA hB f f' L hL hConv hSmooth
        x_star hx_star hLocal hHEB2 hmin x0 hx0
    rcases hcore with ⟨T, K, hK_pos, htail⟩
    refine ⟨T, K, hK_pos, ?_⟩
    intro n
    have hpow : (n + 1 : ℝ) ^ (2 / (2 - 1 : ℝ)) = (n + 1 : ℝ) ^ (2 : ℝ) := by
      norm_num
    simpa [hpow] using htail n

set_option maxHeartbeats 600000 in
/-- The canonical open-loop rule `γ_t = 2 / (t + 2)` satisfies the boosted
theorem under the local quadratic (`q = 2`) dual sharpness condition. -/
theorem frankWolfe_localGap_two_boosted_convergence_of_minimizerSequence_tendsto_zero
    (hC_convex : Convex ℝ C)
    {A : ℝ} (hA : 0 < A)
    (f : E → ℝ) (f' : E → E) (L : NNReal) (hL : 0 < L)
    (hConv : IsFirstOrderConvex f f')
    (hSmooth : IsLipschitzSmoothUpperBound f L f')
    (x_star : E)
    {Mset : Set E}
    (hLocal :
      HasLocalLMOGapPowerOn
        O Mset A 2)
    (xStarSeq : ℕ → E)
    (hxStarSeq : ∀ t, xStarSeq t ∈ C)
    (hxStarSeqM : ∀ t, xStarSeq t ∈ Mset)
    (hvalSeq : ∀ t, f (xStarSeq t) = f x_star)
    (hminSeq : ∀ t, ∀ y ∈ C, f (xStarSeq t) ≤ f y)
    {x0 : E} (hx0 : x0 ∈ C)
    (hδ_zero :
      Tendsto
        (fun t => ‖frankWolfeSequence O f' x0 t - xStarSeq t‖)
        atTop (nhds 0)) :
    Tendsto
      (fun t : ℕ =>
        (t + 2 : ℝ) *
          (f (frankWolfeSequence O f' x0 t) - f x_star))
      atTop (nhds 0) := by
  let xSeq : ℕ → E := frankWolfeSequence O f' x0
  let F : ℕ → ℝ := fun t => f (xSeq t) - f x_star
  let δ : ℕ → ℝ := fun t => ‖xSeq t - xStarSeq t‖
  let h : ℕ → ℝ := fun t => (t + 2 : ℝ) * F t
  let Dsq : ℝ := (Metric.diam C) ^ 2
  let M0 : ℝ := 2 * max (f x0 - f x_star) ((L : ℝ) * Dsq)
  let Ksmall : ℝ := 4 * (L : ℝ) / A
  let a : ℕ → ℝ := fun t => (t : ℝ) * (t + 3 : ℝ) / (t + 2 : ℝ) ^ 2
  let stdConst : ℕ → ℝ :=
    fun t => 2 * (L : ℝ) * Dsq * (t + 3 : ℝ) / (t + 2 : ℝ) ^ 2
  let beta : ℕ → ℝ :=
    fun t => 4 * (L : ℝ) * (δ t) ^ 2 * (t + 3 : ℝ) / (t + 2 : ℝ) ^ 2
  have hxSeq : ∀ t, xSeq t ∈ C := by
    intro t
    simpa [xSeq] using
      frankWolfeSequence_mem
        (O := O)
        hC_convex f' hx0 t
  have hF_nonneg : ∀ t, 0 ≤ F t := by
    intro t
    show 0 ≤ f (xSeq t) - f x_star
    exact primalGap_nonneg_of_minimizerSeq' hvalSeq hminSeq hxSeq t
  have hgap_grad : ∀ t, F t ≤ ‖f' (xSeq t)‖ * δ t := by
    intro t
    have hgap_t :
        f (xSeq t) - f (xStarSeq t) ≤ ‖f' (xSeq t)‖ * ‖xSeq t - xStarSeq t‖ := by
      simpa [xSeq] using
        (primalGap_le_gradNorm_mul_dist
          (f := f) (f' := f') hConv
          (x := xSeq t) (x_star := xStarSeq t))
    simpa [F, δ, hvalSeq t] using hgap_t
  have hsmall_or_refined :
      ∀ t,
        h t ≤ Ksmall * δ t ∨
          F (t + 1) ≤
            (1 - 2 / (t + 2 : ℝ)) * F t +
              (L : ℝ) * (2 / (t + 2 : ℝ)) ^ 2 * (δ t) ^ 2 := by
    intro t
    by_cases hFt0 : F t = 0
    · left
      have hKsmall_nonneg : 0 ≤ Ksmall := by positivity
      have hδ_nonneg : 0 ≤ δ t := by
        dsimp [δ]
        positivity
      simpa [h, hFt0] using (mul_nonneg hKsmall_nonneg hδ_nonneg)
    · by_cases hcase : 2 / (t + 2 : ℝ) ≤ A * ‖f' (xSeq t)‖ / (2 * (L : ℝ))
      · right
        have href :
            f (frankWolfeStep O f' (xSeq t) (2 / (t + 2 : ℝ))) -
                f (xStarSeq t) ≤
              (1 - 2 / (t + 2 : ℝ)) * (f (xSeq t) - f (xStarSeq t)) +
                (L : ℝ) * (2 / (t + 2 : ℝ)) ^ 2 * ‖xSeq t - xStarSeq t‖ ^ 2 := by
          simpa [xSeq, δ] using
            (frankWolfeStep_gap_bound_with_localCorrection_two
              (O := O)
              hLocal
              f f' L hConv hSmooth
              (x := xSeq t) (x_star := xStarSeq t) (hxStarSeq t) (hxStarSeqM t)
              (γ := 2 / (t + 2 : ℝ)) (standardStepSize_mem_Icc t) hcase)
        simpa [F, xSeq, frankWolfeSequence, hvalSeq t, frankWolfeOpenLoopSequence, openLoopStepSize] using href
      · left
        have hδ_pos_t : 0 < δ t := by
          by_contra hδt
          have hδ0 : δ t = 0 := le_antisymm (not_lt.mp hδt) (norm_nonneg _)
          have hxeq : xSeq t = xStarSeq t := by
            exact sub_eq_zero.mp (norm_eq_zero.mp (by simpa [δ] using hδ0))
          have : F t = 0 := by simp [F, hxeq, hvalSeq t]
          exact hFt0 this
        have hcase' :
            A * ‖f' (xSeq t)‖ / (2 * (L : ℝ)) < 2 / (t + 2 : ℝ) := lt_of_not_ge hcase
        have hmul :
            A * ‖f' (xSeq t)‖ < (2 / (t + 2 : ℝ)) * (2 * (L : ℝ)) := by
          exact (_root_.div_lt_iff₀ (show 0 < 2 * (L : ℝ) by positivity)).1 hcase'
        have hgrad_lt :
            ‖f' (xSeq t)‖ < ((2 / (t + 2 : ℝ)) * (2 * (L : ℝ))) / A := by
          have : ‖f' (xSeq t)‖ * A < (2 / (t + 2 : ℝ)) * (2 * (L : ℝ)) := by
            simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
          exact (_root_.lt_div_iff₀ hA).2 this
        have hsmall' :
            F t < (((2 / (t + 2 : ℝ)) * (2 * (L : ℝ))) / A) * δ t := by
          exact lt_of_le_of_lt (hgap_grad t) <|
            mul_lt_mul_of_pos_right hgrad_lt hδ_pos_t
        have hscaled :
            h t < Ksmall * δ t := by
          dsimp [h, Ksmall]
          have hEq :
              (t + 2 : ℝ) * ((((2 / (t + 2 : ℝ)) * (2 * (L : ℝ))) / A) * δ t) =
                (4 * (L : ℝ) / A) * δ t := by
            field_simp [hA.ne', (show (t + 2 : ℝ) ≠ 0 by positivity)]
            ring
          have hmul' :
              (t + 2 : ℝ) * F t <
                (t + 2 : ℝ) * ((((2 / (t + 2 : ℝ)) * (2 * (L : ℝ))) / A) * δ t) := by
            exact mul_lt_mul_of_pos_left hsmall' (by positivity)
          simpa [hEq] using hmul'
        exact le_of_lt hscaled
  have hstd_step :
      ∀ t,
        F (t + 1) ≤
          (1 - 2 / (t + 2 : ℝ)) * F t +
            ((L : ℝ) / 2) * (2 / (t + 2 : ℝ)) ^ 2 * Dsq := by
    intro t
    have href :
        f (frankWolfeStep O f' (xSeq t) (2 / (t + 2 : ℝ))) -
            f (xStarSeq t) ≤
          (1 - 2 / (t + 2 : ℝ)) * (f (xSeq t) - f (xStarSeq t)) +
            ((L : ℝ) / 2) * (2 / (t + 2 : ℝ)) ^ 2 * Dsq := by
      simpa [xSeq, Dsq] using
        (frankWolfeStep_gap_bound
          (O := O)
          (C := C) (f := f) (f' := f') (L := L) hSmooth hConv
          (x := xSeq t) (x_star := xStarSeq t) (hxSeq t) (hxStarSeq t)
          (γ := 2 / (t + 2 : ℝ)) (standardStepSize_mem_Icc t))
    simpa [F, xSeq, frankWolfeSequence, hvalSeq t, frankWolfeOpenLoopSequence, openLoopStepSize] using href
  have hstd_bound :
      ∀ t, F t ≤ M0 / (t + 2 : ℝ) := by
    intro t
    let B : ℝ := max (f x0 - f (xStarSeq 0)) ((L : ℝ) * Dsq)
    have hB_nonneg : 0 ≤ B := by
      have hgap0_nonneg : 0 ≤ f x0 - f (xStarSeq 0) := by
        exact primalGap_nonneg_of_isMinOn (C := C) (f := f) hx0 (hminSeq 0)
      exact le_trans hgap0_nonneg (le_max_left _ _)
    have hfw :=
      frank_wolfe_convergence_of_initialGap_le
        (O := O)
        hC_convex f f' L hSmooth hConv (hxStarSeq 0) hx0
        hB_nonneg (le_max_left _ _) (le_max_right _ _) t
    simpa [B, M0, F, xSeq, hvalSeq 0] using hfw
  have hbounded : ∀ t, h t ≤ M0 := by
    intro t
    calc
      h t = (t + 2 : ℝ) * F t := by rfl
      _ ≤ (t + 2 : ℝ) * (M0 / (t + 2 : ℝ)) := by
            gcongr
            exact hstd_bound t
      _ = M0 := by
            field_simp [show (t + 2 : ℝ) ≠ 0 by positivity]
  have hnonneg_h : ∀ t, 0 ≤ h t := by
    intro t
    dsimp [h]
    exact mul_nonneg (by positivity) (hF_nonneg t)
  apply boosted_convergence_kernel hnonneg_h
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  have hKsmall_event : ∀ᶠ t : ℕ in atTop, Ksmall * δ t < ε / 2 := by
    have hKzero :
        Tendsto (fun t => Ksmall * δ t) atTop (nhds 0) := by
      simpa [δ, Ksmall] using hδ_zero.const_mul Ksmall
    exact hKzero.eventually (Iio_mem_nhds hε2)
  have hδsq_zero : Tendsto (fun t => (δ t) ^ 2) atTop (nhds 0) := by
    simpa using hδ_zero.pow 2
  have hbeta_event : ∀ᶠ t : ℕ in atTop, 4 * (L : ℝ) * (δ t) ^ 2 < ε / 2 := by
    have hbeta_zero :
        Tendsto (fun t => 4 * (L : ℝ) * (δ t) ^ 2) atTop (nhds 0) := by
      simpa using hδsq_zero.const_mul (4 * (L : ℝ))
    exact hbeta_zero.eventually (Iio_mem_nhds hε2)
  have hstdconst_zero : Tendsto (fun t : ℕ => (4 * (L : ℝ) * Dsq) / (t + 2 : ℝ)) atTop (nhds 0) :=
    tendsto_const_div_add_atTop_nhds_zero_nat (4 * (L : ℝ) * Dsq) 2
  have hstdconst_event : ∀ᶠ t : ℕ in atTop, stdConst t < ε / 2 := by
    have hmain := hstdconst_zero.eventually (Iio_mem_nhds hε2)
    filter_upwards [hmain] with t ht
    have hbound_t : stdConst t ≤ (4 * (L : ℝ) * Dsq) / (t + 2 : ℝ) := by
      have hB_nonneg : 0 ≤ (L : ℝ) * Dsq := by positivity
      simpa [stdConst, mul_assoc, mul_left_comm, mul_comm] using
        (frankWolfe_openLoop_stdConst_bound
          (B := (L : ℝ) * Dsq) hB_nonneg t)
    exact lt_of_le_of_lt hbound_t ht
  have hall :
      ∀ᶠ t : ℕ in atTop,
        Ksmall * δ t < ε / 2 ∧
          4 * (L : ℝ) * (δ t) ^ 2 < ε / 2 ∧
          stdConst t < ε / 2 := by
    filter_upwards [hKsmall_event, hbeta_event, hstdconst_event] with t h1 h2 h3
    exact ⟨h1, h2, h3⟩
  rcases Filter.Eventually.exists_forall_of_atTop hall with ⟨T, hT⟩
  have hstable :
      ∀ t ≥ T, h t ≤ ε → h (t + 1) ≤ ε := by
    intro t ht hle
    rcases hT t ht with ⟨hsmallT, hbetaT, hstdT⟩
    rcases hsmall_or_refined t with hleft | hright
    · have hh_succ : h (t + 1) = (t + 3 : ℝ) * F (t + 1) := by
        change ((((t + 1 : ℕ) : ℝ) + 2) * F (t + 1) = (t + 3 : ℝ) * F (t + 1))
        have hcast : (((t + 1 : ℕ) : ℝ) + 2) = (t + 3 : ℝ) := by
          exact_mod_cast (show t + 1 + 2 = t + 3 by omega)
        rw [hcast]
      have hstep : h (t + 1) ≤ a t * h t + stdConst t := by
        have hmul := mul_le_mul_of_nonneg_left (hstd_step t) (by positivity : 0 ≤ (t + 3 : ℝ))
        calc
          h (t + 1) = (t + 3 : ℝ) * F (t + 1) := hh_succ
          _ ≤ (t + 3 : ℝ) *
                ((1 - 2 / (t + 2 : ℝ)) * F t +
                  ((L : ℝ) / 2) * (2 / (t + 2 : ℝ)) ^ 2 * Dsq) := hmul
          _ = a t * h t + stdConst t := by
                simpa [a, h, stdConst, mul_assoc, mul_left_comm, mul_comm] using
                  (frankWolfe_openLoop_scaled_standard_eq
                    (F := F) (Dsq := Dsq) (L := (L : ℝ)) t)
      have hmain : h (t + 1) ≤ h t + stdConst t := by
        have ha_le_one : a t ≤ 1 := by
          simpa [a] using frankWolfe_openLoop_coeff_le_one t
        have hah : a t * h t ≤ h t := by
          simpa using mul_le_mul_of_nonneg_right ha_le_one (hnonneg_h t)
        linarith
      have hlt : h (t + 1) < ε := by
        linarith
      exact le_of_lt hlt
    · have hstep : h (t + 1) ≤ a t * h t + beta t := by
        have hh_succ : h (t + 1) = (t + 3 : ℝ) * F (t + 1) := by
          change ((((t + 1 : ℕ) : ℝ) + 2) * F (t + 1) = (t + 3 : ℝ) * F (t + 1))
          have hcast : (((t + 1 : ℕ) : ℝ) + 2) = (t + 3 : ℝ) := by
            exact_mod_cast (show t + 1 + 2 = t + 3 by omega)
          rw [hcast]
        have hmul := mul_le_mul_of_nonneg_left hright (by positivity : 0 ≤ (t + 3 : ℝ))
        calc
          h (t + 1) = (t + 3 : ℝ) * F (t + 1) := hh_succ
          _ ≤ (t + 3 : ℝ) *
                ((1 - 2 / (t + 2 : ℝ)) * F t +
                  (L : ℝ) * (2 / (t + 2 : ℝ)) ^ 2 * (δ t) ^ 2) := hmul
          _ = a t * h t + beta t := by
                simpa [a, h, beta, mul_assoc, mul_left_comm, mul_comm] using
                  (frankWolfe_openLoop_scaled_refined_eq
                    (F := F) (δ := δ) (L := (L : ℝ)) t)
      have hbeta_le :
          beta t ≤ (ε / 2) * (t + 3 : ℝ) / (t + 2 : ℝ) ^ 2 := by
        let c : ℝ := (t + 3 : ℝ) / (t + 2 : ℝ) ^ 2
        have hc_nonneg : 0 ≤ c := by
          dsimp [c]
          positivity
        have hbeta_base :
            (4 * (L : ℝ) * (δ t) ^ 2) * c ≤ (ε / 2) * c := by
          exact mul_le_mul_of_nonneg_right (le_of_lt hbetaT) hc_nonneg
        have hbeta_eq :
            beta t = (4 * (L : ℝ) * (δ t) ^ 2) * c := by
          dsimp [beta, c]
          rw [div_eq_mul_inv]
          ring
        calc
          beta t = (4 * (L : ℝ) * (δ t) ^ 2) * c := hbeta_eq
          _ ≤ (ε / 2) * c := hbeta_base
          _ = (ε / 2) * (t + 3 : ℝ) / (t + 2 : ℝ) ^ 2 := by
                dsimp [c]
                ring
      have hcoeff :
          a t * ε + (ε / 2) * (t + 3 : ℝ) / (t + 2 : ℝ) ^ 2 ≤ ε := by
        have hcoeff_unit :
            a t + (1 / 2 : ℝ) * (t + 3 : ℝ) / (t + 2 : ℝ) ^ 2 ≤ 1 := by
          simpa [a] using frankWolfe_openLoop_refined_coeff_le_one t
        have hmul :
            ε * (a t + (1 / 2 : ℝ) * (t + 3 : ℝ) / (t + 2 : ℝ) ^ 2) ≤ ε := by
          simpa using mul_le_mul_of_nonneg_left hcoeff_unit (le_of_lt hε)
        have hEq :
            ε * (a t + (1 / 2 : ℝ) * (t + 3 : ℝ) / (t + 2 : ℝ) ^ 2) =
              a t * ε + (ε / 2) * (t + 3 : ℝ) / (t + 2 : ℝ) ^ 2 := by
          ring
        rw [hEq] at hmul
        exact hmul
      have hmain :
          h (t + 1) ≤ a t * ε + (ε / 2) * (t + 3 : ℝ) / (t + 2 : ℝ) ^ 2 := by
        have ha_nonneg : 0 ≤ a t := by
          dsimp [a]
          positivity
        have hah : a t * h t ≤ a t * ε := by
          exact mul_le_mul_of_nonneg_left hle ha_nonneg
        linarith
      exact le_trans hmain hcoeff
  have habove_drop :
      ∀ N0 t, T ≤ N0 → N0 ≤ t → t ≤ 2 * N0 → ε < h t →
        h (t + 1) ≤ h t - ε / (4 * (N0 + 1 : ℝ)) := by
    intro N0 t hTN hN0 htN0 hgt
    rcases hT t (le_trans hTN hN0) with ⟨hsmallT, hbetaT, _hstdT⟩
    rcases hsmall_or_refined t with hleft | hright
    · exfalso
      linarith [hleft, hsmallT, hgt]
    · have hstep : h (t + 1) ≤ a t * h t + beta t := by
        have hh_succ : h (t + 1) = (t + 3 : ℝ) * F (t + 1) := by
          change ((((t + 1 : ℕ) : ℝ) + 2) * F (t + 1) = (t + 3 : ℝ) * F (t + 1))
          have hcast : (((t + 1 : ℕ) : ℝ) + 2) = (t + 3 : ℝ) := by
            exact_mod_cast (show t + 1 + 2 = t + 3 by omega)
          rw [hcast]
        have hmul := mul_le_mul_of_nonneg_left hright (by positivity : 0 ≤ (t + 3 : ℝ))
        calc
          h (t + 1) = (t + 3 : ℝ) * F (t + 1) := hh_succ
          _ ≤ (t + 3 : ℝ) *
                ((1 - 2 / (t + 2 : ℝ)) * F t +
                  (L : ℝ) * (2 / (t + 2 : ℝ)) ^ 2 * (δ t) ^ 2) := hmul
          _ = a t * h t + beta t := by
                simpa [a, h, beta, mul_assoc, mul_left_comm, mul_comm] using
                  (frankWolfe_openLoop_scaled_refined_eq
                    (F := F) (δ := δ) (L := (L : ℝ)) t)
      have hbeta_le :
          beta t ≤ (ε / 2) * (t + 3 : ℝ) / (t + 2 : ℝ) ^ 2 := by
        let c : ℝ := (t + 3 : ℝ) / (t + 2 : ℝ) ^ 2
        have hc_nonneg : 0 ≤ c := by
          dsimp [c]
          positivity
        have hbeta_base :
            (4 * (L : ℝ) * (δ t) ^ 2) * c ≤ (ε / 2) * c := by
          exact mul_le_mul_of_nonneg_right (le_of_lt hbetaT) hc_nonneg
        have hbeta_eq :
            beta t = (4 * (L : ℝ) * (δ t) ^ 2) * c := by
          dsimp [beta, c]
          rw [div_eq_mul_inv]
          ring
        calc
          beta t = (4 * (L : ℝ) * (δ t) ^ 2) * c := hbeta_eq
          _ ≤ (ε / 2) * c := hbeta_base
          _ = (ε / 2) * (t + 3 : ℝ) / (t + 2 : ℝ) ^ 2 := by
                dsimp [c]
                ring
      have hdrop :
          h (t + 1) ≤ h t - ε / (2 * (t + 2 : ℝ)) := by
        have hdrop_aux :
            a t * h t + (ε / 2) * (t + 3 : ℝ) / (t + 2 : ℝ) ^ 2 ≤
              h t - ε / (2 * (t + 2 : ℝ)) := by
          simpa [a] using
            frankWolfe_openLoop_drop_bound t (hε := le_of_lt hε) (hH := le_of_lt hgt)
        linarith
      have hfrac :
          ε / (4 * (N0 + 1 : ℝ)) ≤ ε / (2 * (t + 2 : ℝ)) := by
        exact frankWolfe_openLoop_blockFraction_bound
          (hε := le_of_lt hε) htN0
      have hsub :
          h t - ε / (2 * (t + 2 : ℝ)) ≤ h t - ε / (4 * (N0 + 1 : ℝ)) := by
        linarith
      exact le_trans hdrop hsub
  refine ⟨T, M0, ε / 4, by linarith, hbounded T, hstable, ?_⟩
  have hNseq_succ : ∀ j, 2 ^ (j + 1) * (T + 1) - 1 = 2 * (2 ^ j * (T + 1) - 1) + 1 :=
    nseq_succ T
  have hNseq_ge : ∀ j, T ≤ 2 ^ j * (T + 1) - 1 :=
    nseq_ge T
  have htail_above : ∀ {p t : ℕ}, T ≤ t → t ≤ p → ε < h p → ε < h t :=
    fun htT htp hpgt => tail_above_of_stable hstable htT htp hpgt
  intro k n hkn hngt
  let Nk : ℕ := 2 ^ k * (T + 1) - 1
  have hNk_succ : 2 ^ (k + 1) * (T + 1) - 1 = 2 * Nk + 1 := hNseq_succ k
  have hNk_ge : T ≤ Nk := hNseq_ge k
  have hablock : ∀ t, Nk ≤ t → t ≤ 2 * Nk → ε < h t := by
    intro t hlow hhigh
    have htn : t ≤ n := by rw [hNk_succ] at hkn; omega
    exact htail_above (le_trans hNk_ge hlow) htn hngt
  have hstepblock :
      ∀ t, Nk ≤ t → t ≤ 2 * Nk →
        ε / (4 * (↑Nk + 1 : ℝ)) ≤ h t - h (t + 1) := by
    intro t hlow hhigh
    linarith [habove_drop Nk t hNk_ge hlow hhigh (hablock t hlow hhigh)]
  have hdrop' :=
    block_drop_of_step_drop (h := h) (ε := ε) (N := Nk) hstepblock
  simpa [hNk_succ] using hdrop'

set_option maxHeartbeats 600000 in
/-- The canonical open-loop rule `γ_t = 2/(t+2)` satisfies the boosted theorem
under the local dual sharpness condition for exponents `q = 2` or `q > 2`, once the
iterates approach a varying feasible minimizer sequence. -/
theorem frankWolfe_localGap_boosted_convergence_of_minimizerSequence_tendsto_zero
    (hC_convex : Convex ℝ C)
    {A : ℝ} {q : ℝ} (hq : q = 2 ∨ 2 < q) (hA : 0 < A)
    (f : E → ℝ) (f' : E → E) (L : NNReal) (hL : 0 < L)
    (hConv : IsFirstOrderConvex f f')
    (hSmooth : IsLipschitzSmoothUpperBound f L f')
    (x_star : E)
    {Mset : Set E}
    (hLocal :
      HasLocalLMOGapPowerOn
        O Mset A q)
    (xStarSeq : ℕ → E)
    (hxStarSeq : ∀ t, xStarSeq t ∈ C)
    (hxStarSeqM : ∀ t, xStarSeq t ∈ Mset)
    (hvalSeq : ∀ t, f (xStarSeq t) = f x_star)
    (hminSeq : ∀ t, ∀ y ∈ C, f (xStarSeq t) ≤ f y)
    {x0 : E} (hx0 : x0 ∈ C)
    (hδ_zero :
      Tendsto
        (fun t => ‖frankWolfeSequence O f' x0 t - xStarSeq t‖)
        atTop (nhds 0)) :
    Tendsto
      (fun t : ℕ =>
        (t + 2 : ℝ) *
          (f (frankWolfeSequence O f' x0 t) - f x_star))
      atTop (nhds 0) := by
  rcases hq with rfl | hq3
  · simpa using
      frankWolfe_localGap_two_boosted_convergence_of_minimizerSequence_tendsto_zero
        (O := O)
        hC_convex hA f f' L hL hConv hSmooth x_star hLocal
        xStarSeq hxStarSeq hxStarSeqM hvalSeq hminSeq hx0 hδ_zero
  ·
    let xSeq : ℕ → E := frankWolfeSequence O f' x0
    let F : ℕ → ℝ := fun t => f (xSeq t) - f x_star
    let δ : ℕ → ℝ := fun t => ‖xSeq t - xStarSeq t‖
    let h : ℕ → ℝ := fun t => (t + 2 : ℝ) * F t
    let Dsq : ℝ := (Metric.diam C) ^ 2
    let M0 : ℝ := 2 * max (f x0 - f x_star) ((L : ℝ) * Dsq)
    let a : ℕ → ℝ := fun t => (t : ℝ) * (t + 3 : ℝ) / (t + 2 : ℝ) ^ 2
    let c : ℕ → ℝ := fun t => (t + 3 : ℝ) / (t + 2 : ℝ) ^ 2
    let stdConst : ℕ → ℝ :=
      fun t => 2 * (L : ℝ) * Dsq * (t + 3 : ℝ) / (t + 2 : ℝ) ^ 2
    let betaExp : ℝ := 2 / (q - 2 : ℝ)
    have hq_pos : 0 < q := by linarith
    have hq_sub_pos : 0 < (q - 2 : ℝ) := by linarith
    have hbeta_nonneg : 0 ≤ betaExp := by
      dsimp [betaExp]
      positivity
    have hbeta_pos : 0 < betaExp := by
      dsimp [betaExp]
      positivity
    have hF_nonneg : ∀ t, 0 ≤ F t := by
      intro t
      have hgap_t :
          0 ≤ f (xSeq t) - f (xStarSeq t) := by
        exact
          primalGap_nonneg_of_isMinOn
            (C := C) (f := f)
            (frankWolfeSequence_mem
              (O := O)
              hC_convex f' hx0 t)
            (hminSeq t)
      simpa [F, hvalSeq t] using hgap_t
    have hstd_step :
        ∀ t,
          F (t + 1) ≤
            (1 - 2 / (t + 2 : ℝ)) * F t +
              ((L : ℝ) / 2) * (2 / (t + 2 : ℝ)) ^ 2 * Dsq := by
      intro t
      have href :
          f (frankWolfeStep O f'
                (xSeq t) (2 / (t + 2 : ℝ))) -
              f (xStarSeq t) ≤
            (1 - 2 / (t + 2 : ℝ)) * (f (xSeq t) - f (xStarSeq t)) +
              ((L : ℝ) / 2) * (2 / (t + 2 : ℝ)) ^ 2 * Dsq := by
        simpa [xSeq, Dsq] using
          (frankWolfeStep_gap_bound
            (O := O)
            (C := C) (f := f) (f' := f') (L := L) hSmooth hConv
            (x := xSeq t) (x_star := xStarSeq t)
            (frankWolfeSequence_mem
              (O := O)
              hC_convex f' hx0 t)
            (hxStarSeq t)
            (γ := 2 / (t + 2 : ℝ))
            (standardStepSize_mem_Icc t))
      simpa [F, xSeq, frankWolfeSequence, hvalSeq t, frankWolfeOpenLoopSequence, openLoopStepSize] using href
    have hstd_bound :
        ∀ t, F t ≤ M0 / (t + 2 : ℝ) := by
      intro t
      let B : ℝ := max (f x0 - f (xStarSeq 0)) ((L : ℝ) * Dsq)
      have hB_nonneg : 0 ≤ B := by
        have hgap0_nonneg : 0 ≤ f x0 - f (xStarSeq 0) := by
          exact primalGap_nonneg_of_isMinOn (C := C) (f := f) hx0 (hminSeq 0)
        exact le_trans hgap0_nonneg (le_max_left _ _)
      have hfw :=
        frank_wolfe_convergence_of_initialGap_le
          (O := O)
          hC_convex f f' L hSmooth hConv (hxStarSeq 0) hx0
          hB_nonneg (le_max_left _ _) (le_max_right _ _) t
      simpa [B, M0, Dsq, F, xSeq, hvalSeq 0] using hfw
    have hbounded : ∀ t, h t ≤ M0 := by
      intro t
      calc
        h t = (t + 2 : ℝ) * F t := by rfl
        _ ≤ (t + 2 : ℝ) * (M0 / (t + 2 : ℝ)) := by
              gcongr
              exact hstd_bound t
        _ = M0 := by field_simp [show (t + 2 : ℝ) ≠ 0 by positivity]
    have hnonneg_h : ∀ t, 0 ≤ h t := by
      intro t
      dsimp [h]
      exact mul_nonneg (by positivity) (hF_nonneg t)
    apply boosted_convergence_kernel hnonneg_h
    intro ε hε
    let Csmall : ℝ := 16 * (L : ℝ) / (q * A * ε)
    let Rconst : ℝ := ((q - 2 : ℝ) / q) * (L : ℝ) * Csmall ^ betaExp
    let coeff : ℕ → ℝ :=
      fun t => 4 * (L : ℝ) * (δ t) ^ 2 + 4 * Rconst * (δ t) ^ betaExp
    have hε2 : 0 < ε / 2 := by linarith
    have hδsq_zero : Tendsto (fun t => (δ t) ^ 2) atTop (nhds 0) := by
      simpa using hδ_zero.pow 2
    have hδbeta_zero : Tendsto (fun t => (δ t) ^ betaExp) atTop (nhds 0) :=
      tendsto_rpow_const_zero hδ_zero hbeta_pos
    have hcoeff_zero : Tendsto coeff atTop (nhds 0) := by
      have hleft :
          Tendsto (fun t => 4 * (L : ℝ) * (δ t) ^ 2) atTop (nhds 0) := by
        simpa using hδsq_zero.const_mul (4 * (L : ℝ))
      have hright :
          Tendsto (fun t => 4 * Rconst * (δ t) ^ betaExp) atTop (nhds 0) := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          hδbeta_zero.const_mul (4 * Rconst)
      simpa [coeff] using hleft.add hright
    have hstdconst_zero : Tendsto (fun t : ℕ => (4 * (L : ℝ) * Dsq) / (t + 2 : ℝ)) atTop (nhds 0) :=
      tendsto_const_div_add_atTop_nhds_zero_nat (4 * (L : ℝ) * Dsq) 2
    have hstdconst_event : ∀ᶠ t : ℕ in atTop, stdConst t < ε / 2 := by
      have hmain := hstdconst_zero.eventually (Iio_mem_nhds hε2)
      filter_upwards [hmain] with t ht
      have hbound_t : stdConst t ≤ (4 * (L : ℝ) * Dsq) / (t + 2 : ℝ) := by
        have hB_nonneg : 0 ≤ (L : ℝ) * Dsq := by positivity
        simpa [stdConst, mul_assoc, mul_left_comm, mul_comm] using
          (frankWolfe_openLoop_stdConst_bound
            (B := (L : ℝ) * Dsq) hB_nonneg t)
      exact lt_of_le_of_lt hbound_t ht
    have hcoeff_event : ∀ᶠ t : ℕ in atTop, coeff t < ε / 2 := by
      exact hcoeff_zero.eventually (Iio_mem_nhds hε2)
    have hall :
        ∀ᶠ t : ℕ in atTop, coeff t < ε / 2 ∧ stdConst t < ε / 2 := by
      filter_upwards [hcoeff_event, hstdconst_event] with t h1 h2
      exact ⟨h1, h2⟩
    rcases Filter.Eventually.exists_forall_of_atTop hall with ⟨T, hT⟩
    have hsmall_or_refined :
        ∀ t,
          h t ≤ ε / 2 ∨
            F (t + 1) ≤
              (1 - 2 / (t + 2 : ℝ)) * F t +
                (L : ℝ) * (2 / (t + 2 : ℝ)) ^ 2 * (δ t) ^ 2 +
                Rconst * (2 / (t + 2 : ℝ)) ^ 2 * (δ t) ^ betaExp := by
      intro t
      by_cases hFt0 : F t = 0
      · left
        have hnonneg : 0 ≤ ε / 2 := by linarith
        simpa [h, hFt0] using hnonneg
      · have hF_pos_t : 0 < F t := lt_of_le_of_ne (hF_nonneg t) (by simpa [eq_comm] using hFt0)
        have hδ_pos_t : 0 < δ t := by
          by_contra hδt
          have hδ0 : δ t = 0 := le_antisymm (not_lt.mp hδt) (norm_nonneg _)
          have hxeq : xSeq t = xStarSeq t := by
            exact sub_eq_zero.mp (norm_eq_zero.mp (by simpa [δ] using hδ0))
          have : F t = 0 := by simp [F, hxeq, hvalSeq t]
          exact hFt0 this
        let γt : ℝ := 2 / (t + 2 : ℝ)
        let lamT : ℝ := 4 * (L : ℝ) * γt * δ t / (q * A * F t)
        have hγ_mem : γt ∈ Set.Icc (0 : ℝ) 1 := standardStepSize_mem_Icc t
        have hγ_pos : 0 < γt := by
          dsimp [γt]
          positivity
        by_cases hcase : lamT ≤ Csmall * δ t
        · right
          have hF_seq_pos : 0 < f (xSeq t) - f (xStarSeq t) := by
            simpa [F, hvalSeq t] using hF_pos_t
          have href :
              f (frankWolfeStep O f' (xSeq t) γt) - f (xStarSeq t) ≤
                (1 - γt) * (f (xSeq t) - f (xStarSeq t)) +
                  (L : ℝ) * γt ^ 2 * ‖xSeq t - xStarSeq t‖ ^ 2 +
                  ((q - 2 : ℝ) / q) * (L : ℝ) * γt ^ 2 *
                    lamT ^ ((2 : ℝ) / (q - 2 : ℝ)) := by
            simpa [xSeq, γt, δ, F, lamT, hvalSeq t] using
              (frankWolfeStep_gap_bound_with_localCorrection
                (O := O)
                (hq := hq3) hA hLocal
                f f' L hConv hSmooth
                (x := xSeq t) (x_star := xStarSeq t)
                (hxStarSeq t) (hxStarSeqM t) hγ_mem hγ_pos hF_seq_pos hδ_pos_t)
          have hlam_pow :
              lamT ^ betaExp ≤ (Csmall * δ t) ^ betaExp := by
            exact Real.rpow_le_rpow (by positivity) hcase hbeta_nonneg
          have hlam_pow' :
              lamT ^ betaExp ≤ Csmall ^ betaExp * (δ t) ^ betaExp := by
            calc
              lamT ^ betaExp ≤ (Csmall * δ t) ^ betaExp := hlam_pow
              _ = Csmall ^ betaExp * (δ t) ^ betaExp := by
                    exact Real.mul_rpow (by positivity) (by positivity)
          have hres_le :
              ((q - 2 : ℝ) / q) * (L : ℝ) * γt ^ 2 * lamT ^ betaExp ≤
                Rconst * γt ^ 2 * (δ t) ^ betaExp := by
            calc
              ((q - 2 : ℝ) / q) * (L : ℝ) * γt ^ 2 * lamT ^ betaExp
                  ≤ ((q - 2 : ℝ) / q) * (L : ℝ) * γt ^ 2 *
                      (Csmall ^ betaExp * (δ t) ^ betaExp) := by
                        exact mul_le_mul_of_nonneg_left hlam_pow'
                          (by positivity :
                            0 ≤ ((q - 2 : ℝ) / q) * (L : ℝ) * γt ^ 2)
              _ = Rconst * γt ^ 2 * (δ t) ^ betaExp := by
                    dsimp [Rconst]
                    ring
          have href' :
              F (t + 1) ≤
                (1 - 2 / (t + 2 : ℝ)) * F t +
                  (L : ℝ) * (2 / (t + 2 : ℝ)) ^ 2 * (δ t) ^ 2 +
                  ((q - 2 : ℝ) / q) * (L : ℝ) * γt ^ 2 * lamT ^ betaExp := by
            simpa [F, xSeq, frankWolfeSequence, γt, δ, hvalSeq t, frankWolfeOpenLoopSequence, openLoopStepSize] using href
          linarith
        · left
          have hcase' : Csmall * δ t < lamT := lt_of_not_ge hcase
          have hlam_repr :
              lamT = (4 * (L : ℝ) * γt / (q * A * F t)) * δ t := by
            dsimp [lamT]
            field_simp [hF_pos_t.ne']
          rw [hlam_repr] at hcase'
          have hdiv :
              Csmall < 4 * (L : ℝ) * γt / (q * A * F t) := by
            exact lt_of_mul_lt_mul_right hcase' hδ_pos_t.le
          have hF_bound :
              F t < 4 * (L : ℝ) * γt / (q * A * Csmall) := by
            have hden_pos : 0 < q * A * Csmall := by
              dsimp [Csmall]
              positivity
            have hmul : F t * (q * A * Csmall) < 4 * (L : ℝ) * γt := by
              have hmul' : Csmall * (q * A * F t) < 4 * (L : ℝ) * γt := by
                exact (_root_.lt_div_iff₀ (show 0 < q * A * F t by positivity)).1 hdiv
              simpa [mul_assoc, mul_left_comm, mul_comm] using hmul'
            exact (_root_.lt_div_iff₀ hden_pos).2 hmul
          have hEq :
              4 * (L : ℝ) * γt / (q * A * Csmall) = ε / (2 * (t + 2 : ℝ)) := by
            dsimp [γt, Csmall]
            field_simp [hε.ne', hA.ne', hq_pos.ne']
            ring
          have hh_small : h t < ε / 2 := by
            have htmp : F t < ε / (2 * (t + 2 : ℝ)) := by simpa [hEq] using hF_bound
            dsimp [h]
            have hmul := mul_lt_mul_of_pos_left htmp (by positivity : 0 < (t + 2 : ℝ))
            have hneq : (t + 2 : ℝ) ≠ 0 := by positivity
            have hcalc :
                (t + 2 : ℝ) * (ε / (2 * (t + 2 : ℝ))) = ε / 2 := by
              field_simp [hneq]
            simpa [hcalc] using hmul
          exact le_of_lt hh_small
    have hstable :
        ∀ t ≥ T, h t ≤ ε → h (t + 1) ≤ ε := by
      intro t ht hle
      rcases hT t ht with ⟨hcoeffT, hstdT⟩
      rcases hsmall_or_refined t with hleft | hright
      · have hstep : h (t + 1) ≤ a t * h t + stdConst t := by
          have hh_succ : h (t + 1) = (t + 3 : ℝ) * F (t + 1) := by
            change ((((t + 1 : ℕ) : ℝ) + 2) * F (t + 1) = (t + 3 : ℝ) * F (t + 1))
            have hcast : (((t + 1 : ℕ) : ℝ) + 2) = (t + 3 : ℝ) := by
              exact_mod_cast (show t + 1 + 2 = t + 3 by omega)
            rw [hcast]
          have hmul := mul_le_mul_of_nonneg_left (hstd_step t) (by positivity : 0 ≤ (t + 3 : ℝ))
          calc
            h (t + 1) = (t + 3 : ℝ) * F (t + 1) := hh_succ
            _ ≤ (t + 3 : ℝ) *
                  ((1 - 2 / (t + 2 : ℝ)) * F t +
                    ((L : ℝ) / 2) * (2 / (t + 2 : ℝ)) ^ 2 * Dsq) := hmul
            _ = a t * h t + stdConst t := by
                  simpa [a, h, stdConst, mul_assoc, mul_left_comm, mul_comm] using
                    (frankWolfe_openLoop_scaled_standard_eq
                      (F := F) (Dsq := Dsq) (L := (L : ℝ)) t)
        have ha_le_one : a t ≤ 1 := by
          simpa [a] using frankWolfe_openLoop_coeff_le_one t
        have hah : a t * h t ≤ h t := by
          simpa using mul_le_mul_of_nonneg_right ha_le_one (hnonneg_h t)
        have hlt : h (t + 1) < ε := by
          linarith
        exact le_of_lt hlt
      · have hstep : h (t + 1) ≤ a t * h t + c t * coeff t := by
          have hh_succ : h (t + 1) = (t + 3 : ℝ) * F (t + 1) := by
            change ((((t + 1 : ℕ) : ℝ) + 2) * F (t + 1) = (t + 3 : ℝ) * F (t + 1))
            have hcast : (((t + 1 : ℕ) : ℝ) + 2) = (t + 3 : ℝ) := by
              exact_mod_cast (show t + 1 + 2 = t + 3 by omega)
            rw [hcast]
          have hmul := mul_le_mul_of_nonneg_left hright (by positivity : 0 ≤ (t + 3 : ℝ))
          calc
            h (t + 1) = (t + 3 : ℝ) * F (t + 1) := hh_succ
            _ ≤ (t + 3 : ℝ) *
                  ((1 - 2 / (t + 2 : ℝ)) * F t +
                    (L : ℝ) * (2 / (t + 2 : ℝ)) ^ 2 * (δ t) ^ 2 +
                    Rconst * (2 / (t + 2 : ℝ)) ^ 2 * (δ t) ^ betaExp) := hmul
            _ = a t * h t + c t * coeff t := by
                  dsimp [a, h, c, coeff]
                  field_simp [show (t + 2 : ℝ) ≠ 0 by positivity]
                  ring
        have hc_nonneg : 0 ≤ c t := by
          dsimp [c]
          exact div_nonneg (by positivity) (by positivity)
        have hc_le : c t ≤ 1 - a t := by
          dsimp [c, a]
          have hnum : (t + 3 : ℝ) ≤ (t + 4 : ℝ) := by nlinarith
          have hfrac : (t + 3 : ℝ) / (t + 2 : ℝ) ^ 2 ≤ (t + 4 : ℝ) / (t + 2 : ℝ) ^ 2 := by
            exact (_root_.div_le_div_of_nonneg_right hnum (by positivity))
          have hEq : (t + 4 : ℝ) / (t + 2 : ℝ) ^ 2 = 1 - a t := by
            dsimp [a]
            field_simp [show (t + 2 : ℝ) ≠ 0 by positivity]
            ring
          simpa [hEq] using hfrac
        have hbeta_le : c t * coeff t ≤ c t * (ε / 2) := by
          exact mul_le_mul_of_nonneg_left (le_of_lt hcoeffT) hc_nonneg
        have hmain : h (t + 1) ≤ a t * ε + c t * (ε / 2) := by
          have ha_nonneg : 0 ≤ a t := by
            dsimp [a]
            positivity
          have hah : a t * h t ≤ a t * ε := by
            exact mul_le_mul_of_nonneg_left hle ha_nonneg
          calc
            h (t + 1) ≤ a t * h t + c t * coeff t := hstep
            _ ≤ a t * ε + c t * coeff t := by linarith [hah]
            _ ≤ a t * ε + c t * (ε / 2) := by linarith [hbeta_le]
        have hfinal : a t * ε + c t * (ε / 2) ≤ ε := by
          have hhalf : c t * (ε / 2) ≤ c t * ε := by
            exact mul_le_mul_of_nonneg_left (by linarith) hc_nonneg
          have hfull : c t * ε ≤ (1 - a t) * ε := by
            exact mul_le_mul_of_nonneg_right hc_le (le_of_lt hε)
          linarith
        exact le_trans hmain hfinal
    have habove_drop :
        ∀ N0 t, T ≤ N0 → N0 ≤ t → t ≤ 2 * N0 → ε < h t →
          h (t + 1) ≤ h t - ε / (4 * (N0 + 1 : ℝ)) := by
      intro N0 t hTN hN0 htN0 hgt
      rcases hT t (le_trans hTN hN0) with ⟨hcoeffT, _hstdT⟩
      rcases hsmall_or_refined t with hleft | hright
      · exfalso
        linarith
      · have hstep : h (t + 1) ≤ a t * h t + c t * coeff t := by
          have hh_succ : h (t + 1) = (t + 3 : ℝ) * F (t + 1) := by
            change ((((t + 1 : ℕ) : ℝ) + 2) * F (t + 1) = (t + 3 : ℝ) * F (t + 1))
            have hcast : (((t + 1 : ℕ) : ℝ) + 2) = (t + 3 : ℝ) := by
              exact_mod_cast (show t + 1 + 2 = t + 3 by omega)
            rw [hcast]
          have hmul := mul_le_mul_of_nonneg_left hright (by positivity : 0 ≤ (t + 3 : ℝ))
          calc
            h (t + 1) = (t + 3 : ℝ) * F (t + 1) := hh_succ
            _ ≤ (t + 3 : ℝ) *
                  ((1 - 2 / (t + 2 : ℝ)) * F t +
                    (L : ℝ) * (2 / (t + 2 : ℝ)) ^ 2 * (δ t) ^ 2 +
                    Rconst * (2 / (t + 2 : ℝ)) ^ 2 * (δ t) ^ betaExp) := hmul
            _ = a t * h t + c t * coeff t := by
                  dsimp [a, h, c, coeff]
                  field_simp [show (t + 2 : ℝ) ≠ 0 by positivity]
                  ring
        have hc_nonneg : 0 ≤ c t := by
          dsimp [c]
          positivity
        have hbeta_le : c t * coeff t ≤ c t * (ε / 2) := by
          exact mul_le_mul_of_nonneg_left (le_of_lt hcoeffT) hc_nonneg
        have hdrop :
            h (t + 1) ≤ h t - ε / (2 * (t + 2 : ℝ)) := by
          have hdrop_aux :
              a t * h t + c t * (ε / 2) ≤ h t - ε / (2 * (t + 2 : ℝ)) := by
            calc
              a t * h t + c t * (ε / 2)
                  = (t : ℝ) * (t + 3 : ℝ) / (t + 2 : ℝ) ^ 2 * h t +
                      (ε / 2) * (t + 3 : ℝ) / (t + 2 : ℝ) ^ 2 := by
                        dsimp [a, c]
                        ring
              _ ≤ h t - ε / (2 * (t + 2 : ℝ)) := by
                    exact frankWolfe_openLoop_drop_bound t
                      (hε := le_of_lt hε) (hH := le_of_lt hgt)
          have hmain : h (t + 1) ≤ a t * h t + c t * (ε / 2) := by
            calc
              h (t + 1) ≤ a t * h t + c t * coeff t := hstep
              _ ≤ a t * h t + c t * (ε / 2) := by linarith [hbeta_le]
          exact le_trans hmain hdrop_aux
        have hfrac :
            ε / (4 * (N0 + 1 : ℝ)) ≤ ε / (2 * (t + 2 : ℝ)) := by
          exact frankWolfe_openLoop_blockFraction_bound
            (hε := le_of_lt hε) htN0
        have hsub :
            h t - ε / (2 * (t + 2 : ℝ)) ≤ h t - ε / (4 * (N0 + 1 : ℝ)) := by
          linarith
        exact le_trans hdrop hsub
    refine ⟨T, M0, ε / 4, by linarith, hbounded T, hstable, ?_⟩
    have hNseq_succ : ∀ j, 2 ^ (j + 1) * (T + 1) - 1 = 2 * (2 ^ j * (T + 1) - 1) + 1 :=
      nseq_succ T
    have hNseq_ge : ∀ j, T ≤ 2 ^ j * (T + 1) - 1 :=
      nseq_ge T
    have htail_above : ∀ {p t : ℕ}, T ≤ t → t ≤ p → ε < h p → ε < h t :=
      fun htT htp hpgt => tail_above_of_stable hstable htT htp hpgt
    intro k n hkn hngt
    let Nk : ℕ := 2 ^ k * (T + 1) - 1
    have hNk_succ : 2 ^ (k + 1) * (T + 1) - 1 = 2 * Nk + 1 := hNseq_succ k
    have hNk_ge : T ≤ Nk := hNseq_ge k
    have hablock : ∀ t, Nk ≤ t → t ≤ 2 * Nk → ε < h t := by
      intro t hlow hhigh
      have htn : t ≤ n := by rw [hNk_succ] at hkn; omega
      exact htail_above (le_trans hNk_ge hlow) htn hngt
    have hstepblock :
        ∀ t, Nk ≤ t → t ≤ 2 * Nk →
          ε / (4 * (↑Nk + 1 : ℝ)) ≤ h t - h (t + 1) := by
      intro t hlow hhigh
      linarith [habove_drop Nk t hNk_ge hlow hhigh (hablock t hlow hhigh)]
    have hdrop' :=
      block_drop_of_step_drop (h := h) (ε := ε) (N := Nk) hstepblock
    simpa [hNk_succ] using hdrop'

/-- Canonical open-loop boosted convergence under the local dual sharpness
condition, with no uniqueness assumption: compare to a nearest minimizer
sequence in the optimal level set. -/
theorem frankWolfe_localGap_boosted_convergence_of_minimizer
    (hC_convex : Convex ℝ C)
    {A : ℝ} {q : ℝ} (hq : q = 2 ∨ 2 < q) (hA : 0 < A)
    (f : E → ℝ) (f' : E → E) (L : NNReal) (hL : 0 < L)
    (hConv : IsFirstOrderConvex f f')
    (hSmooth : IsLipschitzSmoothUpperBound f L f')
    {x_star : E} (hx_star : x_star ∈ C)
    (hLocal :
      HasLocalLMOGapPowerOn
        O (C ∩ {y : E | f y = f x_star}) A q)
    (hmin : ∀ y ∈ C, f x_star ≤ f y)
    {x0 : E} (hx0 : x0 ∈ C) :
    Tendsto
      (fun t : ℕ =>
        (t + 2 : ℝ) *
          (f (frankWolfeSequence O f' x0 t) - f x_star))
      atTop (nhds 0) := by
  let xSeq : ℕ → E := frankWolfeSequence O f' x0
  let F : ℕ → ℝ := fun t => f (xSeq t) - f x_star
  let M : Set E := C ∩ {y : E | f y = f x_star}
  have hcont : Continuous f :=
    continuous_of_isFirstOrderConvex_isLipschitzSmoothUpperBound (f := f) (f' := f') (L := L) hConv hSmooth
  have hlevel_closed : IsClosed {y : E | f y = f x_star} :=
    isClosed_eq hcont continuous_const
  have hM_compact : IsCompact M := by
    simpa [M] using O.isCompact.inter_right hlevel_closed
  have hM_nonempty : M.Nonempty := by
    refine ⟨x_star, ?_⟩
    simp [M, hx_star]
  have hxSeq : ∀ t, xSeq t ∈ C := by
    intro t
    simpa [xSeq] using
      frankWolfeSequence_mem
        (O := O)
        hC_convex f' hx0 t
  have hgap_zero :
      Tendsto F atTop (nhds 0) := by
    simpa [F, xSeq] using
      frankWolfe_gap_tendsto_zero_of_isMinOn
        (O := O)
        hC_convex f f' L hConv hSmooth hx_star hmin hx0
  have hdist_zero :
      Tendsto (fun t => Metric.infDist (xSeq t) M) atTop (nhds 0) := by
    simpa [xSeq, M] using
      tendsto_infDist_minimizerSet_of_gap_tendsto_zero
        O.isCompact (f := f) (f' := f') (L := L) hConv hSmooth x_star xSeq hxSeq
        (by simpa [F] using hgap_zero)
  let pSeq : ℕ → E := nearestPoint hM_compact hM_nonempty ∘ xSeq
  have hpSeq_memM : ∀ t, pSeq t ∈ M :=
      fun t => nearestPoint_mem hM_compact hM_nonempty (xSeq t)
  have hpSeq_dist : ∀ t, Metric.infDist (xSeq t) M = dist (xSeq t) (pSeq t) :=
      fun t => infDist_nearestPoint hM_compact hM_nonempty (xSeq t)
  have hδ_zero' : Filter.Tendsto (fun t => dist (xSeq t) (pSeq t)) Filter.atTop (nhds 0) :=
      tendsto_dist_nearestPoint_of_tendsto_infDist hM_compact hM_nonempty hdist_zero
  have hpSeq_mem : ∀ t, pSeq t ∈ C := fun t => (hpSeq_memM t).1
  have hpSeq_val : ∀ t, f (pSeq t) = f x_star := fun t => (hpSeq_memM t).2
  have hpSeq_min : ∀ t, ∀ y ∈ C, f (pSeq t) ≤ f y := fun t y hy => by
    linarith [hmin y hy, hpSeq_val t]
  have hδ_zero : Tendsto (fun t => ‖xSeq t - pSeq t‖) atTop (nhds 0) :=
    hδ_zero'.congr (fun t => dist_eq_norm _ _)
  simpa [xSeq] using
    frankWolfe_localGap_boosted_convergence_of_minimizerSequence_tendsto_zero
      (O := O)
      hC_convex hq hA f f' L hL hConv hSmooth x_star hLocal
      pSeq hpSeq_mem hpSeq_memM hpSeq_val hpSeq_min hx0 hδ_zero

/-- Zero-gradient wrapper for the canonical local open-loop theorem. -/
theorem frankWolfe_localGap_boosted_convergence_of_zeroGradient_minimizer
    (hC_convex : Convex ℝ C)
    {A : ℝ} {q : ℝ} (hq : q = 2 ∨ 2 < q) (hA : 0 < A)
    (f : E → ℝ) (f' : E → E) (L : NNReal) (hL : 0 < L)
    (hConv : IsFirstOrderConvex f f')
    (hSmooth : IsLipschitzSmoothUpperBound f L f')
    {x_star : E} (hx_star : x_star ∈ C) (hgrad : f' x_star = 0)
    (hLocal :
      HasLocalLMOGapPowerOn
        O (C ∩ {y : E | f y = f x_star}) A q)
    {x0 : E} (hx0 : x0 ∈ C) :
    Tendsto
      (fun t : ℕ =>
        (t + 2 : ℝ) *
          (f (frankWolfeSequence O f' x0 t) - f x_star))
      atTop (nhds 0) := by
  exact
    frankWolfe_localGap_boosted_convergence_of_minimizer
      (O := O)
      hC_convex hq hA f f' L hL hConv hSmooth hx_star hLocal
      (fun y _hy =>
        by
          have hgap_nonneg :=
            primalGap_nonneg_of_zero_gradient
              (f := f) (f' := f') hConv
              (x := y) (x_star := x_star) hgrad
          linarith)
      hx0

set_option maxHeartbeats 600000 in
/-- The open-loop family `γ_t = ell / (t + ell)` with `ell ≥ 2` satisfies the
boosted theorem under the local quadratic (`q = 2`) dual sharpness condition,
once the iterates approach a varying feasible minimizer sequence. -/
theorem frankWolfe_localGap_two_openLoop_boosted_convergence_of_minimizerSequence_tendsto_zero
    (hC_convex : Convex ℝ C)
    {ell : ℕ} (hell : 2 ≤ ell)
    {A : ℝ} (hA : 0 < A)
    (f : E → ℝ) (f' : E → E) (L : NNReal) (hL : 0 < L)
    (hConv : IsFirstOrderConvex f f')
    (hSmooth : IsLipschitzSmoothUpperBound f L f')
    (x_star : E)
    (hLocal :
      HasLocalLMOGapPowerOn
        O (C ∩ {y : E | f y = f x_star}) A 2)
    (xStarSeq : ℕ → E)
    (hxStarSeq : ∀ t, xStarSeq t ∈ C)
    (hvalSeq : ∀ t, f (xStarSeq t) = f x_star)
    (hminSeq : ∀ t, ∀ y ∈ C, f (xStarSeq t) ≤ f y)
    {x0 : E} (hx0 : x0 ∈ C)
    (hδ_zero :
      Tendsto
        (fun t => ‖frankWolfeOpenLoopSequence O ell f' x0 t - xStarSeq t‖)
        atTop (nhds 0)) :
    Tendsto
      (fun t : ℕ =>
        (t + ell : ℝ) *
          (f (frankWolfeOpenLoopSequence O ell f' x0 t) - f x_star))
      atTop (nhds 0) := by
  let xSeq : ℕ → E := frankWolfeOpenLoopSequence O ell f' x0
  let F : ℕ → ℝ := fun t => f (xSeq t) - f x_star
  let δ : ℕ → ℝ := fun t => ‖xSeq t - xStarSeq t‖
  let h : ℕ → ℝ := fun t => (t + ell : ℝ) * F t
  let Dsq : ℝ := (Metric.diam C) ^ 2
  let M0 : ℝ := (ell : ℝ) * max (f x0 - f x_star) ((L : ℝ) * Dsq)
  let Ksmall : ℝ := 2 * (ell : ℝ) * (L : ℝ) / A
  let a : ℕ → ℝ := fun t => (t : ℝ) * (t + ell + 1 : ℝ) / (t + ell : ℝ) ^ 2
  let c : ℕ → ℝ := fun t => (t + ell + 1 : ℝ) / (t + ell : ℝ) ^ 2
  let coeff : ℕ → ℝ := fun t => ((ell : ℝ) ^ 2) * (L : ℝ) * (δ t) ^ 2
  let stdConst : ℕ → ℝ :=
    fun t => (((ell : ℝ) ^ 2) / 2) * (L : ℝ) * Dsq * (t + ell + 1 : ℝ) / (t + ell : ℝ) ^ 2
  let Mset : Set E := C ∩ {y : E | f y = f x_star}
  have hell1 : 1 ≤ ell := by omega
  have hell_pos : (0 : ℝ) < ell := by
    exact_mod_cast (show 0 < ell by omega)
  have hKsmall_nonneg : 0 ≤ Ksmall := by
    dsimp [Ksmall]
    positivity
  have hF_nonneg : ∀ t, 0 ≤ F t := by
    intro t
    have hgap_t :
        0 ≤ f (xSeq t) - f (xStarSeq t) := by
      exact
        primalGap_nonneg_of_isMinOn
          (C := C) (f := f)
          (frankWolfeOpenLoopSequence_mem
            (O := O)
            hC_convex hell1 f' hx0 t)
          (hminSeq t)
    simpa [F, hvalSeq t] using hgap_t
  have hgap_grad : ∀ t, F t ≤ ‖f' (xSeq t)‖ * δ t := by
    intro t
    have hgap_t :
        f (xSeq t) - f (xStarSeq t) ≤ ‖f' (xSeq t)‖ * ‖xSeq t - xStarSeq t‖ := by
      simpa [xSeq] using
        (primalGap_le_gradNorm_mul_dist
          (f := f) (f' := f') hConv
          (x := xSeq t) (x_star := xStarSeq t))
    simpa [F, δ, hvalSeq t] using hgap_t
  have hsmall_or_refined :
      ∀ t,
        h t ≤ Ksmall * δ t ∨
          F (t + 1) ≤
            (1 - (ell : ℝ) / (t + ell : ℝ)) * F t +
              (L : ℝ) * ((ell : ℝ) / (t + ell : ℝ)) ^ 2 * (δ t) ^ 2 := by
    intro t
    by_cases hFt0 : F t = 0
    · left
      have hδ_nonneg : 0 ≤ δ t := by
        dsimp [δ]
        positivity
      simpa [h, hFt0] using (mul_nonneg hKsmall_nonneg hδ_nonneg)
    · by_cases hcase :
        openLoopStepSize ell t ≤ A * ‖f' (xSeq t)‖ / (2 * (L : ℝ))
      · right
        have hxStarSeqM : xStarSeq t ∈ Mset := by
          simp [Mset, hxStarSeq t, hvalSeq t]
        have hγ_mem : openLoopStepSize ell t ∈ Set.Icc (0 : ℝ) 1 :=
          openLoopStepSize_mem_Icc hell1 t
        have href :
            f (frankWolfeStep O f' (xSeq t) (openLoopStepSize ell t)) -
                f (xStarSeq t) ≤
              (1 - openLoopStepSize ell t) * (f (xSeq t) - f (xStarSeq t)) +
                (L : ℝ) * (openLoopStepSize ell t) ^ 2 * ‖xSeq t - xStarSeq t‖ ^ 2 := by
          simpa [xSeq, δ, openLoopStepSize] using
            (frankWolfeStep_gap_bound_with_localCorrection_two
              (O := O)
              hLocal
              f f' L hConv hSmooth
              (x := xSeq t) (x_star := xStarSeq t) (hxStarSeq t) hxStarSeqM
              (γ := openLoopStepSize ell t) hγ_mem hcase)
        simpa [F, xSeq, frankWolfeOpenLoopSequence, openLoopStepSize, hvalSeq t] using href
      · left
        have hδ_pos_t : 0 < δ t := by
          by_contra hδt
          have hδ0 : δ t = 0 := le_antisymm (not_lt.mp hδt) (norm_nonneg _)
          have hxeq : xSeq t = xStarSeq t := by
            exact sub_eq_zero.mp (norm_eq_zero.mp (by simpa [δ] using hδ0))
          have : F t = 0 := by simp [F, hxeq, hvalSeq t]
          exact hFt0 this
        have hcase' :
            A * ‖f' (xSeq t)‖ / (2 * (L : ℝ)) < openLoopStepSize ell t := lt_of_not_ge hcase
        have hmul :
            A * ‖f' (xSeq t)‖ < (openLoopStepSize ell t) * (2 * (L : ℝ)) := by
          exact (_root_.div_lt_iff₀ (show 0 < 2 * (L : ℝ) by positivity)).1 hcase'
        have hgrad_lt :
            ‖f' (xSeq t)‖ < ((openLoopStepSize ell t) * (2 * (L : ℝ))) / A := by
          have : ‖f' (xSeq t)‖ * A < (openLoopStepSize ell t) * (2 * (L : ℝ)) := by
            simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
          exact (_root_.lt_div_iff₀ hA).2 this
        have hsmall' :
            F t < (((openLoopStepSize ell t) * (2 * (L : ℝ))) / A) * δ t := by
          exact lt_of_le_of_lt (hgap_grad t) <|
            mul_lt_mul_of_pos_right hgrad_lt hδ_pos_t
        have hscaled :
            h t < Ksmall * δ t := by
          dsimp [h, Ksmall]
          have hden_pos : (0 : ℝ) < t + ell := by
            exact_mod_cast (show 0 < t + ell by omega)
          have hEq :
              (t + ell : ℝ) *
                ((((openLoopStepSize ell t) * (2 * (L : ℝ))) / A) * δ t) =
                  ((2 * (ell : ℝ) * (L : ℝ)) / A) * δ t := by
            dsimp [openLoopStepSize]
            field_simp [hA.ne', hden_pos.ne']
          have hmul' :
              (t + ell : ℝ) * F t <
                (t + ell : ℝ) *
                  ((((openLoopStepSize ell t) * (2 * (L : ℝ))) / A) * δ t) := by
            exact mul_lt_mul_of_pos_left hsmall' hden_pos
          simpa [hEq] using hmul'
        exact le_of_lt hscaled
  have hstd_step :
      ∀ t,
        F (t + 1) ≤
          (1 - (ell : ℝ) / (t + ell : ℝ)) * F t +
            ((L : ℝ) / 2) * ((ell : ℝ) / (t + ell : ℝ)) ^ 2 * Dsq := by
    intro t
    have href :
        f (frankWolfeStep O f'
              (xSeq t) (openLoopStepSize ell t)) -
            f (xStarSeq t) ≤
          (1 - (ell : ℝ) / (t + ell : ℝ)) * (f (xSeq t) - f (xStarSeq t)) +
            ((L : ℝ) / 2) * ((ell : ℝ) / (t + ell : ℝ)) ^ 2 * Dsq := by
      simpa [xSeq, Dsq, openLoopStepSize] using
        (frankWolfeStep_gap_bound
          (O := O)
          (C := C) (f := f) (f' := f') (L := L) hSmooth hConv
          (x := xSeq t) (x_star := xStarSeq t)
          (frankWolfeOpenLoopSequence_mem
            (O := O)
            hC_convex hell1 f' hx0 t)
          (hxStarSeq t)
          (γ := openLoopStepSize ell t)
          (openLoopStepSize_mem_Icc hell1 t))
    simpa [F, xSeq, frankWolfeOpenLoopSequence, hvalSeq t] using href
  have hstd_bound :
      ∀ t, F t ≤ M0 / (t + ell : ℝ) := by
    intro t
    let B : ℝ := max (f x0 - f (xStarSeq 0)) ((L : ℝ) * Dsq)
    have hB_nonneg : 0 ≤ B := by
      have hgap0_nonneg : 0 ≤ f x0 - f (xStarSeq 0) := by
        exact primalGap_nonneg_of_isMinOn (C := C) (f := f) hx0 (hminSeq 0)
      exact le_trans hgap0_nonneg (le_max_left _ _)
    have hfw :=
      open_loop_convergence_of_initialGap_le
        (O := O)
        (C := C) hC_convex (ell := ell) hell
        f f' L hSmooth hConv (hxStarSeq 0) hx0
        hB_nonneg (le_max_left _ _) (le_max_right _ _) t
    simpa [B, M0, Dsq, F, xSeq, hvalSeq 0] using hfw
  have hbounded : ∀ t, h t ≤ M0 := by
    intro t
    calc
      h t = (t + ell : ℝ) * F t := by rfl
      _ ≤ (t + ell : ℝ) * (M0 / (t + ell : ℝ)) := by
            gcongr
            exact hstd_bound t
      _ = M0 := by
            have hneq : (t + ell : ℝ) ≠ 0 := by
              have hpos : (0 : ℝ) < t + ell := by
                exact_mod_cast (show 0 < t + ell by omega)
              exact ne_of_gt hpos
            field_simp [hneq]
  have hnonneg_h : ∀ t, 0 ≤ h t := by
    intro t
    dsimp [h]
    exact mul_nonneg (by positivity) (hF_nonneg t)
  apply boosted_convergence_kernel hnonneg_h
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  have hKsmall_event : ∀ᶠ t : ℕ in atTop, Ksmall * δ t < ε / 2 := by
    have hKzero :
        Tendsto (fun t => Ksmall * δ t) atTop (nhds 0) := by
      simpa [δ, Ksmall] using hδ_zero.const_mul Ksmall
    exact hKzero.eventually (Iio_mem_nhds hε2)
  have hδsq_zero : Tendsto (fun t => (δ t) ^ 2) atTop (nhds 0) :=
    by simpa using hδ_zero.pow 2
  have hcoeff_zero : Tendsto coeff atTop (nhds 0) := by
    convert hδsq_zero.const_mul (((ell : ℝ) ^ 2) * (L : ℝ)) using 1
    · ext t
      ring_nf
  have hcoeff_event : ∀ᶠ t : ℕ in atTop, coeff t < ε / 2 := by
    exact hcoeff_zero.eventually (Iio_mem_nhds hε2)
  have hstdconst_zero :
      Tendsto (fun t : ℕ => (((ell : ℝ) ^ 2) * (L : ℝ) * Dsq) / (t + ell : ℝ))
        atTop (nhds 0) :=
    tendsto_const_div_add_atTop_nhds_zero_nat (((ell : ℝ) ^ 2) * (L : ℝ) * Dsq) ell
  have hstdconst_event : ∀ᶠ t : ℕ in atTop, stdConst t < ε / 2 := by
    have hmain := hstdconst_zero.eventually (Iio_mem_nhds hε2)
    filter_upwards [hmain] with t ht
    have hbound_t : stdConst t ≤ (((ell : ℝ) ^ 2) * (L : ℝ) * Dsq) / (t + ell : ℝ) := by
      have hB_nonneg : 0 ≤ (L : ℝ) * Dsq := by positivity
      simpa [stdConst, mul_assoc, mul_left_comm, mul_comm] using
        (openLoop_stdConst_bound hell1 (B := (L : ℝ) * Dsq) hB_nonneg t)
    exact lt_of_le_of_lt hbound_t ht
  have hall :
      ∀ᶠ t : ℕ in atTop,
        Ksmall * δ t < ε / 2 ∧ coeff t < ε / 2 ∧ stdConst t < ε / 2 := by
    filter_upwards [hKsmall_event, hcoeff_event, hstdconst_event] with t h1 h2 h3
    exact ⟨h1, h2, h3⟩
  rcases Filter.Eventually.exists_forall_of_atTop hall with ⟨T, hT⟩
  have hstable :
      ∀ t ≥ T, h t ≤ ε → h (t + 1) ≤ ε := by
    intro t ht hle
    rcases hT t ht with ⟨hsmallT, hcoeffT, hstdT⟩
    rcases hsmall_or_refined t with hleft | hright
    · have hstep : h (t + 1) ≤ a t * h t + stdConst t := by
        have hh_succ : h (t + 1) = (t + ell + 1 : ℝ) * F (t + 1) := by
          change ((((t + 1 : ℕ) : ℝ) + ell) * F (t + 1) = (t + ell + 1 : ℝ) * F (t + 1))
          have hcast : (((t + 1 : ℕ) : ℝ) + ell) = (t + ell + 1 : ℝ) := by
            exact_mod_cast (show t + 1 + ell = t + ell + 1 by omega)
          rw [hcast]
        have hmul := mul_le_mul_of_nonneg_left (hstd_step t) (by positivity : 0 ≤ (t + ell + 1 : ℝ))
        calc
          h (t + 1) = (t + ell + 1 : ℝ) * F (t + 1) := hh_succ
          _ ≤ (t + ell + 1 : ℝ) *
                ((1 - (ell : ℝ) / (t + ell : ℝ)) * F t +
                  ((L : ℝ) / 2) * ((ell : ℝ) / (t + ell : ℝ)) ^ 2 * Dsq) := hmul
          _ = a t * h t + stdConst t := by
                simpa [a, h, stdConst, mul_assoc, mul_left_comm, mul_comm] using
                  (openLoop_scaled_standard_eq hell1 (F := F) (Dsq := Dsq) (L := (L : ℝ)) t)
      have ha_le_one : a t ≤ 1 := by
        simpa [a] using openLoop_coeff_le_one hell1 t
      have hah : a t * h t ≤ h t := by
        simpa using mul_le_mul_of_nonneg_right ha_le_one (hnonneg_h t)
      have hlt : h (t + 1) < ε := by
        linarith
      exact le_of_lt hlt
    · have hstep : h (t + 1) ≤ a t * h t + c t * coeff t := by
        have hh_succ : h (t + 1) = (t + ell + 1 : ℝ) * F (t + 1) := by
          change ((((t + 1 : ℕ) : ℝ) + ell) * F (t + 1) = (t + ell + 1 : ℝ) * F (t + 1))
          have hcast : (((t + 1 : ℕ) : ℝ) + ell) = (t + ell + 1 : ℝ) := by
            exact_mod_cast (show t + 1 + ell = t + ell + 1 by omega)
          rw [hcast]
        have hmul := mul_le_mul_of_nonneg_left hright (by positivity : 0 ≤ (t + ell + 1 : ℝ))
        calc
          h (t + 1) = (t + ell + 1 : ℝ) * F (t + 1) := hh_succ
          _ ≤ (t + ell + 1 : ℝ) *
                ((1 - (ell : ℝ) / (t + ell : ℝ)) * F t +
                  (L : ℝ) * ((ell : ℝ) / (t + ell : ℝ)) ^ 2 * (δ t) ^ 2) := hmul
          _ = a t * h t + c t * coeff t := by
                dsimp [a, h, c, coeff]
                have hneq : (t + ell : ℝ) ≠ 0 := by
                  have hpos : (0 : ℝ) < t + ell := by
                    exact_mod_cast (show 0 < t + ell by omega)
                  exact ne_of_gt hpos
                field_simp [hneq]
                ring
      have hc_nonneg : 0 ≤ c t := by
        dsimp [c]
        exact div_nonneg (by positivity) (by positivity)
      have hcoeff_le : c t * coeff t ≤ c t * (ε / 2) := by
        exact mul_le_mul_of_nonneg_left (le_of_lt hcoeffT) hc_nonneg
      have hmain : h (t + 1) ≤ a t * ε + c t * (ε / 2) := by
        have ha_nonneg : 0 ≤ a t := by
          dsimp [a]
          positivity
        have hah : a t * h t ≤ a t * ε := by
          exact mul_le_mul_of_nonneg_left hle ha_nonneg
        calc
          h (t + 1) ≤ a t * h t + c t * coeff t := hstep
          _ ≤ a t * ε + c t * coeff t := by linarith [hah]
          _ ≤ a t * ε + c t * (ε / 2) := by linarith [hcoeff_le]
      have hcoeff_le_one :
          a t + (1 / 2 : ℝ) * c t ≤ 1 := by
        have hcoeff_le_one' :
            (t : ℝ) * (t + ell + 1 : ℝ) / (t + ell : ℝ) ^ 2 +
              (1 / 2 : ℝ) * (t + ell + 1 : ℝ) / (t + ell : ℝ) ^ 2 ≤ 1 := by
          exact openLoop_refined_coeff_le_one hell t
        dsimp [a, c]
        convert hcoeff_le_one' using 1
        ring
      have hfinal : a t * ε + c t * (ε / 2) ≤ ε := by
        have hscaled' : ε * (a t + (1 / 2 : ℝ) * c t) ≤ ε * 1 := by
          exact mul_le_mul_of_nonneg_left hcoeff_le_one (le_of_lt hε)
        have hscaled : ε * (a t + (1 / 2 : ℝ) * c t) ≤ ε := by
          simpa using hscaled'
        have hEq : a t * ε + c t * (ε / 2) = ε * (a t + (1 / 2 : ℝ) * c t) := by
          ring
        rw [hEq]
        exact hscaled
      exact le_trans hmain hfinal
  have habove_drop :
      ∀ N0 t, T ≤ N0 → N0 ≤ t → t ≤ 2 * N0 → ε < h t →
        h (t + 1) ≤ h t - ε / (4 * (N0 + ell : ℝ)) := by
    intro N0 t hTN hN0 htN0 hgt
    rcases hT t (le_trans hTN hN0) with ⟨hsmallT, hcoeffT, _hstdT⟩
    rcases hsmall_or_refined t with hleft | hright
    · exfalso
      linarith
    · have hstep : h (t + 1) ≤ a t * h t + c t * coeff t := by
        have hh_succ : h (t + 1) = (t + ell + 1 : ℝ) * F (t + 1) := by
          change ((((t + 1 : ℕ) : ℝ) + ell) * F (t + 1) = (t + ell + 1 : ℝ) * F (t + 1))
          have hcast : (((t + 1 : ℕ) : ℝ) + ell) = (t + ell + 1 : ℝ) := by
            exact_mod_cast (show t + 1 + ell = t + ell + 1 by omega)
          rw [hcast]
        have hmul := mul_le_mul_of_nonneg_left hright (by positivity : 0 ≤ (t + ell + 1 : ℝ))
        calc
          h (t + 1) = (t + ell + 1 : ℝ) * F (t + 1) := hh_succ
          _ ≤ (t + ell + 1 : ℝ) *
                ((1 - (ell : ℝ) / (t + ell : ℝ)) * F t +
                  (L : ℝ) * ((ell : ℝ) / (t + ell : ℝ)) ^ 2 * (δ t) ^ 2) := hmul
          _ = a t * h t + c t * coeff t := by
                dsimp [a, h, c, coeff]
                have hneq : (t + ell : ℝ) ≠ 0 := by
                  have hpos : (0 : ℝ) < t + ell := by
                    exact_mod_cast (show 0 < t + ell by omega)
                  exact ne_of_gt hpos
                field_simp [hneq]
                ring
      have hc_nonneg : 0 ≤ c t := by
        dsimp [c]
        exact div_nonneg (by positivity) (by positivity)
      have hcoeff_le : c t * coeff t ≤ c t * (ε / 2) := by
        exact mul_le_mul_of_nonneg_left (le_of_lt hcoeffT) hc_nonneg
      have hdrop :
          h (t + 1) ≤ h t - ε / (2 * (t + ell : ℝ)) := by
        have hdrop_aux :
            a t * h t + c t * (ε / 2) ≤ h t - ε / (2 * (t + ell : ℝ)) := by
          calc
            a t * h t + c t * (ε / 2)
                = (t : ℝ) * (t + ell + 1 : ℝ) / (t + ell : ℝ) ^ 2 * h t +
                    (ε / 2) * (t + ell + 1 : ℝ) / (t + ell : ℝ) ^ 2 := by
                      dsimp [a, c]
                      ring
            _ ≤ h t - ε / (2 * (t + ell : ℝ)) := by
                  exact openLoop_drop_bound hell t
                    (heps := le_of_lt hε) (hH := le_of_lt hgt)
        have hmain : h (t + 1) ≤ a t * h t + c t * (ε / 2) := by
          calc
            h (t + 1) ≤ a t * h t + c t * coeff t := hstep
            _ ≤ a t * h t + c t * (ε / 2) := by linarith [hcoeff_le]
        exact le_trans hmain hdrop_aux
      have hfrac :
          ε / (4 * (N0 + ell : ℝ)) ≤ ε / (2 * (t + ell : ℝ)) := by
        exact openLoop_blockFraction_bound hell1
          (heps := le_of_lt hε) htN0
      have hsub :
          h t - ε / (2 * (t + ell : ℝ)) ≤ h t - ε / (4 * (N0 + ell : ℝ)) := by
        linarith
      exact le_trans hdrop hsub
  refine ⟨T, M0, ε / (4 * ell : ℝ), by exact div_pos hε (by positivity), hbounded T, hstable, ?_⟩
  have hNseq_succ : ∀ j, 2 ^ (j + 1) * (T + 1) - 1 = 2 * (2 ^ j * (T + 1) - 1) + 1 :=
    nseq_succ T
  have hNseq_ge : ∀ j, T ≤ 2 ^ j * (T + 1) - 1 :=
    nseq_ge T
  have htail_above : ∀ {p t : ℕ}, T ≤ t → t ≤ p → ε < h p → ε < h t :=
    fun htT htp hpgt => tail_above_of_stable hstable htT htp hpgt
  intro k n hkn hngt
  let Nk : ℕ := 2 ^ k * (T + 1) - 1
  have hNk_succ : 2 ^ (k + 1) * (T + 1) - 1 = 2 * Nk + 1 := hNseq_succ k
  have hNk_ge : T ≤ Nk := hNseq_ge k
  have hablock : ∀ t, Nk ≤ t → t ≤ 2 * Nk → ε < h t := by
    intro t hlow hhigh
    have htn : t ≤ n := by rw [hNk_succ] at hkn; omega
    exact htail_above (le_trans hNk_ge hlow) htn hngt
  have hdrop :=
    block_drop_of_step_drop_openLoop (h := h) (N := Nk) hell1 (le_of_lt hε)
      (fun t hlow hhigh => by
        linarith [habove_drop Nk t hNk_ge hlow hhigh (hablock t hlow hhigh)])
  simpa [hNk_succ] using hdrop

set_option maxHeartbeats 600000 in
/-- The open-loop family `γ_t = ell / (t + ell)` with `ell ≥ 2` satisfies the
boosted theorem under the local dual sharpness condition for exponents
`q > 2`, once the iterates approach a varying feasible minimizer sequence. -/
theorem frankWolfe_localGap_openLoop_boosted_convergence_of_minimizerSequence_tendsto_zero_of_two_lt
    (hC_convex : Convex ℝ C)
    {ell : ℕ} (hell : 2 ≤ ell)
    {A : ℝ} {q : ℝ} (hq : 2 < q) (hA : 0 < A)
    (f : E → ℝ) (f' : E → E) (L : NNReal) (hL : 0 < L)
    (hConv : IsFirstOrderConvex f f')
    (hSmooth : IsLipschitzSmoothUpperBound f L f')
    (x_star : E)
    (hLocal :
      HasLocalLMOGapPowerOn
        O (C ∩ {y : E | f y = f x_star}) A q)
    (xStarSeq : ℕ → E)
    (hxStarSeq : ∀ t, xStarSeq t ∈ C)
    (hvalSeq : ∀ t, f (xStarSeq t) = f x_star)
    (hminSeq : ∀ t, ∀ y ∈ C, f (xStarSeq t) ≤ f y)
    {x0 : E} (hx0 : x0 ∈ C)
    (hδ_zero :
      Tendsto
        (fun t => ‖frankWolfeOpenLoopSequence O ell f' x0 t - xStarSeq t‖)
        atTop (nhds 0)) :
    Tendsto
      (fun t : ℕ =>
        (t + ell : ℝ) *
          (f (frankWolfeOpenLoopSequence O ell f' x0 t) - f x_star))
      atTop (nhds 0) := by
  let xSeq : ℕ → E := frankWolfeOpenLoopSequence O ell f' x0
  let F : ℕ → ℝ := fun t => f (xSeq t) - f x_star
  let δ : ℕ → ℝ := fun t => ‖xSeq t - xStarSeq t‖
  let h : ℕ → ℝ := fun t => (t + ell : ℝ) * F t
  let Dsq : ℝ := (Metric.diam C) ^ 2
  let M0 : ℝ := (ell : ℝ) * max (f x0 - f x_star) ((L : ℝ) * Dsq)
  let a : ℕ → ℝ := fun t => (t : ℝ) * (t + ell + 1 : ℝ) / (t + ell : ℝ) ^ 2
  let c : ℕ → ℝ := fun t => (t + ell + 1 : ℝ) / (t + ell : ℝ) ^ 2
  let stdConst : ℕ → ℝ :=
    fun t => (((ell : ℝ) ^ 2) / 2) * (L : ℝ) * Dsq * (t + ell + 1 : ℝ) / (t + ell : ℝ) ^ 2
  let betaExp : ℝ := 2 / (q - 2 : ℝ)
  let Mset : Set E := C ∩ {y : E | f y = f x_star}
  have hell1 : 1 ≤ ell := by omega
  have hell_pos : (0 : ℝ) < ell := by
    exact_mod_cast (show 0 < ell by omega)
  have hq_pos : 0 < q := by linarith
  have hq_sub_pos : 0 < (q - 2 : ℝ) := by
    nlinarith
  have hbeta_nonneg : 0 ≤ betaExp := by
    dsimp [betaExp]
    positivity
  have hbeta_pos : 0 < betaExp := by
    dsimp [betaExp]
    positivity
  have hF_nonneg : ∀ t, 0 ≤ F t := by
    intro t
    have hgap_t :
        0 ≤ f (xSeq t) - f (xStarSeq t) := by
      exact
        primalGap_nonneg_of_isMinOn
          (C := C) (f := f)
          (frankWolfeOpenLoopSequence_mem
            (O := O)
            hC_convex hell1 f' hx0 t)
          (hminSeq t)
    simpa [F, hvalSeq t] using hgap_t
  have hstd_step :
      ∀ t,
        F (t + 1) ≤
          (1 - (ell : ℝ) / (t + ell : ℝ)) * F t +
            ((L : ℝ) / 2) * ((ell : ℝ) / (t + ell : ℝ)) ^ 2 * Dsq := by
    intro t
    have href :
        f (frankWolfeStep O f'
              (xSeq t) (openLoopStepSize ell t)) -
            f (xStarSeq t) ≤
          (1 - (ell : ℝ) / (t + ell : ℝ)) * (f (xSeq t) - f (xStarSeq t)) +
            ((L : ℝ) / 2) * ((ell : ℝ) / (t + ell : ℝ)) ^ 2 * Dsq := by
      simpa [xSeq, Dsq, openLoopStepSize] using
        (frankWolfeStep_gap_bound
          (O := O)
          (C := C) (f := f) (f' := f') (L := L) hSmooth hConv
          (x := xSeq t) (x_star := xStarSeq t)
          (frankWolfeOpenLoopSequence_mem
            (O := O)
            hC_convex hell1 f' hx0 t)
          (hxStarSeq t)
          (γ := openLoopStepSize ell t)
          (openLoopStepSize_mem_Icc hell1 t))
    simpa [F, xSeq, frankWolfeOpenLoopSequence, hvalSeq t] using href
  have hstd_bound :
      ∀ t, F t ≤ M0 / (t + ell : ℝ) := by
    intro t
    let B : ℝ := max (f x0 - f (xStarSeq 0)) ((L : ℝ) * Dsq)
    have hB_nonneg : 0 ≤ B := by
      have hgap0_nonneg : 0 ≤ f x0 - f (xStarSeq 0) := by
        exact primalGap_nonneg_of_isMinOn (C := C) (f := f) hx0 (hminSeq 0)
      exact le_trans hgap0_nonneg (le_max_left _ _)
    have hfw :=
      open_loop_convergence_of_initialGap_le
        (O := O)
        (C := C) hC_convex (ell := ell) hell
        f f' L hSmooth hConv (hxStarSeq 0) hx0
        hB_nonneg (le_max_left _ _) (le_max_right _ _) t
    simpa [B, M0, Dsq, F, xSeq, hvalSeq 0] using hfw
  have hbounded : ∀ t, h t ≤ M0 := by
    intro t
    calc
      h t = (t + ell : ℝ) * F t := by rfl
      _ ≤ (t + ell : ℝ) * (M0 / (t + ell : ℝ)) := by
            gcongr
            exact hstd_bound t
      _ = M0 := by
            have hneq : (t + ell : ℝ) ≠ 0 := by
              have hpos : (0 : ℝ) < t + ell := by
                exact_mod_cast (show 0 < t + ell by omega)
              exact ne_of_gt hpos
            field_simp [hneq]
  have hnonneg_h : ∀ t, 0 ≤ h t := by
    intro t
    dsimp [h]
    exact mul_nonneg (by positivity) (hF_nonneg t)
  apply boosted_convergence_kernel hnonneg_h
  intro ε hε
  let Csmall : ℝ := 8 * (ell : ℝ) * (L : ℝ) / (q * A * ε)
  let Rconst : ℝ := ((q - 2 : ℝ) / q) * (L : ℝ) * Csmall ^ betaExp
  let coeff : ℕ → ℝ :=
    fun t => ((ell : ℝ) ^ 2) * (L : ℝ) * (δ t) ^ 2 + ((ell : ℝ) ^ 2) * Rconst * (δ t) ^ betaExp
  have hε2 : 0 < ε / 2 := by linarith
  have hδsq_zero : Tendsto (fun t => (δ t) ^ 2) atTop (nhds 0) := by
    simpa using hδ_zero.pow 2
  have hδbeta_zero : Tendsto (fun t => (δ t) ^ betaExp) atTop (nhds 0) :=
    tendsto_rpow_const_zero hδ_zero hbeta_pos
  have hcoeff_zero : Tendsto coeff atTop (nhds 0) := by
    have hleft :
        Tendsto (fun t => ((ell : ℝ) ^ 2) * (L : ℝ) * (δ t) ^ 2) atTop (nhds 0) := by
      convert hδsq_zero.const_mul (((ell : ℝ) ^ 2) * (L : ℝ)) using 1
      · ext t
        ring_nf
    have hright :
        Tendsto (fun t => ((ell : ℝ) ^ 2) * Rconst * (δ t) ^ betaExp) atTop (nhds 0) := by
      convert hδbeta_zero.const_mul (((ell : ℝ) ^ 2) * Rconst) using 1
      · ext t
        ring_nf
    simpa [coeff] using hleft.add hright
  have hstdconst_zero : Tendsto (fun t : ℕ => (((ell : ℝ) ^ 2) * (L : ℝ) * Dsq) / (t + ell : ℝ)) atTop (nhds 0) :=
    tendsto_const_div_add_atTop_nhds_zero_nat (((ell : ℝ) ^ 2) * (L : ℝ) * Dsq) ell
  have hstdconst_event : ∀ᶠ t : ℕ in atTop, stdConst t < ε / 2 := by
    have hmain := hstdconst_zero.eventually (Iio_mem_nhds hε2)
    filter_upwards [hmain] with t ht
    have hbound_t : stdConst t ≤ (((ell : ℝ) ^ 2) * (L : ℝ) * Dsq) / (t + ell : ℝ) := by
      have hB_nonneg : 0 ≤ (L : ℝ) * Dsq := by positivity
      simpa [stdConst, mul_assoc, mul_left_comm, mul_comm] using
        (openLoop_stdConst_bound hell1 (B := (L : ℝ) * Dsq) hB_nonneg t)
    exact lt_of_le_of_lt hbound_t ht
  have hcoeff_event : ∀ᶠ t : ℕ in atTop, coeff t < ε / 2 := by
    exact hcoeff_zero.eventually (Iio_mem_nhds hε2)
  have hall :
      ∀ᶠ t : ℕ in atTop, coeff t < ε / 2 ∧ stdConst t < ε / 2 := by
    filter_upwards [hcoeff_event, hstdconst_event] with t h1 h2
    exact ⟨h1, h2⟩
  rcases Filter.Eventually.exists_forall_of_atTop hall with ⟨T, hT⟩
  have hsmall_or_refined :
      ∀ t,
        h t ≤ ε / 2 ∨
          F (t + 1) ≤
            (1 - (ell : ℝ) / (t + ell : ℝ)) * F t +
              (L : ℝ) * ((ell : ℝ) / (t + ell : ℝ)) ^ 2 * (δ t) ^ 2 +
              Rconst * ((ell : ℝ) / (t + ell : ℝ)) ^ 2 * (δ t) ^ betaExp := by
    intro t
    by_cases hFt0 : F t = 0
    · left
      have hnonneg : 0 ≤ ε / 2 := by linarith
      simpa [h, hFt0] using hnonneg
    · have hF_pos_t : 0 < F t := lt_of_le_of_ne (hF_nonneg t) (by simpa [eq_comm] using hFt0)
      have hδ_pos_t : 0 < δ t := by
        by_contra hδt
        have hδ0 : δ t = 0 := le_antisymm (not_lt.mp hδt) (norm_nonneg _)
        have hxeq : xSeq t = xStarSeq t := by
          exact sub_eq_zero.mp (norm_eq_zero.mp (by simpa [δ] using hδ0))
        have : F t = 0 := by simp [F, hxeq, hvalSeq t]
        exact hFt0 this
      let γt : ℝ := openLoopStepSize ell t
      let lamT : ℝ := 4 * (L : ℝ) * γt * δ t / (q * A * F t)
      have hγ_mem : γt ∈ Set.Icc (0 : ℝ) 1 := openLoopStepSize_mem_Icc hell1 t
      have hγ_pos : 0 < γt := by
        dsimp [γt, openLoopStepSize]
        have hden : (0 : ℝ) < t + ell := by
          exact_mod_cast (show 0 < t + ell by omega)
        exact div_pos hell_pos hden
      by_cases hcase : lamT ≤ Csmall * δ t
      · right
        have hF_seq_pos : 0 < f (xSeq t) - f (xStarSeq t) := by
          simpa [F, hvalSeq t] using hF_pos_t
        have hxStarSeqM : xStarSeq t ∈ Mset := by
          simp [Mset, hxStarSeq t, hvalSeq t]
        have href :
            f (frankWolfeStep O f' (xSeq t) γt) - f (xStarSeq t) ≤
              (1 - γt) * (f (xSeq t) - f (xStarSeq t)) +
                (L : ℝ) * γt ^ 2 * ‖xSeq t - xStarSeq t‖ ^ 2 +
                ((q - 2 : ℝ) / q) * (L : ℝ) * γt ^ 2 *
                  lamT ^ ((2 : ℝ) / (q - 2 : ℝ)) := by
          simpa [xSeq, γt, δ, F, lamT, hvalSeq t] using
            (frankWolfeStep_gap_bound_with_localCorrection
              (O := O)
              (hq := hq) hA hLocal
              f f' L hConv hSmooth
              (x := xSeq t) (x_star := xStarSeq t)
              (hxStarSeq t) hxStarSeqM hγ_mem hγ_pos hF_seq_pos hδ_pos_t)
        have hlam_pow :
            lamT ^ betaExp ≤ (Csmall * δ t) ^ betaExp := by
          exact Real.rpow_le_rpow (by positivity) hcase hbeta_nonneg
        have hlam_pow' :
            lamT ^ betaExp ≤ Csmall ^ betaExp * (δ t) ^ betaExp := by
          calc
            lamT ^ betaExp ≤ (Csmall * δ t) ^ betaExp := hlam_pow
            _ = Csmall ^ betaExp * (δ t) ^ betaExp := by
                  exact Real.mul_rpow (by positivity) (by positivity)
        have hres_le :
            ((q - 2 : ℝ) / q) * (L : ℝ) * γt ^ 2 * lamT ^ betaExp ≤
              Rconst * γt ^ 2 * (δ t) ^ betaExp := by
          calc
            ((q - 2 : ℝ) / q) * (L : ℝ) * γt ^ 2 * lamT ^ betaExp
                ≤ ((q - 2 : ℝ) / q) * (L : ℝ) * γt ^ 2 *
                    (Csmall ^ betaExp * (δ t) ^ betaExp) := by
                      exact mul_le_mul_of_nonneg_left hlam_pow'
                        (by positivity :
                          0 ≤ ((q - 2 : ℝ) / q) * (L : ℝ) * γt ^ 2)
            _ = Rconst * γt ^ 2 * (δ t) ^ betaExp := by
                  dsimp [Rconst]
                  ring
        have href' :
            F (t + 1) ≤
              (1 - (ell : ℝ) / (t + ell : ℝ)) * F t +
                (L : ℝ) * ((ell : ℝ) / (t + ell : ℝ)) ^ 2 * (δ t) ^ 2 +
                ((q - 2 : ℝ) / q) * (L : ℝ) * γt ^ 2 * lamT ^ betaExp := by
          simpa [F, xSeq, frankWolfeOpenLoopSequence, γt, openLoopStepSize, δ, hvalSeq t] using href
        have hres_le' :
            ((q - 2 : ℝ) / q) * (L : ℝ) * γt ^ 2 * lamT ^ betaExp ≤
              Rconst * ((ell : ℝ) / (t + ell : ℝ)) ^ 2 * (δ t) ^ betaExp := by
          simpa [γt, openLoopStepSize] using hres_le
        linarith
      · left
        have hcase' : Csmall * δ t < lamT := lt_of_not_ge hcase
        have hlam_repr :
            lamT = (4 * (L : ℝ) * γt / (q * A * F t)) * δ t := by
          dsimp [lamT]
          field_simp [hF_pos_t.ne']
        rw [hlam_repr] at hcase'
        have hdiv :
            Csmall < 4 * (L : ℝ) * γt / (q * A * F t) := by
          exact lt_of_mul_lt_mul_right hcase' hδ_pos_t.le
        have hF_bound :
            F t < 4 * (L : ℝ) * γt / (q * A * Csmall) := by
          have hden_pos : 0 < q * A * Csmall := by
            dsimp [Csmall]
            positivity
          have hmul : F t * (q * A * Csmall) < 4 * (L : ℝ) * γt := by
            have hmul' : Csmall * (q * A * F t) < 4 * (L : ℝ) * γt := by
              exact (_root_.lt_div_iff₀ (show 0 < q * A * F t by positivity)).1 hdiv
            simpa [mul_assoc, mul_left_comm, mul_comm] using hmul'
          exact (_root_.lt_div_iff₀ hden_pos).2 hmul
        have hEq :
            4 * (L : ℝ) * γt / (q * A * Csmall) = ε / (2 * (t + ell : ℝ)) := by
          dsimp [γt, Csmall, openLoopStepSize]
          field_simp [hε.ne', hA.ne', hq_pos.ne', hell_pos.ne']
          ring
        have hh_small : h t < ε / 2 := by
          have htmp : F t < ε / (2 * (t + ell : ℝ)) := by simpa [hEq] using hF_bound
          dsimp [h]
          have hmul := mul_lt_mul_of_pos_left htmp (by positivity : 0 < (t + ell : ℝ))
          have hneq : (t + ell : ℝ) ≠ 0 := by
            have hpos : (0 : ℝ) < t + ell := by
              exact_mod_cast (show 0 < t + ell by omega)
            exact ne_of_gt hpos
          have hcalc :
              (t + ell : ℝ) * (ε / (2 * (t + ell : ℝ))) = ε / 2 := by
            field_simp [hneq]
          simpa [hcalc] using hmul
        exact le_of_lt hh_small
  have hstable :
      ∀ t ≥ T, h t ≤ ε → h (t + 1) ≤ ε := by
    intro t ht hle
    rcases hT t ht with ⟨hcoeffT, hstdT⟩
    rcases hsmall_or_refined t with hleft | hright
    · have hstep : h (t + 1) ≤ a t * h t + stdConst t := by
        have hh_succ : h (t + 1) = (t + ell + 1 : ℝ) * F (t + 1) := by
          change ((((t + 1 : ℕ) : ℝ) + ell) * F (t + 1) = (t + ell + 1 : ℝ) * F (t + 1))
          have hcast : (((t + 1 : ℕ) : ℝ) + ell) = (t + ell + 1 : ℝ) := by
            exact_mod_cast (show t + 1 + ell = t + ell + 1 by omega)
          rw [hcast]
        have hmul := mul_le_mul_of_nonneg_left (hstd_step t) (by positivity : 0 ≤ (t + ell + 1 : ℝ))
        calc
          h (t + 1) = (t + ell + 1 : ℝ) * F (t + 1) := hh_succ
          _ ≤ (t + ell + 1 : ℝ) *
                ((1 - (ell : ℝ) / (t + ell : ℝ)) * F t +
                  ((L : ℝ) / 2) * ((ell : ℝ) / (t + ell : ℝ)) ^ 2 * Dsq) := hmul
          _ = a t * h t + stdConst t := by
                simpa [a, h, stdConst, mul_assoc, mul_left_comm, mul_comm] using
                  (openLoop_scaled_standard_eq hell1 (F := F) (Dsq := Dsq) (L := (L : ℝ)) t)
      have ha_le_one : a t ≤ 1 := by
        simpa [a] using openLoop_coeff_le_one hell1 t
      have hah : a t * h t ≤ h t := by
        simpa using mul_le_mul_of_nonneg_right ha_le_one (hnonneg_h t)
      have hlt : h (t + 1) < ε := by
        linarith
      exact le_of_lt hlt
    · have hstep : h (t + 1) ≤ a t * h t + c t * coeff t := by
        have hh_succ : h (t + 1) = (t + ell + 1 : ℝ) * F (t + 1) := by
          change ((((t + 1 : ℕ) : ℝ) + ell) * F (t + 1) = (t + ell + 1 : ℝ) * F (t + 1))
          have hcast : (((t + 1 : ℕ) : ℝ) + ell) = (t + ell + 1 : ℝ) := by
            exact_mod_cast (show t + 1 + ell = t + ell + 1 by omega)
          rw [hcast]
        have hmul := mul_le_mul_of_nonneg_left hright (by positivity : 0 ≤ (t + ell + 1 : ℝ))
        calc
          h (t + 1) = (t + ell + 1 : ℝ) * F (t + 1) := hh_succ
          _ ≤ (t + ell + 1 : ℝ) *
                ((1 - (ell : ℝ) / (t + ell : ℝ)) * F t +
                  (L : ℝ) * ((ell : ℝ) / (t + ell : ℝ)) ^ 2 * (δ t) ^ 2 +
                  Rconst * ((ell : ℝ) / (t + ell : ℝ)) ^ 2 * (δ t) ^ betaExp) := hmul
          _ = a t * h t + c t * coeff t := by
                dsimp [a, h, c, coeff]
                have hneq : (t + ell : ℝ) ≠ 0 := by
                  have hpos : (0 : ℝ) < t + ell := by
                    exact_mod_cast (show 0 < t + ell by omega)
                  exact ne_of_gt hpos
                field_simp [hneq]
                ring
      have hc_nonneg : 0 ≤ c t := by
        dsimp [c]
        exact div_nonneg (by positivity) (by positivity)
      have hbeta_le : c t * coeff t ≤ c t * (ε / 2) := by
        exact mul_le_mul_of_nonneg_left (le_of_lt hcoeffT) hc_nonneg
      have hmain : h (t + 1) ≤ a t * ε + c t * (ε / 2) := by
        have ha_nonneg : 0 ≤ a t := by
          dsimp [a]
          positivity
        have hah : a t * h t ≤ a t * ε := by
          exact mul_le_mul_of_nonneg_left hle ha_nonneg
        calc
          h (t + 1) ≤ a t * h t + c t * coeff t := hstep
          _ ≤ a t * ε + c t * coeff t := by linarith [hah]
          _ ≤ a t * ε + c t * (ε / 2) := by linarith [hbeta_le]
      have hcoeff_le_one :
          a t + (1 / 2 : ℝ) * c t ≤ 1 := by
        have hcoeff_le_one' :
            (t : ℝ) * (t + ell + 1 : ℝ) / (t + ell : ℝ) ^ 2 +
              (1 / 2 : ℝ) * (t + ell + 1 : ℝ) / (t + ell : ℝ) ^ 2 ≤ 1 := by
          exact openLoop_refined_coeff_le_one hell t
        dsimp [a, c]
        convert hcoeff_le_one' using 1
        ring
      have hfinal : a t * ε + c t * (ε / 2) ≤ ε := by
        have hscaled' : ε * (a t + (1 / 2 : ℝ) * c t) ≤ ε * 1 := by
          exact mul_le_mul_of_nonneg_left hcoeff_le_one (le_of_lt hε)
        have hscaled : ε * (a t + (1 / 2 : ℝ) * c t) ≤ ε := by
          simpa using hscaled'
        have hEq : a t * ε + c t * (ε / 2) = ε * (a t + (1 / 2 : ℝ) * c t) := by
          ring
        rw [hEq]
        exact hscaled
      exact le_trans hmain hfinal
  have habove_drop :
      ∀ N0 t, T ≤ N0 → N0 ≤ t → t ≤ 2 * N0 → ε < h t →
        h (t + 1) ≤ h t - ε / (4 * (N0 + ell : ℝ)) := by
    intro N0 t hTN hN0 htN0 hgt
    rcases hT t (le_trans hTN hN0) with ⟨hcoeffT, _hstdT⟩
    rcases hsmall_or_refined t with hleft | hright
    · exfalso
      linarith
    · have hstep : h (t + 1) ≤ a t * h t + c t * coeff t := by
        have hh_succ : h (t + 1) = (t + ell + 1 : ℝ) * F (t + 1) := by
          change ((((t + 1 : ℕ) : ℝ) + ell) * F (t + 1) = (t + ell + 1 : ℝ) * F (t + 1))
          have hcast : (((t + 1 : ℕ) : ℝ) + ell) = (t + ell + 1 : ℝ) := by
            exact_mod_cast (show t + 1 + ell = t + ell + 1 by omega)
          rw [hcast]
        have hmul := mul_le_mul_of_nonneg_left hright (by positivity : 0 ≤ (t + ell + 1 : ℝ))
        calc
          h (t + 1) = (t + ell + 1 : ℝ) * F (t + 1) := hh_succ
          _ ≤ (t + ell + 1 : ℝ) *
                ((1 - (ell : ℝ) / (t + ell : ℝ)) * F t +
                  (L : ℝ) * ((ell : ℝ) / (t + ell : ℝ)) ^ 2 * (δ t) ^ 2 +
                  Rconst * ((ell : ℝ) / (t + ell : ℝ)) ^ 2 * (δ t) ^ betaExp) := hmul
          _ = a t * h t + c t * coeff t := by
                dsimp [a, h, c, coeff]
                have hneq : (t + ell : ℝ) ≠ 0 := by
                  have hpos : (0 : ℝ) < t + ell := by
                    exact_mod_cast (show 0 < t + ell by omega)
                  exact ne_of_gt hpos
                field_simp [hneq]
                ring
      have hc_nonneg : 0 ≤ c t := by
        dsimp [c]
        exact div_nonneg (by positivity) (by positivity)
      have hbeta_le : c t * coeff t ≤ c t * (ε / 2) := by
        exact mul_le_mul_of_nonneg_left (le_of_lt hcoeffT) hc_nonneg
      have hdrop :
          h (t + 1) ≤ h t - ε / (2 * (t + ell : ℝ)) := by
        have hdrop_aux :
            a t * h t + c t * (ε / 2) ≤ h t - ε / (2 * (t + ell : ℝ)) := by
          calc
            a t * h t + c t * (ε / 2)
                = (t : ℝ) * (t + ell + 1 : ℝ) / (t + ell : ℝ) ^ 2 * h t +
                    (ε / 2) * (t + ell + 1 : ℝ) / (t + ell : ℝ) ^ 2 := by
                      dsimp [a, c]
                      ring
            _ ≤ h t - ε / (2 * (t + ell : ℝ)) := by
                  exact openLoop_drop_bound hell t
                    (heps := le_of_lt hε) (hH := le_of_lt hgt)
        have hmain : h (t + 1) ≤ a t * h t + c t * (ε / 2) := by
          calc
            h (t + 1) ≤ a t * h t + c t * coeff t := hstep
            _ ≤ a t * h t + c t * (ε / 2) := by linarith [hbeta_le]
        exact le_trans hmain hdrop_aux
      have hfrac :
          ε / (4 * (N0 + ell : ℝ)) ≤ ε / (2 * (t + ell : ℝ)) := by
        exact openLoop_blockFraction_bound hell1
          (heps := le_of_lt hε) htN0
      have hsub :
          h t - ε / (2 * (t + ell : ℝ)) ≤ h t - ε / (4 * (N0 + ell : ℝ)) := by
        linarith
      exact le_trans hdrop hsub
  refine ⟨T, M0, ε / (4 * ell : ℝ), by exact div_pos hε (by positivity), hbounded T, hstable, ?_⟩
  have hNseq_succ : ∀ j, 2 ^ (j + 1) * (T + 1) - 1 = 2 * (2 ^ j * (T + 1) - 1) + 1 :=
    nseq_succ T
  have hNseq_ge : ∀ j, T ≤ 2 ^ j * (T + 1) - 1 :=
    nseq_ge T
  have htail_above : ∀ {p t : ℕ}, T ≤ t → t ≤ p → ε < h p → ε < h t :=
    fun htT htp hpgt => tail_above_of_stable hstable htT htp hpgt
  intro k n hkn hngt
  let Nk : ℕ := 2 ^ k * (T + 1) - 1
  have hNk_succ : 2 ^ (k + 1) * (T + 1) - 1 = 2 * Nk + 1 := hNseq_succ k
  have hNk_ge : T ≤ Nk := hNseq_ge k
  have hablock : ∀ t, Nk ≤ t → t ≤ 2 * Nk → ε < h t := by
    intro t hlow hhigh
    have htn : t ≤ n := by rw [hNk_succ] at hkn; omega
    exact htail_above (le_trans hNk_ge hlow) htn hngt
  have hdrop :=
    block_drop_of_step_drop_openLoop (h := h) (N := Nk) hell1 (le_of_lt hε)
      (fun t hlow hhigh => by
        linarith [habove_drop Nk t hNk_ge hlow hhigh (hablock t hlow hhigh)])
  simpa [hNk_succ] using hdrop

/-- The open-loop family `γ_t = ell / (t + ell)` with `ell ≥ 2` satisfies the
boosted theorem under the local dual sharpness condition for exponents `q = 2`
or `q > 2`, once the iterates approach a varying feasible minimizer sequence. -/
theorem frankWolfe_localGap_openLoop_boosted_convergence_of_minimizerSequence_tendsto_zero
    (hC_convex : Convex ℝ C)
    {ell : ℕ} (hell : 2 ≤ ell)
    {A : ℝ} {q : ℝ} (hq : q = 2 ∨ 2 < q) (hA : 0 < A)
    (f : E → ℝ) (f' : E → E) (L : NNReal) (hL : 0 < L)
    (hConv : IsFirstOrderConvex f f')
    (hSmooth : IsLipschitzSmoothUpperBound f L f')
    (x_star : E)
    (hLocal :
      HasLocalLMOGapPowerOn
        O (C ∩ {y : E | f y = f x_star}) A q)
    (xStarSeq : ℕ → E)
    (hxStarSeq : ∀ t, xStarSeq t ∈ C)
    (hvalSeq : ∀ t, f (xStarSeq t) = f x_star)
    (hminSeq : ∀ t, ∀ y ∈ C, f (xStarSeq t) ≤ f y)
    {x0 : E} (hx0 : x0 ∈ C)
    (hδ_zero :
      Tendsto
        (fun t => ‖frankWolfeOpenLoopSequence O ell f' x0 t - xStarSeq t‖)
        atTop (nhds 0)) :
    Tendsto
      (fun t : ℕ =>
        (t + ell : ℝ) *
          (f (frankWolfeOpenLoopSequence O ell f' x0 t) - f x_star))
      atTop (nhds 0) := by
  rcases hq with rfl | hq_gt
  · simpa using
      frankWolfe_localGap_two_openLoop_boosted_convergence_of_minimizerSequence_tendsto_zero
        (O := O)
        hC_convex hell hA f f' L hL hConv hSmooth x_star hLocal
        xStarSeq hxStarSeq hvalSeq hminSeq hx0 hδ_zero
  · exact
      frankWolfe_localGap_openLoop_boosted_convergence_of_minimizerSequence_tendsto_zero_of_two_lt
        (O := O)
        hC_convex hell hq_gt hA f f' L hL hConv hSmooth x_star hLocal
        xStarSeq hxStarSeq hvalSeq hminSeq hx0 hδ_zero

/-- Open-loop family boosted convergence under the local dual sharpness
condition, with no uniqueness assumption. -/
theorem frankWolfe_localGap_openLoop_boosted_convergence_of_minimizer
    (hC_convex : Convex ℝ C)
    {ell : ℕ} (hell : 2 ≤ ell)
    {A : ℝ} {q : ℝ} (hq : q = 2 ∨ 2 < q) (hA : 0 < A)
    (f : E → ℝ) (f' : E → E) (L : NNReal) (hL : 0 < L)
    (hConv : IsFirstOrderConvex f f')
    (hSmooth : IsLipschitzSmoothUpperBound f L f')
    {x_star : E} (hx_star : x_star ∈ C)
    (hLocal :
      HasLocalLMOGapPowerOn
        O (C ∩ {y : E | f y = f x_star}) A q)
    (hmin : ∀ y ∈ C, f x_star ≤ f y)
    {x0 : E} (hx0 : x0 ∈ C) :
    Tendsto
      (fun t : ℕ =>
        (t + ell : ℝ) *
          (f (frankWolfeOpenLoopSequence O ell f' x0 t) - f x_star))
      atTop (nhds 0) := by
  have hell1 : 1 ≤ ell := by omega
  let xSeq : ℕ → E := frankWolfeOpenLoopSequence O ell f' x0
  let F : ℕ → ℝ := fun t => f (xSeq t) - f x_star
  let M : Set E := C ∩ {y : E | f y = f x_star}
  have hcont : Continuous f :=
    continuous_of_isFirstOrderConvex_isLipschitzSmoothUpperBound (f := f) (f' := f') (L := L) hConv hSmooth
  have hlevel_closed : IsClosed {y : E | f y = f x_star} :=
    isClosed_eq hcont continuous_const
  have hM_compact : IsCompact M := by
    simpa [M] using O.isCompact.inter_right hlevel_closed
  have hM_nonempty : M.Nonempty := by
    refine ⟨x_star, ?_⟩
    simp [M, hx_star]
  have hxSeq : ∀ t, xSeq t ∈ C := by
    intro t
    simpa [xSeq] using
      frankWolfeOpenLoopSequence_mem
        (O := O)
        hC_convex hell1 f' hx0 t
  have hgap_zero :
      Tendsto F atTop (nhds 0) := by
    let B : ℝ := max (f x0 - f x_star) ((L : ℝ) * (Metric.diam C) ^ 2)
    have hB_nonneg : 0 ≤ B := by
      have hgap0_nonneg : 0 ≤ f x0 - f x_star := by
        exact primalGap_nonneg_of_isMinOn (C := C) (f := f) hx0 hmin
      exact le_trans hgap0_nonneg (le_max_left _ _)
    have hnonneg : ∀ t, 0 ≤ F t := by
      intro t
      exact primalGap_nonneg_of_isMinOn (C := C) (f := f) (hxSeq t) hmin
    have hbound :
        ∀ t, F t ≤ ((ell : ℝ) * B) / (t + ell : ℝ) := by
      intro t
      simpa [F, xSeq, B] using
        (open_loop_convergence_of_initialGap_le
          (O := O)
          (C := C) hC_convex (ell := ell) hell
          f f' L hSmooth hConv hx_star hx0
          hB_nonneg (le_max_left _ _) (le_max_right _ _) t)
    exact squeeze_zero hnonneg hbound
      (tendsto_const_div_add_atTop_nhds_zero_nat ((ell : ℝ) * B) ell)
  have hdist_zero :
      Tendsto (fun t => Metric.infDist (xSeq t) M) atTop (nhds 0) := by
    simpa [xSeq, M] using
      tendsto_infDist_minimizerSet_of_gap_tendsto_zero
        O.isCompact (f := f) (f' := f') (L := L) hConv hSmooth x_star xSeq hxSeq
        (by simpa [F] using hgap_zero)
  let pSeq : ℕ → E := nearestPoint hM_compact hM_nonempty ∘ xSeq
  have hpSeq_memM : ∀ t, pSeq t ∈ M :=
      fun t => nearestPoint_mem hM_compact hM_nonempty (xSeq t)
  have hpSeq_dist : ∀ t, Metric.infDist (xSeq t) M = dist (xSeq t) (pSeq t) :=
      fun t => infDist_nearestPoint hM_compact hM_nonempty (xSeq t)
  have hδ_zero' : Filter.Tendsto (fun t => dist (xSeq t) (pSeq t)) Filter.atTop (nhds 0) :=
      tendsto_dist_nearestPoint_of_tendsto_infDist hM_compact hM_nonempty hdist_zero
  have hpSeq_mem : ∀ t, pSeq t ∈ C := fun t => (hpSeq_memM t).1
  have hpSeq_val : ∀ t, f (pSeq t) = f x_star := fun t => (hpSeq_memM t).2
  have hpSeq_min : ∀ t, ∀ y ∈ C, f (pSeq t) ≤ f y := fun t y hy => by
    linarith [hmin y hy, hpSeq_val t]
  have hδ_zero : Tendsto (fun t => ‖xSeq t - pSeq t‖) atTop (nhds 0) :=
    hδ_zero'.congr (fun t => dist_eq_norm _ _)
  simpa [xSeq] using
    frankWolfe_localGap_openLoop_boosted_convergence_of_minimizerSequence_tendsto_zero
      (O := O)
      hC_convex hell hq hA f f' L hL hConv hSmooth x_star hLocal
      pSeq hpSeq_mem hpSeq_val hpSeq_min hx0 hδ_zero

/-- Zero-gradient wrapper for the local open-loop family theorem. -/
theorem frankWolfe_localGap_openLoop_boosted_convergence_of_zeroGradient_minimizer
    (hC_convex : Convex ℝ C)
    {ell : ℕ} (hell : 2 ≤ ell)
    {A : ℝ} {q : ℝ} (hq : q = 2 ∨ 2 < q) (hA : 0 < A)
    (f : E → ℝ) (f' : E → E) (L : NNReal) (hL : 0 < L)
    (hConv : IsFirstOrderConvex f f')
    (hSmooth : IsLipschitzSmoothUpperBound f L f')
    {x_star : E} (hx_star : x_star ∈ C) (hgrad : f' x_star = 0)
    (hLocal :
      HasLocalLMOGapPowerOn
        O (C ∩ {y : E | f y = f x_star}) A q)
    {x0 : E} (hx0 : x0 ∈ C) :
    Tendsto
      (fun t : ℕ =>
        (t + ell : ℝ) *
          (f (frankWolfeOpenLoopSequence O ell f' x0 t) - f x_star))
      atTop (nhds 0) := by
  exact
    frankWolfe_localGap_openLoop_boosted_convergence_of_minimizer
      (O := O)
      hC_convex hell hq hA f f' L hL hConv hSmooth hx_star hLocal
      (fun y _hy =>
        by
          have hgap_nonneg :=
            primalGap_nonneg_of_zero_gradient
              (f := f) (f' := f') hConv
              (x := y) (x_star := x_star) hgrad
          linarith)
      hx0

end LocalGapBoostedConvergence

end Lemmata.FrankWolfeLDS
