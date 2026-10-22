module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Tactic

@[expose] public section

/-!
# Geometry used by the distributional lower bound

This module formalizes the ball-inclusion definition of a strongly convex set
used in `tex/sc-lmo-distributional.tex`.  It is intentionally separate from the
support-inequality predicate `IsStronglyConvex` in `BoostedConvergence.lean`.

Paper correspondence:
* Definition `def:strong-set` -> `IsStronglyConvexBall`
* preservation under intersections -> `isStronglyConvexBall_sInter`
* positive rescaling -> `IsStronglyConvexBall.smul`
-/

open Set InnerProductSpace
local notation "inner" => inner ℝ

namespace Lemmata.DistributionalLowerBounds.Core.Distributional

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Squared-norm identity for a two-point affine combination in a real inner-product
space.  This is the quantitative source of the unit ball's curvature. -/
lemma norm_affineCombination_sq
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (x y : H) (θ : ℝ) :
    ‖θ • x + (1 - θ) • y‖ ^ 2 =
      θ * ‖x‖ ^ 2 + (1 - θ) * ‖y‖ ^ 2 - θ * (1 - θ) * ‖x - y‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    real_inner_comm, starRingEnd_apply, star_trivial]
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, norm_sub_sq_real]
  ring

/-- Ball-inclusion definition of an `α`-strongly convex set.  The nonnegativity
assumption is included so that the displayed radius is a genuine radius. -/
def IsStronglyConvexBall (C : Set E) (α : ℝ) : Prop :=
  0 ≤ α ∧
    ∀ x ∈ C, ∀ y ∈ C, ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
      Metric.closedBall (θ • x + (1 - θ) • y)
        ((α / 2) * θ * (1 - θ) * ‖x - y‖ ^ 2) ⊆ C

/-- Arbitrary intersections preserve the same strong-convexity parameter. -/
theorem isStronglyConvexBall_sInter {𝒞 : Set (Set E)} {α : ℝ}
    (hα : 0 ≤ α) (h𝒞 : ∀ C ∈ 𝒞, IsStronglyConvexBall C α) :
    IsStronglyConvexBall (⋂₀ 𝒞) α := by
  refine ⟨hα, ?_⟩
  intro x hx y hy θ hθ u hu
  rw [Set.mem_sInter] at hx hy ⊢
  intro C hC
  exact (h𝒞 C hC).2 x (hx C hC) y (hy C hC) θ hθ hu

/-- Binary intersections preserve the same parameter. -/
theorem IsStronglyConvexBall.inter {C D : Set E} {α : ℝ}
    (hC : IsStronglyConvexBall C α) (hD : IsStronglyConvexBall D α) :
    IsStronglyConvexBall (C ∩ D) α := by
  refine ⟨hC.1, ?_⟩
  intro x hx y hy θ hθ u hu
  exact ⟨hC.2 x hx.1 y hy.1 θ hθ hu, hD.2 x hx.2 y hy.2 θ hθ hu⟩

/-- Scaling a set by a positive factor `r` divides its strong-convexity
parameter by `r`.  We express the scaled set as a preimage to avoid any choice
of representatives. -/
theorem IsStronglyConvexBall.preimage_smul {C : Set E} {α r : ℝ}
    (hC : IsStronglyConvexBall C α) (hr : 0 < r) :
    IsStronglyConvexBall {x : E | r • x ∈ C} (r * α) := by
  refine ⟨mul_nonneg hr.le hC.1, ?_⟩
  intro x hx y hy θ hθ u hu
  change r • u ∈ C
  apply hC.2 (r • x) hx (r • y) hy θ hθ
  rw [Metric.mem_closedBall, dist_eq_norm] at hu ⊢
  have hrnorm : ‖r • (u - (θ • x + (1 - θ) • y))‖ =
      r * ‖u - (θ • x + (1 - θ) • y)‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
  have hcenter :
      r • u - (θ • (r • x) + (1 - θ) • (r • y)) =
        r • (u - (θ • x + (1 - θ) • y)) := by
    module
  have hsub : ‖r • x - r • y‖ = r * ‖x - y‖ := by
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
  rw [hcenter, hrnorm, hsub]
  calc
    r * ‖u - (θ • x + (1 - θ) • y)‖
        ≤ r * (((r * α) / 2) * θ * (1 - θ) * ‖x - y‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hu hr.le
    _ = (α / 2) * θ * (1 - θ) * (r * ‖x - y‖) ^ 2 := by ring

/-- Every closed unit ball in a real inner-product space is `1`-strongly
convex in the paper's ball-inclusion convention. -/
theorem isStronglyConvexBall_closedBall_one
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (c : H) : IsStronglyConvexBall (Metric.closedBall c 1) 1 := by
  refine ⟨by norm_num, ?_⟩
  intro x hx y hy θ hθ u hu
  rw [Metric.mem_closedBall] at hx hy hu ⊢
  have hx' : ‖x - c‖ ≤ 1 := by simpa [dist_eq_norm] using hx
  have hy' : ‖y - c‖ ≤ 1 := by simpa [dist_eq_norm] using hy
  have hθ0 : 0 ≤ θ := hθ.1
  have hθ1 : θ ≤ 1 := hθ.2
  have hθc : 0 ≤ 1 - θ := sub_nonneg.mpr hθ1
  let a : ℝ := θ * (1 - θ) * ‖x - y‖ ^ 2
  have hxy : ‖x - y‖ ≤ 2 := by
    calc
      ‖x - y‖ = ‖(x - c) - (y - c)‖ := by
        congr 1
        abel
      _ ≤ ‖x - c‖ + ‖y - c‖ := norm_sub_le _ _
      _ ≤ 2 := by linarith
  have hxy0 : 0 ≤ ‖x - y‖ := norm_nonneg _
  have hxy_sq : ‖x - y‖ ^ 2 ≤ 4 := by nlinarith
  have hθprod : θ * (1 - θ) ≤ 1 / 4 := by
    nlinarith [sq_nonneg (θ - 1 / 2)]
  have ha0 : 0 ≤ a := by
    dsimp [a]
    positivity
  have ha1 : a ≤ 1 := by
    dsimp [a]
    nlinarith
  let m : H := θ • x + (1 - θ) • y
  have hm_center :
      m - c = θ • (x - c) + (1 - θ) • (y - c) := by
    dsimp [m]
    module
  have hm_sq :
      ‖m - c‖ ^ 2 =
        θ * ‖x - c‖ ^ 2 + (1 - θ) * ‖y - c‖ ^ 2 - a := by
    rw [hm_center, norm_affineCombination_sq]
    have hsub : (x - c) - (y - c) = x - y := by abel
    rw [hsub]
  have hx_sq : ‖x - c‖ ^ 2 ≤ 1 := by
    have := norm_nonneg (x - c)
    nlinarith
  have hy_sq : ‖y - c‖ ^ 2 ≤ 1 := by
    have := norm_nonneg (y - c)
    nlinarith
  have hm_sq_le : ‖m - c‖ ^ 2 ≤ 1 - a := by
    rw [hm_sq]
    nlinarith
  have hrhs0 : 0 ≤ 1 - a / 2 := by nlinarith
  have hm_le : ‖m - c‖ ≤ 1 - a / 2 := by
    apply (sq_le_sq₀ (norm_nonneg _) hrhs0).mp
    calc
      ‖m - c‖ ^ 2 ≤ 1 - a := hm_sq_le
      _ ≤ (1 - a / 2) ^ 2 := by nlinarith [sq_nonneg a]
  have hu' : dist u m ≤ a / 2 := by
    dsimp [m, a]
    calc
      dist u (θ • x + (1 - θ) • y) ≤
          (1 / 2 : ℝ) * θ * (1 - θ) * ‖x - y‖ ^ 2 := hu
      _ = θ * (1 - θ) * ‖x - y‖ ^ 2 / 2 := by ring
  calc
    dist u c ≤ dist u m + dist m c := dist_triangle _ _ _
    _ ≤ a / 2 + (1 - a / 2) := by
      have hmc : dist m c ≤ 1 - a / 2 := by simpa [dist_eq_norm] using hm_le
      gcongr
    _ = 1 := by ring

end Lemmata.DistributionalLowerBounds.Core.Distributional
