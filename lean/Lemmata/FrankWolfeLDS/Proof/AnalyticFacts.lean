module

public import Lemmata.FrankWolfeLDS.Proof.ToMathlib
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Topology.Order.Compact
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

@[expose] public section

namespace Lemmata.FrankWolfeLDS

open InnerProductSpace Set Filter
open scoped NNReal Topology
local notation "inner" => inner ℝ

/-!
### Interim objective-function predicates

`IsLipschitzSmoothUpperBound` and `IsFirstOrderConvex` are interim predicates used
throughout the FW convergence theorems. They are not upstream candidates in their
current form:

- `IsLipschitzSmoothUpperBound` should ultimately be replaced by `LipschitzWith L f'`
  (already in Mathlib) once the Descent Lemma is proved (thread 6ea4de).
- `IsFirstOrderConvex` encodes the global subgradient condition; Mathlib has no
  subdifferential theory yet. A proper upstream version requires that foundation
  first (thread 6ea4de).
-/

section GradientPredicates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A quadratic upper model with curvature constant `L`.
Interim predicate — see module docstring. -/
def IsLipschitzSmoothUpperBound (f : E → ℝ) (L : ℝ≥0) (f' : E → E) : Prop :=
  ∀ x y : E, f y ≤ f x + ⟪f' x, y - x⟫_ℝ + (L : ℝ) / 2 * ‖y - x‖ ^ 2

/-- First-order convexity: `f' x` is a global subgradient of `f` at every `x`.
Interim predicate — see module docstring. -/
def IsFirstOrderConvex (f : E → ℝ) (f' : E → E) : Prop :=
  ∀ x y : E, f x + ⟪f' x, y - x⟫_ℝ ≤ f y

/-- Convexity over the whole space together with pointwise gradient representations
implies the first-order support inequality. -/
theorem IsFirstOrderConvex.of_convexOn_hasGradientAt [CompleteSpace E]
    {f : E → ℝ} {f' : E → E}
    (hconv : ConvexOn ℝ (Set.univ : Set E) f)
    (hgrad : ∀ x, HasGradientAt f (f' x) x) :
    IsFirstOrderConvex f f' := by
  intro x y
  let g : ℝ → ℝ := fun t => f (AffineMap.lineMap x y t)
  have hconv_g : ConvexOn ℝ (Set.univ : Set ℝ) g := by
    have h := hconv.comp_affineMap (AffineMap.lineMap x y)
    rw [Set.preimage_univ] at h
    exact h
  have hderiv : HasDerivAt g (⟪f' x, y - x⟫_ℝ) (0 : ℝ) := by
    have hfx : HasFDerivAt f (InnerProductSpace.toDualMap ℝ E (f' x)) x :=
      (hgrad x).hasFDerivAt
    have hfx0 : HasFDerivAt f (InnerProductSpace.toDualMap ℝ E (f' x))
        ((AffineMap.lineMap x y) (0 : ℝ)) := by simpa using hfx
    have hline : HasDerivAt (AffineMap.lineMap x y) (y - x) (0 : ℝ) := by
      simpa using AffineMap.hasDerivAt_lineMap (a := x) (b := y) (x := (0 : ℝ))
    have h := HasFDerivAt.comp_hasDerivAt (0 : ℝ) hfx0 hline
    simp only [InnerProductSpace.toDualMap_apply_apply] at h
    exact h
  have hslope : ⟪f' x, y - x⟫_ℝ ≤ slope g 0 1 :=
    hconv_g.le_slope_of_hasDerivAt (by simp) (by simp) (by norm_num) hderiv
  have hslope' : slope g 0 1 = f y - f x := by simp [g, slope]
  linarith [hslope, hslope']

/-- The first-order lower bound together with the quadratic smoothness upper bound
implies continuity of `f`. -/
theorem continuous_of_isFirstOrderConvex_isLipschitzSmoothUpperBound
    {f : E → ℝ} {f' : E → E} {L : ℝ≥0}
    (hConv : IsFirstOrderConvex f f')
    (hSmooth : IsLipschitzSmoothUpperBound f L f') :
    Continuous f := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun y => norm_nonneg _)
    (g := fun y => ‖f' x‖ * ‖y - x‖ + (L : ℝ) / 2 * ‖y - x‖ ^ 2) ?_ ?_
  · intro y
    have h1 : ⟪f' x, y - x⟫_ℝ ≤ f y - f x := by linarith [hConv x y]
    have h2 : -(‖f' x‖ * ‖y - x‖) ≤ ⟪f' x, y - x⟫_ℝ := by
      have := real_inner_le_norm (-f' x) (y - x)
      simp [inner_neg_left] at this; linarith
    have h3 : f y - f x ≤ ‖f' x‖ * ‖y - x‖ + (L : ℝ) / 2 * ‖y - x‖ ^ 2 := by
      have := hSmooth x y
      have h4 : ⟪f' x, y - x⟫_ℝ ≤ ‖f' x‖ * ‖y - x‖ := real_inner_le_norm _ _
      linarith
    rw [Real.norm_eq_abs]
    apply abs_le.mpr
    constructor
    · linarith [mul_nonneg (by positivity : (0 : ℝ) ≤ (L : ℝ) / 2) (sq_nonneg ‖y - x‖)]
    · linarith
  · have hnorm : Tendsto (fun y : E => ‖y - x‖) (𝓝 x) (𝓝 0) := tendsto_norm_sub_self x
    simpa using (tendsto_const_nhds.mul hnorm).add (tendsto_const_nhds.mul (hnorm.pow 2))

end GradientPredicates

/-- A linear functional attains its minimum on a nonempty compact set. -/
theorem LMO_exists
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {C : Set E} (hC_compact : IsCompact C) (hC_nonempty : C.Nonempty) (g : E) :
    ∃ v ∈ C, ∀ y ∈ C, (inner g v : ℝ) ≤ inner g y := by
  obtain ⟨v, hvC, hvmin⟩ :=
    hC_compact.exists_isMinOn (α := ℝ) hC_nonempty
      ((continuous_const.inner continuous_id : Continuous fun y : E => inner g y).continuousOn)
  exact ⟨v, hvC, hvmin⟩



/-! ### Combinatorial and analytic utilities for the convergence engine -/

/-- If a sequence drops by a uniform amount on every step of the block
`[N, 2N]`, then the endpoint `2N + 1` inherits the corresponding total drop. -/
lemma block_drop_of_step_drop
    {h : ℕ → ℝ} {ε : ℝ} {N : ℕ}
    (hstep :
      ∀ t, N ≤ t → t ≤ 2 * N →
        ε / (4 * (N + 1 : ℝ)) ≤ h t - h (t + 1)) :
    h (2 * N + 1) ≤ h N - ε / 4 := by
  let c : ℝ := ε / (4 * (N + 1 : ℝ))
  have hiter : ∀ k ≤ N + 1, h (N + k) ≤ h N - c * k := by
    intro k hk
    induction k with
    | zero =>
        simp [c]
    | succ k ih =>
        have hkN : k ≤ N := by omega
        have hik : h (N + k) ≤ h N - c * k := by
          exact ih (Nat.le_trans hkN (Nat.le_succ N))
        have hstepk : c ≤ h (N + k) - h (N + k + 1) := by
          have hlow : N ≤ N + k := Nat.le_add_right N k
          have hhigh : N + k ≤ 2 * N := by omega
          simpa [c, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
            hstep (N + k) hlow hhigh
        have hnext : h (N + k + 1) ≤ h (N + k) - c := by linarith
        calc
          h (N + (k + 1)) = h (N + k + 1) := by rw [Nat.add_assoc]
          _ ≤ h (N + k) - c := hnext
          _ ≤ (h N - c * k) - c := by linarith
          _ = h N - c * (k + 1 : ℕ) := by
              rw [show (c * (k + 1 : ℕ) : ℝ) = c * ((k : ℝ) + 1) by
                    push_cast; ring]
              ring
  have hend := hiter (N + 1) le_rfl
  have hc : c * (N + 1 : ℕ) = ε / 4 := by
    dsimp [c]
    field_simp
    push_cast; ring
  have hEqNat : N + (N + 1) = 2 * N + 1 := by omega
  have hend' : h (2 * N + 1) ≤ h N - c * ((N + 1 : ℕ) : ℝ) := by
    simpa [hEqNat] using hend
  calc
    h (2 * N + 1) ≤ h N - c * ((N + 1 : ℕ) : ℝ) := hend'
    _ = h N - ε / 4 := by rw [hc]

/-- Open-loop variant of `block_drop_of_step_drop`: if the per-step drop is
≥ ε/(4*(N+ℓ)) on every step of `[N, 2N]`, then h(2N+1) ≤ h(N) - ε/(4*ℓ). -/
lemma block_drop_of_step_drop_openLoop
    {h : ℕ → ℝ} {ε : ℝ} {N ell : ℕ} (hell1 : 1 ≤ ell) (hε : 0 ≤ ε)
    (hstep : ∀ t, N ≤ t → t ≤ 2 * N →
        ε / (4 * (N + ell : ℝ)) ≤ h t - h (t + 1)) :
    h (2 * N + 1) ≤ h N - ε / (4 * (ell : ℝ)) := by
  have hell_pos : (0 : ℝ) < ell := by exact_mod_cast (show 0 < ell by omega)
  have hNell_pos : (0 : ℝ) < N + ell := by exact_mod_cast (show 0 < N + ell by omega)
  let εblock : ℝ := ε * ((N + 1 : ℕ) : ℝ) / (N + ell : ℝ)
  have hstepblock :
      ∀ t, N ≤ t → t ≤ 2 * N → εblock / (4 * (↑N + 1 : ℝ)) ≤ h t - h (t + 1) := by
    intro t hlow hhigh
    have hEq : εblock / (4 * (↑N + 1 : ℝ)) = ε / (4 * (N + ell : ℝ)) := by
      dsimp [εblock]
      have hneq1 : (N + ell : ℝ) ≠ 0 := ne_of_gt hNell_pos
      have hneq2 : (↑N + 1 : ℝ) ≠ 0 := by positivity
      field_simp [hneq1, hneq2]
      push_cast; ring
    rw [hEq]
    exact hstep t hlow hhigh
  have hdrop := block_drop_of_step_drop (h := h) (ε := εblock) (N := N) hstepblock
  have hratio : ε / (4 * (ell : ℝ)) ≤ εblock / 4 := by
    dsimp [εblock]
    have hfrac : (1 : ℝ) / ell ≤ (↑N + 1 : ℝ) / (N + ell : ℝ) := by
      rw [_root_.div_le_div_iff₀ hell_pos hNell_pos]
      have hell_ge : (1 : ℝ) ≤ ell := by exact_mod_cast hell1
      have hN_nonneg : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      nlinarith
    have hscaled := mul_le_mul_of_nonneg_left hfrac (by linarith : 0 ≤ ε / 4)
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hscaled
  linarith

/-- Dyadic sequence successor identity. -/
lemma nseq_succ (T j : ℕ) :
    2 ^ (j + 1) * (T + 1) - 1 = 2 * (2 ^ j * (T + 1) - 1) + 1 := by
  have : 2 ^ (j + 1) * (T + 1) = 2 * (2 ^ j * (T + 1)) := by ring
  have hmpos : 0 < 2 ^ j * (T + 1) := by positivity
  omega

/-- Dyadic sequence lower bound. -/
lemma nseq_ge (T j : ℕ) : T ≤ 2 ^ j * (T + 1) - 1 := by
  have : T + 1 ≤ 2 ^ j * (T + 1) := by
    simpa [one_mul] using Nat.mul_le_mul_right (T + 1) Nat.one_le_two_pow
  omega


/-- If `h` is `ε`-stable past `T` (via `hstable`) and `ε < h p`,
then `ε < h t` for every `t ∈ [T, p]`. -/
lemma tail_above_of_stable {h : ℕ → ℝ} {ε : ℝ} {T : ℕ}
    (hstable : ∀ t ≥ T, h t ≤ ε → h (t + 1) ≤ ε)
    {p t : ℕ} (htT : T ≤ t) (htp : t ≤ p) (hpgt : ε < h p) : ε < h t := by
  by_contra hnot
  have hle : h t ≤ ε := le_of_not_gt hnot
  have htail : ∀ m, t ≤ m → h m ≤ ε := by
    intro m hm
    induction hm with
    | refl => exact hle
    | @step m hm ih => exact hstable m (le_trans htT hm) ih
  exact not_lt_of_ge (htail p htp) hpgt

/-! ### Descent lemmas used by the uniformly convex and boosted convergence engines -/

/-- The auxiliary Polyak scale
`max (sqrt (2 F_t / L), F_t / G)` vanishes whenever `F_t -> 0`. -/
lemma tendsto_polyakScale_zero
    {F : ℕ → ℝ} {L G : ℝ}
    (hF_zero : Tendsto F atTop (nhds 0)) :
    Tendsto (fun t => max (Real.sqrt (2 * F t / L)) (F t / G)) atTop (nhds 0) := by
  have hsqrt_zero :
      Tendsto (fun t => Real.sqrt (2 * F t / L)) atTop (nhds 0) := by
    have hscaled :
        Tendsto (fun t => 2 * F t / L) atTop (nhds 0) := by
      simpa using (tendsto_const_nhds.mul hF_zero).div_const L
    simpa using (Filter.Tendsto.sqrt hscaled)
  have hlin_zero :
      Tendsto (fun t => F t / G) atTop (nhds 0) := by
    simpa using hF_zero.div_const G
  simpa using hsqrt_zero.max hlin_zero

/-- A logistic step dominates the quadratic decrease model `x - c x^2`. -/
lemma quadratic_step_le_logistic_step
    {x c : ℝ} (hx : 0 ≤ x) (hc : 0 ≤ c) :
    x - c * x ^ 2 ≤ x / (1 + c * x) := by
  have hden : 0 < 1 + c * x := by
    nlinarith
  have hEq :
      x / (1 + c * x) - (x - c * x ^ 2) =
        c ^ 2 * x ^ 3 / (1 + c * x) := by
    field_simp [hden.ne']
    ring
  have hnonneg : 0 ≤ c ^ 2 * x ^ 3 / (1 + c * x) := by
    positivity
  linarith [hEq]

/-- The logistic map `x ↦ x / (1 + c x)` is monotone on the nonnegative reals. -/
lemma logistic_step_mono
    {x y c : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hc : 0 ≤ c) :
    x / (1 + c * x) ≤ y / (1 + c * y) := by
  have hxden : 0 < 1 + c * x := by
    nlinarith
  have hyden : 0 < 1 + c * y := by
    nlinarith [hx, hxy, hc]
  refine (div_le_div_iff₀ hxden hyden).2 ?_
  nlinarith

/-- A nonnegative sequence satisfying the quadratic recursion
`B_{t+1} ≤ B_t - c B_t^2` admits the standard logistic upper bound. -/
theorem quadraticDescent_bound
    {B : ℕ → ℝ} {c : ℝ}
    (hc : 0 ≤ c)
    (hB_nonneg : ∀ t, 0 ≤ B t)
    (hstep : ∀ t, B (t + 1) ≤ B t - c * (B t) ^ 2) :
    ∀ t : ℕ, B t ≤ B 0 / (1 + c * t * B 0) := by
  intro t
  induction t with
  | zero =>
      have hden : (1 + c * (0 : ℕ) * B 0 : ℝ) = 1 := by ring
      simp
  | succ t ih =>
      have hBt_nonneg : 0 ≤ B t := hB_nonneg t
      have hnum_nonneg : 0 ≤ B 0 := hB_nonneg 0
      have hden_nonneg : 0 ≤ 1 + c * t * B 0 := by
        positivity
      have hlog :
          B (t + 1) ≤ B t / (1 + c * B t) := by
        exact (hstep t).trans (quadratic_step_le_logistic_step hBt_nonneg hc)
      have hmono :
          B t / (1 + c * B t) ≤
            (B 0 / (1 + c * t * B 0)) / (1 + c * (B 0 / (1 + c * t * B 0))) := by
        exact logistic_step_mono hBt_nonneg ih hc
      have hEq :
          (B 0 / (1 + c * t * B 0)) / (1 + c * (B 0 / (1 + c * t * B 0))) =
            B 0 / (1 + c * (t + 1 : ℕ) * B 0) := by
        let s : ℝ := 1 + c * t * B 0
        have hden_pos : 0 < s := by
          positivity
        have hden2_pos : 0 < 1 + c * (t + 1 : ℕ) * B 0 := by
          positivity
        calc
          (B 0 / s) / (1 + c * (B 0 / s))
              = (B 0 / s) / ((1 + c * (t + 1 : ℕ) * B 0) / s) := by
                    congr 2
                    field_simp [hden_pos.ne']
                    dsimp [s]
                    push_cast
                    ring_nf
          _ = B 0 / (1 + c * (t + 1 : ℕ) * B 0) := by
                field_simp [hden_pos.ne', hden2_pos.ne']
      exact hlog.trans (hmono.trans (by simp [hEq]))

end Lemmata.FrankWolfeLDS
