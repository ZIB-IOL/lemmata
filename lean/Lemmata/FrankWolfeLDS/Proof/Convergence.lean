module

public import Lemmata.FrankWolfeLDS.Proof.Basic
public import Lemmata.FrankWolfeLDS.Proof.ToMathlib
public import Mathlib.Tactic

@[expose] public section

namespace Lemmata.FrankWolfeLDS

open InnerProductSpace Set
local notation "inner" => inner ℝ

section Convergence

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {C : Set E} (O : Oracle C)

/-- The global short-step size for one Frank-Wolfe step.

When `s = x` (the LMO returns the current point, i.e., x is already a first-order
stationary point and the Frank-Wolfe gap is zero), the denominator vanishes and
Lean's `a / 0 = 0` convention gives step size 0, which is the correct mathematical
answer — no improving direction exists.

Callers should assume `0 < (L : ℝ)` (as required by convergence theorems); the
`L = 0` case also yields step size 0 via the same convention. -/
noncomputable def globalShortStepSize (f' : E → E) (L : NNReal) (x : E) : ℝ :=
  let s := LMO O (f' x)
  min ((inner (f' x) (x - s) : ℝ) / ((L : ℝ) * ‖s - x‖ ^ 2)) 1

/-- The Frank-Wolfe update with the global short-step rule. -/
noncomputable def globalShortStep (f' : E → E) (L : NNReal) (x : E) : E :=
  frankWolfeStep O f' x
    (globalShortStepSize O f' L x)

/-- The global short-step iterate sequence. -/
noncomputable def globalShortStepSequence (f' : E → E) (L : NNReal) (x0 : E) : ℕ → E
  | 0 => x0
  | t + 1 => globalShortStep O f' L
      (globalShortStepSequence f' L x0 t)

/-- The Frank-Wolfe segment is continuous in the step size. -/
lemma continuous_frankWolfeStep_in_step (f' : E → E) (x : E) :
    Continuous fun γ : ℝ => frankWolfeStep O f' x γ := by
  unfold frankWolfeStep
  fun_prop

/-- The exact line-search step size exists because the one-dimensional
restriction is continuous on the compact interval `[0,1]`. -/
lemma exactLineSearchSize_exists
    (f : E → ℝ) (f' : E → E) (hCont : Continuous f) (x : E) :
    ∃ γ ∈ Set.Icc (0 : ℝ) 1,
      ∀ η ∈ Set.Icc (0 : ℝ) 1,
        f (frankWolfeStep O f' x γ) ≤
          f (frankWolfeStep O f' x η) := by
  let φ : ℝ → ℝ := fun γ => f (frankWolfeStep O f' x γ)
  have hφ_cont : Continuous φ := by
    exact hCont.comp (continuous_frankWolfeStep_in_step (O := O) (f' := f') (x := x))
  obtain ⟨γ, hγmin⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1)).exists_isMinOn
      (α := ℝ)
      (by
        refine ⟨0, ?_⟩
        constructor <;> norm_num)
      hφ_cont.continuousOn
  exact ⟨γ, hγmin.1, hγmin.2⟩

/-- An exact line-search rule along the oracle's Frank-Wolfe segments: a step size in `[0,1]` at
every point that minimizes `f` on the segment. When there are several minimizers, `step` is the
rule that selects one of them; every result below holds for every such rule. -/
structure LineSearch (f : E → ℝ) (f' : E → E) where
  /-- The selected step size. -/
  step : E → ℝ
  /-- It lies in `[0,1]`. -/
  step_mem : ∀ x, step x ∈ Set.Icc (0 : ℝ) 1
  /-- It minimizes `f` on the segment. -/
  step_opt : ∀ x, ∀ η ∈ Set.Icc (0 : ℝ) 1,
    f (frankWolfeStep O f' x (step x)) ≤ f (frankWolfeStep O f' x η)

/-- The canonical (choice-based) exact line-search rule of a continuous objective. -/
noncomputable def LineSearch.ofContinuous (f : E → ℝ) (f' : E → E) (hCont : Continuous f) :
    LineSearch O f f' where
  step x := Classical.choose (exactLineSearchSize_exists (O := O) (f := f) (f' := f') hCont x)
  step_mem x := (Classical.choose_spec
    (exactLineSearchSize_exists (O := O) (f := f) (f' := f') hCont x)).1
  step_opt x := (Classical.choose_spec
    (exactLineSearchSize_exists (O := O) (f := f) (f' := f') hCont x)).2

/-- The step size selected by the line-search rule. -/
def exactLineSearchSize (f : E → ℝ) (f' : E → E) (hLS : LineSearch O f f') (x : E) : ℝ :=
  hLS.step x

/-- The Frank-Wolfe update with exact line search on the current oracle
segment. -/
noncomputable def exactLineSearch
    (f : E → ℝ) (f' : E → E) (hLS : LineSearch O f f') (x : E) : E :=
  frankWolfeStep O f' x
    (exactLineSearchSize O f f' hLS x)

/-- The exact line-search iterate sequence. -/
noncomputable def exactLineSearchSequence
    (f : E → ℝ) (f' : E → E) (hLS : LineSearch O f f') (x0 : E) : ℕ → E
  | 0 => x0
  | t + 1 => exactLineSearch O f f' hLS
      (exactLineSearchSequence f f' hLS x0 t)

/-- The global short-step size always lies in `[0,1]`. -/
lemma globalShortStepSize_mem_Icc (f' : E → E) (L : NNReal) {x : E} (hx : x ∈ C) :
    globalShortStepSize O f' L x ∈ Set.Icc (0 : ℝ) 1 := by
  let s := LMO O (f' x)
  have hg_nonneg : 0 ≤ (inner (f' x) (x - s) : ℝ) := by
    rw [inner_sub_right]
    linarith [LMO_le O (f' x) hx]
  have hquot_nonneg :
      0 ≤ (inner (f' x) (x - s) : ℝ) / ((L : ℝ) * ‖s - x‖ ^ 2) := by
    exact div_nonneg hg_nonneg (by positivity)
  constructor
  · dsimp [globalShortStepSize, s]
    exact le_min hquot_nonneg zero_le_one
  · dsimp [globalShortStepSize, s]
    exact min_le_right _ _

/-- Exact line-search step sizes stay in `[0,1]`. -/
lemma exactLineSearchSize_mem_Icc
    (f : E → ℝ) (f' : E → E) (hLS : LineSearch O f f') (x : E) :
    exactLineSearchSize O f f' hLS x ∈ Set.Icc (0 : ℝ) 1 :=
  hLS.step_mem x

/-- Exact line search minimizes the objective on the current Frank-Wolfe
segment. -/
lemma exactLineSearch_optimal
    (f : E → ℝ) (f' : E → E) (hLS : LineSearch O f f') (x : E)
    {γ : ℝ} (hγ : γ ∈ Set.Icc (0 : ℝ) 1) :
    f (exactLineSearch O f f' hLS x) ≤
      f (frankWolfeStep O f' x γ) :=
  hLS.step_opt x γ hγ

/-- One global short step stays in the feasible set. -/
lemma globalShortStep_mem (hC_convex : Convex ℝ C) (f' : E → E) (L : NNReal)
    {x : E} (hx : x ∈ C) :
    globalShortStep O f' L x ∈ C := by
  simpa [globalShortStep] using
    frankWolfeStep_mem O hC_convex f' hx
      (globalShortStepSize_mem_Icc O f' L hx)

/-- One exact line-search Frank-Wolfe step stays in the feasible set. -/
lemma exactLineSearch_mem
    (hC_convex : Convex ℝ C)
    (f : E → ℝ) (f' : E → E) (hLS : LineSearch O f f')
    {x : E} (hx : x ∈ C) :
    exactLineSearch O f f' hLS x ∈ C := by
  simpa [exactLineSearch] using
    frankWolfeStep_mem O hC_convex f' hx
      (exactLineSearchSize_mem_Icc
        (O := O)
        (f := f) (f' := f') hLS x)

/-- Global short-step iterates remain feasible. -/
theorem globalShortStepSequence_mem (hC_convex : Convex ℝ C)
    (f' : E → E) (L : NNReal) {x0 : E} (hx0 : x0 ∈ C) (t : ℕ) :
    globalShortStepSequence O f' L x0 t ∈ C := by
  induction t with
  | zero =>
      simpa [globalShortStepSequence] using hx0
  | succ t ih =>
      simpa [globalShortStepSequence] using
        globalShortStep_mem O hC_convex f' L ih

/-- Exact line-search iterates remain feasible. -/
theorem exactLineSearchSequence_mem
    (hC_convex : Convex ℝ C)
    (f : E → ℝ) (f' : E → E) (hLS : LineSearch O f f')
    {x0 : E} (hx0 : x0 ∈ C) (t : ℕ) :
    exactLineSearchSequence O f f' hLS x0 t ∈ C := by
  induction t with
  | zero =>
      simpa [exactLineSearchSequence] using hx0
  | succ t ih =>
      simpa [exactLineSearchSequence] using
        exactLineSearch_mem O hC_convex f f' hLS ih

/-- Scalar model decrease for the global short-step rule. -/
lemma shortStepScalar_decrease_lower_bound
    {g a : ℝ} (hg : 0 ≤ g) (ha : 0 ≤ a) :
    (1 / 2 : ℝ) * min g (g ^ 2 / a) ≤
      min (g / a) 1 * g - (a / 2) * (min (g / a) 1) ^ 2 := by
  by_cases ha0 : a = 0
  · subst ha0
    have hmin0 : min g 0 = 0 := min_eq_right hg
    simp [hmin0]
  · have ha_pos : 0 < a := lt_of_le_of_ne ha (by simpa [eq_comm] using ha0)
    by_cases hq : g / a ≤ 1
    · have hγ : min (g / a) 1 = g / a := min_eq_left hq
      have hmin : min g (g ^ 2 / a) = g ^ 2 / a := by
        have hga : g ≤ a := by
          simpa using (_root_.div_le_iff₀ ha_pos).1 hq
        apply min_eq_right
        rw [_root_.div_le_iff₀ ha_pos]
        nlinarith
      rw [hγ, hmin]
      have hEq :
          g / a * g - (a / 2) * (g / a) ^ 2 = (1 / 2 : ℝ) * (g ^ 2 / a) := by
        field_simp [ha0]
        ring
      linarith [hEq]
    · have hq' : 1 < g / a := lt_of_not_ge hq
      have hγ : min (g / a) 1 = 1 := min_eq_right (le_of_lt hq')
      have hmin : min g (g ^ 2 / a) = g := by
        apply min_eq_left
        rw [_root_.le_div_iff₀ ha_pos]
        nlinarith [(_root_.lt_div_iff₀ ha_pos).1 hq']
      have hga : a < g := by
        simpa using ((_root_.lt_div_iff₀ ha_pos).1 hq')
      rw [hγ, hmin]
      nlinarith

/-- The global short-step size maximizes the scalar quadratic lower model on
`[0,1]` whenever the curvature coefficient is positive. -/
lemma shortStepScalar_model_optimal
    {g a γ : ℝ} (ha : 0 < a) (hγ : γ ∈ Set.Icc (0 : ℝ) 1) :
    γ * g - (a / 2) * γ ^ 2 ≤
      min (g / a) 1 * g - (a / 2) * (min (g / a) 1) ^ 2 := by
  by_cases hq : g / a ≤ 1
  · have hmin : min (g / a) 1 = g / a := min_eq_left hq
    rw [hmin]
    have hsquare' : 0 ≤ (a / 2) * (γ - g / a) ^ 2 := by
      positivity
    have hEq :
        (a / 2) * (γ - g / a) ^ 2 =
          (g / a * g - (a / 2) * (g / a) ^ 2) -
            (γ * g - (a / 2) * γ ^ 2) := by
      field_simp [ha.ne']
      ring
    linarith [hsquare', hEq]
  · have hq' : 1 < g / a := lt_of_not_ge hq
    have hmin : min (g / a) 1 = 1 := min_eq_right (le_of_lt hq')
    have hga : a < g := by
      simpa using ((_root_.lt_div_iff₀ ha).1 hq')
    have h1γ : 0 ≤ 1 - γ := by linarith [hγ.2]
    have hinner : 0 ≤ g - (a / 2) * (1 + γ) := by
      nlinarith [hga, hγ.1, hγ.2]
    have hfac : 0 ≤ (1 - γ) * (g - (a / 2) * (1 + γ)) :=
      mul_nonneg h1γ hinner
    rw [hmin]
    have hEq :
        g - a / 2 - (γ * g - (a / 2) * γ ^ 2) =
          (1 - γ) * (g - (a / 2) * (1 + γ)) := by
      ring
    linarith [hfac, hEq]

/-- [FW-DEC-SS] The global short-step rule satisfies the universal one-step
decrease bound. -/
lemma globalShortStep_decrease
    (f : E → ℝ) (f' : E → E) (L : NNReal)
    (hSmooth : IsLipschitzSmoothUpperBound f L f')
    {x : E} (hx : x ∈ C) :
    let s := LMO O (f' x)
    let g : ℝ := inner (f' x) (x - s)
    let Dsq : ℝ := ‖s - x‖ ^ 2
    (1 / 2 : ℝ) * min g (g ^ 2 / ((L : ℝ) * Dsq)) ≤
      f x - f (globalShortStep O f' L x) := by
  let s := LMO O (f' x)
  let g : ℝ := inner (f' x) (x - s)
  let Dsq : ℝ := ‖s - x‖ ^ 2
  let γ := globalShortStepSize O f' L x
  have hγ : γ ∈ Set.Icc (0 : ℝ) 1 :=
    globalShortStepSize_mem_Icc O f' L hx
  have hg_nonneg : 0 ≤ g := by
    dsimp [g, s]
    rw [inner_sub_right]
    linarith [LMO_le O (f' x) hx]
  have hmodel :
      (1 / 2 : ℝ) * min g (g ^ 2 / ((L : ℝ) * Dsq)) ≤
        γ * g - (((L : ℝ) * Dsq) / 2) * γ ^ 2 := by
    simpa [γ, globalShortStepSize, s, g, Dsq, mul_assoc, mul_left_comm, mul_comm] using
      (shortStepScalar_decrease_lower_bound
        (g := g) (a := (L : ℝ) * Dsq) hg_nonneg (by positivity))
  have hsmooth0 := hSmooth x (globalShortStep O f' L x)
  have hsmooth1 :
      f (globalShortStep O f' L x) ≤
        f x + γ * inner (f' x) (s - x) + (L / 2 : ℝ) * (γ ^ 2 * Dsq) := by
    simpa [globalShortStep, frankWolfeStep, γ, s, Dsq, inner_smul_right, norm_smul, Real.norm_of_nonneg hγ.1, pow_two, mul_assoc, mul_left_comm, mul_comm] using
      hsmooth0
  have hinner : (inner (f' x) (s - x) : ℝ) = -g := by
    dsimp [g]
    rw [inner_sub_right, inner_sub_right]
    ring
  have hcurv :
      (L / 2 : ℝ) * (γ ^ 2 * Dsq) = (((L : ℝ) * Dsq) / 2) * γ ^ 2 := by
    ring
  have hdec :
      γ * g - (((L : ℝ) * Dsq) / 2) * γ ^ 2 ≤
        f x - f (globalShortStep O f' L x) := by
    rw [hinner, hcurv] at hsmooth1
    linarith
  exact le_trans hmodel hdec

/-- One global short step satisfies the standard affine-plus-curvature
recursion against any comparison step size `γ ∈ [0,1]`. -/
lemma globalShortStep_gap_bound
    (f : E → ℝ) (f' : E → E) (L : NNReal) (hL : 0 < L)
    (hSmooth : IsLipschitzSmoothUpperBound f L f')
    (hConv : IsFirstOrderConvex f f')
    {x x_star : E} (hx : x ∈ C) (hx_star : x_star ∈ C)
    {γ : ℝ} (hγ : γ ∈ Set.Icc (0 : ℝ) 1) :
    f (globalShortStep O f' L x) - f x_star ≤
      (1 - γ) * (f x - f x_star) + (L / 2 : ℝ) * γ ^ 2 * (Metric.diam C) ^ 2 := by
  have hL_real : 0 < (L : ℝ) := NNReal.coe_pos.mpr hL
  let s := LMO O (f' x)
  let g : ℝ := inner (f' x) (x - s)
  let Dsq : ℝ := ‖s - x‖ ^ 2
  let γss := globalShortStepSize O f' L x
  have hs : s ∈ C := LMO_mem O (f' x)
  have hlinear :
      (inner (f' x) (s - x) : ℝ) ≤ f x_star - f x := by
    have hmin :
        (inner (f' x) (s - x) : ℝ) ≤ inner (f' x) (x_star - x) := by
      rw [inner_sub_right, inner_sub_right]
      linarith [LMO_le O (f' x) hx_star]
    have hfirst :
        inner (f' x) (x_star - x) ≤ f x_star - f x := by
      linarith [hConv x x_star]
    exact le_trans hmin hfirst
  have hdiam :
      Dsq ≤ Metric.diam C ^ 2 := by
    dsimp [Dsq]
    rw [← dist_eq_norm]
    exact pow_le_pow_left₀ dist_nonneg
      (Metric.dist_le_diam_of_mem O.isCompact.isBounded hs hx) 2
  have hsmooth0 := hSmooth x (globalShortStep O f' L x)
  have hsmooth :
      f (globalShortStep O f' L x) ≤
        f x + γss * inner (f' x) (s - x) + (L / 2 : ℝ) * (γss ^ 2 * Dsq) := by
    simpa [globalShortStep, frankWolfeStep, γss, s, Dsq, inner_smul_right, norm_smul, Real.norm_of_nonneg (globalShortStepSize_mem_Icc O f' L hx).1, pow_two, mul_assoc, mul_left_comm, mul_comm] using
      hsmooth0
  have hinner : (inner (f' x) (s - x) : ℝ) = -g := by
    dsimp [g]
    rw [inner_sub_right, inner_sub_right]
    ring
  have hcurv_ss :
      (L / 2 : ℝ) * (γss ^ 2 * Dsq) = (((L : ℝ) * Dsq) / 2) * γss ^ 2 := by
    ring
  have hcurv_cmp :
      (L / 2 : ℝ) * (γ ^ 2 * Dsq) = (((L : ℝ) * Dsq) / 2) * γ ^ 2 := by
    ring
  have hbest :
      f x + γss * inner (f' x) (s - x) + (L / 2 : ℝ) * (γss ^ 2 * Dsq) ≤
        f x + γ * inner (f' x) (s - x) + (L / 2 : ℝ) * (γ ^ 2 * Dsq) := by
    by_cases hD0 : Dsq = 0
    · have hsx : s = x := by
        exact sub_eq_zero.mp (norm_eq_zero.mp (by simpa [Dsq] using hD0))
      have hsinner0 : (inner (f' x) (s - x) : ℝ) = 0 := by simp [hsx]
      have hγss0 : γss = 0 := by
        dsimp [γss, globalShortStepSize]
        simp [s, hsx]
      simp [hsinner0, hγss0, hD0]
    · have hD_nonneg : 0 ≤ Dsq := by
        dsimp [Dsq]
        positivity
      have hD_pos : 0 < Dsq := lt_of_le_of_ne hD_nonneg (by simpa [eq_comm] using hD0)
      have hopt :
          γ * g - (((L : ℝ) * Dsq) / 2) * γ ^ 2 ≤
            γss * g - (((L : ℝ) * Dsq) / 2) * γss ^ 2 := by
        simpa [γss, globalShortStepSize, s, Dsq, mul_assoc, mul_left_comm, mul_comm] using
          (shortStepScalar_model_optimal
            (g := g) (a := (L : ℝ) * Dsq) (γ := γ)
            (mul_pos hL_real hD_pos) hγ)
      rw [hinner, hcurv_ss, hcurv_cmp]
      linarith
  have hlin_scaled : γ * inner (f' x) (s - x) ≤ γ * (f x_star - f x) := by
    exact mul_le_mul_of_nonneg_left hlinear hγ.1
  have hdiam_scaled : γ ^ 2 * Dsq ≤ γ ^ 2 * (Metric.diam C) ^ 2 := by
    exact mul_le_mul_of_nonneg_left hdiam (by positivity : 0 ≤ γ ^ 2)
  have hcurv :
      (L / 2 : ℝ) * (γ ^ 2 * Dsq) ≤
        (L / 2 : ℝ) * (γ ^ 2 * (Metric.diam C) ^ 2) := by
    exact mul_le_mul_of_nonneg_left hdiam_scaled (by positivity : 0 ≤ (L / 2 : ℝ))
  calc
    f (globalShortStep O f' L x) - f x_star
        ≤ f x + γ * inner (f' x) (s - x) + (L / 2 : ℝ) * (γ ^ 2 * Dsq) - f x_star := by
          linarith
    _ ≤ f x + γ * (f x_star - f x) + (L / 2 : ℝ) * (γ ^ 2 * Dsq) - f x_star := by
          linarith
    _ ≤ f x + γ * (f x_star - f x) + (L / 2 : ℝ) * (γ ^ 2 * (Metric.diam C) ^ 2) - f x_star := by
          linarith
    _ = (1 - γ) * (f x - f x_star) + (L / 2 : ℝ) * γ ^ 2 * (Metric.diam C) ^ 2 := by
          ring

/-- One Frank-Wolfe step satisfies the standard affine-plus-curvature recursion. -/
lemma frankWolfeStep_gap_bound
    (f : E → ℝ) (f' : E → E) (L : NNReal)
    (hSmooth : IsLipschitzSmoothUpperBound f L f')
    (hConv : IsFirstOrderConvex f f')
    {x x_star : E} (hx : x ∈ C) (hx_star : x_star ∈ C)
    {γ : ℝ} (hγ : γ ∈ Set.Icc (0 : ℝ) 1) :
    f (frankWolfeStep O f' x γ) - f x_star ≤
      (1 - γ) * (f x - f x_star) + (L / 2 : ℝ) * γ ^ 2 * (Metric.diam C) ^ 2 := by
  let s := LMO O (f' x)
  have hs : s ∈ C := LMO_mem O (f' x)
  have hlinear :
      (inner (f' x) (s - x) : ℝ) ≤ f x_star - f x := by
    have hmin :
        (inner (f' x) (s - x) : ℝ) ≤ inner (f' x) (x_star - x) := by
      rw [inner_sub_right, inner_sub_right]
      linarith [LMO_le O (f' x) hx_star]
    have hfirst :
        inner (f' x) (x_star - x) ≤ f x_star - f x := by
      linarith [hConv x x_star]
    exact le_trans hmin hfirst
  have hdiam :
      ‖γ • (s - x)‖ ^ 2 ≤ γ ^ 2 * (Metric.diam C) ^ 2 := by
    rw [norm_smul, Real.norm_of_nonneg hγ.1, mul_pow, ← dist_eq_norm]
    gcongr
    exact Metric.dist_le_diam_of_mem O.isCompact.isBounded hs hx
  have hsmooth0 := hSmooth x (frankWolfeStep O f' x γ)
  have hsmooth :
      f (frankWolfeStep O f' x γ) ≤
        f x + γ * inner (f' x) (s - x) + (L / 2 : ℝ) * ‖γ • (s - x)‖ ^ 2 := by
    simpa [frankWolfeStep, s, inner_smul_right] using hsmooth0
  have hlin_scaled : γ * inner (f' x) (s - x) ≤ γ * (f x_star - f x) := by
    exact mul_le_mul_of_nonneg_left hlinear hγ.1
  have hcurv :
      (L / 2 : ℝ) * ‖γ • (s - x)‖ ^ 2 ≤
        (L / 2 : ℝ) * (γ ^ 2 * (Metric.diam C) ^ 2) := by
    exact mul_le_mul_of_nonneg_left hdiam (by positivity : 0 ≤ (L / 2 : ℝ))
  calc
    f (frankWolfeStep O f' x γ) - f x_star
        ≤ f x + γ * (f x_star - f x) + (L / 2 : ℝ) * (γ ^ 2 * (Metric.diam C) ^ 2) - f x_star := by
          linarith
    _ = (1 - γ) * (f x - f x_star) + (L / 2 : ℝ) * γ ^ 2 * (Metric.diam C) ^ 2 := by
          ring

/-- Abstract one-step gap kernel for the quadratic (p=2) geometry correction.
Given a geometry lower bound `A * ‖f' x‖ * r ^ 2 ≤ ⟨f'(x), x_star - s⟩` and
the step-size smallness condition `γ * L ≤ A * ‖f' x‖`, the Frank-Wolfe step
satisfies the refined gap recursion with curvature term `L * γ² * ‖x - x_star‖²`. -/
lemma frankWolfeStep_gap_bound_quadratic_kernel
    (f : E → ℝ) (f' : E → E) (L : NNReal)
    (hConv : IsFirstOrderConvex f f')
    (hSmooth : IsLipschitzSmoothUpperBound f L f')
    {x x_star : E}
    {γ : ℝ} (hγ : γ ∈ Set.Icc (0 : ℝ) 1)
    {A : ℝ}
    (hγsmall : γ * (L : ℝ) ≤ A * ‖f' x‖)
    (h_corr : A * ‖f' x‖ * ‖x_star - LMO O (f' x)‖ ^ 2 ≤
                (inner (f' x) (x_star - LMO O (f' x)) : ℝ)) :
    f (frankWolfeStep O f' x γ) - f x_star ≤
      (1 - γ) * (f x - f x_star) + (L : ℝ) * γ ^ 2 * ‖x - x_star‖ ^ 2 := by
  let s := LMO O (f' x)
  let d : ℝ := ‖s - x‖
  let r : ℝ := ‖x_star - s‖
  have hlinear :
      f (frankWolfeStep O f' x γ) - f x_star ≤
        (1 - γ) * (f x - f x_star) -
          γ * (inner (f' x) (x_star - s) : ℝ) +
          (L / 2 : ℝ) * γ ^ 2 * d ^ 2 := by
    have hsmooth0 := hSmooth x (frankWolfeStep O f' x γ)
    have hsmooth :
        f (frankWolfeStep O f' x γ) ≤
          f x + γ * inner (f' x) (s - x) + (L / 2 : ℝ) * γ ^ 2 * d ^ 2 := by
      simpa [frankWolfeStep, s, d, inner_smul_right, norm_smul, Real.norm_of_nonneg hγ.1, pow_two, mul_assoc, mul_left_comm, mul_comm] using hsmooth0
    have hfirst : (inner (f' x) (x_star - x) : ℝ) ≤ f x_star - f x := by
      linarith [hConv x x_star]
    have hexpand :
        (inner (f' x) (s - x) : ℝ) =
          (inner (f' x) (x_star - x) : ℝ) - (inner (f' x) (x_star - s) : ℝ) := by
      rw [inner_sub_right, inner_sub_right, inner_sub_right]
      ring
    rw [hexpand] at hsmooth
    linarith [mul_le_mul_of_nonneg_left hfirst hγ.1]
  have hdist : d ^ 2 ≤ 2 * ‖x - x_star‖ ^ 2 + 2 * r ^ 2 := by
    have hdecomp : s - x = (s - x_star) + (x_star - x) := by abel
    have htri : d ≤ ‖x - x_star‖ + r := by
      calc d = ‖s - x‖ := rfl
        _ = ‖(s - x_star) + (x_star - x)‖ := by rw [hdecomp]
        _ ≤ ‖s - x_star‖ + ‖x_star - x‖ := norm_add_le _ _
        _ = ‖x - x_star‖ + r := by simp [r, norm_sub_rev, add_comm]
    have hd_nonneg : 0 ≤ d := by dsimp [d]; positivity
    have hr_nonneg : 0 ≤ r := by dsimp [r]; positivity
    have hsq : d ^ 2 ≤ (‖x - x_star‖ + r) ^ 2 := by
      nlinarith [htri, hd_nonneg, norm_nonneg (x - x_star), hr_nonneg]
    nlinarith [sq_nonneg (‖x - x_star‖ - r)]
  have hcurv :
      (L / 2 : ℝ) * γ ^ 2 * d ^ 2 ≤
        (L : ℝ) * γ ^ 2 * ‖x - x_star‖ ^ 2 + A * γ * ‖f' x‖ * r ^ 2 := by
    have hbase :
        (L / 2 : ℝ) * γ ^ 2 * d ^ 2 ≤
          (L / 2 : ℝ) * γ ^ 2 * (2 * ‖x - x_star‖ ^ 2 + 2 * r ^ 2) :=
      mul_le_mul_of_nonneg_left hdist (by positivity)
    have hrterm : (L : ℝ) * γ ^ 2 * r ^ 2 ≤ A * γ * ‖f' x‖ * r ^ 2 := by
      have hLγ : (L : ℝ) * γ ≤ A * ‖f' x‖ := by linarith [hγsmall]
      have hr2 : (0 : ℝ) ≤ r ^ 2 := by positivity
      nlinarith [hγ.1, hr2, mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hLγ hγ.1) hr2]
    linarith
  have h_corr_scaled :
      A * γ * ‖f' x‖ * r ^ 2 ≤ γ * (inner (f' x) (x_star - s) : ℝ) := by
    have : r = ‖x_star - s‖ := rfl
    nlinarith [mul_le_mul_of_nonneg_left h_corr hγ.1]
  linarith

/-- [FW-DEC-LS] Exact line search decreases at least as much as the global
short-step rule on the same Frank-Wolfe segment. -/
lemma exactLineSearch_decrease
    (f : E → ℝ) (f' : E → E) (L : NNReal)
    (hLS : LineSearch O f f')
    (hSmooth : IsLipschitzSmoothUpperBound f L f')
    {x : E} (hx : x ∈ C) :
    let s := LMO O (f' x)
    let g : ℝ := inner (f' x) (x - s)
    let Dsq : ℝ := ‖s - x‖ ^ 2
    (1 / 2 : ℝ) * min g (g ^ 2 / ((L : ℝ) * Dsq)) ≤
      f x - f (exactLineSearch O f f' hLS x) := by
  let s := LMO O (f' x)
  let g : ℝ := inner (f' x) (x - s)
  let Dsq : ℝ := ‖s - x‖ ^ 2
  let γss := globalShortStepSize O f' L x
  have hopt :
      f (exactLineSearch O f f' hLS x) ≤
        f (globalShortStep O f' L x) := by
    simpa [exactLineSearch, globalShortStep, γss] using
      exactLineSearch_optimal
        (O := O)
        (f := f) (f' := f') hLS x
        (γ := γss)
        (globalShortStepSize_mem_Icc
          (O := O)
          (f' := f') (L := L) hx)
  have hss :
      (1 / 2 : ℝ) * min g (g ^ 2 / ((L : ℝ) * Dsq)) ≤
        f x - f (globalShortStep O f' L x) := by
    simpa [s, g, Dsq] using
      (globalShortStep_decrease
        (O := O)
        (f := f) (f' := f') (L := L) hSmooth hx)
  linarith

/-- Exact line search satisfies the same affine-plus-curvature recursion as any
comparison Frank-Wolfe step. -/
lemma exactLineSearch_gap_bound
    (f : E → ℝ) (f' : E → E) (L : NNReal)
    (hLS : LineSearch O f f')
    (hSmooth : IsLipschitzSmoothUpperBound f L f')
    (hConv : IsFirstOrderConvex f f')
    {x x_star : E} (hx : x ∈ C) (hx_star : x_star ∈ C)
    {γ : ℝ} (hγ : γ ∈ Set.Icc (0 : ℝ) 1) :
    f (exactLineSearch O f f' hLS x) - f x_star ≤
      (1 - γ) * (f x - f x_star) + (L / 2 : ℝ) * γ ^ 2 * (Metric.diam C) ^ 2 := by
  have hopt :
      f (exactLineSearch O f f' hLS x) ≤
        f (frankWolfeStep O f' x γ) := by
    exact exactLineSearch_optimal
      (O := O)
      (f := f) (f' := f') hLS x hγ
  have hcmp :=
    frankWolfeStep_gap_bound
      (O := O)
      (f := f) (f' := f') (L := L) hSmooth hConv
      (x := x) (x_star := x_star) hx hx_star hγ
  linarith

/-- Arithmetic update for the open-loop step size `gamma_t = ell / (t + ell)`. -/
lemma openLoop_rate_update {ell : ℕ} (hell : 2 ≤ ell) (B : ℝ) (hB : 0 ≤ B) (t : ℕ) :
    (1 - (ell : ℝ) / (t + ell : ℝ)) * (((ell : ℝ) * B) / (t + ell : ℝ)) +
        (B / 2) * ((ell : ℝ) / (t + ell : ℝ)) ^ 2 ≤
      ((ell : ℝ) * B) / (t + ell + 1 : ℝ) := by
  have hcoeff :
      (1 - (ell : ℝ) / (t + ell : ℝ)) * ((ell : ℝ) / (t + ell : ℝ)) +
          (1 / 2 : ℝ) * ((ell : ℝ) / (t + ell : ℝ)) ^ 2 ≤
        (ell : ℝ) / (t + ell + 1 : ℝ) := by
    have hell_ge : (2 : ℝ) ≤ ell := by exact_mod_cast hell
    have hell_pos : (0 : ℝ) < ell := by
      nlinarith
    have hden1_pos : (0 : ℝ) < t + ell := by
      nlinarith
    have hden2_pos : (0 : ℝ) < t + ell + 1 := by
      nlinarith
    have hneq1 : (t + ell : ℝ) ≠ 0 := ne_of_gt hden1_pos
    have hneq2 : (t + ell + 1 : ℝ) ≠ 0 := ne_of_gt hden2_pos
    have hEq :
        (ell : ℝ) / (t + ell + 1 : ℝ) -
          ((1 - (ell : ℝ) / (t + ell : ℝ)) * ((ell : ℝ) / (t + ell : ℝ)) +
            (1 / 2 : ℝ) * ((ell : ℝ) / (t + ell : ℝ)) ^ 2) =
          (ell : ℝ) *
              (((ell : ℝ) - 2) * t + (ell : ℝ) * ((ell : ℝ) - 1)) /
            (2 * (t + ell : ℝ) ^ 2 * (t + ell + 1 : ℝ)) := by
      field_simp [hneq1, hneq2]
      ring
    have hnum_nonneg :
        0 ≤ ((ell : ℝ) - 2) * t + (ell : ℝ) * ((ell : ℝ) - 1) := by
      nlinarith
    have hfrac_nonneg :
        0 ≤
          (ell : ℝ) *
              (((ell : ℝ) - 2) * t + (ell : ℝ) * ((ell : ℝ) - 1)) /
            (2 * (t + ell : ℝ) ^ 2 * (t + ell + 1 : ℝ)) := by
      apply div_nonneg
      · exact mul_nonneg (le_of_lt hell_pos) hnum_nonneg
      · positivity
    linarith [hEq]
  rw [show
        (1 - (ell : ℝ) / (t + ell : ℝ)) * (((ell : ℝ) * B) / (t + ell : ℝ)) +
          (B / 2) * ((ell : ℝ) / (t + ell : ℝ)) ^ 2 =
            B *
              ((1 - (ell : ℝ) / (t + ell : ℝ)) * ((ell : ℝ) / (t + ell : ℝ)) +
                (1 / 2 : ℝ) * ((ell : ℝ) / (t + ell : ℝ)) ^ 2) by ring]
  rw [show ((ell : ℝ) * B) / (t + ell + 1 : ℝ) = B * ((ell : ℝ) / (t + ell + 1 : ℝ)) by ring]
  exact mul_le_mul_of_nonneg_left hcoeff hB

omit [InnerProductSpace ℝ E] in
/-- The curvature term `(L/2)*γ²*diam²` is bounded by `(B/2)*γ²` whenever `L*diam² ≤ B`. -/
private lemma curv_bound_of_LD_le
    {L : NNReal} {B γ : ℝ}
    (hcurv_bound : (L : ℝ) * (Metric.diam C) ^ 2 ≤ B) :
    (L / 2 : ℝ) * γ ^ 2 * (Metric.diam C) ^ 2 ≤ (B / 2 : ℝ) * γ ^ 2 := by
  have hfac_nonneg : 0 ≤ (1 / 2 : ℝ) * γ ^ 2 := by positivity
  have hscaled :
      ((1 / 2 : ℝ) * γ ^ 2) * ((L : ℝ) * (Metric.diam C) ^ 2) ≤
        ((1 / 2 : ℝ) * γ ^ 2) * B :=
    mul_le_mul_of_nonneg_left hcurv_bound hfac_nonneg
  nlinarith [hscaled]

/-- Open-loop Frank-Wolfe satisfies the standard `O(1/t)` rate for every
integer parameter `ell >= 2`. -/
theorem open_loop_convergence_of_initialGap_le
  (hC_convex : Convex ℝ C) {ell : ℕ} (hell : 2 ≤ ell)
  (f : E → ℝ) (f' : E → E) (L : NNReal)
  (hSmooth : IsLipschitzSmoothUpperBound f L f')
  (hConv : IsFirstOrderConvex f f')
  {x_star : E} (hx_star : x_star ∈ C)
  {x0 : E} (hx0 : x0 ∈ C)
  {B : ℝ} (hB_nonneg : 0 ≤ B)
  (h0_bound : f x0 - f x_star ≤ B)
  (hcurv_bound : (L : ℝ) * (Metric.diam C) ^ 2 ≤ B) :
  ∀ t : ℕ,
    f (frankWolfeOpenLoopSequence O ell f' x0 t) - f x_star ≤
      ((ell : ℝ) * B) / (t + ell : ℝ) := by
  have hell1 : 1 ≤ ell := by omega
  intro t
  induction t with
  | zero =>
      have hbase :
          f (frankWolfeOpenLoopSequence O ell f' x0 0) - f x_star ≤
            ((ell : ℝ) * B) / (0 + ell : ℝ) := by
        calc
          f (frankWolfeOpenLoopSequence O ell f' x0 0) - f x_star
              = f x0 - f x_star := by simp [frankWolfeOpenLoopSequence]
          _ ≤ B := h0_bound
          _ = ((ell : ℝ) * B) / (0 + ell : ℝ) := by
                have hell_ne : (ell : ℝ) ≠ 0 := by positivity
                field_simp [hell_ne]
                ring_nf
      simpa using hbase
  | succ t ih =>
      have hx_t :
          frankWolfeOpenLoopSequence O ell f' x0 t ∈ C :=
        frankWolfeOpenLoopSequence_mem
          (O := O)
          hC_convex hell1 f' hx0 t
      have hstep :
          f (frankWolfeOpenLoopSequence O ell f' x0 (t + 1)) - f x_star ≤
            (1 - (ell : ℝ) / (t + ell : ℝ)) *
                (f (frankWolfeOpenLoopSequence O ell f' x0 t) - f x_star) +
              (L / 2 : ℝ) * ((ell : ℝ) / (t + ell : ℝ)) ^ 2 * (Metric.diam C) ^ 2 := by
        simpa [frankWolfeOpenLoopSequence, openLoopStepSize] using
          (frankWolfeStep_gap_bound (O := O)
            (f := f) (f' := f') (L := L) hSmooth hConv
            (x := frankWolfeOpenLoopSequence O ell f' x0 t)
            (x_star := x_star) hx_t hx_star
            (γ := openLoopStepSize ell t)
            (openLoopStepSize_mem_Icc hell1 t))
      have hcoeff_nonneg : 0 ≤ 1 - (ell : ℝ) / (t + ell : ℝ) := by
        have hγ_le :
            openLoopStepSize ell t ≤ 1 :=
          (openLoopStepSize_mem_Icc hell1 t).2
        simpa [openLoopStepSize] using sub_nonneg.mpr hγ_le
      have hcurv :
          (L / 2 : ℝ) * ((ell : ℝ) / (t + ell : ℝ)) ^ 2 * (Metric.diam C) ^ 2 ≤
            (B / 2 : ℝ) * ((ell : ℝ) / (t + ell : ℝ)) ^ 2 :=
        curv_bound_of_LD_le hcurv_bound
      have hmiddle :
          (1 - (ell : ℝ) / (t + ell : ℝ)) *
              (f (frankWolfeOpenLoopSequence O ell f' x0 t) - f x_star) +
            (L / 2 : ℝ) * ((ell : ℝ) / (t + ell : ℝ)) ^ 2 * (Metric.diam C) ^ 2 ≤
          (1 - (ell : ℝ) / (t + ell : ℝ)) *
              (((ell : ℝ) * B) / (t + ell : ℝ)) +
            (B / 2 : ℝ) * ((ell : ℝ) / (t + ell : ℝ)) ^ 2 :=
        add_le_add (by gcongr) hcurv
      have htail :
          (1 - (ell : ℝ) / (t + ell : ℝ)) * (((ell : ℝ) * B) / (t + ell : ℝ)) +
            (B / 2 : ℝ) * ((ell : ℝ) / (t + ell : ℝ)) ^ 2 ≤
          ((ell : ℝ) * B) / (t + ell + 1 : ℝ) := by
        exact openLoop_rate_update hell B hB_nonneg t
      have hsucc_denom : (↑(t + 1) + ell : ℝ) = (t + ell + 1 : ℝ) := by
        exact_mod_cast (show t + 1 + ell = t + ell + 1 by omega)
      rw [hsucc_denom]
      exact hstep.trans (hmiddle.trans htail)

/-- Open-loop Frank-Wolfe satisfies the standard `O(1/t)` rate for every
integer parameter `ell >= 2`. -/
theorem open_loop_convergence
  (hC_convex : Convex ℝ C) {ell : ℕ} (hell : 2 ≤ ell)
  (f : E → ℝ) (f' : E → E) (L : NNReal)
  (hSmooth : IsLipschitzSmoothUpperBound f L f')
  (hConv : IsFirstOrderConvex f f')
  {x_star : E} (hx_star : x_star ∈ C)
  {x0 : E} (hx0 : x0 ∈ C)
  (h0_bound : f x0 - f x_star ≤ L * (Metric.diam C) ^ 2) :
  ∀ t : ℕ,
    f (frankWolfeOpenLoopSequence O ell f' x0 t) - f x_star ≤
      ((ell : ℝ) * (L : ℝ) * (Metric.diam C) ^ 2) / (t + ell : ℝ) := by
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    (open_loop_convergence_of_initialGap_le
      (O := O)
      hC_convex hell f f' L hSmooth hConv hx_star hx0
      (B := (L : ℝ) * (Metric.diam C) ^ 2)
      (by positivity) h0_bound le_rfl)

/-- The scaled coefficient in the open-loop proof is bounded by `1`. -/
lemma openLoop_coeff_le_one {ell : ℕ} (hell : 1 ≤ ell) (t : ℕ) :
    (t : ℝ) * (t + ell + 1 : ℝ) / (t + ell : ℝ) ^ 2 ≤ 1 := by
  have hden_pos : 0 < (t + ell : ℝ) ^ 2 := by positivity
  have hell_ge : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  exact (_root_.div_le_iff₀ hden_pos).2 (by nlinarith [show (0 : ℝ) ≤ t by positivity])

/-- The open-loop curvature tail is bounded by a standard `1 / t` tail. -/
lemma openLoop_stdConst_bound {ell : ℕ} (hell : 1 ≤ ell)
    {B : ℝ} (hB : 0 ≤ B) (t : ℕ) :
    (((ell : ℝ) ^ 2) / 2) * B * (t + ell + 1 : ℝ) / (t + ell : ℝ) ^ 2 ≤
      ((ell : ℝ) ^ 2) * B / (t + ell : ℝ) := by
  have hpos : 0 < (t + ell : ℝ) := by positivity
  have hratio : (t + ell + 1 : ℝ) / (t + ell : ℝ) ≤ 2 := by
    refine (_root_.div_le_iff₀ hpos).2 ?_
    have hell_ge : (1 : ℝ) ≤ ell := by exact_mod_cast hell
    nlinarith [show (0 : ℝ) ≤ t by positivity]
  have hinv_nonneg : 0 ≤ (t + ell : ℝ)⁻¹ := by positivity
  have hfrac' :
      ((t + ell + 1 : ℝ) / (t + ell : ℝ)) * (t + ell : ℝ)⁻¹ ≤ 2 * (t + ell : ℝ)⁻¹ := by
    exact mul_le_mul_of_nonneg_right hratio hinv_nonneg
  have hfrac :
      (t + ell + 1 : ℝ) / (t + ell : ℝ) ^ 2 ≤ 2 / (t + ell : ℝ) := by
    simpa [div_eq_mul_inv, pow_two, mul_assoc, mul_left_comm, mul_comm] using hfrac'
  calc
    (((ell : ℝ) ^ 2) / 2) * B * (t + ell + 1 : ℝ) / (t + ell : ℝ) ^ 2
        = ((((ell : ℝ) ^ 2) / 2) * B) * ((t + ell + 1 : ℝ) / (t + ell : ℝ) ^ 2) := by
            rw [div_eq_mul_inv]
            ring
    _ ≤ ((((ell : ℝ) ^ 2) / 2) * B) * (2 / (t + ell : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hfrac (by positivity)
    _ = ((ell : ℝ) ^ 2) * B / (t + ell : ℝ) := by
          rw [div_eq_mul_inv]
          ring

/-- Auxiliary coefficient bound for the refined open-loop stability step. -/
lemma openLoop_refined_coeff_le_one {ell : ℕ} (hell : 2 ≤ ell) (t : ℕ) :
    (t : ℝ) * (t + ell + 1 : ℝ) / (t + ell : ℝ) ^ 2 +
      (1 / 2 : ℝ) * (t + ell + 1 : ℝ) / (t + ell : ℝ) ^ 2 ≤ 1 := by
  have hden_pos : 0 < (t + ell : ℝ) ^ 2 := by positivity
  rw [← add_div]
  have hell_ge : (2 : ℝ) ≤ ell := by exact_mod_cast hell
  exact (_root_.div_le_iff₀ hden_pos).2 (by nlinarith [show (0 : ℝ) ≤ t by positivity])

/-- The refined open-loop coefficient is separated from `1` by a concrete
`1 / (2 (t + ell))` slack. -/
lemma openLoop_refined_coeff_drop {ell : ℕ} (hell : 2 ≤ ell) (t : ℕ) :
    (t : ℝ) * (t + ell + 1 : ℝ) / (t + ell : ℝ) ^ 2 +
      (1 / 2 : ℝ) * (t + ell + 1 : ℝ) / (t + ell : ℝ) ^ 2 ≤
        1 - 1 / (2 * (t + ell : ℝ)) := by
  have hEq :
      (t : ℝ) * (t + ell + 1 : ℝ) / (t + ell : ℝ) ^ 2 +
        (1 / 2 : ℝ) * (t + ell + 1 : ℝ) / (t + ell : ℝ) ^ 2 =
          1 -
            (((2 * (ell : ℝ) - 3) * t + 2 * (ell : ℝ) ^ 2 - (ell : ℝ) - 1) /
              (2 * (t + ell : ℝ) ^ 2)) := by
    have hneq : (t + ell : ℝ) ≠ 0 := by positivity
    field_simp [hneq]
    ring
  rw [hEq]
  have hslack :
      1 / (2 * (t + ell : ℝ)) ≤
        ((2 * (ell : ℝ) - 3) * t + 2 * (ell : ℝ) ^ 2 - (ell : ℝ) - 1) /
          (2 * (t + ell : ℝ) ^ 2) := by
    have hneq : (t + ell : ℝ) ≠ 0 := by positivity
    have hnum :
        (t + ell : ℝ) ≤ (2 * (ell : ℝ) - 3) * t + 2 * (ell : ℝ) ^ 2 - (ell : ℝ) - 1 := by
      have hell_ge : (2 : ℝ) ≤ ell := by exact_mod_cast hell
      nlinarith [show (0 : ℝ) ≤ t by positivity]
    have hleft :
        1 / (2 * (t + ell : ℝ)) = (t + ell : ℝ) / (2 * (t + ell : ℝ) ^ 2) := by
      field_simp [hneq]
    rw [hleft]
    exact div_le_div_of_nonneg_right hnum (by positivity : 0 ≤ 2 * (t + ell : ℝ) ^ 2)
  linarith

/-- Scaling the standard one-step bound by `t + ell + 1` yields the `h_{t+1}`
form used in the generalized open-loop proof. -/
lemma openLoop_scaled_standard_eq {ell : ℕ} (hell : 1 ≤ ell)
    {F : ℕ → ℝ} {Dsq L : ℝ} (t : ℕ) :
    (t + ell + 1 : ℝ) *
        ((1 - (ell : ℝ) / (t + ell : ℝ)) * F t +
          (L / 2) * ((ell : ℝ) / (t + ell : ℝ)) ^ 2 * Dsq) =
      ((t : ℝ) * (t + ell + 1 : ℝ) / (t + ell : ℝ) ^ 2) * ((t + ell : ℝ) * F t) +
        (((ell : ℝ) ^ 2) / 2) * L * Dsq * (t + ell + 1 : ℝ) / (t + ell : ℝ) ^ 2 := by
  have hden_pos : (0 : ℝ) < t + ell := by
    have hell_pos : (0 : ℝ) < ell := by
      exact_mod_cast lt_of_lt_of_le (by norm_num : 0 < (1 : ℕ)) hell
    nlinarith
  have hneq : (t + ell : ℝ) ≠ 0 := ne_of_gt hden_pos
  field_simp [hneq]
  ring

/-- Scaling the refined one-step bound by `t + ell + 1` yields the `h_{t+1}`
form used in the generalized open-loop proof. -/
lemma openLoop_scaled_refined_eq {ell : ℕ} (hell : 1 ≤ ell)
    {F δ : ℕ → ℝ} {L : ℝ} (t : ℕ) :
    (t + ell + 1 : ℝ) *
        ((1 - (ell : ℝ) / (t + ell : ℝ)) * F t +
          L * ((ell : ℝ) / (t + ell : ℝ)) ^ 2 * (δ t) ^ 2) =
      ((t : ℝ) * (t + ell + 1 : ℝ) / (t + ell : ℝ) ^ 2) * ((t + ell : ℝ) * F t) +
        ((ell : ℝ) ^ 2) * L * (δ t) ^ 2 * (t + ell + 1 : ℝ) / (t + ell : ℝ) ^ 2 := by
  have hden_pos : (0 : ℝ) < t + ell := by
    have hell_pos : (0 : ℝ) < ell := by
      exact_mod_cast lt_of_lt_of_le (by norm_num : 0 < (1 : ℕ)) hell
    nlinarith
  have hneq : (t + ell : ℝ) ≠ 0 := ne_of_gt hden_pos
  field_simp [hneq]
  ring

/-- If `H >= eps`, then the refined open-loop affine update is already smaller
than `H` by at least `eps / (2 (t + ell))`. -/
lemma openLoop_drop_bound {ell : ℕ} (hell : 2 ≤ ell)
    (t : ℕ) {eps H : ℝ} (heps : 0 ≤ eps) (hH : eps ≤ H) :
    (t : ℝ) * (t + ell + 1 : ℝ) / (t + ell : ℝ) ^ 2 * H +
      (eps / 2) * (t + ell + 1 : ℝ) / (t + ell : ℝ) ^ 2 ≤
        H - eps / (2 * (t + ell : ℝ)) := by
  let a : ℝ := (t : ℝ) * (t + ell + 1 : ℝ) / (t + ell : ℝ) ^ 2
  let c : ℝ := (t + ell + 1 : ℝ) / (t + ell : ℝ) ^ 2
  have hH_nonneg : 0 ≤ H := le_trans heps hH
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    positivity
  have hβ : (eps / 2) * c ≤ (H / 2) * c := by
    exact mul_le_mul_of_nonneg_right (by linarith) hc_nonneg
  have hcoeff :
      a + (1 / 2 : ℝ) * c ≤ 1 - 1 / (2 * (t + ell : ℝ)) := by
    dsimp [a, c]
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      openLoop_refined_coeff_drop hell t
  have hscaled :
      H * (a + (1 / 2 : ℝ) * c) ≤ H * (1 - 1 / (2 * (t + ell : ℝ))) := by
    exact mul_le_mul_of_nonneg_left hcoeff hH_nonneg
  have hdiv :
      eps / (2 * (t + ell : ℝ)) ≤ H / (2 * (t + ell : ℝ)) := by
    have hfac_nonneg : 0 ≤ (2 * (t + ell : ℝ))⁻¹ := by positivity
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      (mul_le_mul_of_nonneg_right hH hfac_nonneg)
  calc
    (t : ℝ) * (t + ell + 1 : ℝ) / (t + ell : ℝ) ^ 2 * H +
        (eps / 2) * (t + ell + 1 : ℝ) / (t + ell : ℝ) ^ 2
        = a * H + (eps / 2) * c := by
            dsimp [a, c]
            ring
    _ ≤ a * H + (H / 2) * c := by linarith
    _ = H * (a + (1 / 2 : ℝ) * c) := by ring
    _ ≤ H * (1 - 1 / (2 * (t + ell : ℝ))) := hscaled
    _ = H - H / (2 * (t + ell : ℝ)) := by ring
    _ ≤ H - eps / (2 * (t + ell : ℝ)) := by linarith

/-- On the block `N0 <= t <= 2 N0`, the reciprocal denominator `2 (t + ell)`
is at most `4 (N0 + ell)`. -/
lemma openLoop_blockFraction_bound {ell : ℕ} (hell : 1 ≤ ell)
    {eps : ℝ} (heps : 0 ≤ eps) {N0 t : ℕ}
    (htN0 : t ≤ 2 * N0) :
    eps / (4 * (N0 + ell : ℝ)) ≤ eps / (2 * (t + ell : ℝ)) := by
  have hden_nat : 2 * (t + ell) ≤ 4 * (N0 + ell) := by
    omega
  have hden : 2 * (t + ell : ℝ) ≤ 4 * (N0 + ell : ℝ) := by
    exact_mod_cast hden_nat
  have hleft_pos : (0 : ℝ) < 2 * (t + ell : ℝ) := by
    have hell_pos : (0 : ℝ) < ell := by
      exact_mod_cast lt_of_lt_of_le (by norm_num : 0 < (1 : ℕ)) hell
    nlinarith
  have hinv :
      (4 * (N0 + ell : ℝ))⁻¹ ≤ (2 * (t + ell : ℝ))⁻¹ := by
    exact inv_anti₀ hleft_pos hden
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
    (mul_le_mul_of_nonneg_left hinv heps)

/-- Arithmetic update for the canonical step size `γ_t = 2 / (t + 2)`. -/
lemma standard_rate_update (L Dsq : ℝ) (hL : 0 ≤ L) (hDsq : 0 ≤ Dsq) (t : ℕ) :
    (1 - 2 / (t + 2 : ℝ)) * (2 * L * Dsq / (t + 2 : ℝ)) +
        (L / 2) * (2 / (t + 2 : ℝ)) ^ 2 * Dsq ≤
      (2 * L * Dsq) / (t + 3 : ℝ) := by
  have htwo : (0 : ℝ) < t + 2 := by positivity
  have hthree : (0 : ℝ) < t + 3 := by positivity
  have hcoeff_eq :
      (1 - 2 / (t + 2 : ℝ)) * (2 / (t + 2 : ℝ)) + (1 / 2 : ℝ) * (2 / (t + 2 : ℝ)) ^ 2 =
        2 * (t + 1 : ℝ) / (t + 2 : ℝ) ^ 2 := by
    field_simp [htwo.ne']
    ring
  have hcoeff_bound :
      2 * (t + 1 : ℝ) / (t + 2 : ℝ) ^ 2 ≤ 2 / (t + 3 : ℝ) := by
    have hsq : (0 : ℝ) < (t + 2 : ℝ) ^ 2 := by positivity
    refine (_root_.le_div_iff₀ hthree).2 ?_
    have htmp : 2 * (t + 1 : ℝ) * (t + 3) / (t + 2 : ℝ) ^ 2 ≤ 2 := by
      refine (_root_.div_le_iff₀ hsq).2 ?_
      nlinarith
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using htmp
  have hcoeff :
      (1 - 2 / (t + 2 : ℝ)) * (2 / (t + 2 : ℝ)) + (1 / 2 : ℝ) * (2 / (t + 2 : ℝ)) ^ 2 ≤
        2 / (t + 3 : ℝ) := by
    rw [hcoeff_eq]
    exact hcoeff_bound
  have hLD_nonneg : 0 ≤ L * Dsq := by nlinarith
  rw [show (1 - 2 / (t + 2 : ℝ)) * (2 * L * Dsq / (t + 2 : ℝ)) +
        (L / 2) * (2 / (t + 2 : ℝ)) ^ 2 * Dsq =
          (L * Dsq) *
            ((1 - 2 / (t + 2 : ℝ)) * (2 / (t + 2 : ℝ)) + (1 / 2 : ℝ) * (2 / (t + 2 : ℝ)) ^ 2) by
        ring]
  rw [show (2 * L * Dsq) / (t + 3 : ℝ) = (L * Dsq) * (2 / (t + 3 : ℝ)) by ring]
  exact mul_le_mul_of_nonneg_left hcoeff hLD_nonneg

omit [InnerProductSpace ℝ E] in
/-- Shared inductive step for the three standard-step-size O(1/t) rate proofs (γ_t = 2/(t+2)).
Abstracts over current gap `a` and next gap `b`; caller supplies the one-step bound. -/
private lemma standard_rate_induction_step
    {L : NNReal} {a b B : ℝ} (hB_nonneg : 0 ≤ B)
    (hcurv_bound : (L : ℝ) * (Metric.diam C) ^ 2 ≤ B)
    (t : ℕ)
    (ih : a ≤ (2 * B) / (t + 2 : ℝ))
    (hstep : b ≤ (1 - 2 / (t + 2 : ℝ)) * a +
        (L / 2 : ℝ) * (2 / (t + 2 : ℝ)) ^ 2 * (Metric.diam C) ^ 2) :
    b ≤ (2 * B) / ((t + 1 : ℕ) + 2 : ℝ) := by
  have hcoeff_nonneg : 0 ≤ 1 - 2 / (t + 2 : ℝ) :=
    sub_nonneg.mpr (standardStepSize_mem_Icc t).2
  have hcurv := curv_bound_of_LD_le (L := L) (γ := 2 / (t + 2 : ℝ)) hcurv_bound
  have hmiddle :
      (1 - 2 / (t + 2 : ℝ)) * a +
          (L / 2 : ℝ) * (2 / (t + 2 : ℝ)) ^ 2 * (Metric.diam C) ^ 2 ≤
        (1 - 2 / (t + 2 : ℝ)) * ((2 * B) / (t + 2 : ℝ)) +
          (B / 2 : ℝ) * (2 / (t + 2 : ℝ)) ^ 2 :=
    add_le_add (mul_le_mul_of_nonneg_left ih hcoeff_nonneg) hcurv
  have htail :
      (1 - 2 / (t + 2 : ℝ)) * ((2 * B) / (t + 2 : ℝ)) +
          (B / 2 : ℝ) * (2 / (t + 2 : ℝ)) ^ 2 ≤
        (2 * B) / (t + 3 : ℝ) := by
    simpa using standard_rate_update (L := B) (Dsq := 1) hB_nonneg (by positivity) t
  have hsucc_denom : ((t + 1 : ℕ) : ℝ) + 2 = t + 3 := by
    push_cast; ring
  rw [hsucc_denom]
  exact hstep.trans (hmiddle.trans htail)

/-- [FW-STD] The Frank-Wolfe convergence theorem for the canonical step size
`γ_t = 2 / (t + 2)`: `O(1/t)` rate on compact convex sets. -/
theorem frank_wolfe_convergence_of_initialGap_le
  (hC_convex : Convex ℝ C) (f : E → ℝ) (f' : E → E) (L : NNReal)
  (hSmooth : IsLipschitzSmoothUpperBound f L f')
  (hConv : IsFirstOrderConvex f f')
  {x_star : E} (hx_star : x_star ∈ C)
  {x0 : E} (hx0 : x0 ∈ C)
  {B : ℝ} (hB_nonneg : 0 ≤ B)
  (h0_bound : f x0 - f x_star ≤ B)
  (hcurv_bound : (L : ℝ) * (Metric.diam C) ^ 2 ≤ B) :
  ∀ t : ℕ, f (frankWolfeSequence O f' x0 t) - f x_star ≤
    (2 * B) / (t + 2 : ℝ) :=
by
  intro t
  induction t with
  | zero =>
      have hbase :
          f (frankWolfeSequence O f' x0 0) - f x_star ≤
            (2 * B) / (0 + 2 : ℝ) := by
        calc
          f (frankWolfeSequence O f' x0 0) - f x_star
              = f x0 - f x_star := by simp [frankWolfeSequence, frankWolfeOpenLoopSequence]
          _ ≤ B := h0_bound
          _ = (2 * B) / (0 + 2 : ℝ) := by ring
      have hzero :
          (2 * B) / ((0 : ℕ) + 2 : ℝ) =
            (2 * B) / (0 + 2 : ℝ) := by
        ring_nf
      rw [hzero]
      exact hbase
  | succ t ih =>
      have hx_t :
          frankWolfeSequence O f' x0 t ∈ C :=
        frankWolfeSequence_mem O hC_convex f' hx0 t
      have hstep :
          f (frankWolfeSequence O f' x0 (t + 1)) - f x_star ≤
            (1 - 2 / (t + 2 : ℝ)) *
                (f (frankWolfeSequence O f' x0 t) - f x_star) +
              (L / 2 : ℝ) * (2 / (t + 2 : ℝ)) ^ 2 * (Metric.diam C) ^ 2 := by
        simpa [frankWolfeSequence, frankWolfeOpenLoopSequence, openLoopStepSize] using
          (frankWolfeStep_gap_bound (O := O)
            (f := f) (f' := f') (L := L) hSmooth hConv
            (x := frankWolfeSequence O f' x0 t) (x_star := x_star)
            hx_t hx_star (γ := 2 / (t + 2 : ℝ))
            (standardStepSize_mem_Icc t))
      exact standard_rate_induction_step hB_nonneg hcurv_bound t ih hstep

/-- [FW-STD] The Frank-Wolfe convergence theorem for the canonical step size
`γ_t = 2 / (t + 2)`: `O(1/t)` rate on compact convex sets. -/
theorem frank_wolfe_convergence
  (hC_convex : Convex ℝ C) (f : E → ℝ) (f' : E → E) (L : NNReal)
  (hSmooth : IsLipschitzSmoothUpperBound f L f')
  (hConv : IsFirstOrderConvex f f')
  {x_star : E} (hx_star : x_star ∈ C)
  {x0 : E} (hx0 : x0 ∈ C)
  (h0_bound : f x0 - f x_star ≤ L * (Metric.diam C) ^ 2) :
  ∀ t : ℕ, f (frankWolfeSequence O f' x0 t) - f x_star ≤
    (2 * L * (Metric.diam C) ^ 2) / (t + 2 : ℝ) :=
by
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    (frank_wolfe_convergence_of_initialGap_le
      (O := O)
      hC_convex f f' L hSmooth hConv hx_star hx0
      (B := (L : ℝ) * (Metric.diam C) ^ 2)
      (by positivity) h0_bound le_rfl)

theorem exact_line_search_convergence_of_initialGap_le
  (hC_convex : Convex ℝ C) (f : E → ℝ) (f' : E → E)
  (hLS : LineSearch O f f')
  (L : NNReal)
  (hSmooth : IsLipschitzSmoothUpperBound f L f')
  (hConv : IsFirstOrderConvex f f')
  {x_star : E} (hx_star : x_star ∈ C)
  {x0 : E} (hx0 : x0 ∈ C)
  {B : ℝ} (hB_nonneg : 0 ≤ B)
  (h0_bound : f x0 - f x_star ≤ B)
  (hcurv_bound : (L : ℝ) * (Metric.diam C) ^ 2 ≤ B) :
  ∀ t : ℕ,
    f (exactLineSearchSequence O f f' hLS x0 t) - f x_star ≤
      (2 * B) / (t + 2 : ℝ) := by
  intro t
  induction t with
  | zero =>
      have hbase :
          f (exactLineSearchSequence O f f' hLS x0 0) - f x_star ≤
            (2 * B) / (0 + 2 : ℝ) := by
        calc
          f (exactLineSearchSequence O f f' hLS x0 0) - f x_star
              = f x0 - f x_star := by simp [exactLineSearchSequence]
          _ ≤ B := h0_bound
          _ = (2 * B) / (0 + 2 : ℝ) := by ring
      have hzero :
          (2 * B) / ((0 : ℕ) + 2 : ℝ) =
            (2 * B) / (0 + 2 : ℝ) := by
        ring_nf
      rw [hzero]
      exact hbase
  | succ t ih =>
      have hx_t :
          exactLineSearchSequence O f f' hLS x0 t ∈ C :=
        exactLineSearchSequence_mem
          (O := O)
          hC_convex f f' hLS hx0 t
      have hstep :
          f (exactLineSearchSequence O f f' hLS x0 (t + 1)) - f x_star ≤
            (1 - 2 / (t + 2 : ℝ)) *
                (f (exactLineSearchSequence O f f' hLS x0 t) - f x_star) +
              (L / 2 : ℝ) * (2 / (t + 2 : ℝ)) ^ 2 * (Metric.diam C) ^ 2 := by
        simpa [exactLineSearchSequence] using
          (exactLineSearch_gap_bound
            (O := O)
            (f := f) (f' := f') (L := L) hLS hSmooth hConv
            (x := exactLineSearchSequence O f f' hLS x0 t)
            (x_star := x_star) hx_t hx_star
            (γ := 2 / (t + 2 : ℝ)) (standardStepSize_mem_Icc t))
      exact standard_rate_induction_step hB_nonneg hcurv_bound t ih hstep

/-- [FW-STD-LS] Exact line-search Frank-Wolfe satisfies the same standard
`O(1/t)` rate on compact convex sets. -/
theorem exact_line_search_convergence
  (hC_convex : Convex ℝ C) (f : E → ℝ) (f' : E → E)
  (hLS : LineSearch O f f')
  (L : NNReal)
  (hSmooth : IsLipschitzSmoothUpperBound f L f')
  (hConv : IsFirstOrderConvex f f')
  {x_star : E} (hx_star : x_star ∈ C)
  {x0 : E} (hx0 : x0 ∈ C)
  (h0_bound : f x0 - f x_star ≤ L * (Metric.diam C) ^ 2) :
  ∀ t : ℕ,
    f (exactLineSearchSequence O f f' hLS x0 t) - f x_star ≤
      (2 * L * (Metric.diam C) ^ 2) / (t + 2 : ℝ) := by
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    (exact_line_search_convergence_of_initialGap_le
      (O := O)
      hC_convex f f' hLS L hSmooth hConv hx_star hx0
      (B := (L : ℝ) * (Metric.diam C) ^ 2)
      (by positivity) h0_bound le_rfl)

/-- [FW-STD-SS] The global short-step Frank-Wolfe sequence satisfies the same
standard `O(1/t)` rate on compact convex sets. -/
theorem global_short_step_convergence_of_initialGap_le
  (hC_convex : Convex ℝ C) (f : E → ℝ) (f' : E → E) (L : NNReal)
  (hL : 0 < L)
  (hSmooth : IsLipschitzSmoothUpperBound f L f')
  (hConv : IsFirstOrderConvex f f')
  {x_star : E} (hx_star : x_star ∈ C)
  {x0 : E} (hx0 : x0 ∈ C)
  {B : ℝ} (hB_nonneg : 0 ≤ B)
  (h0_bound : f x0 - f x_star ≤ B)
  (hcurv_bound : (L : ℝ) * (Metric.diam C) ^ 2 ≤ B) :
  ∀ t : ℕ, f (globalShortStepSequence O f' L x0 t) - f x_star ≤
    (2 * B) / (t + 2 : ℝ) := by
  intro t
  induction t with
  | zero =>
      have hbase :
          f (globalShortStepSequence O f' L x0 0) - f x_star ≤
            (2 * B) / (0 + 2 : ℝ) := by
        calc
          f (globalShortStepSequence O f' L x0 0) - f x_star
              = f x0 - f x_star := by simp [globalShortStepSequence]
          _ ≤ B := h0_bound
          _ = (2 * B) / (0 + 2 : ℝ) := by ring
      have hzero :
          (2 * B) / ((0 : ℕ) + 2 : ℝ) =
            (2 * B) / (0 + 2 : ℝ) := by
        ring_nf
      rw [hzero]
      exact hbase
  | succ t ih =>
      have hx_t :
          globalShortStepSequence O f' L x0 t ∈ C :=
        globalShortStepSequence_mem O hC_convex f' L hx0 t
      have hstep :
          f (globalShortStepSequence O f' L x0 (t + 1)) - f x_star ≤
            (1 - 2 / (t + 2 : ℝ)) *
                (f (globalShortStepSequence O f' L x0 t) - f x_star) +
              (L / 2 : ℝ) * (2 / (t + 2 : ℝ)) ^ 2 * (Metric.diam C) ^ 2 := by
        simpa [globalShortStepSequence] using
          (globalShortStep_gap_bound (O := O)
            (f := f) (f' := f') (L := L) (hL := hL) hSmooth hConv
            (x := globalShortStepSequence O f' L x0 t) (x_star := x_star)
            hx_t hx_star (γ := 2 / (t + 2 : ℝ))
            (standardStepSize_mem_Icc t))
      exact standard_rate_induction_step hB_nonneg hcurv_bound t ih hstep

/-- [FW-STD-SS] The global short-step Frank-Wolfe sequence satisfies the same
standard `O(1/t)` rate on compact convex sets. -/
theorem global_short_step_convergence
  (hC_convex : Convex ℝ C) (f : E → ℝ) (f' : E → E) (L : NNReal)
  (hL : 0 < L)
  (hSmooth : IsLipschitzSmoothUpperBound f L f')
  (hConv : IsFirstOrderConvex f f')
  {x_star : E} (hx_star : x_star ∈ C)
  {x0 : E} (hx0 : x0 ∈ C)
  (h0_bound : f x0 - f x_star ≤ L * (Metric.diam C) ^ 2) :
  ∀ t : ℕ, f (globalShortStepSequence O f' L x0 t) - f x_star ≤
    (2 * L * (Metric.diam C) ^ 2) / (t + 2 : ℝ) := by
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    (global_short_step_convergence_of_initialGap_le
      (O := O)
      hC_convex f f' L hL hSmooth hConv hx_star hx0
      (B := (L : ℝ) * (Metric.diam C) ^ 2)
      (by positivity) h0_bound le_rfl)

/-- [FW-STD-AFTER-FIRST] The canonical open-loop Frank-Wolfe sequence satisfies
the standard `2LD²/(t+2)` bound after the first step, with no initial-gap
assumption. -/
theorem frank_wolfe_convergence_after_first_step
  (hC_convex : Convex ℝ C) (f : E → ℝ) (f' : E → E) (L : NNReal)
  (hSmooth : IsLipschitzSmoothUpperBound f L f')
  (hConv : IsFirstOrderConvex f f')
  {x_star : E} (hx_star : x_star ∈ C)
  {x0 : E} (hx0 : x0 ∈ C) :
  ∀ t : ℕ, 1 ≤ t →
    f (frankWolfeSequence O f' x0 t) - f x_star ≤
      (2 * L * (Metric.diam C) ^ 2) / (t + 2 : ℝ) := by
  let B : ℝ := (L : ℝ) * (Metric.diam C) ^ 2
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    positivity
  intro t ht
  rcases t with _ | n
  · omega
  · clear ht
    induction n with
    | zero =>
        have hstep :
            f (frankWolfeSequence O f' x0 1) - f x_star ≤
              ((L : ℝ) / 2) * (Metric.diam C) ^ 2 := by
          have href :
              f (frankWolfeStep O f' x0 (1 : ℝ)) - f x_star ≤
                (1 - (1 : ℝ)) * (f x0 - f x_star) +
                  (L / 2 : ℝ) * (1 : ℝ) ^ 2 * (Metric.diam C) ^ 2 := by
            exact
              frankWolfeStep_gap_bound
                (O := O)
                (f := f) (f' := f') (L := L) hSmooth hConv
                (x := x0) (x_star := x_star) hx0 hx_star
                (γ := 1) (by constructor <;> norm_num)
          simpa [frankWolfeSequence, frankWolfeOpenLoopSequence, openLoopStepSize] using href
        have hhalf :
            ((L : ℝ) / 2) * (Metric.diam C) ^ 2 ≤
              (2 * L * (Metric.diam C) ^ 2) / (1 + 2 : ℝ) := by
          dsimp [B] at hB_nonneg
          nlinarith
        simpa using hstep.trans hhalf
    | succ n ih =>
        have hx_t :
            frankWolfeSequence O f' x0 (n + 1) ∈ C :=
          frankWolfeSequence_mem O hC_convex f' hx0 (n + 1)
        have hstep :
            f (frankWolfeSequence O f' x0 ((n + 1) + 1)) - f x_star ≤
              (1 - 2 / (((n + 1 : ℕ) : ℝ) + 2)) *
                  (f (frankWolfeSequence O f' x0 (n + 1)) - f x_star) +
                (L / 2 : ℝ) * (2 / (((n + 1 : ℕ) : ℝ) + 2)) ^ 2 * (Metric.diam C) ^ 2 := by
          simpa [frankWolfeSequence, frankWolfeOpenLoopSequence, openLoopStepSize] using
            (frankWolfeStep_gap_bound
              (O := O)
              (f := f) (f' := f') (L := L) hSmooth hConv
              (x := frankWolfeSequence O f' x0 (n + 1))
              (x_star := x_star) hx_t hx_star
              (γ := 2 / (((n + 1 : ℕ) : ℝ) + 2))
              (standardStepSize_mem_Icc (n + 1)))
        have ihB :
            f (frankWolfeSequence O f' x0 (n + 1)) - f x_star ≤
              (2 * B) / ((n + 1 : ℕ) + 2 : ℝ) := by
          simpa [B, mul_assoc, mul_left_comm, mul_comm] using ih
        simpa [B, mul_assoc, mul_left_comm, mul_comm] using
            (standard_rate_induction_step
              (L := L) (B := B) hB_nonneg (by dsimp [B]; exact le_rfl)
              (n + 1) ihB hstep)

/-- [FW-STD-LS-AFTER-FIRST] Exact line search satisfies the standard
`2LD²/(t+2)` bound after the first step, with no initial-gap assumption. -/
theorem exact_line_search_convergence_after_first_step
  (hC_convex : Convex ℝ C) (f : E → ℝ) (f' : E → E)
  (hLS : LineSearch O f f')
  (L : NNReal)
  (hSmooth : IsLipschitzSmoothUpperBound f L f')
  (hConv : IsFirstOrderConvex f f')
  {x_star : E} (hx_star : x_star ∈ C)
  {x0 : E} (hx0 : x0 ∈ C) :
  ∀ t : ℕ, 1 ≤ t →
    f (exactLineSearchSequence O f f' hLS x0 t) - f x_star ≤
      (2 * L * (Metric.diam C) ^ 2) / (t + 2 : ℝ) := by
  let B : ℝ := (L : ℝ) * (Metric.diam C) ^ 2
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    positivity
  intro t ht
  rcases t with _ | n
  · omega
  · clear ht
    induction n with
    | zero =>
        have hstep :
            f (exactLineSearchSequence O f f' hLS x0 1) - f x_star ≤
              ((L : ℝ) / 2) * (Metric.diam C) ^ 2 := by
          have href :
              f (exactLineSearch O f f' hLS x0) - f x_star ≤
                (1 - (1 : ℝ)) * (f x0 - f x_star) +
                  (L / 2 : ℝ) * (1 : ℝ) ^ 2 * (Metric.diam C) ^ 2 := by
            exact
              exactLineSearch_gap_bound
                (O := O)
                (f := f) (f' := f') (L := L) hLS hSmooth hConv
                (x := x0) (x_star := x_star) hx0 hx_star
                (γ := 1) (by constructor <;> norm_num)
          simpa [exactLineSearchSequence] using href
        have hhalf :
            ((L : ℝ) / 2) * (Metric.diam C) ^ 2 ≤
              (2 * L * (Metric.diam C) ^ 2) / (1 + 2 : ℝ) := by
          dsimp [B] at hB_nonneg
          nlinarith
        simpa using hstep.trans hhalf
    | succ n ih =>
        have hx_t :
            exactLineSearchSequence O f f' hLS x0 (n + 1) ∈ C :=
          exactLineSearchSequence_mem
            (O := O)
            hC_convex f f' hLS hx0 (n + 1)
        have hstep :
            f (exactLineSearchSequence O f f' hLS x0 ((n + 1) + 1)) - f x_star ≤
              (1 - 2 / (((n + 1 : ℕ) : ℝ) + 2)) *
                  (f (exactLineSearchSequence O f f' hLS x0 (n + 1)) - f x_star) +
                (L / 2 : ℝ) * (2 / (((n + 1 : ℕ) : ℝ) + 2)) ^ 2 * (Metric.diam C) ^ 2 := by
          simpa [exactLineSearchSequence] using
            (exactLineSearch_gap_bound
              (O := O)
              (f := f) (f' := f') (L := L) hLS hSmooth hConv
              (x := exactLineSearchSequence O f f' hLS x0 (n + 1))
              (x_star := x_star) hx_t hx_star
              (γ := 2 / (((n + 1 : ℕ) : ℝ) + 2))
              (standardStepSize_mem_Icc (n + 1)))
        have ihB :
            f (exactLineSearchSequence O f f' hLS x0 (n + 1)) -
                f x_star ≤
              (2 * B) / ((n + 1 : ℕ) + 2 : ℝ) := by
          simpa [B, mul_assoc, mul_left_comm, mul_comm] using ih
        simpa [B, mul_assoc, mul_left_comm, mul_comm] using
            (standard_rate_induction_step
              (L := L) (B := B) hB_nonneg (by dsimp [B]; exact le_rfl)
              (n + 1) ihB hstep)

/-- [FW-STD-SS-AFTER-FIRST] The global short-step sequence satisfies the
standard `2LD²/(t+2)` bound after the first step, with no initial-gap
assumption. -/
theorem global_short_step_convergence_after_first_step
  (hC_convex : Convex ℝ C) (f : E → ℝ) (f' : E → E) (L : NNReal)
  (hL : 0 < L)
  (hSmooth : IsLipschitzSmoothUpperBound f L f')
  (hConv : IsFirstOrderConvex f f')
  {x_star : E} (hx_star : x_star ∈ C)
  {x0 : E} (hx0 : x0 ∈ C) :
  ∀ t : ℕ, 1 ≤ t →
    f (globalShortStepSequence O f' L x0 t) - f x_star ≤
      (2 * L * (Metric.diam C) ^ 2) / (t + 2 : ℝ) := by
  let B : ℝ := (L : ℝ) * (Metric.diam C) ^ 2
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    positivity
  intro t ht
  rcases t with _ | n
  · omega
  · clear ht
    induction n with
    | zero =>
        have hstep :
            f (globalShortStepSequence O f' L x0 1) - f x_star ≤
              ((L : ℝ) / 2) * (Metric.diam C) ^ 2 := by
          have href :
              f (globalShortStep O f' L x0) - f x_star ≤
                (1 - (1 : ℝ)) * (f x0 - f x_star) +
                  (L / 2 : ℝ) * (1 : ℝ) ^ 2 * (Metric.diam C) ^ 2 := by
            exact
              globalShortStep_gap_bound
                (O := O)
                (f := f) (f' := f') (L := L) (hL := hL) hSmooth hConv
                (x := x0) (x_star := x_star) hx0 hx_star
                (γ := 1) (by constructor <;> norm_num)
          simpa [globalShortStepSequence] using href
        have hhalf :
            ((L : ℝ) / 2) * (Metric.diam C) ^ 2 ≤
              (2 * L * (Metric.diam C) ^ 2) / (1 + 2 : ℝ) := by
          dsimp [B] at hB_nonneg
          nlinarith
        simpa using hstep.trans hhalf
    | succ n ih =>
        have hx_t :
            globalShortStepSequence O f' L x0 (n + 1) ∈ C :=
          globalShortStepSequence_mem O hC_convex f' L hx0 (n + 1)
        have hstep :
            f (globalShortStepSequence O f' L x0 ((n + 1) + 1)) - f x_star ≤
              (1 - 2 / (((n + 1 : ℕ) : ℝ) + 2)) *
                  (f (globalShortStepSequence O f' L x0 (n + 1)) - f x_star) +
                (L / 2 : ℝ) * (2 / (((n + 1 : ℕ) : ℝ) + 2)) ^ 2 * (Metric.diam C) ^ 2 := by
          simpa [globalShortStepSequence] using
            (globalShortStep_gap_bound
              (O := O)
              (f := f) (f' := f') (L := L) (hL := hL) hSmooth hConv
              (x := globalShortStepSequence O f' L x0 (n + 1))
              (x_star := x_star) hx_t hx_star
              (γ := 2 / (((n + 1 : ℕ) : ℝ) + 2))
              (standardStepSize_mem_Icc (n + 1)))
        have ihB :
            f (globalShortStepSequence O f' L x0 (n + 1)) -
                f x_star ≤
              (2 * B) / ((n + 1 : ℕ) + 2 : ℝ) := by
          simpa [B, mul_assoc, mul_left_comm, mul_comm] using ih
        simpa [B, mul_assoc, mul_left_comm, mul_comm] using
            (standard_rate_induction_step
              (L := L) (B := B) hB_nonneg (by dsimp [B]; exact le_rfl)
              (n + 1) ihB hstep)

/-- Abstract dyadic-blocking convergence kernel.

Given a nonneg sequence `h`, if for every `ε > 0` there exist `T`, an upper bound
`M` with `h T ≤ M`, and a per-block drop `ε_drop > 0` such that
- `h` is `ε`-stable past `T` (once below `ε`, stays below), and
- whenever `h n > ε`, the dyadic block `[Nseq k, Nseq (k+1)]` drops by at least
  `ε_drop` (where `Nseq k = 2^k * (T+1) - 1`),

then `h` tends to zero. -/
lemma boosted_convergence_kernel
    {h : ℕ → ℝ}
    (hnneg : ∀ t, 0 ≤ h t)
    (hT : ∀ ε > 0,
        ∃ (T : ℕ) (M ε_drop : ℝ), 0 < ε_drop ∧ h T ≤ M ∧
          (∀ t ≥ T, h t ≤ ε → h (t + 1) ≤ ε) ∧
          ∀ k n,
            2 ^ (k + 1) * (T + 1) - 1 ≤ n → ε < h n →
            h (2 ^ (k + 1) * (T + 1) - 1) ≤ h (2 ^ k * (T + 1) - 1) - ε_drop) :
    Filter.Tendsto h Filter.atTop (nhds 0) := by
  refine Metric.tendsto_atTop.2 ?_
  intro ε_out hε_out
  let ε : ℝ := ε_out / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨T, M, ε_drop, hε_drop, hbound_T, hstable, hblock_drop⟩ := hT ε hε
  let Nseq : ℕ → ℕ := fun k => 2 ^ k * (T + 1) - 1
  have hNseq_succ : ∀ k, Nseq (k + 1) = 2 * Nseq k + 1 :=
    fun k => by simp only [Nseq]; exact nseq_succ T k
  have hNseq_ge : ∀ k, T ≤ Nseq k :=
    fun k => by simp only [Nseq]; exact nseq_ge T k
  have hNseq_mono : Monotone Nseq := by
    intro i j hij
    induction hij with
    | refl => rfl
    | @step j hj ih =>
        rw [hNseq_succ j]; omega
  obtain ⟨m, hm'⟩ : ∃ m : ℕ, M / ε_drop < m := exists_nat_gt (M / ε_drop)
  have hm : M < (m : ℝ) * ε_drop := (_root_.div_lt_iff₀ hε_drop).1 hm'
  refine ⟨Nseq m, ?_⟩
  intro n hn
  have hle : h n ≤ ε := by
    by_cases hngt : ε < h n
    · have hrec : ∀ k ≤ m, h (Nseq k) ≤ M - (k : ℝ) * ε_drop := by
        intro k hk
        induction k with
        | zero =>
            have hN0 : Nseq 0 = T := by simp [Nseq]
            simp only [Nat.cast_zero, zero_mul, sub_zero, hN0]
            exact hbound_T
        | succ k ih =>
            have hk' : k ≤ m := Nat.le_trans (Nat.le_succ k) hk
            have hdrop : h (Nseq (k + 1)) ≤ h (Nseq k) - ε_drop :=
              hblock_drop k n (le_trans (hNseq_mono hk) hn) hngt
            calc
              h (Nseq (k + 1)) ≤ h (Nseq k) - ε_drop := hdrop
              _ ≤ (M - (k : ℝ) * ε_drop) - ε_drop := by linarith [ih hk']
              _ = M - ((k + 1 : ℕ) : ℝ) * ε_drop := by push_cast; ring
      have hneg : h (Nseq m) < 0 := by linarith [hrec m le_rfl]
      exact absurd hneg (not_lt.mpr (hnneg (Nseq m)))
    · exact le_of_not_gt hngt
  have hlt : h n < ε_out := by dsimp [ε] at hle; linarith
  change dist (h n) 0 < ε_out
  simp only [Real.dist_eq, sub_zero, abs_of_nonneg (hnneg n)]
  exact hlt

end Convergence

end Lemmata.FrankWolfeLDS
