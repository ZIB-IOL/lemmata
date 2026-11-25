module

public import Lemmata.FrankWolfeLDS.Defs
public import Lemmata.FrankWolfeLDS.Proof.AnalyticFacts
public import Mathlib.Tactic

@[expose] public section

namespace Lemmata.FrankWolfeLDS

open InnerProductSpace Set
local notation "inner" => inner ℝ

section FrankWolfe

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {C : Set E}

/-- A linear minimization oracle for a compact set `C`, as the proofs use it: a selection rule
`lmo` that returns a minimizer of `⟪g, ·⟫` over `C` for every direction `g`
(`IsLinearMinimizationOracle`), bundled with the compactness of `C`. Every result below holds
for every such rule. -/
structure Oracle (C : Set E) where
  /-- The selection rule. -/
  lmo : E → E
  /-- It returns a minimizer of the linear functional. -/
  isLMO : IsLinearMinimizationOracle C lmo
  /-- The feasible region is compact. -/
  isCompact : IsCompact C

/-- The canonical (choice-based) oracle of a compact nonempty set. -/
noncomputable def Oracle.ofCompact [CompleteSpace E] (hC_compact : IsCompact C) (hC_nonempty : C.Nonempty) :
    Oracle C where
  lmo g := (LMO_exists hC_compact hC_nonempty g).choose
  isLMO g := (LMO_exists hC_compact hC_nonempty g).choose_spec
  isCompact := hC_compact

/-- The feasible region of an oracle is nonempty. -/
lemma Oracle.nonempty (O : Oracle C) : C.Nonempty := ⟨O.lmo 0, (O.isLMO 0).1⟩

variable (O : Oracle C)

/-- The atom returned by the oracle for the direction `g`. -/
def LMO (g : E) : E := O.lmo g

lemma LMO_mem (g : E) : LMO O g ∈ C := (O.isLMO g).1

lemma LMO_le (g : E) {y : E} (hy : y ∈ C) : (inner g (LMO O g) : ℝ) ≤ inner g y :=
  (O.isLMO g).2 y hy

/-- The Frank-Wolfe iteration step -/
noncomputable def frankWolfeStep (f' : E → E) (x : E) (γ : ℝ) : E :=
  x + γ • (LMO O (f' x) - x)

/-- The open-loop step size `ℓ / (t + ℓ)`. -/
noncomputable def openLoopStepSize (ℓ : ℕ) (t : ℕ) : ℝ :=
  ℓ / (t + ℓ : ℝ)

/-- The open-loop Frank-Wolfe sequence with `γ_t = ℓ / (t + ℓ)`. -/
noncomputable def frankWolfeOpenLoopSequence (ℓ : ℕ) (f' : E → E) (x0 : E) : ℕ → E
  | 0 => x0
  | t + 1 =>
      frankWolfeStep O f'
        (frankWolfeOpenLoopSequence ℓ f' x0 t) (openLoopStepSize ℓ t)

/-- The standard Frank-Wolfe sequence with γ_t = 2 / (t + 2). -/
noncomputable abbrev frankWolfeSequence (f' : E → E) (x0 : E) : ℕ → E :=
  frankWolfeOpenLoopSequence O 2 f' x0

/-- An open-loop step size lies in the unit interval as soon as `ℓ ≥ 1`. -/
lemma openLoopStepSize_mem_Icc {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (t : ℕ) :
    openLoopStepSize ℓ t ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · dsimp [openLoopStepSize]
    exact div_nonneg (by positivity) (by positivity)
  · dsimp [openLoopStepSize]
    have hden : (0 : ℝ) < t + ℓ := by
      exact_mod_cast (show 0 < t + ℓ by omega)
    have hnum : (ℓ : ℝ) ≤ 1 * (t + ℓ : ℝ) := by
      nlinarith
    exact (_root_.div_le_iff₀ hden).2 hnum

/-- The standard Frank-Wolfe step size lies in the unit interval. -/
lemma standardStepSize_mem_Icc (t : ℕ) : (2 / (t + 2 : ℝ)) ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · positivity
  · have hden : (0 : ℝ) < t + 2 := by positivity
    have hnum : (2 : ℝ) ≤ 1 * (t + 2 : ℝ) := by
      nlinarith [show (0 : ℝ) ≤ t by positivity]
    exact (_root_.div_le_iff₀ hden).2 hnum

/-- A Frank-Wolfe step stays in the feasible set when the step size is in `[0, 1]`. -/
lemma frankWolfeStep_mem (hC_convex : Convex ℝ C) (f' : E → E) {x : E} (hx : x ∈ C) {γ : ℝ}
    (hγ : γ ∈ Set.Icc (0 : ℝ) 1) :
    frankWolfeStep O f' x γ ∈ C := by
  simpa [frankWolfeStep] using
    Convex.add_smul_sub_mem hC_convex hx (LMO_mem O (f' x)) hγ

/-- Open-loop iterates remain in the convex set. -/
theorem frankWolfeOpenLoopSequence_mem (hC_convex : Convex ℝ C)
    {ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    (f' : E → E) {x0 : E} (hx0 : x0 ∈ C) (t : ℕ) :
    frankWolfeOpenLoopSequence O ℓ f' x0 t ∈ C := by
  induction t with
  | zero =>
      simpa [frankWolfeOpenLoopSequence] using hx0
  | succ t ih =>
      simpa [frankWolfeOpenLoopSequence] using
        frankWolfeStep_mem O hC_convex f' ih
          (openLoopStepSize_mem_Icc hℓ t)

/-- Iterates remain in the convex set. -/
theorem frankWolfeSequence_mem (hC_convex : Convex ℝ C)
    (f' : E → E) {x0 : E} (hx0 : x0 ∈ C) (t : ℕ) :
    frankWolfeSequence O f' x0 t ∈ C :=
  frankWolfeOpenLoopSequence_mem O hC_convex (by norm_num) f' hx0 t

/-! ### Convergence helper lemmas -/

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
/-- A minimizer over the feasible set has nonnegative primal gap on that set. -/
lemma primalGap_nonneg_of_isMinOn
    (f : E → ℝ)
    {x x_star : E} (hx : x ∈ C)
    (hmin : ∀ y ∈ C, f x_star ≤ f y) :
    0 ≤ f x - f x_star := by
  linarith [hmin x hx]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
/-- If `xStarSeq t` minimizes `f` on `C` with value `f x_star`, then the primal gap
`f (xSeq t) - f x_star` is nonneg for feasible `xSeq t`. -/
lemma primalGap_nonneg_of_minimizerSeq'
    {f : E → ℝ} {x_star : E} {xSeq xStarSeq : ℕ → E}
    (hvalSeq : ∀ t, f (xStarSeq t) = f x_star)
    (hminSeq : ∀ t, ∀ y ∈ C, f (xStarSeq t) ≤ f y)
    (hxSeq : ∀ t, xSeq t ∈ C)
    (t : ℕ) :
    0 ≤ f (xSeq t) - f x_star := by
  have := primalGap_nonneg_of_isMinOn (C := C) (f := f) (hxSeq t) (hminSeq t)
  linarith [hvalSeq t]


omit [InnerProductSpace ℝ E] in
/-- If `δ t = ‖xSeq t - xStarSeq t‖` and the primal gap `f (xSeq t) - f x_star` is
positive for all `t`, then `δ t > 0` for all `t`. -/
lemma norm_sub_pos_of_primalGap_pos_of_valSeq
    {f : E → ℝ} {x_star : E} {xSeq xStarSeq : ℕ → E}
    (hvalSeq : ∀ t, f (xStarSeq t) = f x_star)
    (hF_pos : ∀ t, 0 < f (xSeq t) - f x_star)
    (t : ℕ) :
    0 < ‖xSeq t - xStarSeq t‖ := by
  by_contra h
  push Not at h
  have h0 : ‖xSeq t - xStarSeq t‖ = 0 := le_antisymm h (norm_nonneg _)
  have heq : xSeq t = xStarSeq t :=
    sub_eq_zero.mp (norm_eq_zero.mp h0)
  have : f (xSeq t) - f x_star = 0 := by
    rw [heq, hvalSeq]; ring
  linarith [hF_pos t]

end FrankWolfe

end Lemmata.FrankWolfeLDS
