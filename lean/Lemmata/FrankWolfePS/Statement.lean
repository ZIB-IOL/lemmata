module

public import Lemmata.FrankWolfePS.Unique.Prescribed
public import Lemmata.FrankWolfePS.Unique.Symmetric
public import Lemmata.FrankWolfePS.Lower.Family
public import Lemmata.FrankWolfePS.Lower.Comparison
public import Lemmata.FrankWolfePS.Lower.Identity
public import Lemmata.FrankWolfePS.Upper.Method
public import Lemmata.FrankWolfePS.Upper.Complexity
public import Lemmata.FrankWolfePS.Joint.Complexity

@[expose] public section

/-!
# Frank–Wolfe oracle complexity with prescribed set smoothness: the statements

Definitions used by the statements, and every result as a named proposition. `Main.lean` proves
them. A body is `β`-smooth when its unit outward normals are `β`-Lipschitz
(`Upper.LipschitzNormals C β`). A method requiring no more than `T` linear minimization oracle
calls is a `Method E T` (`Model.lean`).
-/

namespace Lemmata.FrankWolfePS
open MeasureTheory
open scoped RealInnerProductSpace NNReal

section Defs
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `O` is an exact linear minimization oracle for `C`: every reply `O q` minimizes `⟪q, ·⟫`
over `C`. -/
def IsLMO (C : Set E) (O : E → E) : Prop := ∀ q, Unique.MinAt C q (O q)

/-- The linear minimization oracle of a body whose nonzero directions have unique minimizers:
the minimizer for `q ≠ 0`, and the public point `x₀` for `q = 0`. -/
noncomputable def uniqueLMO (C : Set E) (x₀ : E) : E → E := Unique.reply C x₀

end Defs

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- The class of the lower bound without tie-breaking: compact convex bodies with nonempty
interior, diameter at most `D`, `β`-Lipschitz unit normals and a unique minimizer in every
nonzero direction, containing the public point `x₀`. -/
def PrescribedBody (β D : ℝ) (x₀ : Ambient ι) (C : Set (Ambient ι)) : Prop :=
  IsCompact C ∧ Convex ℝ C ∧ (interior C).Nonempty ∧ Metric.diam C ≤ D ∧
    Upper.LipschitzNormals C β ∧ (∀ q, q ≠ 0 → ∃! x, Unique.MinAt C q x) ∧ x₀ ∈ C

/-- The hard body at smoothness `β` and diameter `D`: the simplex `{(a u, 1/β) : u ∈ Δ_I}`,
`a = (D - 2/β)/√2`, plus the closed ball of radius `1/β`. -/
noncomputable def hardBody (β D : ℝ) (I : Finset ι) : Set (Ambient ι) :=
  physicalBody ((D - 2 / β) / Real.sqrt 2) (1 / β) I

/-- The vertex oracle of the hard body: for `q ≠ 0` the point `(a e_j, 1/β) - q / (β ‖q‖)`,
where `j ∈ I` minimizes `(q_j, j)` lexicographically; for `q = 0` the public start point
`(a e_anchor, 0)`. -/
noncomputable def vertexOracle (β D : ℝ) (anchor : ι) (I : Finset ι) : Ambient ι → Ambient ι :=
  physOracle ((D - 2 / β) / Real.sqrt 2) (1 / β) anchor I

/-- **No tie-breaking.** For every measurable randomized method requiring no more than `T`
linear minimization oracle calls, there is a body, chosen before the method's random tape, with
a unique minimizer in every nonzero direction, `β`-Lipschitz unit normals and diameter at most
`D`, on which the method returns an infeasible point or one with gap at least
`L (D - 2/β)² / (64 (T + 1))` with probability at least `1/5`. The ambient dimension is
`256 (T + 1) + 1`; the objective is the hard quadratic. -/
def LowerBoundUniqueLMO : Prop :=
  ∀ {ι Ω : Type} [Fintype ι] [LinearOrder ι] [MeasurableSpace Ω] (T : ℕ) (anchor : ι),
    Fintype.card ι = 256 * (T + 1) → ∀ {L β D : ℝ}, 0 < L → 0 < β → 2 < β * D →
    ∀ (μ : Measure Ω) [IsProbabilityMeasure μ] (s : Ω → Method (Ambient ι) T),
      Method.IsMeasurable s →
    ∃ C : Set (Ambient ι), PrescribedBody β D (Unique.hardStart β D anchor) C ∧
      IsLMO C (uniqueLMO C (Unique.hardStart β D anchor)) ∧
      1 / 5 ≤ μ.real {ω | (s ω).run (uniqueLMO C (Unique.hardStart β D anchor)) ∉ C ∨
        L * (D - 2 / β) ^ 2 / (64 * ((T : ℝ) + 1)) ≤
          hardObjective L (1 / β) ((s ω).run (uniqueLMO C (Unique.hardStart β D anchor))) -
            sInf (hardObjective L (1 / β) '' C)}

/-- **Feasible methods, without tie-breaking.** If the method returns a feasible point on every
body of the class (answered by its unique oracle), some body of the class gives gap at least
`L (D - 2/β)² / (64 (T + 1))` with probability at least `3/4`, and expected gap at least
`3 L (D - 2/β)² / (256 (T + 1))`. -/
def LowerBoundUniqueFeasible : Prop :=
  ∀ {ι Ω : Type} [Fintype ι] [LinearOrder ι] [MeasurableSpace Ω] (T : ℕ) (anchor : ι),
    Fintype.card ι = 256 * (T + 1) → ∀ {L β D : ℝ}, 0 < L → 0 < β → 2 < β * D →
    ∀ (μ : Measure Ω) [IsProbabilityMeasure μ] (s : Ω → Method (Ambient ι) T),
      Method.IsMeasurable s →
      (∀ C, PrescribedBody β D (Unique.hardStart β D anchor) C → ∀ ω,
        (s ω).run (uniqueLMO C (Unique.hardStart β D anchor)) ∈ C) →
    ∃ C : Set (Ambient ι), PrescribedBody β D (Unique.hardStart β D anchor) C ∧
      IsLMO C (uniqueLMO C (Unique.hardStart β D anchor)) ∧
      3 / 4 ≤ μ.real {ω | L * (D - 2 / β) ^ 2 / (64 * ((T : ℝ) + 1)) ≤
          hardObjective L (1 / β) ((s ω).run (uniqueLMO C (Unique.hardStart β D anchor))) -
            sInf (hardObjective L (1 / β) '' C)} ∧
      3 * L * (D - 2 / β) ^ 2 / (256 * ((T : ℝ) + 1)) ≤
        ∫ ω, hardObjective L (1 / β) ((s ω).run (uniqueLMO C (Unique.hardStart β D anchor))) -
          sInf (hardObjective L (1 / β) '' C) ∂μ

/-- **With a vertex tie rule.** If the oracle answers with vertices by a fixed lexicographic tie
rule, the hard body itself works: exact diameter `D`, probability `1/4`, constant `32`. -/
def LowerBoundVertexRule : Prop :=
  ∀ {ι Ω : Type} [Fintype ι] [LinearOrder ι] [MeasurableSpace Ω] (T : ℕ) (anchor : ι),
    Fintype.card ι = 256 * (T + 1) → ∀ {L β D : ℝ}, 0 < L → 0 < β → 2 < β * D →
    ∀ (μ : Measure Ω) [IsProbabilityMeasure μ] (s : Ω → Method (Ambient ι) T),
      Method.IsMeasurable s →
    ∃ I : Finset ι, I.card = 8 * (T + 1) ∧ anchor ∈ I ∧
      IsCompact (hardBody β D I) ∧ Convex ℝ (hardBody β D I) ∧
      Metric.diam (hardBody β D I) = D ∧ Upper.LipschitzNormals (hardBody β D I) β ∧
      IsLMO (hardBody β D I) (vertexOracle β D anchor I) ∧
      1 / 4 ≤ μ.real {ω | (s ω).run (vertexOracle β D anchor I) ∉ hardBody β D I ∨
        L * (D - 2 / β) ^ 2 / (32 * ((T : ℝ) + 1)) ≤
          hardObjective L (1 / β) ((s ω).run (vertexOracle β D anchor I)) -
            sInf (hardObjective L (1 / β) '' hardBody β D I)}

/-- **The posterior identity.** For every method requiring no more than `T` calls to the vertex
oracle, the final ratio of hidden labels not yet found to labels not yet tested, summed over the
uniform prior on the hidden sets, is the number of hidden sets times `(d - 1)/(N - 1)`,
`d = 8(T + 1)`, `N = 256(T + 1)`: its average is its initial value. -/
def PosteriorIdentity : Prop :=
  ∀ {ι : Type} [Fintype ι] [LinearOrder ι] (T : ℕ) (anchor : ι),
    Fintype.card ι = 256 * (T + 1) → ∀ (s : Method (Ambient ι) T) (R : ℝ),
    ∑ S ∈ shells T anchor, (s.orders R anchor).compile.ratio (insert anchor S)
        (Finset.univ.erase anchor) (8 * (T + 1) - 1) =
      (shells T anchor).card * (((8 * (T + 1) - 1 : ℕ) : ℝ) / ((256 * (T + 1) - 1 : ℕ) : ℝ))

/-- **Feasible methods.** If the method returns feasible points on every instance of the hard
family, one instance has gap at least `L (D - 2/β)² / (32 (T + 1))` with probability at least
`3/4` and expected gap at least `3 L (D - 2/β)² / (128 (T + 1))`. -/
def LowerBoundFeasible : Prop :=
  ∀ {ι Ω : Type} [Fintype ι] [LinearOrder ι] [MeasurableSpace Ω] (T : ℕ) (anchor : ι),
    Fintype.card ι = 256 * (T + 1) → ∀ {L β D : ℝ}, 0 < L → 0 < β → 2 < β * D →
    ∀ (μ : Measure Ω) [IsProbabilityMeasure μ] (s : Ω → Method (Ambient ι) T),
      Method.IsMeasurable s →
      (∀ I : Finset ι, anchor ∈ I → ∀ ω, (s ω).run (vertexOracle β D anchor I) ∈ hardBody β D I) →
    ∃ I : Finset ι, I.card = 8 * (T + 1) ∧ anchor ∈ I ∧ Metric.diam (hardBody β D I) = D ∧
      3 / 4 ≤ μ.real {ω | L * (D - 2 / β) ^ 2 / (32 * ((T : ℝ) + 1)) ≤
          hardObjective L (1 / β) ((s ω).run (vertexOracle β D anchor I)) -
            sInf (hardObjective L (1 / β) '' hardBody β D I)} ∧
      3 * L * (D - 2 / β) ^ 2 / (128 * ((T : ℝ) + 1)) ≤
        ∫ ω, hardObjective L (1 / β) ((s ω).run (vertexOracle β D anchor I)) -
          sInf (hardObjective L (1 / β) '' hardBody β D I) ∂μ

/-- **Deterministic methods.** In dimension `64 (T + 1) + 1`, every deterministic method
requiring no more than `T` calls to the vertex oracle fails on some body of the hard family: it
returns an infeasible point or one with gap at least `L (D - 2/β)² / (32 (T + 1))`. -/
def LowerBoundDeterministic : Prop :=
  ∀ {ι : Type} [Fintype ι] [LinearOrder ι] (T : ℕ) (anchor : ι),
    Fintype.card ι = 64 * (T + 1) → ∀ {L β D : ℝ}, 0 < L → 0 < β → 2 < β * D →
    ∀ s : Method (Ambient ι) T,
    ∃ I : Finset ι, I.card = 8 * (T + 1) ∧ anchor ∈ I ∧ Metric.diam (hardBody β D I) = D ∧
      (s.run (vertexOracle β D anchor I) ∉ hardBody β D I ∨
        L * (D - 2 / β) ^ 2 / (32 * ((T : ℝ) + 1)) ≤
          hardObjective L (1 / β) (s.run (vertexOracle β D anchor I)) -
            sInf (hardObjective L (1 / β) '' hardBody β D I))

/-- The penalized error of a point for the hard body (the performance measure of Grimmer and
Liu): the gap of the hard objective plus `ρ` times the distance to the body. -/
noncomputable def penalizedError (L β D ρ : ℝ) (I : Finset ι) (x : Ambient ι) : ℝ :=
  hardObjective L (1 / β) x - sInf (hardObjective L (1 / β) '' hardBody β D I) +
    ρ * Metric.infDist x (hardBody β D I)

/-- **A distance penalty for infeasible outputs.** For a penalty weight `ρ ≥ L (2D + 32/β)`, every
measurable randomized method requiring no more than `T` calls to the vertex oracle has, on some
body of the hard family, penalized error at least `L (D - 2/β)² / (256 (T + 1))` with probability
at least `1/4`; the mean of the penalized error, in `[0, ∞]`, is at least
`L (D - 2/β)² / (1024 (T + 1))`. No feasibility is assumed. -/
def LowerBoundPenalized : Prop :=
  ∀ {ι Ω : Type} [Fintype ι] [LinearOrder ι] [MeasurableSpace Ω] (T : ℕ) (anchor : ι),
    Fintype.card ι = 256 * (T + 1) → ∀ {L β D ρ : ℝ}, 0 < L → 0 < β → 2 < β * D →
    L * (2 * D + 32 / β) ≤ ρ →
    ∀ (μ : Measure Ω) [IsProbabilityMeasure μ] (s : Ω → Method (Ambient ι) T),
      Method.IsMeasurable s →
    ∃ I : Finset ι, I.card = 8 * (T + 1) ∧ anchor ∈ I ∧ Metric.diam (hardBody β D I) = D ∧
      1 / 4 ≤ μ.real {ω | L * (D - 2 / β) ^ 2 / (256 * ((T : ℝ) + 1)) ≤
        penalizedError L β D ρ I ((s ω).run (vertexOracle β D anchor I))} ∧
      ENNReal.ofReal (L * (D - 2 / β) ^ 2 / (1024 * ((T : ℝ) + 1))) ≤
        ∫⁻ ω, ENNReal.ofReal (penalizedError L β D ρ I ((s ω).run (vertexOracle β D anchor I))) ∂μ

/-- **The hard family.** Each body is compact and convex with nonempty interior and diameter
exactly `D`; its unit normals are `β`-Lipschitz and no smaller constant works; it is not
uniformly convex for any modulus; the vertex oracle is exact. -/
def HardBodyGeometry : Prop :=
  ∀ {ι : Type} [Fintype ι] [LinearOrder ι] {β D : ℝ}, 0 < β → 2 < β * D →
    ∀ (anchor : ι) (I : Finset ι), anchor ∈ I → 1 < I.card →
      IsCompact (hardBody β D I) ∧ Convex ℝ (hardBody β D I) ∧
      (interior (hardBody β D I)).Nonempty ∧ Metric.diam (hardBody β D I) = D ∧
      Upper.LipschitzNormals (hardBody β D I) β ∧
      (∀ β' < β, ¬ Upper.LipschitzNormals (hardBody β D I) β') ∧
      (∀ α > 0, ¬ Lemmata.FrankWolfe.IsUniformlyConvexSet (hardBody β D I) α 2) ∧
      IsLMO (hardBody β D I) (vertexOracle β D anchor I)

/-- **The optimum of the hard family.** The hard objective has the explicit minimizer `z⋆`
on each body, and local dual sharpness fails at `z⋆` for the vertex oracle: for every constant
`A > 0`, every exponent `q` and every set `M ∋ z⋆`. -/
def HardBodyOptimum : Prop :=
  ∀ {ι : Type} [Fintype ι] [LinearOrder ι] {L β D : ℝ}, 0 < L → 0 < β → 2 < β * D →
    ∀ (anchor : ι) (I : Finset ι), 1 < I.card →
      let a := (D - 2 / β) / Real.sqrt 2
      hardMinimizer a (1 / β) I ∈ hardBody β D I ∧
      (∀ z ∈ hardBody β D I,
        hardObjective L (1 / β) (hardMinimizer a (1 / β) I) ≤ hardObjective L (1 / β) z) ∧
      ∀ M : Set (Ambient ι), hardMinimizer a (1 / β) I ∈ M → ∀ A q : ℝ, 0 < A →
        ¬ Lemmata.FrankWolfeLDS.LocalDualSharpness (hardBody β D I)
          (vertexOracle β D anchor I) M A q

/-- **Why the jitter.** Without jitter the bulged body is symmetric in the hidden labels: its
unique lowest point has horizontal coordinates `A/|I|` on `I` and `0` off `I`, so one vertical
query reveals `I`. -/
def SymmetricBulgeReveals : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {A s : ℝ}, 0 < s → ∀ {I : Finset ι}, I.Nonempty →
    ∀ x : Ambient ι, Unique.MinAt (Unique.Body (Unique.baseV A) s I) vert x →
      ∀ i, x (some i) = if i ∈ I then A / I.card else 0

/-- **Rolling ball and parallel body.** On a compact convex body with `β`-Lipschitz unit
normals, every supporting normal `n` at `z` gives the inner ball `B(z - n/β, 1/β) ⊆ C`, and `C`
is its erosion `K` plus the ball of radius `1/β`, with `diam C = 2/β + diam K`. -/
def RollingBall : Prop :=
  ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E] [Nontrivial E]
    {C : Set E}, IsCompact C → Convex ℝ C → C.Nonempty → ∀ {β : ℝ}, 0 < β →
    Upper.LipschitzNormals C β →
      (∀ z ∈ C, ∀ n : E, ‖n‖ = 1 → Supports C z n →
        Metric.closedBall (z - (1 / β) • n) (1 / β) ⊆ C) ∧
      C = Rounded (Upper.erosion C (1 / β)) (1 / β) ∧
      Metric.diam C = 2 * (1 / β) + Metric.diam (Upper.erosion C (1 / β))

/-- **The matching upper bound.** For `T ≥ 2` there is a method requiring no more than `T`
linear minimization oracle calls (and no gradient) that, on every compact convex body with
`β`-Lipschitz unit normals and diameter at least `2/β`, and for every exact oracle, returns a
feasible point with gap at most `2 L (diam C - 2/β)² / (T + 1)` for the isotropic quadratic
`L ‖x - u‖² / 2`. -/
def QuadraticUpperBound : Prop :=
  ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E] (T : ℕ), 2 ≤ T →
    ∀ {L β : ℝ}, 0 < L → 0 < β → ∀ u e : E, e ≠ 0 →
    ∃ s : Method E T, ∀ C : Set E, IsCompact C → Convex ℝ C → Upper.LipschitzNormals C β →
      2 / β ≤ Metric.diam C → ∀ O : Upper.LMO C,
        s.run O.query ∈ C ∧ ∀ w ∈ C, Upper.iso L u (s.run O.query) - Upper.iso L u w ≤
          2 * L * (Metric.diam C - 2 / β) ^ 2 / ((T : ℝ) + 1)

/-- **Sliding for smooth convex objectives.** For a differentiable convex objective with
`L`-Lipschitz gradient on a compact convex body with `β`-Lipschitz normals, the sliding method
makes exactly `n ≥ 1` gradient evaluations, no more than `1 + n + 9 δ² n (n + 1) / A` linear
minimization oracle calls (`δ = diam C - 2/β`, `A = δ² + 4/β²`), and returns a feasible point
with gap at most `15 (2L) A / (2 (n + 1)(n + 2))`. -/
def SlidingUpperBound : Prop :=
  ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E] {C : Set E},
    IsCompact C → Convex ℝ C → ∀ {β : ℝ}, 0 < β → Upper.LipschitzNormals C β →
    2 * (1 / β) ≤ Metric.diam C → ∀ (O : Upper.LMO C) {f : E → ℝ} {L : ℝ≥0}, 0 < (L : ℝ) →
    Differentiable ℝ f → ConvexOn ℝ Set.univ f → LipschitzWith L (gradient f) →
    ∀ e : E, e ≠ 0 → ∀ {n : ℕ}, 0 < n →
      let δ := Metric.diam C - 2 * (1 / β)
      let A := δ ^ 2 + 4 * (1 / β) ^ 2
      let ans := Upper.slidingRun O (gradient f) L (1 / β) (Metric.diam C) e n
      ans.1 ∈ C ∧ ans.2.2 = n ∧ (ans.2.1 : ℝ) ≤ 1 + n + 9 * δ ^ 2 * (n : ℝ) * ((n : ℝ) + 1) / A ∧
        ∀ w ∈ C, f ans.1 - f w ≤ 15 * (2 * (L : ℝ)) * A / (2 * ((n : ℝ) + 1) * ((n : ℝ) + 2))

/-- **A linear rate with inner and outer tangent balls.** If every supporting normal of `C`
carries an inner ball of radius `r` and an outer ball of radius `R ≥ r`, and `f` is
`μ`-strongly convex with `L`-Lipschitz gradient, the joint method requires one oracle call and
one gradient per iteration (one oracle call in total with `ball = true` when `R = r`), keeps its
iterates feasible, and after `n` iterations has gap at most `(1 - c μ/L)ⁿ L (diam C)² / 2`,
`c = min{1, r/(2(R - r))}/2` (and `c = 1` if `R = r`). -/
def JointLinearRate : Prop :=
  ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E] [Nontrivial E]
    {C : Set E}, IsCompact C → Convex ℝ C → ∀ {r R μ : ℝ}, 0 < r → r ≤ R →
    Joint.InnerBall C r → Joint.OuterBall C R → ∀ (O : Upper.LMO C) {f : E → ℝ} {L : ℝ≥0},
    0 < μ → Differentiable ℝ f → StrongConvexOn Set.univ μ f → LipschitzWith L (gradient f) →
    ∀ (ball : Bool), (ball = true → R = r) → ∀ {x₀ : E}, x₀ ∈ C → ∀ n : ℕ,
      let ans := Joint.jointRun O (gradient f) L r ball x₀ n
      ans.1 ∈ C ∧ ans.2.1 ≤ 1 + n * (if ball then 0 else 1) ∧ ans.2.2 ≤ 1 + n ∧
        ∀ w ∈ C, f ans.1 - f w ≤ (1 - Joint.share r R * (μ / L)) ^ n *
          ((L : ℝ) / 2 * (Metric.diam C) ^ 2)

/-- **Comparison with Grimmer and Liu.** The expression in their dimension-dependent bound is
at most `β δ² / (4 √2 T)` in every dimension `d > T`. -/
def GrimmerLiuComparison : Prop :=
  ∀ {β δ d T : ℝ}, 0 < β → 0 ≤ δ → 0 < T → T < d →
    glExpression β δ d T ≤ β * δ ^ 2 / (4 * Real.sqrt 2 * T)

end Lemmata.FrankWolfePS
