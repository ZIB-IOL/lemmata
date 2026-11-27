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
them. A set is `β`-smooth when its unit outer normals are `β`-Lipschitz
(`Upper.LipschitzNormals C β`). A method requiring no more than `T` calls to a linear
minimization oracle (LMO) is a `Method E T` (`Model.lean`); a randomized method is a family
`s : Ω → Method E T` indexed by the outcome `ω` of a random experiment with law `μ`.
-/

namespace Lemmata.FrankWolfePS
open MeasureTheory
open scoped RealInnerProductSpace NNReal

section Defs
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `O` is a linear minimization oracle (LMO) of `C`: every answer `O q` lies in `C` and
minimizes `⟪q, ·⟫` over `C`. -/
def IsLMO (C : Set E) (O : E → E) : Prop := ∀ q, Unique.MinAt C q (O q)

/-- The LMO of a body on which every nonzero direction has exactly one minimizer: it answers
`q ≠ 0` with this minimizer and `q = 0` with the given point `x₀`. -/
noncomputable def uniqueLMO (C : Set E) (x₀ : E) : E → E := Unique.reply C x₀

end Defs

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- The class `𝒞(β, D, x₀)`: `β`-smooth convex bodies (compact, convex, with nonempty interior)
of diameter at most `D` that contain `x₀` and on which every nonzero direction has exactly one
minimizer. -/
def PrescribedBody (β D : ℝ) (x₀ : Ambient ι) (C : Set (Ambient ι)) : Prop :=
  IsCompact C ∧ Convex ℝ C ∧ (interior C).Nonempty ∧ Metric.diam C ≤ D ∧
    Upper.LipschitzNormals C β ∧ (∀ q, q ≠ 0 → ∃! x, Unique.MinAt C q x) ∧ x₀ ∈ C

/-- The hard body `C_I` at smoothness `β` and diameter `D`: the scaled simplex
`{(a u, 1/β) : u ∈ Δ_I}`, `a = (D - 2/β)/√2`, plus the closed ball of radius `1/β`. -/
noncomputable def hardBody (β D : ℝ) (I : Finset ι) : Set (Ambient ι) :=
  physicalBody ((D - 2 / β) / Real.sqrt 2) (1 / β) I

/-- The vertex LMO of the hard body `C_I`: it answers `q ≠ 0` with `(a e_j, 1/β) - q/(β ‖q‖)`,
where `j ∈ I` has the smallest coordinate `q_j` (the smallest such index in case of ties), and
`q = 0` with `(a e_{i₀}, 0)`. -/
noncomputable def vertexLMO (β D : ℝ) (i₀ : ι) (I : Finset ι) : Ambient ι → Ambient ι :=
  physOracle ((D - 2 / β) / Real.sqrt 2) (1 / β) i₀ I

/-- **Lower bound without tie-breaking.** For every measurable randomized method requiring no
more than `T` LMO calls there is a body `C` of the class `𝒞(β, D, x₀)`, depending on the method
but not on `ω`, on which the method returns, with probability at least `1/5`, an infeasible point
or a point with primal gap at least `L (D - 2/β)² / (64 (T + 1))`. The dimension is
`256 (T + 1) + 1`, and `x₀ = (0.99 (D - 2/β)/√2 · e_{i₀}, 0)`. -/
def LowerBoundUniqueLMO : Prop :=
  ∀ {ι Ω : Type} [Fintype ι] [LinearOrder ι] [MeasurableSpace Ω] (T : ℕ) (i₀ : ι),
    Fintype.card ι = 256 * (T + 1) → ∀ {L β D : ℝ}, 0 < L → 0 < β → 2 < β * D →
    ∀ (μ : Measure Ω) [IsProbabilityMeasure μ] (s : Ω → Method (Ambient ι) T),
      Method.IsMeasurable s →
    ∃ C : Set (Ambient ι), PrescribedBody β D (Unique.hardStart β D i₀) C ∧
      IsLMO C (uniqueLMO C (Unique.hardStart β D i₀)) ∧
      1 / 5 ≤ μ.real {ω | (s ω).run (uniqueLMO C (Unique.hardStart β D i₀)) ∉ C ∨
        L * (D - 2 / β) ^ 2 / (64 * ((T : ℝ) + 1)) ≤
          hardObjective L (1 / β) ((s ω).run (uniqueLMO C (Unique.hardStart β D i₀))) -
            sInf (hardObjective L (1 / β) '' C)}

/-- **Methods with feasible outputs.** If the method returns a point of `C` on every body `C` of
the class, some body of the class gives primal gap at least `L (D - 2/β)² / (64 (T + 1))` with
probability at least `3/4`, and expected primal gap at least `3 L (D - 2/β)² / (256 (T + 1))`. -/
def LowerBoundUniqueFeasible : Prop :=
  ∀ {ι Ω : Type} [Fintype ι] [LinearOrder ι] [MeasurableSpace Ω] (T : ℕ) (i₀ : ι),
    Fintype.card ι = 256 * (T + 1) → ∀ {L β D : ℝ}, 0 < L → 0 < β → 2 < β * D →
    ∀ (μ : Measure Ω) [IsProbabilityMeasure μ] (s : Ω → Method (Ambient ι) T),
      Method.IsMeasurable s →
      (∀ C, PrescribedBody β D (Unique.hardStart β D i₀) C → ∀ ω,
        (s ω).run (uniqueLMO C (Unique.hardStart β D i₀)) ∈ C) →
    ∃ C : Set (Ambient ι), PrescribedBody β D (Unique.hardStart β D i₀) C ∧
      IsLMO C (uniqueLMO C (Unique.hardStart β D i₀)) ∧
      3 / 4 ≤ μ.real {ω | L * (D - 2 / β) ^ 2 / (64 * ((T : ℝ) + 1)) ≤
          hardObjective L (1 / β) ((s ω).run (uniqueLMO C (Unique.hardStart β D i₀))) -
            sInf (hardObjective L (1 / β) '' C)} ∧
      3 * L * (D - 2 / β) ^ 2 / (256 * ((T : ℝ) + 1)) ≤
        ∫ ω, hardObjective L (1 / β) ((s ω).run (uniqueLMO C (Unique.hardStart β D i₀))) -
          sInf (hardObjective L (1 / β) '' C) ∂μ

/-- **Lower bound with the vertex LMO.** With the vertex LMO, which breaks ties by index, a
hard body itself works: diameter exactly `D`, probability `1/4`, constant `32`. -/
def LowerBoundVertexLMO : Prop :=
  ∀ {ι Ω : Type} [Fintype ι] [LinearOrder ι] [MeasurableSpace Ω] (T : ℕ) (i₀ : ι),
    Fintype.card ι = 256 * (T + 1) → ∀ {L β D : ℝ}, 0 < L → 0 < β → 2 < β * D →
    ∀ (μ : Measure Ω) [IsProbabilityMeasure μ] (s : Ω → Method (Ambient ι) T),
      Method.IsMeasurable s →
    ∃ I : Finset ι, I.card = 8 * (T + 1) ∧ i₀ ∈ I ∧
      IsCompact (hardBody β D I) ∧ Convex ℝ (hardBody β D I) ∧
      Metric.diam (hardBody β D I) = D ∧ Upper.LipschitzNormals (hardBody β D I) β ∧
      IsLMO (hardBody β D I) (vertexLMO β D i₀ I) ∧
      1 / 4 ≤ μ.real {ω | (s ω).run (vertexLMO β D i₀ I) ∉ hardBody β D I ∨
        L * (D - 2 / β) ^ 2 / (32 * ((T : ℝ) + 1)) ≤
          hardObjective L (1 / β) ((s ω).run (vertexLMO β D i₀ I)) -
            sInf (hardObjective L (1 / β) '' hardBody β D I)}

/-- **The expected ratio of undecided indices.** For a method requiring no more than `T` calls
to the vertex LMO, the ratio `h/|U|` at the end of the run (`U` the undecided indices, `h` the
number of indices of `I` among them), summed over the index sets `I ∋ i₀` of size
`d = 8 (T + 1)`, is their number times `(d - 1)/(N - 1)`, `N = 256 (T + 1)`. -/
def PosteriorIdentity : Prop :=
  ∀ {ι : Type} [Fintype ι] [LinearOrder ι] (T : ℕ) (i₀ : ι),
    Fintype.card ι = 256 * (T + 1) → ∀ (s : Method (Ambient ι) T) (R : ℝ),
    ∑ S ∈ shells T i₀, (s.orders R i₀).compile.ratio (insert i₀ S)
        (Finset.univ.erase i₀) (8 * (T + 1) - 1) =
      (shells T i₀).card * (((8 * (T + 1) - 1 : ℕ) : ℝ) / ((256 * (T + 1) - 1 : ℕ) : ℝ))

/-- **Vertex LMO, methods with feasible outputs.** If the method returns a point of `C_I` on
every hard body, some hard body gives primal gap at least `L (D - 2/β)² / (32 (T + 1))` with
probability at least `3/4`, and expected primal gap at least `3 L (D - 2/β)² / (128 (T + 1))`. -/
def LowerBoundFeasible : Prop :=
  ∀ {ι Ω : Type} [Fintype ι] [LinearOrder ι] [MeasurableSpace Ω] (T : ℕ) (i₀ : ι),
    Fintype.card ι = 256 * (T + 1) → ∀ {L β D : ℝ}, 0 < L → 0 < β → 2 < β * D →
    ∀ (μ : Measure Ω) [IsProbabilityMeasure μ] (s : Ω → Method (Ambient ι) T),
      Method.IsMeasurable s →
      (∀ I : Finset ι, i₀ ∈ I → ∀ ω, (s ω).run (vertexLMO β D i₀ I) ∈ hardBody β D I) →
    ∃ I : Finset ι, I.card = 8 * (T + 1) ∧ i₀ ∈ I ∧ Metric.diam (hardBody β D I) = D ∧
      3 / 4 ≤ μ.real {ω | L * (D - 2 / β) ^ 2 / (32 * ((T : ℝ) + 1)) ≤
          hardObjective L (1 / β) ((s ω).run (vertexLMO β D i₀ I)) -
            sInf (hardObjective L (1 / β) '' hardBody β D I)} ∧
      3 * L * (D - 2 / β) ^ 2 / (128 * ((T : ℝ) + 1)) ≤
        ∫ ω, hardObjective L (1 / β) ((s ω).run (vertexLMO β D i₀ I)) -
          sInf (hardObjective L (1 / β) '' hardBody β D I) ∂μ

/-- **Deterministic methods.** In dimension `64 (T + 1) + 1`, every deterministic method
requiring no more than `T` calls to the vertex LMO returns, on some hard body, an infeasible point
or a point with primal gap at least `L (D - 2/β)² / (32 (T + 1))`. -/
def LowerBoundDeterministic : Prop :=
  ∀ {ι : Type} [Fintype ι] [LinearOrder ι] (T : ℕ) (i₀ : ι),
    Fintype.card ι = 64 * (T + 1) → ∀ {L β D : ℝ}, 0 < L → 0 < β → 2 < β * D →
    ∀ s : Method (Ambient ι) T,
    ∃ I : Finset ι, I.card = 8 * (T + 1) ∧ i₀ ∈ I ∧ Metric.diam (hardBody β D I) = D ∧
      (s.run (vertexLMO β D i₀ I) ∉ hardBody β D I ∨
        L * (D - 2 / β) ^ 2 / (32 * ((T : ℝ) + 1)) ≤
          hardObjective L (1 / β) (s.run (vertexLMO β D i₀ I)) -
            sInf (hardObjective L (1 / β) '' hardBody β D I))

/-- The penalized error of a point for the hard body `C_I`: its primal gap plus `ρ` times its
distance to `C_I` (the performance measure of Grimmer and Liu). -/
noncomputable def penalizedError (L β D ρ : ℝ) (I : Finset ι) (x : Ambient ι) : ℝ :=
  hardObjective L (1 / β) x - sInf (hardObjective L (1 / β) '' hardBody β D I) +
    ρ * Metric.infDist x (hardBody β D I)

/-- **A penalty for infeasible outputs.** For `ρ ≥ L (2D + 32/β)` and every measurable
randomized method requiring no more than `T` calls to the vertex LMO, some hard body gives
penalized error at least `L (D - 2/β)² / (256 (T + 1))` with probability at least `1/4`; the
mean of the penalized error, in `[0, ∞]`, is at least `L (D - 2/β)² / (1024 (T + 1))`. -/
def LowerBoundPenalized : Prop :=
  ∀ {ι Ω : Type} [Fintype ι] [LinearOrder ι] [MeasurableSpace Ω] (T : ℕ) (i₀ : ι),
    Fintype.card ι = 256 * (T + 1) → ∀ {L β D ρ : ℝ}, 0 < L → 0 < β → 2 < β * D →
    L * (2 * D + 32 / β) ≤ ρ →
    ∀ (μ : Measure Ω) [IsProbabilityMeasure μ] (s : Ω → Method (Ambient ι) T),
      Method.IsMeasurable s →
    ∃ I : Finset ι, I.card = 8 * (T + 1) ∧ i₀ ∈ I ∧ Metric.diam (hardBody β D I) = D ∧
      1 / 4 ≤ μ.real {ω | L * (D - 2 / β) ^ 2 / (256 * ((T : ℝ) + 1)) ≤
        penalizedError L β D ρ I ((s ω).run (vertexLMO β D i₀ I))} ∧
      ENNReal.ofReal (L * (D - 2 / β) ^ 2 / (1024 * ((T : ℝ) + 1))) ≤
        ∫⁻ ω, ENNReal.ofReal (penalizedError L β D ρ I ((s ω).run (vertexLMO β D i₀ I))) ∂μ

/-- **Properties of the hard bodies.** Each hard body is compact and convex with nonempty
interior and diameter exactly `D`; it is `β`-smooth and not `β'`-smooth for `β' < β`; it is not
`(α, 2)`-uniformly convex for any `α > 0`; and the vertex LMO is an LMO of it. -/
def HardBodyGeometry : Prop :=
  ∀ {ι : Type} [Fintype ι] [LinearOrder ι] {β D : ℝ}, 0 < β → 2 < β * D →
    ∀ (i₀ : ι) (I : Finset ι), i₀ ∈ I → 1 < I.card →
      IsCompact (hardBody β D I) ∧ Convex ℝ (hardBody β D I) ∧
      (interior (hardBody β D I)).Nonempty ∧ Metric.diam (hardBody β D I) = D ∧
      Upper.LipschitzNormals (hardBody β D I) β ∧
      (∀ β' < β, ¬ Upper.LipschitzNormals (hardBody β D I) β') ∧
      (∀ α > 0, ¬ Lemmata.FrankWolfe.IsUniformlyConvexSet (hardBody β D I) α 2) ∧
      IsLMO (hardBody β D I) (vertexLMO β D i₀ I)

/-- **The minimizer of the objective.** The objective has the explicit minimizer `z⋆` on each
hard body, and local dual sharpness around any set `M ∋ z⋆` fails for the vertex LMO, for every
constant `A > 0` and every exponent `q`. -/
def HardBodyOptimum : Prop :=
  ∀ {ι : Type} [Fintype ι] [LinearOrder ι] {L β D : ℝ}, 0 < L → 0 < β → 2 < β * D →
    ∀ (i₀ : ι) (I : Finset ι), 1 < I.card →
      let a := (D - 2 / β) / Real.sqrt 2
      hardMinimizer a (1 / β) I ∈ hardBody β D I ∧
      (∀ z ∈ hardBody β D I,
        hardObjective L (1 / β) (hardMinimizer a (1 / β) I) ≤ hardObjective L (1 / β) z) ∧
      ∀ M : Set (Ambient ι), hardMinimizer a (1 / β) I ∈ M → ∀ A q : ℝ, 0 < A →
        ¬ Lemmata.FrankWolfeLDS.LocalDualSharpness (hardBody β D I)
          (vertexLMO β D i₀ I) M A q

/-- **A symmetric thickening reveals the index set.** If the vertices `(A e_j, 1)` are not
perturbed, every lowest point of the thickened simplex rounded by the unit ball has horizontal
coordinates `A/|I|` on `I` and `0` elsewhere, so one call in the vertical direction reveals
`I`. -/
def SymmetricThickeningReveals : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {A s : ℝ}, 0 < s → ∀ {I : Finset ι}, I.Nonempty →
    ∀ x : Ambient ι, Unique.MinAt (Unique.Body (Unique.baseV A) s I) vert x →
      ∀ i, x (some i) = if i ∈ I then A / I.card else 0

/-- **Inner balls and the inner parallel body.** On a nonempty compact convex `β`-smooth set
`C`, every unit outer normal `n` at `z ∈ C` gives the ball `B(z - n/β, 1/β) ⊆ C`; `C` is its
inner parallel body `K` plus the ball of radius `1/β`, and `diam C = 2/β + diam K`. -/
def RollingBall : Prop :=
  ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E] [Nontrivial E]
    {C : Set E}, IsCompact C → Convex ℝ C → C.Nonempty → ∀ {β : ℝ}, 0 < β →
    Upper.LipschitzNormals C β →
      (∀ z ∈ C, ∀ n : E, ‖n‖ = 1 → Supports C z n →
        Metric.closedBall (z - (1 / β) • n) (1 / β) ⊆ C) ∧
      C = Rounded (Upper.erosion C (1 / β)) (1 / β) ∧
      Metric.diam C = 2 * (1 / β) + Metric.diam (Upper.erosion C (1 / β))

/-- **Upper bound for isotropic quadratics.** For `T ≥ 2`, Frank–Wolfe on the inner parallel
body requires no more than `T` LMO calls and no gradient; on every compact convex `β`-smooth set
of diameter at least `2/β`, with every LMO, it returns a point of the set with primal gap at
most `2 L (diam C - 2/β)² / (T + 1)` for `L ‖x - u‖² / 2`. -/
def QuadraticUpperBound : Prop :=
  ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E] (T : ℕ), 2 ≤ T →
    ∀ {L β : ℝ}, 0 < L → 0 < β → ∀ u e : E, e ≠ 0 →
    ∃ s : Method E T, ∀ C : Set E, IsCompact C → Convex ℝ C → Upper.LipschitzNormals C β →
      2 / β ≤ Metric.diam C → ∀ O : Upper.LMO C,
        s.run O.query ∈ C ∧ ∀ w ∈ C, Upper.iso L u (s.run O.query) - Upper.iso L u w ≤
          2 * L * (Metric.diam C - 2 / β) ^ 2 / ((T : ℝ) + 1)

/-- **Smooth convex objectives.** For a differentiable convex objective with `L`-Lipschitz
gradient on a compact convex `β`-smooth set, conditional gradient sliding on `K × B_{1/β}`
evaluates exactly `n ≥ 1` gradients, requires no more than `1 + n + 9 δ² n (n + 1) / A` LMO calls
(`δ = diam C - 2/β`, `A = δ² + 4/β²`), and returns a point of the set with primal gap at most
`15 (2L) A / (2 (n + 1)(n + 2))`. -/
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

/-- **A linear rate with inner and outer tangent balls.** If every boundary point of `C` has an
inner tangent ball of radius `r` and an outer one of radius `R ≥ r`, and `f` is `μ`-strongly
convex with `L`-Lipschitz gradient, projected gradient with Frank–Wolfe projections uses at most
`n + 1` gradients and `n + 1` LMO calls in `n` iterations (one LMO call in total in the variant
`ball = true`, allowed when `R = r`), keeps its iterates in `C`, and has primal gap at most
`(1 - c μ/L)ⁿ L (diam C)² / 2`, `c = min{1, r/(2(R - r))}/2` (`c = 1` if `R = r`). -/
def TangentBallsLinearRate : Prop :=
  ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E] [Nontrivial E]
    {C : Set E}, IsCompact C → Convex ℝ C → ∀ {r R μ : ℝ}, 0 < r → r ≤ R →
    Joint.InnerBall C r → Joint.OuterBall C R → ∀ (O : Upper.LMO C) {f : E → ℝ} {L : ℝ≥0},
    0 < μ → Differentiable ℝ f → StrongConvexOn Set.univ μ f → LipschitzWith L (gradient f) →
    ∀ (ball : Bool), (ball = true → R = r) → ∀ {x₀ : E}, x₀ ∈ C → ∀ n : ℕ,
      let ans := Joint.projectedGradientRun O (gradient f) L r ball x₀ n
      ans.1 ∈ C ∧ ans.2.1 ≤ 1 + n * (if ball then 0 else 1) ∧ ans.2.2 ≤ 1 + n ∧
        ∀ w ∈ C, f ans.1 - f w ≤ (1 - Joint.share r R * (μ / L)) ^ n *
          ((L : ℝ) / 2 * (Metric.diam C) ^ 2)

/-- **The bound of Grimmer and Liu at fixed parameters.** The quantity in their
dimension-dependent lower bound is at most `β δ² / (4 √2 T)` in every dimension `d > T`. -/
def GrimmerLiuComparison : Prop :=
  ∀ {β δ d T : ℝ}, 0 < β → 0 ≤ δ → 0 < T → T < d →
    glExpression β δ d T ≤ β * δ ^ 2 / (4 * Real.sqrt 2 * T)

end Lemmata.FrankWolfePS
