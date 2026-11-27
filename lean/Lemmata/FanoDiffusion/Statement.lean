module

public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.Probability.Kernel.Composition.ParallelComp
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

@[expose] public section

/-!
# Statements

-- DOCS_BEGIN_STATEMENT
-/

namespace Lemmata.FanoDiffusion

open MeasureTheory ProbabilityTheory InformationTheory Real
open scoped ENNReal

universe u

/-- The **mutual information** of the two coordinates of a joint law `μ` on `α × β`:
`I = D(μ ‖ μ_X ⊗ μ_Y)`, the Kullback–Leibler divergence from the product of the marginals. -/
noncomputable def mutualInfo {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure (α × β)) : ℝ≥0∞ :=
  klDiv μ (μ.fst.prod μ.snd)

/-- The joint law of `(X, X̂)` for a Markov chain `X → Y → X̂`: `μ` is the joint law of `(X, Y)`,
and `X̂` is drawn from `κ(Y)`. -/
noncomputable def chainLaw {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] (μ : Measure (α × β)) (κ : Kernel β γ) : Measure (α × γ) :=
  (Kernel.id ∥ₖ κ) ∘ₘ μ

/-- **Proposition 2.1** for order `α = 1` (information diffusion Fano inequality). Let `P` and `Q`
be probability measures and `R` a measurable event with `p_min ≤ Q(R) ≤ p_max`, where
`0 ≤ p_min`, `0 < p_max` and `p_min + p_max < 1`. If `D(P ‖ Q) < ∞`, then
`P(R) ≤ (D(P ‖ Q) + H(P(R)) + log (1 - p_min))/log ((1 - p_min)/p_max)`, with `H` the binary
entropy. Logarithms are natural. -/
def InfoDiffusionFanoKL : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P Q : Measure Ω) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (R : Set Ω) (pmin pmax : ℝ),
    MeasurableSet R → 0 ≤ pmin → 0 < pmax → pmin + pmax < 1 → pmin ≤ Q.real R →
    Q.real R ≤ pmax → klDiv P Q ≠ ∞ →
      P.real R ≤ ((klDiv P Q).toReal + binEntropy (P.real R) + log (1 - pmin)) /
        log ((1 - pmin) / pmax)

/-- **Proposition 2.2** (Fano inequality for arbitrary relations). Let `X → Y → X̂` be a Markov
chain, with `μ` the joint law of `(X, Y)` and `X̂` drawn from `κ(Y)`, and let `R` be a measurable
relation between values of `X` and of `X̂`. If `p_min ≤ P[(X, x̂) ∈ R] ≤ p_max` for every `x̂`,
where `0 ≤ p_min`, `0 < p_max` and `p_min + p_max < 1`, and `I(X; Y) < ∞`, then
`P[R] ≤ (I(X; X̂) + H(P[R]) + log (1 - p_min))/log ((1 - p_min)/p_max)` and the right-hand side is
at most the same expression with `I(X; Y)`. -/
def FanoArbitraryRelation : Prop :=
  ∀ {α β γ : Type u} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure (α × β)) [IsProbabilityMeasure μ] (κ : Kernel β γ) [IsMarkovKernel κ]
    (R : Set (α × γ)) (pmin pmax : ℝ),
    MeasurableSet R → 0 ≤ pmin → 0 < pmax → pmin + pmax < 1 →
    (∀ z, pmin ≤ μ.fst.real {x | (x, z) ∈ R} ∧ μ.fst.real {x | (x, z) ∈ R} ≤ pmax) →
    mutualInfo μ ≠ ∞ →
      (chainLaw μ κ).real R ≤ ((mutualInfo (chainLaw μ κ)).toReal +
          binEntropy ((chainLaw μ κ).real R) + log (1 - pmin)) / log ((1 - pmin) / pmax) ∧
      ((mutualInfo (chainLaw μ κ)).toReal + binEntropy ((chainLaw μ κ).real R) +
          log (1 - pmin)) / log ((1 - pmin) / pmax) ≤
        ((mutualInfo μ).toReal + binEntropy ((chainLaw μ κ).real R) + log (1 - pmin)) /
          log ((1 - pmin) / pmax)

/-- **Corollary 2.6** (distance-based Fano inequality, mutual information version). Let
`X → Y → X̂` be a Markov chain with `X` uniform on a finite set `α` and `X̂` with values in `α`,
let `ρ : α → α → ℝ` and `t ∈ ℝ`, and let `0 < N < |α|` bound `|{x | ρ(x, x̂) ≤ t}|` for every `x̂`.
With `P_t = P[ρ(X, X̂) > t]`, if `I(X; Y) < ∞` then
`P_t ≥ 1 - (I(X; Y) + H(P_t))/log (|α|/N)`. -/
def DistanceFano : Prop :=
  ∀ {α β : Type u} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace β] (μ : Measure (α × β)) [IsProbabilityMeasure μ] (κ : Kernel β α)
    [IsMarkovKernel κ] (ρ : α → α → ℝ) (t : ℝ) (N : ℕ),
    (∀ x, μ.fst {x} = (Fintype.card α : ℝ≥0∞)⁻¹) → 0 < N → N < Fintype.card α →
    (∀ z, (Finset.univ.filter fun x => ρ x z ≤ t).card ≤ N) → mutualInfo μ ≠ ∞ →
      1 - ((mutualInfo μ).toReal + binEntropy ((chainLaw μ κ).real {p | t < ρ p.1 p.2})) /
          log (Fintype.card α / N) ≤
        (chainLaw μ κ).real {p | t < ρ p.1 p.2}

/-- **Corollary 2.7** (continuous Fano inequality). Let `X → Y → X̂` be a Markov chain with `X`
uniform on a measurable set `S` of finite positive volume and `X̂` with values in the same space,
let `ρ` be measurable, `t ∈ ℝ`, and let `0 < V < vol(S)` bound `vol({x | ρ(x, x̂) ≤ t} ∩ S)` for
every `x̂`. With `P_t = P[ρ(X, X̂) > t]`, if `I(X; Y) < ∞` then
`P_t ≥ 1 - (I(X; Y) + log 2)/log (vol(S)/V)`. -/
def ContinuousFano : Prop :=
  ∀ {α β : Type u} [MeasureSpace α] [MeasurableSpace β] (μ : Measure (α × β))
    [IsProbabilityMeasure μ] (κ : Kernel β α) [IsMarkovKernel κ] (S : Set α) (ρ : α → α → ℝ)
    (t V : ℝ),
    MeasurableSet S → volume S ≠ ∞ → μ.fst = (volume S)⁻¹ • volume.restrict S →
    Measurable (Function.uncurry ρ) → 0 < V → V < volume.real S →
    (∀ z, volume.real ({x | ρ x z ≤ t} ∩ S) ≤ V) → mutualInfo μ ≠ ∞ →
      1 - ((mutualInfo μ).toReal + log 2) / log (volume.real S / V) ≤
        (chainLaw μ κ).real {p | t < ρ p.1 p.2}

/-- The **Hellinger integral** `∫ (dP/dQ)^α dQ` of order `α`. For `α < 1` the singular part of `P`
does not contribute; for `α > 1` it is used with `P ≪ Q`. -/
noncomputable def hellingerInt {Ω : Type*} [MeasurableSpace Ω] (α : ℝ) (P Q : Measure Ω) : ℝ≥0∞ :=
  ∫⁻ x, P.rnDeriv Q x ^ α ∂Q

/-- The **Rényi divergence** of order `α ≠ 1`: `D_α(P ‖ Q) = log (∫ (dP/dQ)^α dQ)/(α - 1)`. -/
noncomputable def renyiDiv {Ω : Type*} [MeasurableSpace Ω] (α : ℝ) (P Q : Measure Ω) : ℝ :=
  log (hellingerInt α P Q).toReal / (α - 1)

/-- The **binary Rényi entropy** of order `α ≠ 1`: `H_α(p) = log (p^α + (1 - p)^α)/(1 - α)`. -/
noncomputable def binRenyiEntropy (α p : ℝ) : ℝ :=
  log (p ^ α + (1 - p) ^ α) / (1 - α)

/-- **Proposition 2.1** for orders `α ≠ 1`, corrected. Let `P` and `Q` be probability measures
and `R` a measurable event with `p_min ≤ Q(R) ≤ p_max`, where `0 ≤ p_min`, `0 < p_max` and
`p_min + p_max < 1`, and let `0 < α ≠ 1`, with `P ≪ Q` if `α > 1`. If the Hellinger integral is
positive and finite, then with `p = P(R)`, `A = D_α(P ‖ Q) + H_α(p) + log (1 - p_min)` and
`B = (1 - p_min)/p_max`,
`p^α/(p^α + (1 - p)^α) ≤ (exp ((α - 1) A) - 1)/(B^{α-1} - 1)`. -/
def InfoDiffusionFanoRenyi : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P Q : Measure Ω) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (R : Set Ω) (pmin pmax α : ℝ),
    MeasurableSet R → 0 ≤ pmin → 0 < pmax → pmin + pmax < 1 → pmin ≤ Q.real R →
    Q.real R ≤ pmax → 0 < α → α ≠ 1 → (1 < α → P ≪ Q) → hellingerInt α P Q ≠ 0 →
    hellingerInt α P Q ≠ ∞ →
      P.real R ^ α / (P.real R ^ α + (1 - P.real R) ^ α) ≤
        (exp ((α - 1) * (renyiDiv α P Q + binRenyiEntropy α (P.real R) + log (1 - pmin))) - 1) /
          (((1 - pmin) / pmax) ^ (α - 1) - 1)

/-- **Proposition 2.1** for orders `α > 1`, as stated in the paper: under the assumptions of
`InfoDiffusionFanoRenyi` with `α > 1`,
`P(R) ≤ ((exp ((α - 1) A) - 1)/(B^{α-1} - 1))^{1/α}`. -/
def InfoDiffusionFanoRenyiGtOne : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P Q : Measure Ω) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (R : Set Ω) (pmin pmax α : ℝ),
    MeasurableSet R → 0 ≤ pmin → 0 < pmax → pmin + pmax < 1 → pmin ≤ Q.real R →
    Q.real R ≤ pmax → 1 < α → P ≪ Q → hellingerInt α P Q ≠ ∞ →
      P.real R ≤
        ((exp ((α - 1) * (renyiDiv α P Q + binRenyiEntropy α (P.real R) + log (1 - pmin))) - 1) /
          (((1 - pmin) / pmax) ^ (α - 1) - 1)) ^ (1 / α)

/-- The **Shannon entropy** `H(X) = -Σ_a P(a) log P(a)` of a law on a finite type. -/
noncomputable def entropy {α : Type*} [Fintype α] [MeasurableSpace α] (ν : Measure α) : ℝ :=
  ∑ a, negMulLog (ν.real {a})

/-- The **conditional entropy** `H(X | X̂) = H(X, X̂) - H(X̂)` of a joint law on finite types. -/
noncomputable def condEntropy {α γ : Type*} [Fintype α] [Fintype γ] [MeasurableSpace α]
    [MeasurableSpace γ] (ν : Measure (α × γ)) : ℝ :=
  entropy ν - entropy ν.snd

/-- **Mutual information and entropy.** For a joint law of `(X, X̂)` on finite sets, `I(X; X̂)` is
finite and equals `H(X) - H(X | X̂)`. -/
def MutualInfoEntropy : Prop :=
  ∀ {α γ : Type u} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] [Fintype γ]
    [MeasurableSpace γ] [MeasurableSingletonClass γ] (ν : Measure (α × γ)) [IsProbabilityMeasure ν],
    mutualInfo ν ≠ ∞ ∧ (mutualInfo ν).toReal = entropy ν.fst - condEntropy ν

/-- **The entropy of the uniform law** on a finite set `α` is `log |α|`. -/
def EntropyUniform : Prop :=
  ∀ {α : Type u} [Fintype α] [MeasurableSpace α] (ν : Measure α),
    (∀ a, ν {a} = (Fintype.card α : ℝ≥0∞)⁻¹) → entropy ν = log (Fintype.card α)

/-- **Corollary 2.3** (entropy version of the Fano inequality). Let `ν` be the joint law of
`(X, X̂)` on finite sets and `R` a relation with `p_min ≤ P[(X, x̂) ∈ R] ≤ p_max` for every `x̂`,
where `0 ≤ p_min < 1` and `0 < p_max`. Then
`H(X | X̂) ≤ H(X) + log p_max + H(P[¬R]) + P[¬R] log ((1 - p_min)/p_max)`. -/
def EntropyFano : Prop :=
  ∀ {α γ : Type u} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] [Fintype γ]
    [MeasurableSpace γ] [MeasurableSingletonClass γ] (ν : Measure (α × γ)) [IsProbabilityMeasure ν]
    (R : Set (α × γ)) (pmin pmax : ℝ), 0 ≤ pmin → pmin < 1 → 0 < pmax →
    (∀ z, pmin ≤ ν.fst.real {x | (x, z) ∈ R} ∧ ν.fst.real {x | (x, z) ∈ R} ≤ pmax) →
      condEntropy ν ≤ entropy ν.fst + log pmax + binEntropy (ν.real Rᶜ) +
        ν.real Rᶜ * log ((1 - pmin) / pmax)

/-- **Corollary 2.5** (distance-based Fano inequality). Let `ν` be the joint law of `(X, X̂)` with
`X` uniform on a finite set `α` and `X̂ ∈ α`, let `ρ : α → α → ℝ` and `t ∈ ℝ`, and let
`N_min ≤ |{x | ρ(x, x̂) ≤ t}| ≤ N_max` for every `x̂`, with `0 < N_max` and `N_min < |α|`. With
`P_t = P[ρ(X, X̂) > t]`, `H(X | X̂) ≤ H(P_t) + P_t log ((|α| - N_min)/N_max) + log N_max`. -/
def DistanceFanoEntropy : Prop :=
  ∀ {α : Type u} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (ν : Measure (α × α)) [IsProbabilityMeasure ν] (ρ : α → α → ℝ) (t : ℝ) (Nmin Nmax : ℕ),
    (∀ x, ν.fst {x} = (Fintype.card α : ℝ≥0∞)⁻¹) → 0 < Nmax → Nmin < Fintype.card α →
    (∀ z, Nmin ≤ (Finset.univ.filter fun x => ρ x z ≤ t).card ∧
      (Finset.univ.filter fun x => ρ x z ≤ t).card ≤ Nmax) →
      condEntropy ν ≤ binEntropy (ν.real {p | t < ρ p.1 p.2}) +
        ν.real {p | t < ρ p.1 p.2} * log ((Fintype.card α - Nmin) / Nmax) + log Nmax

end Lemmata.FanoDiffusion
