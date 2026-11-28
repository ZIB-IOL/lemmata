module

public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

@[expose] public section

/-!
# Statements

-- DOCS_BEGIN_STATEMENT
-/

namespace Lemmata.OracleComplexity

universe u

/-- A deterministic adaptive query algorithm with queries `Q`, answers `A` and outputs `X`: it
either stops with an output, or asks a query and continues according to the answer. -/
inductive QueryTree (Q A X : Type u) : Type u
  | ret (x : X) : QueryTree Q A X
  | ask (q : Q) (next : A → QueryTree Q A X) : QueryTree Q A X

namespace QueryTree

variable {Q A X : Type u}

/-- The output of the algorithm when the oracle answers query `q` by `ans q`. -/
def output : QueryTree Q A X → (Q → A) → X
  | ret x, _ => x
  | ask q next, ans => output (next (ans q)) ans

/-- The number of queries the algorithm asks when the oracle answers query `q` by `ans q`. -/
def queries : QueryTree Q A X → (Q → A) → ℕ
  | ret _, _ => 0
  | ask q next, ans => queries (next (ans q)) ans + 1

end QueryTree

section Information

variable {F Q A X : Type u}

/-- The probability `∑_{f ∈ G} p f` of a finite set `G` of instances. -/
def weight (p : F → ℝ) (G : Finset F) : ℝ := ∑ f ∈ G, p f

open Classical in
/-- The entropy (in nats) of the answer to the query `q` given that the instance lies in `G`,
multiplied by the probability of `G`: `∑_a -p(G_a) log p(G_a) + p(G) log p(G)`, where `G_a` is the
set of instances in `G` with answer `a`. -/
noncomputable def answerEntropy (p : F → ℝ) (oracle : F → Q → A) (q : Q) (G : Finset F) : ℝ :=
  ∑ a ∈ G.image (fun f => oracle f q),
    Real.negMulLog (weight p (G.filter (fun f => oracle f q = a))) - Real.negMulLog (weight p G)

open Classical in
/-- Every query the algorithm asks reveals at most `C` nats about the instance: for the set `G` of
instances that reach the query, the answer has conditional entropy at most `C` given `G`. -/
def InfoBounded (p : F → ℝ) (oracle : F → Q → A) (C : ℝ) : QueryTree Q A X → Finset F → Prop
  | .ret _, _ => True
  | .ask q next, G => answerEntropy p oracle q G ≤ C * weight p G ∧
      ∀ a, InfoBounded p oracle C (next a) (G.filter (fun f => oracle f q = a))

end Information

open Classical in
/-- **Lemma III.1** (information-theoretic lower bound, in expectation). Let the instance be drawn
from a finite set `F` with probabilities `p`, and let a deterministic query algorithm identify it
with error probability `P_e`, every query revealing at most `C` nats about the instance. Then
`H(F) ≤ C E[T] + h(P_e) + P_e log(|F| - 1)`, where `T` is the number of queries and `h` the binary
entropy; for `C > 0`, `E[T] ≥ (H(F) - h(P_e) - P_e log(|F| - 1))/C`. -/
def InfoLowerBound : Prop :=
  ∀ {F Q A : Type u} [Fintype F] (p : F → ℝ) (oracle : F → Q → A) (C : ℝ) (t : QueryTree Q A F),
    (∀ f, 0 ≤ p f) → ∑ f, p f = 1 → InfoBounded p oracle C t Finset.univ →
      ∑ f, Real.negMulLog (p f) ≤
        C * ∑ f, p f * (t.queries (oracle f) : ℝ) +
          Real.binEntropy (∑ f ∈ Finset.univ.filter (fun f => t.output (oracle f) ≠ f), p f) +
          (∑ f ∈ Finset.univ.filter (fun f => t.output (oracle f) ≠ f), p f) *
            Real.log ((Fintype.card F : ℝ) - 1)

/-- **Lemma III.5** (oracle emulation). If the oracle `O₁` is emulated by the oracle `O₂`, with
query translation `qe` and answer translation `ae` such that `O₁(x) = ae(x, O₂(qe(x)))` on every
instance, then every algorithm for `O₁` turns into an algorithm for `O₂` with the same output and
the same number of queries on every instance. Hence lower bounds on the number of queries for `O₂`
hold for `O₁`. -/
def Emulation : Prop :=
  ∀ {F Q₁ A₁ Q₂ A₂ X : Type u} (oracle₁ : F → Q₁ → A₁) (oracle₂ : F → Q₂ → A₂) (qe : Q₁ → Q₂)
    (ae : Q₁ → A₂ → A₁), (∀ f x, oracle₁ f x = ae x (oracle₂ f (qe x))) →
    ∀ t : QueryTree Q₁ A₁ X, ∃ t' : QueryTree Q₂ A₂ X, ∀ f,
      t'.output (oracle₂ f) = t.output (oracle₁ f) ∧ t'.queries (oracle₂ f) = t.queries (oracle₁ f)

end Lemmata.OracleComplexity
