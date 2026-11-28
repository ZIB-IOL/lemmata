module

public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
public import Mathlib.Basic.Real.Sign
public import Mathlib.Topology.EMetricSpace.Lipschitz

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

/-- The string guessing oracle (Oracle III.2) for a hidden string `S ∈ {0,1}^M`: a query is a list
of guesses `(i, b)` of bits `S i = b`, and the answer is the index of the first wrong guess, or
`none` if all guesses are right. -/
def stringGuess {M : ℕ} (S : Fin M → Bool) (q : List (Fin M × Bool)) : Option ℕ :=
  q.findIdx? (fun g => S g.1 != g.2)

open Classical in
/-- **Proposition III.3** (string guessing problem). Let the hidden string `S ∈ {0,1}^M` be
uniformly random, and let a deterministic query algorithm using the string guessing oracle identify
`S` with error probability `P_e`. Then the expected number of queries is at least
`((1 - P_e) M - h(P_e)/log 2)/2`, and hence at least `((1 - P_e) M - 1)/2`. -/
def StringGuessing : Prop :=
  ∀ (M : ℕ) (t : QueryTree (List (Fin M × Bool)) (Option ℕ) (Fin M → Bool)),
    let Pe := ((Finset.univ.filter (fun S => t.output (stringGuess S) ≠ S)).card : ℝ) / 2 ^ M
    let ET := (∑ S, (t.queries (stringGuess S) : ℝ)) / 2 ^ M
    ((1 - Pe) * M - Real.binEntropy Pe / Real.log 2) / 2 ≤ ET ∧ ((1 - Pe) * M - 1) / 2 ≤ ET

section Box

/-- `+1` for the bit `1` (right) and `-1` for the bit `0` (left). -/
def bitSign (b : Bool) : ℝ := if b then 1 else -1

/-- The center `c_j(S) = ∑_{i<j} ±4^{-(i+1)}` of the interval `[c_j - 4^{-j}, c_j + 4^{-j}]` of the
first `j` bits of `S`: each bit moves to the left or right quarter of the current interval. -/
noncomputable def boxCenter {M : ℕ} (S : Fin M → Bool) (j : ℕ) : ℝ :=
  ∑ i : Fin M, if (i : ℕ) < j then bitSign (S i) * (1 / 4) ^ ((i : ℕ) + 1) else 0

/-- The levels `b_j = 1 - 4/7 (1 - 8^{-j})`: `b₀ = 1` and `b_{j+1} = b_j - 2^{-3j-1}`. -/
noncomputable def boxLevel (j : ℕ) : ℝ := 1 - 4 / 7 * (1 - (1 / 8) ^ j)

/-- The piece of depth `j`: `b_j - 8^{-j} + 2^{-j} |x - c_j(S)|`, equal to `b_j` at the endpoints of
the interval of the first `j` bits. -/
noncomputable def boxPiece {M : ℕ} (S : Fin M → Bool) (j : ℕ) (x : ℝ) : ℝ :=
  boxLevel j - (1 / 8) ^ j + (1 / 2) ^ j * |x - boxCenter S j|

/-- The hard function of Section IV.A for the string `S ∈ {0,1}^M`: the maximum of the pieces of
depths `0, …, M`. -/
noncomputable def boxFn {M : ℕ} (S : Fin M → Bool) (x : ℝ) : ℝ :=
  (Finset.range (M + 1)).sup' Finset.nonempty_range_add_one (fun j => boxPiece S j x)

/-- The slope `2^{-j} sign(x - c_j(S))` of the piece of depth `j` at `x`. -/
noncomputable def pieceSlope {M : ℕ} (S : Fin M → Bool) (j : ℕ) (x : ℝ) : ℝ :=
  (1 / 2) ^ j * Real.sign (x - boxCenter S j)

/-- The maximum of the pieces of depths `0, …, j` at `x`, with the slope of the first piece that
attains it. -/
noncomputable def boxBest {M : ℕ} (S : Fin M → Bool) (x : ℝ) : ℕ → ℝ × ℝ
  | 0 => (boxPiece S 0 x, pieceSlope S 0 x)
  | j + 1 =>
    if (boxBest S x j).1 < boxPiece S (j + 1) x then (boxPiece S (j + 1) x, pieceSlope S (j + 1) x)
    else boxBest S x j

/-- The first-order oracle of Section IV.A: the value of the hard function and the slope of the
first piece attaining the maximum. -/
noncomputable def boxOracle {M : ℕ} (S : Fin M → Bool) (x : ℝ) : ℝ × ℝ := boxBest S x M

end Box

/-- The hard functions of Section IV.A are convex and `1`-Lipschitz, and `boxOracle` is a
first-order oracle for them: it answers the value and a subgradient. -/
def BoxOracleValid : Prop :=
  ∀ (M : ℕ) (S : Fin M → Bool), ConvexOn ℝ Set.univ (boxFn S) ∧ LipschitzWith 1 (boxFn S) ∧
    ∀ x, (boxOracle S x).1 = boxFn S x ∧ ∀ y, boxFn S x + (boxOracle S x).2 * (y - x) ≤ boxFn S y

/-- **Lemma IV.3** (packing). The hard function `boxFn S` has minimum `b_M - 8^{-M}`, attained at
`c_M(S)`, and for `ε < 8^{-M}` a point that is `ε`-optimal for two hard functions `boxFn S` and
`boxFn S'` has `S = S'`. -/
def BoxPacking : Prop :=
  ∀ (M : ℕ) (S : Fin M → Bool), (∀ y, boxLevel M - (1 / 8) ^ M ≤ boxFn S y) ∧
    boxFn S (boxCenter S M) = boxLevel M - (1 / 8) ^ M ∧
    ∀ (S' : Fin M → Bool) (ε x : ℝ), ε < (1 / 8) ^ M → (∀ y, boxFn S x ≤ boxFn S y + ε) →
      (∀ y, boxFn S' x ≤ boxFn S' y + ε) → S = S'

/-- **Lemma IV.5** (emulation by string guessing). The oracle `boxOracle` is emulated by the
string guessing oracle on strings of length `M`: there are a query translation `q` and an answer
translation `a` with `boxOracle S x = a(x, O_S(q(x)))` for every string `S` and point `x`. -/
def BoxEmulation : Prop :=
  ∀ M : ℕ, ∃ (qe : ℝ → List (Fin M × Bool)) (ae : ℝ → Option ℕ → ℝ × ℝ),
    ∀ (S : Fin M → Bool) (x : ℝ), boxOracle S x = ae x (stringGuess S (qe x))

open Classical in
/-- **Theorem IV.2, one-dimensional case.** Let `S ∈ {0,1}^M` be uniformly random and
`ε < 8^{-M}`. Every deterministic algorithm that queries the oracle `boxOracle S` and outputs an
`ε`-minimizer of `boxFn S` with error probability `P_e` asks at least `((1 - P_e) M - 1)/2` queries
in expectation; with `M = ⌊log₂(1/ε)/3⌋` (when this is below `log₂(1/ε)/3`) this is
`Ω((1 - P_e) log(1/ε))`. -/
def BoxLowerBound : Prop :=
  ∀ (M : ℕ) (ε : ℝ), ε < (1 / 8) ^ M → ∀ t : QueryTree ℝ (ℝ × ℝ) ℝ,
    let Pe := ((Finset.univ.filter (fun S : Fin M → Bool =>
      ¬ ∀ y, boxFn S (t.output (boxOracle S)) ≤ boxFn S y + ε)).card : ℝ) / 2 ^ M
    ((1 - Pe) * M - 1) / 2 ≤ (∑ S : Fin M → Bool, (t.queries (boxOracle S) : ℝ)) / 2 ^ M

end Lemmata.OracleComplexity
