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

/-- The left slope of the piece of depth `j` at `x`: `2^{-j}` if `x` lies to the right of its
center, `-2^{-j}` otherwise. -/
noncomputable def pieceLeft {M : ℕ} (S : Fin M → Bool) (j : ℕ) (x : ℝ) : ℝ :=
  if boxCenter S j < x then (1 / 2) ^ j else -(1 / 2) ^ j

/-- The right slope of the piece of depth `j` at `x`: `-2^{-j}` if `x` lies to the left of its
center, `2^{-j}` otherwise. -/
noncomputable def pieceRight {M : ℕ} (S : Fin M → Bool) (j : ℕ) (x : ℝ) : ℝ :=
  if x < boxCenter S j then -(1 / 2) ^ j else (1 / 2) ^ j

open Classical in
/-- The left derivative of the hard function at `x`: the smallest left slope of a piece attaining
the maximum (the other pieces count as `1`, at least every slope). -/
noncomputable def boxLeft {M : ℕ} (S : Fin M → Bool) (x : ℝ) : ℝ :=
  (Finset.range (M + 1)).inf' Finset.nonempty_range_add_one
    (fun j => if boxPiece S j x = boxFn S x then pieceLeft S j x else 1)

open Classical in
/-- The right derivative of the hard function at `x`: the largest right slope of a piece attaining
the maximum (the other pieces count as `-1`, at most every slope). -/
noncomputable def boxRight {M : ℕ} (S : Fin M → Bool) (x : ℝ) : ℝ :=
  (Finset.range (M + 1)).sup' Finset.nonempty_range_add_one
    (fun j => if boxPiece S j x = boxFn S x then pieceRight S j x else -1)

/-- The first-order oracle of Section IV.A: the value of the hard function, and its right
derivative if this is positive, otherwise its left derivative. Both are subgradients, and the
chosen one is the slope at which the function increases on one side of `x`. -/
noncomputable def boxOracle {M : ℕ} (S : Fin M → Bool) (x : ℝ) : ℝ × ℝ :=
  (boxFn S x, if 0 < boxRight S x then boxRight S x else boxLeft S x)

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

/-- An oracle `O` for a family of functions `F` is local if instances that agree near `x` get the
same answer at `x`. -/
def IsLocalOracle {ι E α : Type*} [TopologicalSpace E] (F : ι → E → ℝ) (O : ι → E → α) : Prop :=
  ∀ i i' x, (∀ᶠ y in nhds x, F i y = F i' y) → O i x = O i' x

/-- **Lemma IV.5, locality.** The oracle of the hard functions of Section IV.A is local. -/
def BoxLocal : Prop :=
  ∀ M : ℕ, IsLocalOracle (fun S : Fin M → Bool => boxFn S) (fun S => boxOracle S)

section Cube

variable {n M : ℕ} [NeZero n]

/-- The hard function of Section IV.B for strings `S₁, …, Sₙ ∈ {0,1}^M`: the maximum over the
coordinates of the one-dimensional hard functions, `f_S(x) = max_i f_{S_i}(x_i)`. -/
noncomputable def cubeFn (S : Fin n → Fin M → Bool) (x : Fin n → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => boxFn (S i) (x i))

open Classical in
/-- The least coordinate whose function attains the maximum. -/
noncomputable def cubeCoord (S : Fin n → Fin M → Bool) (x : Fin n → ℝ) : Fin n :=
  (Finset.univ.filter (fun i => boxFn (S i) (x i) = cubeFn S x)).min' (by
    obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun i => boxFn (S i) (x i))
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi.symm⟩⟩)

/-- The single-coordinate oracle of Section IV.B: the value, the least coordinate `i` attaining the
maximum, and the slope `λ` of the oracle of that coordinate; the subgradient is `λ e_i`. -/
noncomputable def cubeOracle (S : Fin n → Fin M → Bool) (x : Fin n → ℝ) : ℝ × Fin n × ℝ :=
  (cubeFn S x, cubeCoord S x, (boxOracle (S (cubeCoord S x)) (x (cubeCoord S x))).2)

/-- The concatenation of `S₁, …, Sₙ` into a string of length `n M`. -/
def cubeString (S : Fin n → Fin M → Bool) : Fin (n * M) → Bool :=
  fun p => S (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2

end Cube

/-- The hard functions of Section IV.B are convex and `1`-Lipschitz for the maximum norm, and
`cubeOracle` is a first-order oracle whose subgradient lies on a coordinate axis. -/
def CubeOracleValid : Prop :=
  ∀ (n M : ℕ) [NeZero n] (S : Fin n → Fin M → Bool), ConvexOn ℝ Set.univ (cubeFn S) ∧
    LipschitzWith 1 (cubeFn S) ∧ ∀ x, (cubeOracle S x).1 = cubeFn S x ∧
      ∀ y, cubeFn S x + (cubeOracle S x).2.2 * (y (cubeOracle S x).2.1 - x (cubeOracle S x).2.1) ≤
        cubeFn S y

/-- **Lemma IV.6** (packing). The minimum of `cubeFn S` is `b_M - 8^{-M}`, attained at the point
with coordinates `c_M(S_i)`, and for `ε < 8^{-M}` a point that is `ε`-optimal for `cubeFn S` and
`cubeFn S'` has `S = S'`. -/
def CubePacking : Prop :=
  ∀ (n M : ℕ) [NeZero n] (S : Fin n → Fin M → Bool),
    (∀ y, boxLevel M - (1 / 8) ^ M ≤ cubeFn S y) ∧
    cubeFn S (fun i => boxCenter (S i) M) = boxLevel M - (1 / 8) ^ M ∧
    ∀ (S' : Fin n → Fin M → Bool) (ε : ℝ) (x : Fin n → ℝ), ε < (1 / 8) ^ M →
      (∀ y, cubeFn S x ≤ cubeFn S y + ε) → (∀ y, cubeFn S' x ≤ cubeFn S' y + ε) → S = S'

/-- **Lemma IV.7** (emulation). The oracle `cubeOracle` is emulated by the string guessing oracle on
the concatenation of the strings, of length `n M`. -/
def CubeEmulation : Prop :=
  ∀ (n M : ℕ) [NeZero n], ∃ (qe : (Fin n → ℝ) → List (Fin (n * M) × Bool))
    (ae : (Fin n → ℝ) → Option ℕ → ℝ × Fin n × ℝ), ∀ (S : Fin n → Fin M → Bool) (x : Fin n → ℝ),
      cubeOracle S x = ae x (stringGuess (cubeString S) (qe x))

/-- **Lemma IV.7, locality.** The oracle of the hard functions of Section IV.B is local. -/
def CubeLocal : Prop :=
  ∀ (n M : ℕ) [NeZero n],
    IsLocalOracle (fun S : Fin n → Fin M → Bool => cubeFn S) (fun S => cubeOracle S)

open Classical in
/-- **Theorem IV.2.** Let `S₁, …, Sₙ ∈ {0,1}^M` be uniformly random and `ε < 8^{-M}`. Every
deterministic algorithm that queries the single-coordinate oracle `cubeOracle S` and outputs an
`ε`-minimizer of `cubeFn S` with error probability `P_e` asks at least `((1 - P_e) n M - 1)/2`
queries in expectation, that is `Ω((1 - P_e) n log(1/ε))`. -/
def CubeLowerBound : Prop :=
  ∀ (n M : ℕ) [NeZero n] (ε : ℝ), ε < (1 / 8) ^ M →
    ∀ t : QueryTree (Fin n → ℝ) (ℝ × Fin n × ℝ) (Fin n → ℝ),
      let Pe := ((Finset.univ.filter (fun S : Fin n → Fin M → Bool =>
        ¬ ∀ y, cubeFn S (t.output (cubeOracle S)) ≤ cubeFn S y + ε)).card : ℝ) / 2 ^ (n * M)
      ((1 - Pe) * (n * M) - 1) / 2 ≤
        (∑ S : Fin n → Fin M → Bool, (t.queries (cubeOracle S) : ℝ)) / 2 ^ (n * M)

end Lemmata.OracleComplexity
