module

public import Lemmata.OracleComplexity.LowScale
public import Lemmata.OracleComplexity.Maximal
public import Lemmata.OracleComplexity.Tail

@[expose] public section

namespace Lemmata.OracleComplexity

-- DOCS_BEGIN_MAIN
/-- Lemma III.1: if every query reveals at most `C` nats about the instance, then
`H(F) ≤ C E[T] + h(P_e) + P_e log(|F| - 1)`. -/
theorem info_lower_bound : InfoLowerBound := Proof.info_lower_bound

/-- Lemma III.1 in probability (corrected): for `C ≥ 0` and `P_e ≤ 1/2`,
`P[T < d] log|F| ≤ log|F| - H(F) + C d + h(P_e) + P_e log(|F| - 1)`. -/
theorem info_tail_bound : InfoTailBound := Proof.info_tail_bound

/-- Lemma III.5: an algorithm for an emulated oracle runs with the emulating oracle, with the same
outputs and the same numbers of queries. -/
theorem emulation : Emulation := Proof.emulation

/-- Proposition III.3: identifying a uniformly random string of length `M` with the string guessing
oracle and error probability `P_e` takes at least `((1 - P_e) M - 1)/2` queries in expectation. -/
theorem string_guessing : StringGuessing := Proof.string_guessing

/-- Proposition III.3 in probability: the string guessing problem stops after fewer than `d`
queries with probability at most `P_e + (2d + 1)/M`. -/
theorem string_guessing_tail : StringGuessingTail := Proof.string_guessing_tail

/-- The hard functions of Section IV.A are convex and `1`-Lipschitz, and `boxOracle` answers their
value and a subgradient. -/
theorem box_oracle_valid : BoxOracleValid := Proof.box_oracle_valid

/-- Lemma IV.3: for `ε < 8^{-M}`, the `ε`-minimizers of different hard functions are disjoint. -/
theorem box_packing : BoxPacking := Proof.box_packing

/-- Lemma IV.5: the oracle of the hard functions is emulated by the string guessing oracle. -/
theorem box_emulation : BoxEmulation := Proof.box_emulation

/-- Theorem IV.2, one-dimensional case: finding an `ε`-minimizer of a random hard function takes at
least `((1 - P_e) M - 1)/2` queries in expectation. -/
theorem box_lower_bound : BoxLowerBound := Proof.box_lower_bound

/-- Lemma IV.5, locality: the oracle of the hard functions of Section IV.A is local. -/
theorem box_local : BoxLocal := Proof.box_local

/-- The hard functions of Section IV.B are convex and `1`-Lipschitz for the maximum norm, and
`cubeOracle` answers their value and a subgradient on a coordinate axis. -/
theorem cube_oracle_valid : CubeOracleValid := Proof.cube_oracle_valid

/-- Lemma IV.6: for `ε < 8^{-M}`, the `ε`-minimizers of different hard functions of Section IV.B
are disjoint. -/
theorem cube_packing : CubePacking := Proof.cube_packing

/-- Lemma IV.7: the oracle of Section IV.B is emulated by the string guessing oracle on the
concatenation of the strings. -/
theorem cube_emulation : CubeEmulation := Proof.cube_emulation

/-- Lemma IV.7, locality: the oracle of Section IV.B is local. -/
theorem cube_local : CubeLocal := Proof.cube_local

/-- Theorem IV.2: finding an `ε`-minimizer of a random hard function of Section IV.B with the
single-coordinate oracle takes at least `((1 - P_e) n M - 1)/2` queries in expectation. -/
theorem cube_lower_bound : CubeLowerBound := Proof.cube_lower_bound
/-- The hard functions of Section V.A are convex and `1`-Lipschitz for the `ℓ^p` norm, and their
oracle answers the value and a subgradient on a coordinate axis. -/
theorem lp_oracle_valid : LpOracleValid := Proof.lp_oracle_valid

/-- Lemma V.3 (standard basis): for `M ε^p < 1`, an `ε`-minimizer over the unit `ℓ^p` ball
determines the signs. -/
theorem lp_packing : LpPacking := Proof.lp_packing

/-- Lemma V.4: the oracle of Section V.A is emulated by the string guessing oracle. -/
theorem lp_emulation : LpEmulation := Proof.lp_emulation

/-- Lemma V.4, locality: the oracle of Section V.A is local. -/
theorem lp_local : LpLocal := Proof.lp_local

/-- Theorem V.1 (standard basis): for `M ≤ n` and `M ε^p < 1`, minimizing a random hard function
of Section V.A over the unit `ℓ^p` ball takes at least `((1 - P_e) M - 1)/2` queries in
expectation. -/
theorem lp_lower_bound : LpLowerBound := Proof.lp_lower_bound

/-- Proposition V.5: for `ε < n^{-1/p} 8^{-M}`, the hard functions of Section IV.B rescaled into the
unit `ℓ^p` ball need at least `((1 - P_e) n M - 1)/2` queries in expectation. -/
theorem low_scale_lower_bound : LowScaleLowerBound := Proof.low_scale_lower_bound

/-- Lemma VI.2: the maximal oracle is local and emulates every local oracle. -/
theorem maximal_oracle : MaximalOracle := Proof.maximal_oracle
-- DOCS_END_MAIN

end Lemmata.OracleComplexity
