module

public import Lemmata.OracleComplexity.CubeEmul

@[expose] public section

/-!
# The lower bound of Section IV.B

An algorithm for the hard functions of Section IV.B runs with the string guessing oracle on the
concatenation of the strings (Lemma IV.7), and the coordinates of an `ε`-minimizer decode the
strings (Lemma IV.6). Since concatenation is a bijection between `n`-tuples of strings of length
`M` and strings of length `n M`, Proposition III.3 for strings of length `n M` gives
Theorem IV.2.
-/

namespace Lemmata.OracleComplexity

variable {n M : ℕ} [NeZero n]

omit [NeZero n] in
/-- Concatenation of the strings is a bijection. -/
def cubeEquiv : (Fin n → Fin M → Bool) ≃ (Fin (n * M) → Bool) where
  toFun := cubeString
  invFun U := fun i k => U (finProdFinEquiv (i, k))
  left_inv S := by
    funext i k
    simp [cubeString]
  right_inv U := by
    funext p
    show U (finProdFinEquiv ((finProdFinEquiv.symm p).1, (finProdFinEquiv.symm p).2)) = U p
    rw [Prod.mk.eta, Equiv.apply_symm_apply]

namespace Proof

theorem cube_emulation : CubeEmulation := fun _ M _ =>
  ⟨cubeQuery (M := M), cubeAnswer M, fun S x => cube_emul S x⟩

theorem cube_lower_bound : CubeLowerBound := by
  classical
  intro n M _ ε hε t Pe
  obtain ⟨t', ht'⟩ := Proof.emulation (fun S : Fin n → Fin M → Bool => cubeOracle S)
    (fun S : Fin n → Fin M → Bool => stringGuess (cubeString S)) (cubeQuery (M := M))
    (cubeAnswer M) (fun S x => cube_emul S x) t
  set dec : (Fin n → ℝ) → Fin (n * M) → Bool :=
    fun y => cubeString (fun i (k : Fin M) => pathBit (y i) k) with hdec
  set t'' := mapOut dec t' with ht''
  have hsg := (Proof.string_guessing (n * M) t'').2
  have hq : ∀ S : Fin n → Fin M → Bool,
      t''.queries (stringGuess (cubeString S)) = t.queries (cubeOracle S) := by
    intro S
    rw [ht'', (mapOut_spec _ _ t').2, (ht' S).2]
  have hout : ∀ S : Fin n → Fin M → Bool,
      t''.output (stringGuess (cubeString S)) = dec (t.output (cubeOracle S)) := by
    intro S
    rw [ht'', (mapOut_spec _ _ t').1, (ht' S).1]
  -- sums over strings of length `n M` are sums over tuples of strings
  have hsum : ∑ U : Fin (n * M) → Bool, (t''.queries (stringGuess U) : ℝ) =
      ∑ S : Fin n → Fin M → Bool, (t.queries (cubeOracle S) : ℝ) := by
    rw [← Equiv.sum_comp cubeEquiv]
    exact Finset.sum_congr rfl (fun S _ => by rw [show cubeEquiv S = cubeString S from rfl, hq])
  have hcard : ∀ inst : DecidablePred (fun U : Fin (n * M) → Bool =>
      t''.output (stringGuess U) ≠ U),
      ((@Finset.filter _ _ inst Finset.univ).card : ℝ) ≤
        ((Finset.univ.filter (fun S : Fin n → Fin M → Bool =>
          ¬ ∀ y, cubeFn S (t.output (cubeOracle S)) ≤ cubeFn S y + ε)).card : ℝ) := by
    intro inst
    have hmap : (@Finset.filter _ _ inst Finset.univ) ⊆ (Finset.univ.filter
        (fun S : Fin n → Fin M → Bool =>
          ¬ ∀ y, cubeFn S (t.output (cubeOracle S)) ≤ cubeFn S y + ε)).map
            cubeEquiv.toEmbedding := by
      intro U hU
      rw [Finset.mem_filter] at hU
      rw [Finset.mem_map]
      refine ⟨cubeEquiv.symm U, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun hopt => hU.2 ?_⟩,
        by simp⟩
      have hU' : U = cubeString (cubeEquiv.symm U) := (cubeEquiv.apply_symm_apply U).symm
      rw [hU', hout]
      show cubeString (fun i (k : Fin M) =>
          pathBit ((t.output (cubeOracle (cubeEquiv.symm U))) i) k) = cubeString (cubeEquiv.symm U)
      congr 1
      funext i k
      exact cube_decode hε hopt i k
    have := Finset.card_le_card hmap
    rw [Finset.card_map] at this
    exact_mod_cast this
  have hpos : (0 : ℝ) < 2 ^ (n * M) := by positivity
  have hnM : ((n * M : ℕ) : ℝ) = (n : ℝ) * M := by push_cast; ring
  rw [hsum, hnM] at hsg
  have hM : (0 : ℝ) ≤ (n : ℝ) * M := by positivity
  refine le_trans ?_ hsg
  have key : ∀ c : ℝ, c ≤ ((Finset.univ.filter (fun S : Fin n → Fin M → Bool =>
      ¬ ∀ y, cubeFn S (t.output (cubeOracle S)) ≤ cubeFn S y + ε)).card : ℝ) →
      ((1 - Pe) * (n * M) - 1) / 2 ≤ ((1 - c / 2 ^ (n * M)) * (n * M) - 1) / 2 := by
    intro c hc
    have h1 : c / 2 ^ (n * M) ≤ Pe := by
      simp only [Pe]
      exact div_le_div_of_nonneg_right hc hpos.le
    have := mul_le_mul_of_nonneg_right h1 hM
    linarith
  exact key _ (hcard _)

end Proof

end Lemmata.OracleComplexity
