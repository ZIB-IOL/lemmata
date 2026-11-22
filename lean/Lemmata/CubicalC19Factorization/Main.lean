module

public import Lemmata.CubicalC19Factorization.Statement
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

public section

namespace Lemmata.CubicalC19Factorization

noncomputable section

theorem cube_dirac_symbol_square
    (mass k0 k1 k2 : ℂ) (amplitude : Cell8) :
    cubeDiracSymbol mass k0 k1 k2
        (cubeDiracSymbol mass k0 k1 k2 amplitude) =
      fun corner => (mass ^ 2 + k0 ^ 2 + k1 ^ 2 + k2 ^ 2) * amplitude corner := by
  funext corner
  fin_cases corner <;>
    simp [cubeDiracSymbol, cubeParityBeta, cubeIncidenceLinear,
      cubeIncidenceGamma, cubeIncidenceSign, cubeIncidenceFlip,
      cellFlip0, cellFlip1, cellFlip2, cellBit0, cellBit1, cellBit2] <;>
    ring

theorem c19_continuum_speed_square : c19ContinuumSpeed ^ 2 = 12 := by
  norm_num [c19ContinuumSpeed]

theorem cube_square_at_c19_normalization
    (mass : ℂ) (momentum : Fin 3 → ℝ) (amplitude : Cell8) :
    (fun corner =>
      (mass ^ 2 +
        (((c19ContinuumSpeed : ℝ) : ℂ) * momentum 0) ^ 2 +
        (((c19ContinuumSpeed : ℝ) : ℂ) * momentum 1) ^ 2 +
        (((c19ContinuumSpeed : ℝ) : ℂ) * momentum 2) ^ 2) *
          amplitude corner) =
      c19ContinuumScalarSymbol mass momentum amplitude := by
  funext corner
  have hc : (((c19ContinuumSpeed : ℝ) : ℂ) ^ 2) = 12 := by
    exact_mod_cast c19_continuum_speed_square
  simp only [c19ContinuumScalarSymbol]
  rw [mul_pow, mul_pow, mul_pow, hc]
  ring

theorem cube_flavor_commutes_c19_symbol
    (mass : ℂ) (momentum : Fin 3 → ℝ) (amplitude : Cell8) :
    cubeFlavor (c19ContinuumDiracSymbol mass momentum amplitude) =
      c19ContinuumDiracSymbol mass momentum (cubeFlavor amplitude) := by
  funext corner
  fin_cases corner <;>
    simp [cubeFlavor, c19ContinuumDiracSymbol, cubeDiracSymbol,
      cubeParityBeta, cubeIncidenceLinear, cubeIncidenceGamma,
      cubeIncidenceSign, cubeIncidenceFlip, cellFlip0, cellFlip1,
      cellFlip2, cellBit0, cellBit1, cellBit2] <;>
    ring_nf

theorem c19_symbol_neg
    (mass : ℂ) (momentum : Fin 3 → ℝ) (amplitude : Cell8) :
    c19ContinuumDiracSymbol mass momentum (fun corner => -amplitude corner) =
      fun corner => -c19ContinuumDiracSymbol mass momentum amplitude corner := by
  funext corner
  fin_cases corner <;>
    simp [c19ContinuumDiracSymbol, cubeDiracSymbol, cubeParityBeta,
      cubeIncidenceLinear, cubeIncidenceGamma, cubeIncidenceSign,
      cubeIncidenceFlip, cellFlip0, cellFlip1, cellFlip2, cellBit0,
      cellBit1, cellBit2] <;> ring

-- DOCS_BEGIN_MAIN
/-- The cubical signed-incidence symbol factors the C19 continuum symbol. -/
theorem cubical_c19_factorization : C19Factorization := by
  intro mass momentum amplitude
  simp only [c19ContinuumDiracSymbol]
  rw [cube_dirac_symbol_square]
  exact cube_square_at_c19_normalization mass momentum amplitude

/-- The cubical C19 symbol preserves the exhaustive two-flavor split. -/
theorem cubical_c19_two_flavor_classification :
    C19TwoFlavorClassification := by
  constructor
  · intro amplitude
    funext corner
    simp [cubeFlavorPlusProjection, cubeFlavorMinusProjection]
    ring
  constructor
  · intro amplitude
    funext corner
    fin_cases corner <;>
      simp [cubeFlavorPlusProjection, cubeFlavor, cellFlip1, cellFlip2,
        cellBit2] <;>
      ring_nf <;> rw [Complex.I_sq] <;> ring
  constructor
  · intro amplitude
    funext corner
    fin_cases corner <;>
      simp [cubeFlavorMinusProjection, cubeFlavor, cellFlip1, cellFlip2,
        cellBit2] <;>
      ring_nf <;> rw [Complex.I_sq] <;> ring
  constructor
  · intro amplitude hplus hminus
    funext corner
    have h := congrFun (hplus.symm.trans hminus) corner
    simp only [Pi.zero_apply]
    have hzero : amplitude corner - (-amplitude corner) = 0 :=
      sub_eq_zero.mpr h
    linear_combination (1 / 2 : ℂ) * hzero
  constructor
  · intro mass momentum amplitude hplus
    rw [cube_flavor_commutes_c19_symbol, hplus]
  · intro mass momentum amplitude hminus
    rw [cube_flavor_commutes_c19_symbol, hminus, c19_symbol_neg]
-- DOCS_END_MAIN

end

end Lemmata.CubicalC19Factorization
