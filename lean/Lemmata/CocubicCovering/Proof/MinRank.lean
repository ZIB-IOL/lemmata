module

public import Lemmata.CocubicCovering.Proof.Quadratics
public meta import Lemmata.CocubicCovering.Proof.Quadratics
public import Lemmata.CocubicCovering.Proof.RankTwelve
public meta import Lemmata.CocubicCovering.Proof.RankTwelve
public import Lemmata.CocubicCovering.Proof.RankTen
public meta import Lemmata.CocubicCovering.Proof.RankTen
public import Lemmata.CocubicCovering.Proof.Ambient
public meta import Lemmata.CocubicCovering.Proof.Ambient

@[expose] public section

set_option Elab.async false

namespace Lemmata.CocubicCovering.Covering

open CoveringPolynomial
open scoped BigOperators

def levelSix_pure_decision (i : Fin 27) : Decidable (∀ term ∈ CoveringLevelSix.multiplier i, term.card = 2) :=
  inferInstance

@[noinline, never_extract]
def levelSix_pure_check (i : Fin 27) : Bool :=
  @decide (∀ term ∈ CoveringLevelSix.multiplier i, term.card = 2) (levelSix_pure_decision i)

theorem levelSix_pure_check_sound (i : Fin 27) (computed : levelSix_pure_check i = true) :
    ∀ term ∈ CoveringLevelSix.multiplier i, term.card = 2 := by
  unfold levelSix_pure_check at computed
  exact @of_decide_eq_true (∀ term ∈ CoveringLevelSix.multiplier i, term.card = 2) (levelSix_pure_decision i) computed

private theorem levelSix_pure (i : Fin 27) :
    ∀ term ∈ CoveringLevelSix.multiplier i, term.card = 2 := by
  have computed : ∀ (i : Fin 27), levelSix_pure_check i = true := by native_decide
  exact levelSix_pure_check_sound i (computed i)

def common_pure_decision (i : Fin 24) : Decidable (∀ term ∈ CoveringMatrix.multiplier i, term.card = 2) :=
  inferInstance

@[noinline, never_extract]
def common_pure_check (i : Fin 24) : Bool :=
  @decide (∀ term ∈ CoveringMatrix.multiplier i, term.card = 2) (common_pure_decision i)

theorem common_pure_check_sound (i : Fin 24) (computed : common_pure_check i = true) :
    ∀ term ∈ CoveringMatrix.multiplier i, term.card = 2 := by
  unfold common_pure_check at computed
  exact @of_decide_eq_true (∀ term ∈ CoveringMatrix.multiplier i, term.card = 2) (common_pure_decision i) computed

private theorem common_pure (i : Fin 24) :
    ∀ term ∈ CoveringMatrix.multiplier i, term.card = 2 := by
  have computed : ∀ (i : Fin 24), common_pure_check i = true := by native_decide
  exact common_pure_check_sound i (computed i)

private theorem levelSix_mem_quadraticMultipliers (v : Vector 27) :
    CoveringLevelSix.multiplierLinear v ∈ quadraticMultipliers (eval form9) := by
  change CoveringLevelSix.multiplierLinear v ∈ homogeneousQuadratics 9 ∧
    CoveringLevelSix.multiplierLinear v * eval form9 ∈ reedMuller 9 7
  refine ⟨?_, CoveringLevelSix.multiplierLinear_products v⟩
  change (∑ i : Fin 27, v i • CoveringLevelSix.multiplierFunction i) ∈
    homogeneousQuadratics 9
  apply (homogeneousQuadratics 9).sum_mem
  intro i hi
  apply (homogeneousQuadratics 9).smul_mem (v i)
  exact decode_mem_homogeneousQuadratics 9 (CoveringLevelSix.multiplier i)
    (CoveringLevelSix.multiplier_bounded i) (levelSix_pure i)

private theorem ambient_mem_quadraticMultipliers (a : Fin 2) (v : Vector 24) :
    CoveringAmbient.multiplierLinear a v ∈
      quadraticMultipliers (eval (CoveringAmbient.form a)) := by
  change CoveringAmbient.multiplierLinear a v ∈ homogeneousQuadratics (CoveringAmbient.dimension a) ∧
    CoveringAmbient.multiplierLinear a v * eval (CoveringAmbient.form a) ∈
      reedMuller (CoveringAmbient.dimension a) (CoveringAmbient.dimension a - 2)
  refine ⟨?_, CoveringAmbient.multiplierLinear_products a v⟩
  change (∑ i : Fin 24, v i • CoveringAmbient.multiplierFunction a i) ∈
    homogeneousQuadratics (CoveringAmbient.dimension a)
  apply (homogeneousQuadratics (CoveringAmbient.dimension a)).sum_mem
  intro i hi
  apply (homogeneousQuadratics (CoveringAmbient.dimension a)).smul_mem (v i)
  exact decode_mem_homogeneousQuadratics (CoveringAmbient.dimension a) (CoveringMatrix.multiplier i)
    (CoveringAmbient.multiplier_bounded a i) (common_pure i)

theorem form9_pairing_rank_ge_twelve (h : BooleanFunction 9) (hh : h ∈ reedMuller 9 5) :
    12 ≤ rank (pairing (eval form9) h) := by
  have hle := rank_supportGram_le_pairing (eval form9) h CoveringLevelSix.multiplierLinear
    levelSix_mem_quadraticMultipliers
  obtain ⟨v, hv, hgram⟩ := CoveringLevelSix.exists_pointed_realization h hh
  rw [hgram] at hle
  exact (CoveringRankTwelve.rank_at_least_twelve v hv).trans hle

private theorem ambient_pairing_rank_ge_ten (a : Fin 2)
    (h : BooleanFunction (CoveringAmbient.dimension a))
    (hh : h ∈ reedMuller (CoveringAmbient.dimension a) (CoveringAmbient.dimension a - 4)) :
    10 ≤ rank (pairing (eval (CoveringAmbient.form a)) h) := by
  have hle := rank_supportGram_le_pairing (eval (CoveringAmbient.form a)) h
    (CoveringAmbient.multiplierLinear a) (ambient_mem_quadraticMultipliers a)
  obtain ⟨v, hv, hgram⟩ := CoveringAmbient.exists_pointed_realization a h hh
  rw [hgram] at hle
  exact (CoveringRankTen.rank_at_least_ten v hv).trans hle

theorem form10_pairing_rank_ge_ten (h : BooleanFunction 10) (hh : h ∈ reedMuller 10 6) :
    10 ≤ rank (pairing (eval form10) h) :=
  ambient_pairing_rank_ge_ten 0 h hh

theorem form11_pairing_rank_ge_ten (h : BooleanFunction 11) (hh : h ∈ reedMuller 11 7) :
    10 ≤ rank (pairing (eval form11) h) :=
  ambient_pairing_rank_ge_ten 1 h hh

end Lemmata.CocubicCovering.Covering
