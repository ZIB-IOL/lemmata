module

/-
Copyright (c) 2026 Kirill Khoruzhii. Licensed under Apache-2.0.
Modified for the arbitrary-field tensor-rank formalization; namespace and imports
adapted for Lemmata. See docs/tensor-rank/NOTICE.txt for upstream attribution
and modification notices, and docs/tensor-rank/LICENSE.txt for the license.
-/

public import Lemmata.TensorRank.Proof.CyclicBound

@[expose] public section

set_option autoImplicit false

open scoped BigOperators

namespace Lemmata.TensorRank

-- DOCS_BEGIN_MAIN
variable {𝕜 : Type*} [Field 𝕜]

open Tensor (asymptoticRank)

theorem squareRootBound (k : ℕ) (hk : 0 < k) :
    (∀ (d : Fin k → ℕ) (T : Tensor 𝕜 (Fin k) (fun i => Fin (d i))),
      asymptoticRank T ≤ Real.sqrt (∏ i, (d i : ℝ))) ∧
    (∀ (n : ℕ) (T : Cubical (𝕜 := 𝕜) k n),
      asymptoticRank T ≤ (n : ℝ) ^ ((k : ℝ) / 2)) := by
  let : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  have h := squareRoot_of_graphExponentBound (𝕜 := 𝕜) graphExponent_le_quarter_square
  constructor
  · intro d T
    simpa only [Fintype.card_fin] using h (Fin k) (fun i => Fin (d i)) T
  · intro n T
    exact cubical_of_squareRoot h k n hk T

theorem evenCubicalSharpness (r n : ℕ) (hr : 0 < r) :
    IsGreatest (cubicalRanks (𝕜 := 𝕜) (r + r) n) ((n : ℝ) ^ r) ∧
    (∀ T : Cubical (𝕜 := 𝕜) (r + r) n, (balancedMatrix (𝕜 := 𝕜) r n T).det ≠ 0 →
      asymptoticRank T = (n : ℝ) ^ r) := by
  have h := squareRoot_of_graphExponentBound (𝕜 := 𝕜) graphExponent_le_quarter_square
  exact ⟨evenCubicalMaximum_of_squareRoot h r n hr,
    evenCubicalNonsingular_of_squareRoot h r n hr⟩

theorem completeGraphBounds (k d : ℕ) (hk : 2 ≤ k) (hd : 1 ≤ d) :
    (d : ℝ) ^ (k ^ 2 / 4) ≤ asymptoticRank (completeGraph (𝕜 := 𝕜) k d) ∧
    asymptoticRank (completeGraph (𝕜 := 𝕜) k d) ≤ (d : ℝ) ^ ((k : ℝ) ^ 2 / 4) ∧
    (Even k → asymptoticRank (completeGraph (𝕜 := 𝕜) k d) = (d : ℝ) ^ ((k : ℝ) ^ 2 / 4)) := by
  have h := completeGraphBounds_of_graphExponentBound (𝕜 := 𝕜)
    graphExponent_le_quarter_square k d hk hd
  refine ⟨?_, h.2, ?_⟩
  · simpa only [pow_two, Real.rpow_natCast] using h.1
  · intro heven
    obtain ⟨r, rfl⟩ := even_iff_exists_two_mul.mp heven
    have hr : 0 < r := by omega
    have he : (((2 * r : ℕ) : ℝ) ^ 2 / 4) = ((r ^ 2 : ℕ) : ℝ) := by
      push_cast
      ring
    rw [he, Real.rpow_natCast]
    exact evenCompleteGraphRank_of_graphExponentBound graphExponent_le_quarter_square r d hr hd
-- DOCS_END_MAIN

end Lemmata.TensorRank
