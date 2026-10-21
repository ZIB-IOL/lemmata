module

public import Lemmata.TensorRank.Proof.PolynomialSpectrum

@[expose] public section

set_option autoImplicit false

open scoped BigOperators

namespace Lemmata.TensorRank

open Tensor (asymptoticRank)

-- DOCS_BEGIN_MAIN
theorem squareRootBound (k : ℕ) (hk : 0 < k) :
    (∀ (d : Fin k → ℕ) (T : Tensor ℂ (Fin k) (fun i => Fin (d i))),
      asymptoticRank T ≤ Real.sqrt (∏ i, (d i : ℝ))) ∧
    (∀ (n : ℕ) (T : Cubical k n),
      asymptoticRank T ≤ (n : ℝ) ^ ((k : ℝ) / 2)) := by
  let : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  have h := squareRoot_of_graphExponentBound graphExponent_le_quarter_square
  constructor
  · intro d T
    simpa only [Fintype.card_fin] using h (Fin k) (fun i => Fin (d i)) T
  · intro n T
    exact cubical_of_squareRoot h k n hk T

theorem evenCubicalSharpness (r n : ℕ) (hr : 0 < r) :
    IsGreatest (cubicalRanks (r + r) n) ((n : ℝ) ^ r) ∧
    (∀ T : Cubical (r + r) n, (balancedMatrix r n T).det ≠ 0 →
      asymptoticRank T = (n : ℝ) ^ r) := by
  have h := squareRoot_of_graphExponentBound graphExponent_le_quarter_square
  exact ⟨evenCubicalMaximum_of_squareRoot h r n hr,
    evenCubicalNonsingular_of_squareRoot h r n hr⟩

theorem completeGraphBounds (k d : ℕ) (hk : 2 ≤ k) (hd : 1 ≤ d) :
    (d : ℝ) ^ (k ^ 2 / 4) ≤ asymptoticRank (completeGraph k d) ∧
    asymptoticRank (completeGraph k d) ≤ (d : ℝ) ^ ((k : ℝ) ^ 2 / 4) ∧
    (Even k → asymptoticRank (completeGraph k d) = (d : ℝ) ^ ((k : ℝ) ^ 2 / 4)) := by
  have h := completeGraphBounds_of_graphExponentBound graphExponent_le_quarter_square k d hk hd
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
