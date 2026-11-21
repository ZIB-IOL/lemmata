module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Tactic

@[expose] public section

namespace Lemmata.C19IsotropicSymbol

noncomputable section

abbrev Site := ℤ × ℤ × ℤ
abbrev WaveVector := ℝ × ℝ × ℝ

structure Bond where
  offset : Site
  weight : ℕ
  deriving DecidableEq

def positiveBonds : List Bond :=
  [⟨(1, 0, 0), 2⟩, ⟨(0, 1, 0), 2⟩, ⟨(0, 0, 1), 2⟩,
   ⟨(1, 1, 0), 1⟩, ⟨(1, -1, 0), 1⟩, ⟨(1, 0, 1), 1⟩,
   ⟨(1, 0, -1), 1⟩, ⟨(0, 1, 1), 1⟩, ⟨(0, 1, -1), 1⟩]

def dotSite (k : WaveVector) (s : Site) : ℝ :=
  k.1 * s.1 + k.2.1 * s.2.1 + k.2.2 * s.2.2

def scaleWave (h : ℝ) (k : WaveVector) : WaveVector :=
  (h * k.1, h * k.2.1, h * k.2.2)

def waveNormSq (k : WaveVector) : ℝ :=
  k.1 ^ 2 + k.2.1 ^ 2 + k.2.2 ^ 2

def speedSq : ℝ :=
  2 * (positiveBonds.map fun b =>
    (b.weight : ℝ) * (b.offset.1 : ℝ) ^ 2).sum

def spaceSymbol (k : WaveVector) : ℝ :=
  4 * (positiveBonds.map fun b =>
    (b.weight : ℝ) * (1 - Real.cos (dotSite k b.offset))).sum

def spatialErrorWeight (k : WaveVector) : ℝ :=
  (positiveBonds.map fun b =>
    (b.weight : ℝ) * (dotSite k b.offset) ^ 4).sum / 6

def C19SymbolStatement : Prop :=
  (∀ k : WaveVector,
    2 * (positiveBonds.map fun b =>
      (b.weight : ℝ) * (dotSite k b.offset) ^ 2).sum =
      speedSq * waveNormSq k) ∧
  speedSq = 12 ∧
  ∀ h : ℝ, ∀ k : WaveVector,
    |spaceSymbol (scaleWave h k) - h ^ 2 * (speedSq * waveNormSq k)| ≤
      h ^ 4 * spatialErrorWeight k

end
end Lemmata.C19IsotropicSymbol
