module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

@[expose] public section

namespace Lemmata.C19CoupledPhaseGap

/-- The Fourier structure factor of the weighted cubic C19 neighborhood. -/
noncomputable def structureFactor (k0 k1 k2 : ℝ) : ℝ :=
  8 * ((1 - Real.cos k0) + (1 - Real.cos k1) + (1 - Real.cos k2)) +
    8 * ((1 - Real.cos k0 * Real.cos k1) +
      (1 - Real.cos k0 * Real.cos k2) +
      (1 - Real.cos k1 * Real.cos k2))

/-- The phase stiffness with the geometry-derived scale `chi0 = 19`. -/
noncomputable def phaseStiffness (psiRadius chiRadius k0 k1 k2 : ℝ) : ℝ :=
  (psiRadius ^ 2 * chiRadius ^ 2 / (19 : ℝ) ^ 2) *
    structureFactor k0 k1 k2

/-- The propagating phase eigenvalue with kinetic normalization `B = 1197`. -/
noncomputable def propagatingOmegaSquared
    (psiRadius chiRadius k0 k1 k2 : ℝ) : ℝ :=
  phaseStiffness psiRadius chiRadius k0 k1 k2 *
    (1 / psiRadius ^ 2 + 1 / ((1197 : ℝ) * chiRadius ^ 2))

/--
The propagating phase eigenvalue is positive whenever both radii and the C19
structure factor are nonzero in the indicated sense.
-/
def CoupledPhaseGap : Prop :=
  ∀ psiRadius chiRadius k0 k1 k2 : ℝ,
    psiRadius ≠ 0 →
    chiRadius ≠ 0 →
    0 < structureFactor k0 k1 k2 →
    0 < propagatingOmegaSquared psiRadius chiRadius k0 k1 k2

end Lemmata.C19CoupledPhaseGap
