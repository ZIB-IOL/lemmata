module

public import Mathlib.Analysis.Real.Sqrt

@[expose] public section

namespace Lemmata.SchrodingerRemainderBound

/-- The nonnegative relativistic energy for positive mass and real momentum. -/
noncomputable def relativisticEnergy (mass momentum : ℝ) : ℝ :=
  Real.sqrt (mass ^ 2 + momentum ^ 2)

/-- The relativistic energy after subtracting the rest energy. -/
noncomputable def restEnergyRemoved (mass momentum : ℝ) : ℝ :=
  relativisticEnergy mass momentum - mass

/-- The leading nonrelativistic kinetic energy. -/
noncomputable def schrodingerEnergy (mass momentum : ℝ) : ℝ :=
  momentum ^ 2 / (2 * mass)

/-- The exact correction to the leading nonrelativistic kinetic energy. -/
noncomputable def schrodingerRemainder (mass momentum : ℝ) : ℝ :=
  -(momentum ^ 4) /
    (2 * mass * (relativisticEnergy mass momentum + mass) ^ 2)

/--
Exact nonrelativistic decomposition of the positive relativistic branch,
together with a uniform quartic bound on its correction.
-/
def RemainderBoundStatement : Prop :=
  ∀ mass momentum : ℝ, 0 < mass →
    restEnergyRemoved mass momentum =
        schrodingerEnergy mass momentum + schrodingerRemainder mass momentum ∧
      |schrodingerRemainder mass momentum| ≤ momentum ^ 4 / (8 * mass ^ 3)

end Lemmata.SchrodingerRemainderBound
