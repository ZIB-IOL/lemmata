module

public import Lemmata.BellFollowup.Frequency.Main

@[expose] public section
namespace Lemmata.BellFollowup.Frequency

/-- The antiperiodic cube of a single signed interval of length `l`, evaluated
by its quadratic formula on the fundamental interval. -/
def intervalCube (l : ℕ) (r : ℤ) : ℤ :=
  let t := r % (l : ℤ)
  let v := 2 * (t + 1) * (t + 2 - (l : ℤ)) - (l : ℤ)
  if r % (2*(l : ℤ)) < l then v else -v

/-- Pull back the interval cube along the phase map and multiply by the
squared fiber size. This is the integer closed form for a frequency cube. -/
def reducedCube (m s r : ℕ) : ℤ :=
  let g := Nat.gcd m s
  (g : ℤ)^2 * intervalCube (m/g) (((s/g)*r : ℕ) : ℤ)

/-- Canonical frequency profile in the closed interval-cube formula. -/
def reducedCandidate (m : ℕ) (i : Fin ((m+1)/2)) : Fin ((m+1)/2) → ℤ :=
  let s := 2*i.val+1
  folded m (canonicalShift m s) (reducedCube m s)

/-- The first profile with one additional signed cyclic shift. -/
def reducedShifted (m : ℕ) : Fin ((m+1)/2) → ℤ :=
  folded m (canonicalShift m 1 + 1) (reducedCube m 1)
end Lemmata.BellFollowup.Frequency
