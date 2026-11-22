module

public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Shifted three-party sign strategies outside the signed frequency hull

Coordinates are twice the even part of a negacyclic triple convolution. The
usual Reynolds coordinates differ by the positive constant `2 * m^2`.
Both the candidate points and the witness are computed from sign strategies.
-/

namespace Lemmata.BellFollowup.Frequency

open scoped BigOperators

/-- Antiperiodic square-wave sign row of odd frequency `s`. -/
def threshold (m s x : ℕ) : ℤ :=
  if s * x % (2 * m) < m then 1 else -1

/-- Convolve two rows on the quotient with `X^m = -1`. The arguments are
their antiperiodic extensions to residues modulo `2*m`. -/
def convolve (m : ℕ) (a b : ℕ → ℤ) (r : ℕ) : ℤ :=
  ∑ t : Fin m, a t * b ((r + 2 * m - t.val) % (2 * m))

/-- The antiperiodic cube of the frequency sign row. -/
def cube (m s : ℕ) : ℕ → ℤ :=
  convolve m (convolve m (threshold m s) (threshold m s)) (threshold m s)

/-- Shift bringing the triple phase to zero or the closest positive phase. -/
def canonicalShift (m s : ℕ) : ℕ :=
  let g := Nat.gcd m s
  let l := m / g
  let u := s / g
  ((List.range (2 * l)).find? fun k =>
    (u * k + 3 * (l - 1) / 2) % (2 * l) == 0).getD 0

/-- Double the even part of a signed shift applied to an antiperiodic row. -/
def folded (m shift : ℕ) (c : ℕ → ℤ) (r : Fin ((m+1)/2)) : ℤ :=
  c ((2*m + r.val - shift) % (2*m)) +
  c ((4*m - r.val - shift) % (2*m))

/-- One projected deterministic strategy for each canonical odd frequency. -/
def candidate (m : ℕ) (i : Fin ((m+1)/2)) : Fin ((m+1)/2) → ℤ :=
  let s := 2*i.val+1
  folded m (canonicalShift m s) (cube m s)

/-- The first frequency point with one additional signed cyclic shift. -/
def shifted (m : ℕ) : Fin ((m+1)/2) → ℤ :=
  folded m (canonicalShift m 1 + 1) (cube m 1)

/-- Integer score of a projected profile. -/
def dot {d : ℕ} (w v : Fin d → ℤ) : ℤ := ∑ i, w i * v i

/-- Cast a finite integer profile to the real coordinate space. -/
def realProfile {d : ℕ} (v : Fin d → ℤ) : Fin d → ℝ := fun r => (v r : ℝ)

/-- Real convex hull of a finite family of profiles and their negatives. -/
def signedHull {d : ℕ} (V : Fin d → Fin d → ℤ) : Set (Fin d → ℝ) :=
  convexHull ℝ {x | ∃ i, x = realProfile (V i) ∨ x = -realProfile (V i)}

/-- Real convex hull of the signed canonical three-party frequency profiles. -/
def frequencyHull (m : ℕ) : Set (Fin ((m+1)/2) → ℝ) := signedHull (candidate m)

private noncomputable def form {d : ℕ} (w : Fin d → ℤ) : (Fin d → ℝ) →ₗ[ℝ] ℝ where
  toFun x := ∑ i, (w i : ℝ) * x i
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' a x := by
    change (∑ i, (w i : ℝ) * (a * x i)) = a * ∑ i, (w i : ℝ) * x i
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

private theorem form_cast {d : ℕ} (w v : Fin d → ℤ) :
    form w (realProfile v) = (dot w v : ℝ) := by
  simp [form, realProfile, dot]

/-- A strict integer separation excludes the shifted atom from the entire real hull. -/
theorem outside_signedHull_of_score {d : ℕ} (V : Fin d → Fin d → ℤ)
    (v w : Fin d → ℤ) (b : ℤ)
    (h : ∀ i, -b ≤ dot w (V i) ∧ dot w (V i) ≤ b)
    (hs : b < dot w v) : realProfile v ∉ signedHull V := by
  let half : Set (Fin d → ℝ) := {x | form w x ≤ (b : ℝ)}
  have hc : Convex ℝ half := convex_halfSpace_le (form w).isLinear _
  have hmem : signedHull V ⊆ half := by
    apply convexHull_min _ hc
    rintro x ⟨i, hi | hi⟩
    · subst x
      change form w (realProfile (V i)) ≤ (b : ℝ)
      rw [form_cast]
      exact_mod_cast (h i).2
    · subst x
      change form w (-realProfile (V i)) ≤ (b : ℝ)
      rw [map_neg, form_cast]
      have hn : -dot w (V i) ≤ b := by linarith [(h i).1]
      exact_mod_cast hn
  intro hin
  have hle := hmem hin
  change form w (realProfile v) ≤ (b : ℝ) at hle
  rw [form_cast] at hle
  have hlt : (b : ℝ) < (dot w v : ℝ) := by exact_mod_cast hs
  exact (not_lt_of_ge hle) hlt

/-- A strict integer separation excludes the shifted atom from the entire real hull. -/
theorem outside_of_score {m : ℕ} (w : Fin ((m+1)/2) → ℤ) (b : ℤ)
    (h : ∀ i, -b ≤ dot w (candidate m i) ∧ dot w (candidate m i) ≤ b)
    (hs : b < dot w (shifted m)) : realProfile (shifted m) ∉ frequencyHull m := outside_signedHull_of_score (candidate m) (shifted m) w b h hs

/- The closed expression for the convolution square avoids recomputing a
quadratic sum for each entry of the cube. Its equality to the actual square
on every needed index is itself checked by the kernel in each instance. -/
private def fastSquare (m s t : ℕ) : ℤ :=
  let g := Nat.gcd m s
  let l := m/g
  let z := (s/g)*t
  let v := (g : ℤ) * (2 * ((z % l : ℕ) : ℤ) + 2 - (l : ℤ))
  if z % (2*l) < l then v else -v

private def fastCube (m s : ℕ) : ℕ → ℤ := convolve m (fastSquare m s) (threshold m s)

private theorem cube_eq_fast {m s : ℕ}
    (hs : ∀ t : Fin m, convolve m (threshold m s) (threshold m s) t = fastSquare m s t) :
    cube m s = fastCube m s := by
  funext r
  unfold cube fastCube convolve
  apply Finset.sum_congr rfl
  intro t _
  exact congrArg (fun z : ℤ => z * threshold m s ((r + 2 * m - t.val) % (2 * m))) (hs t)

private def fastCandidate (m : ℕ) (i : Fin ((m+1)/2)) : Fin ((m+1)/2) → ℤ :=
  let s := 2*i.val+1
  folded m (canonicalShift m s) (fastCube m s)

private def fastShifted (m : ℕ) : Fin ((m+1)/2) → ℤ :=
  folded m (canonicalShift m 1 + 1) (fastCube m 1)

private theorem certify {m : ℕ} (hm : 0 < (m+1)/2) (w : Fin ((m+1)/2) → ℤ) (b : ℤ)
    (sq : ∀ (i : Fin ((m+1)/2)) (t : Fin m),
      convolve m (threshold m (2*i.val+1)) (threshold m (2*i.val+1)) t =
        fastSquare m (2*i.val+1) t)
    (hb : ∀ i, -b ≤ dot w (fastCandidate m i) ∧ dot w (fastCandidate m i) ≤ b)
    (hs : b < dot w (fastShifted m)) : realProfile (shifted m) ∉ frequencyHull m := by
  apply outside_of_score w b
  · intro i
    simpa only [candidate, fastCandidate, cube_eq_fast (sq i)] using hb i
  · have hzero := cube_eq_fast (sq ⟨0, hm⟩)
    change cube m 1 = fastCube m 1 at hzero
    simpa only [shifted, fastShifted, hzero] using hs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- At seventeen settings, an additional shift gives score 7118 against bound 7114. -/
theorem shifted17_outside : realProfile (shifted 17) ∉ frequencyHull 17 := by
  let w : Fin 9 → ℤ := ![5,7,9,5,6,0,1,-7,-27]
  apply certify (by decide) w 7114 <;> decide +kernel

/-- At twenty-eight settings, an additional shift gives score 174748 against bound 174740. -/
theorem shifted28_outside : realProfile (shifted 28) ∉ frequencyHull 28 := by
  let w : Fin 14 → ℤ := ![0,92,0,88,0,69,0,43,0,13,0,-43,0,-263]
  apply certify (by decide) w 174740 <;> decide +kernel

/-- At thirty-two settings, an additional shift gives score 39476 against bound 39468. -/
theorem shifted32_outside : realProfile (shifted 32) ∉ frequencyHull 32 := by
  let w : Fin 16 → ℤ := ![5,5,9,4,8,3,8,2,6,-1,5,-5,4,-11,1,-44]
  apply certify (by decide) w 39468 <;> decide +kernel

end Lemmata.BellFollowup.Frequency
