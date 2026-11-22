module

public import Lemmata.ModifiedE8Bell.Statement
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Finset.Max
public import Mathlib.Tactic
public meta import Lemmata.ModifiedE8Bell.Statement

@[expose] public section

namespace Lemmata.ModifiedE8Bell
open scoped BigOperators

/-- Reconstruction from the eight chamber gaps, in order d,s,t,a,b,c,e,f. -/
def basis : Coordinate → Vector := ![
  ![0, 1, -1, 0, 0, 0, 0, 0],
  ![0, 1, 1, 0, 0, 0, 0, 0],
  ![0, 1, 1, 2, 0, 0, 0, 0],
  ![0, 1, 1, 2, 2, 0, 0, 0],
  ![0, 1, 1, 2, 2, 2, 0, 0],
  ![0, 1, 1, 2, 2, 2, 2, 0],
  ![0, 1, 1, 2, 2, 2, 2, 2],
  ![2, 5, 7, 10, 8, 6, 4, 2]]

def coordinates (g : Vector) (j : Coordinate) : ℤ := ∑ k, basis j k * g k

def rootGap (i : Setting) : Vector :=
  ![(root i 7 + root i 0 - root i 1 - root i 2 - root i 3 - root i 4 - root i 5 - root i 6) / 2,
    (root i 0 + root i 1) / 2, (root i 1 - root i 0) / 2,
    (root i 2 - root i 1) / 2, (root i 3 - root i 2) / 2,
    (root i 4 - root i 3) / 2, (root i 5 - root i 4) / 2,
    (root i 6 - root i 5) / 2]

def baseGap : Vector := ![2,29,-17,-1,-1,-1,-1,-1]
def gap (a : Signing) (k : Coordinate) : ℤ :=
  baseGap k - ∑ i, if a i then 0 else rootGap i k

def sumRoot (a : Signing) (j : Coordinate) : ℤ := ∑ i, sign (a i) * root i j

def rho : Vector := ![0,1,2,3,4,5,6,23]
def rootHeight (i : Setting) : ℤ := ∑ j, rho j * root i j

def height (a : Signing) : ℤ := ∑ i, sign (a i) * rootHeight i

def wallScale (k : Coordinate) : ℤ := if k = 0 then 1 else 2

/-- Images of the 120 root lines under each of the eight simple reflections. -/
def reflectionIndices : Array (Array ℕ) := #[
  #[88, 1, 89, 3, 90, 5, 92, 7, 96, 9, 104, 11, 12, 56, 14, 86, 16, 85, 18, 83, 20, 79, 22, 71, 119, 25, 26, 84, 28, 82, 30, 78, 32, 70, 118, 35, 36, 81, 38, 77, 40, 69, 117, 43, 44, 75, 46, 67, 115, 49, 50, 63, 111, 53, 103, 55, 13, 57, 58, 59, 60, 61, 62, 51, 64, 65, 66, 47, 68, 41, 33, 23, 72, 73, 74, 45, 76, 39, 31, 21, 80, 37, 29, 19, 27, 17, 15, 87, 0, 2, 4, 91, 6, 93, 94, 95, 8, 97, 98, 99, 100, 101, 102, 54, 10, 105, 106, 107, 108, 109, 110, 52, 112, 113, 114, 48, 116, 42, 34, 24],
  #[0, 1, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 119, 57, 58, 116, 60, 114, 113, 63, 64, 110, 109, 67, 107, 69, 70, 104, 72, 102, 101, 75, 99, 77, 78, 96, 95, 81, 82, 92, 84, 90, 89, 87, 88, 86, 85, 91, 83, 93, 94, 80, 79, 97, 98, 76, 100, 74, 73, 103, 71, 105, 106, 68, 108, 66, 65, 111, 112, 62, 61, 115, 59, 117, 118, 56],
  #[0, 1, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 118, 117, 59, 115, 61, 62, 112, 111, 65, 66, 108, 68, 106, 105, 71, 103, 73, 74, 100, 76, 98, 97, 79, 80, 94, 93, 83, 91, 85, 86, 88, 87, 89, 90, 84, 92, 82, 81, 95, 96, 78, 77, 99, 75, 101, 102, 72, 104, 70, 69, 107, 67, 109, 110, 64, 63, 113, 114, 60, 116, 58, 57, 119],
  #[2, 3, 0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 59, 58, 61, 60, 62, 63, 65, 64, 66, 67, 68, 69, 71, 70, 73, 72, 74, 75, 76, 77, 79, 78, 80, 81, 83, 82, 85, 84, 86, 87, 89, 88, 90, 91, 92, 93, 95, 94, 96, 97, 99, 98, 101, 100, 102, 103, 104, 105, 107, 106, 109, 108, 110, 111, 113, 112, 114, 115, 116, 117, 119, 118],
  #[0, 1, 4, 5, 2, 3, 6, 7, 8, 9, 10, 11, 12, 13, 16, 17, 14, 15, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 36, 37, 38, 39, 40, 41, 42, 43, 28, 29, 30, 31, 32, 33, 34, 35, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 58, 57, 59, 60, 62, 61, 63, 64, 66, 65, 67, 68, 70, 69, 71, 72, 74, 73, 75, 76, 78, 77, 79, 80, 82, 81, 83, 84, 86, 85, 87, 88, 90, 89, 91, 92, 94, 93, 95, 96, 98, 97, 99, 100, 102, 101, 103, 104, 106, 105, 107, 108, 110, 109, 111, 112, 114, 113, 115, 116, 118, 117, 119],
  #[0, 1, 2, 3, 6, 7, 4, 5, 8, 9, 10, 11, 12, 13, 14, 15, 18, 19, 16, 17, 20, 21, 22, 23, 24, 25, 28, 29, 26, 27, 30, 31, 32, 33, 34, 35, 36, 37, 44, 45, 46, 47, 48, 49, 38, 39, 40, 41, 42, 43, 50, 51, 52, 53, 54, 55, 56, 57, 60, 61, 58, 59, 62, 63, 64, 65, 68, 69, 66, 67, 70, 71, 72, 73, 76, 77, 74, 75, 78, 79, 80, 81, 84, 85, 82, 83, 86, 87, 88, 89, 92, 93, 90, 91, 94, 95, 96, 97, 100, 101, 98, 99, 102, 103, 104, 105, 108, 109, 106, 107, 110, 111, 112, 113, 116, 117, 114, 115, 118, 119],
  #[0, 1, 2, 3, 4, 5, 8, 9, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17, 20, 21, 18, 19, 22, 23, 24, 25, 26, 27, 30, 31, 28, 29, 32, 33, 34, 35, 38, 39, 36, 37, 40, 41, 42, 43, 44, 45, 50, 51, 52, 53, 46, 47, 48, 49, 54, 55, 56, 57, 58, 59, 64, 65, 66, 67, 60, 61, 62, 63, 68, 69, 70, 71, 72, 73, 74, 75, 80, 81, 82, 83, 76, 77, 78, 79, 84, 85, 86, 87, 88, 89, 90, 91, 96, 97, 98, 99, 92, 93, 94, 95, 100, 101, 102, 103, 104, 105, 106, 107, 112, 113, 114, 115, 108, 109, 110, 111, 116, 117, 118, 119],
  #[0, 1, 2, 3, 4, 5, 6, 7, 10, 11, 8, 9, 12, 13, 14, 15, 16, 17, 18, 19, 22, 23, 20, 21, 24, 25, 26, 27, 28, 29, 32, 33, 30, 31, 34, 35, 36, 37, 40, 41, 38, 39, 42, 43, 46, 47, 44, 45, 48, 49, 50, 51, 54, 55, 52, 53, 56, 57, 58, 59, 60, 61, 62, 63, 72, 73, 74, 75, 76, 77, 78, 79, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 104, 105, 106, 107, 108, 109, 110, 111, 96, 97, 98, 99, 100, 101, 102, 103, 112, 113, 114, 115, 116, 117, 118, 119]]

def reflectionIndex (k : Coordinate) (i : Setting) : Setting :=
  ⟨((reflectionIndices[k.val]?.getD #[])[i.val]?.getD 0) % 120, Nat.mod_lt _ (by decide)⟩

def reflectionFlips : Array (Array Bool) := #[
  #[false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false],
  #[false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, true, false, true, true, false, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, true, false, false, true, false, true, true, false, false, true, true, false, true, false, false, true, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, false, true, true, false, true, false, false, true],
  #[true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true, false, true, false, false, true, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, false, true, true, false, true, false, false, true, true, false, false, true, false, true, true, false, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, true, false, false, true, false, true, true, false],
  #[false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false],
  #[false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false],
  #[false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false],
  #[false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false],
  #[false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]]

def reflectionFlip (k : Coordinate) (i : Setting) : Bool :=
  (reflectionFlips[k.val]?.getD #[])[i.val]?.getD false

def reflectionSign (k : Coordinate) (i : Setting) : ℤ :=
  if reflectionFlip k i then -1 else 1

def reflect (k : Coordinate) (a : Signing) (i : Setting) : Bool :=
  if reflectionFlip k i then !(a (reflectionIndex k i)) else a (reflectionIndex k i)

set_option maxRecDepth 100000
set_option maxHeartbeats 0

-- Finite structural checks, independent of the chamber enumeration.
theorem root_reconstruction : ∀ i j, coordinates (rootGap i) j = root i j := by
  native_decide

theorem root_gap_total : ∀ k, (∑ i, rootGap i k) = 2 * baseGap k := by
  native_decide

theorem root_coordinate_bound : (∑ i, |root i 7|) = 92 := by
  native_decide

theorem reflection_involution : ∀ k i,
    reflectionIndex k (reflectionIndex k i) = i := by
  native_decide

theorem reflection_flip_involution : ∀ k i,
    reflectionSign k (reflectionIndex k i) = reflectionSign k i := by
  native_decide

theorem reflection_height : ∀ k i,
    reflectionSign k i * rootHeight (reflectionIndex k i) =
      rootHeight i - wallScale k * rootGap i k := by
  native_decide

theorem reflection_matrix : ∀ k i j,
    reflectionSign k i * reflectionSign k j *
      fourMatrix (reflectionIndex k i) (reflectionIndex k j) = fourMatrix i j := by
  native_decide

end Lemmata.ModifiedE8Bell
