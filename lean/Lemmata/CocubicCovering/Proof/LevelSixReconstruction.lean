module

public import Lemmata.CocubicCovering.Proof.MatrixReduction
public meta import Lemmata.CocubicCovering.Proof.MatrixReduction
public import Lemmata.CocubicCovering.Compute.Linear
public meta import Lemmata.CocubicCovering.Compute.Linear
public import Mathlib.Data.Fintype.Fin

@[expose] public section

namespace Lemmata.CocubicCovering.CoveringLevelSixReconstruction

open scoped BigOperators
open CoveringAffine CoveringBits CoveringPolynomial CoveringCongruence
open CoveringMatrixReduction

def coreData : Array (List Nat) := #[[0x400, 0x200], [0xd8d, 0x306], [0xd3c, 0x2a0], [0xdc2, 0x200, 0x32], [0x975, 0x527], [0x939, 0x510, 0x200], [0x80b, 0x3a4], [0x80f, 0x583, 0x305], [0x93e, 0x583, 0x305], [0x831, 0x480, 0x231, 0x133], [0x800, 0x582, 0x200, 0x31], [0x800, 0x400, 0x201, 0x10e, 0x8e, 0x42, 0x1d], [0x800, 0x400, 0x200, 0x81, 0x55, 0x31, 0x3]]
def restrictionData : Array Nat := #[0x4008, 0x401a, 0x4014, 0x4060, 0x4065, 0x4050, 0x4053, 0x4057, 0x4057, 0x4040, 0x4040, 0x0, 0x0]
def crossProfileData : Array (List Nat) := #[[0x1, 0x2, 0x4, 0x8, 0x10, 0x20, 0x200, 0x400, 0x800, 0x20000], [0x1, 0x2, 0x4, 0x8, 0x10, 0x20, 0x200, 0x400, 0x800, 0x10000], [0x1, 0x2, 0x4, 0x8, 0x10, 0x20, 0x200, 0x400, 0x800, 0x10000], [0x1, 0x2, 0x4, 0x8, 0x10, 0x200, 0x400, 0x800, 0x20a02], [0x1, 0x2, 0x4, 0x8, 0x10, 0x20, 0x200, 0x400, 0x800, 0x8000], [0x1, 0x2, 0x4, 0x8, 0x10, 0x20, 0x200, 0x400, 0x10021], [0x1, 0x2, 0x4, 0x8, 0x10, 0x20, 0x200, 0x400, 0x800, 0x10000], [0x1, 0x2, 0x4, 0x8, 0x10, 0x20, 0x200, 0x400, 0x831], [0x1, 0x2, 0x4, 0x8, 0x10, 0x20, 0x200, 0x400, 0x831], [0x1, 0x2, 0x4, 0x8, 0x10, 0x200, 0x10021, 0x802], [0x1, 0x2, 0x4, 0x8, 0x10, 0x200, 0x10021, 0x802], [0x1, 0x2, 0x4, 0x8, 0x20], [0x1, 0x4, 0x8, 0x10, 0x800]]
def outsideProfileData : Array (List Nat) := #[[0x40, 0x80, 0x100, 0x1000, 0x2000, 0x4000, 0x40000, 0x80000, 0x100000, 0x200000, 0x400000, 0x800000, 0x1000000, 0x2000000, 0x4000000], [0x40, 0x80, 0x100, 0x1000, 0x2000, 0x4000, 0x40000, 0x80000, 0x100000, 0x200000, 0x400000, 0x800000, 0x1000000, 0x2000000, 0x4000000], [0x40, 0x80, 0x100, 0x1000, 0x2000, 0x4000, 0x40000, 0x80000, 0x100000, 0x200000, 0x400000, 0x800000, 0x1000000, 0x2000000, 0x4000000], [0x40, 0x80, 0x100, 0x1000, 0x2000, 0x4000, 0x40000, 0x80000, 0x100000, 0x200000, 0x400000, 0x800000, 0x1000000, 0x2000000, 0x4000000], [0x40, 0x80, 0x100, 0x1000, 0x2000, 0x4000, 0x40000, 0x80000, 0x100000, 0x200000, 0x400000, 0x800000, 0x1000000, 0x2000000, 0x4000000], [0x40, 0x80, 0x100, 0x1000, 0x2000, 0x4000, 0x40000, 0x80000, 0x100000, 0x200000, 0x400000, 0x800000, 0x1000000, 0x2000000, 0x4000000], [0x40, 0x80, 0x100, 0x1000, 0x2000, 0x4000, 0x40000, 0x80000, 0x100000, 0x200000, 0x400000, 0x800000, 0x1000000, 0x2000000, 0x4000000], [0x40, 0x80, 0x100, 0x1000, 0x2000, 0x4000, 0x40000, 0x80000, 0x100000, 0x200000, 0x400000, 0x800000, 0x1000000, 0x2000000, 0x4000000], [0x40, 0x80, 0x100, 0x1000, 0x2000, 0x4000, 0x40000, 0x80000, 0x100000, 0x200000, 0x400000, 0x800000, 0x1000000, 0x2000000, 0x4000000], [0x40, 0x80, 0x100, 0x1000, 0x2000, 0x4000, 0x40000, 0x80000, 0x100000, 0x200000, 0x400000, 0x800000, 0x1000000, 0x2000000, 0x4000000], [0x40, 0x80, 0x100, 0x1000, 0x2000, 0x4000, 0x40000, 0x80000, 0x100000, 0x200000, 0x400000, 0x800000, 0x1000000, 0x2000000, 0x4000000], [0x40, 0x80, 0x100, 0x1000, 0x2000, 0x4000, 0x40000, 0x80000, 0x100000, 0x200000, 0x400000, 0x800000, 0x1000000, 0x2000000, 0x4000000], [0x40, 0x80, 0x100, 0x1000, 0x2000, 0x4000, 0x40000, 0x80000, 0x100000, 0x200000, 0x400000, 0x800000, 0x1000000, 0x2000000, 0x4000000]]

def restriction (s : Fin 13) : Nat := restrictionData[s.val]?.getD 0
def core (s : Fin 13) : List Nat := coreData[s.val]?.getD []
def crossProfile (s : Fin 13) : List Nat := crossProfileData[s.val]?.getD []
def outsideProfile (s : Fin 13) : List Nat := outsideProfileData[s.val]?.getD []
def wCoordinates (i : Fin 12) : Nat :=
  (#[1,2,4,8,16,32,512,1024,2048,32768,65536,131072][i.val]?).getD 0

def sourceConstraintRows (s : Fin 13) : List Nat :=
  (List.finRange 15).map (fun i =>
    (2 ^ (111 + i.val)) ^^^ (if (restriction s).testBit i.val then 2 ^ 126 else 0)) ++
  (core s).flatMap (fun q => (List.finRange 27).map (fun column =>
    composeRow (composeRow q wCoordinates) (fun i => CoveringLevelSix.matrixRows i column)))



def constraintList (s : Fin 13) : List Nat := sourceConstraintRows s
def constraintCount (s : Fin 13) : Nat := (constraintList s).length
def constraints (s : Fin 13) (i : Fin (constraintCount s)) : Nat := (constraintList s).get i

def unpackMatrix (bits : Nat) : Array Nat :=
  (Array.range 27).map fun i => (bits >>> (27 * i)) &&& (2 ^ 27 - 1)

def packedPair (matrix left right : Nat) : Bool := Id.run do
  let mut value := false
  for i in [:27] do
    if left.testBit i then
      value := Bool.xor value (Lemmata.CocubicCovering.Compute.Linear.parity (((matrix >>> (27*i)) &&& (2^27-1)) &&& right))
  return value

def crossProjection (s : Fin 13) (matrix : Nat) : Nat := Id.run do
  let mut value := 0
  let left := (crossProfile s).toArray
  let right := (outsideProfile s).toArray
  for i in [:left.size] do
    for j in [:15] do
      if packedPair matrix (left[i]?.getD 0) (right[j]?.getD 0) then
        value := value ||| 2 ^ (i*15+j)
  return value

structure Reconstruction where
  base : Array Nat
  cross : Array (Array Nat)
  outside : Array (Array Nat)
  crossCoefficients : Array Nat
  outsideCoefficients : Array Nat
  witnesses : Array Nat

def generate (s : Fin 13) : Reconstruction := Id.run do
  let constraintBasis := Lemmata.CocubicCovering.Compute.Linear.build 126 (constraintList s).toArray
  let rows := (Array.range 729).map fun entry =>
    Lemmata.CocubicCovering.Compute.Linear.normalForm 126 constraintBasis
      (CoveringLevelSix.matrixRows (Fin.ofNat 27 (entry / 27)) (Fin.ofNat 27 entry))
  let mut constant := 0
  for entry in [:729] do
    if (rows[entry]?.getD 0).testBit 126 then constant := constant ||| 2 ^ entry
  let rawDirections := (Array.range 126).map fun parameter => Id.run do
    let mut matrix := 0
    for entry in [:729] do
      if (rows[entry]?.getD 0).testBit parameter then matrix := matrix ||| 2 ^ entry
    return matrix
  let directions := (Lemmata.CocubicCovering.Compute.Linear.orderedBasis 729 rawDirections).map fun matrix =>
    matrix ||| (crossProjection s matrix <<< 729)
  let width := 729 + (crossProfile s).length * 15
  let basis := Lemmata.CocubicCovering.Compute.Linear.basis width directions
  let crosses := basis.filter fun value => value >>> 729 != 0
  let outsides := basis.filter fun value => value >>> 729 == 0
  let ordered := crosses ++ outsides
  let decomposition := Lemmata.CocubicCovering.Compute.Linear.build width ordered
  let mut coefficients := Array.replicate ordered.size 0
  for parameter in [:126] do
    let matrix := rawDirections[parameter]?.getD 0
    let result := Lemmata.CocubicCovering.Compute.Linear.solve width decomposition (matrix ||| (crossProjection s matrix <<< 729))
    for i in [:ordered.size] do
      if result.coefficients.testBit i then
        coefficients := coefficients.set! i ((coefficients[i]?.getD 0) ^^^ 2 ^ parameter)
  let crossCoefficients := coefficients.extract 0 crosses.size
  let outsideCoefficients := coefficients.extract crosses.size coefficients.size
  let cross := crosses.map unpackMatrix
  let outside := outsides.map unpackMatrix
  let fullConstraintBasis := Lemmata.CocubicCovering.Compute.Linear.build 127 (constraintList s).toArray
  let witnesses := (Array.range 729).map fun entry => Id.run do
    let mut reconstructed := if constant.testBit entry then 2 ^ 126 else 0
    for i in [:ordered.size] do
      if (ordered[i]?.getD 0).testBit entry then
        reconstructed := reconstructed ^^^ (coefficients[i]?.getD 0)
    let original := CoveringLevelSix.matrixRows (Fin.ofNat 27 (entry / 27)) (Fin.ofNat 27 entry)
    return (Lemmata.CocubicCovering.Compute.Linear.solve 127 fullConstraintBasis (original ^^^ reconstructed)).coefficients
  return ⟨unpackMatrix constant, cross, outside, crossCoefficients, outsideCoefficients, witnesses⟩

def reconstructions : Array Reconstruction := (List.finRange 13).toArray.map generate
def result (s : Fin 13) : Reconstruction := reconstructions[s.val]?.getD ⟨#[], #[], #[], #[], #[], #[]⟩
def base (s : Fin 13) (i : Fin 27) : Nat := (result s).base[i.val]?.getD 0
def crossCount (s : Fin 13) : Nat := (result s).cross.size
def outsideCount (s : Fin 13) : Nat := (result s).outside.size
def cross (s : Fin 13) (k : Fin (crossCount s)) (i : Fin 27) : Nat :=
  ((result s).cross[k.val]?.getD #[])[i.val]?.getD 0
def outside (s : Fin 13) (k : Fin (outsideCount s)) (i : Fin 27) : Nat :=
  ((result s).outside[k.val]?.getD #[])[i.val]?.getD 0
def crossCoefficients (s : Fin 13) (k : Fin (crossCount s)) : Nat :=
  (result s).crossCoefficients[k.val]?.getD 0
def outsideCoefficients (s : Fin 13) (k : Fin (outsideCount s)) : Nat :=
  (result s).outsideCoefficients[k.val]?.getD 0
def witnesses (s : Fin 13) (i j : Fin 27) : Nat :=
  (result s).witnesses[i.val*27+j.val]?.getD 0

def Checked (s : Fin 13) : Prop :=
  forall i j : Fin 27, CoveringLevelSix.matrixRows i j =
    affineRow (base s) (cross s) (outside s) (crossCoefficients s) (outsideCoefficients s) i j ^^^
      composeRow (witnesses s i j) (constraints s)


set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem checked : ∀ s : Fin 13, Checked s := by
  unfold Checked
  native_decide

theorem original_constraints (s : Fin 13) : constraintList s = sourceConstraintRows s := rfl

theorem constraint_mem_source (s : Fin 13) (i : Fin (constraintCount s)) :
    constraints s i ∈ sourceConstraintRows s := by
  rw [← original_constraints]
  exact List.get_mem (constraintList s) i

theorem constraints_vanish_of_local_and_kernel (s : Fin 13) (v : Vector 127)
    (hpoint : v (Fin.last 126) = 1)
    (hlocal : ∀ i : Fin 15, v ⟨111 + i.val, by omega⟩ =
      ofBool ((restriction s).testBit i.val))
    (hcore : ∀ q ∈ core s,
      Matrix.toBilin' (coefficientMatrix CoveringLevelSix.matrixRows v)
        (decodeMask (composeRow q wCoordinates)) = 0) :
    ∀ i, evalRow (constraints s i) v = 0 := by
  intro i
  have hmem := constraint_mem_source s i
  unfold sourceConstraintRows at hmem
  rcases List.mem_append.mp hmem with hfirst | hsecond
  · obtain ⟨j, hj, heq⟩ := List.mem_map.mp hfirst
    rw [← heq]
    exact evalRow_local_assignment v hpoint (restriction s) j (hlocal j)
  · obtain ⟨q, hq, hrow⟩ := List.mem_flatMap.mp hsecond
    obtain ⟨column, hcolumn, heq⟩ := List.mem_map.mp hrow
    rw [← heq]
    exact evalRow_kernel_eq_zero CoveringLevelSix.matrixRows v
      (composeRow q wCoordinates) (hcore q hq) column

theorem realization (s : Fin 13) (v : Vector 127) (hpoint : v (Fin.last 126) = 1)
    (hconstraints : forall k, evalRow (constraints s k) v = 0) (i j : Fin 27) :
    coefficientMatrix CoveringLevelSix.matrixRows v i j =
      ofBool ((base s i).testBit j.val) +
        (∑ k, ofBool ((cross s k i).testBit j.val) * evalRow (crossCoefficients s k) v) +
        ∑ k, ofBool ((outside s k i).testBit j.val) * evalRow (outsideCoefficients s k) v :=
  matrix_reconstruction _ _ _ _ _ _ _ _ (checked s) v hpoint hconstraints i j


end Lemmata.CocubicCovering.CoveringLevelSixReconstruction
