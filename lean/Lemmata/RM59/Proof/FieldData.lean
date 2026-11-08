module

public import Lemmata.RM59.Proof.F8
public meta import Lemmata.RM59.Proof.F8

@[expose] public section

namespace Lemmata.RM59.FieldData

abbrev PackedPoint := Fin 512
abbrev FieldPoint := Fin 3 → F8Scalar

def support35 : List PackedPoint :=
  [35, 39, 26, 61, 136, 171, 261, 291, 271, 266, 400, 435, 64, 119, 104,
    124, 196, 245, 200, 218, 322, 339, 331, 348, 351, 378, 484, 498, 461, 504]

def support53 : List PackedPoint :=
  [1, 8, 10, 56, 60, 128, 160, 167, 258, 292, 289, 388, 416, 420, 392, 399,
    64, 120, 127, 196, 202, 201, 322, 383, 378, 449, 487, 481, 463, 457, 508, 506]

def verticalFlat : List PackedPoint := [0, 64, 128, 192, 256, 320, 384, 448]

def bitCount (mask : Nat) : Nat := (List.range 9).countP fun i => mask.testBit i

def packedMoment (word : List PackedPoint) (mask : Nat) : Bool :=
  word.foldl (fun value x => Bool.xor value (Nat.land x.val mask == mask)) false

def momentMasks : List (Fin 512) :=
  (List.finRange 512).filter fun mask => bitCount mask.val ≤ 3

def coordinates (x : PackedPoint) : FieldPoint :=
  fun i => F8Scalar.ofNat (x.val / 8 ^ i.val)

def determinant (u v w : FieldPoint) : F8Scalar :=
  u 0 * (v 1 * w 2 - v 2 * w 1) -
    u 1 * (v 0 * w 2 - v 2 * w 0) +
    u 2 * (v 0 * w 1 - v 1 * w 0)

def basisCovector (i : Fin 9) : FieldPoint :=
  fun j => if i.val / 3 = j.val then
    F8Scalar.traceDual (F8Scalar.ofNat (2 ^ (i.val % 3))) else 0

def frameDeterminant (p₀ p₁ p₂ p₃ : PackedPoint) : F8Scalar :=
  determinant (fun j => coordinates p₁ j - coordinates p₀ j)
    (fun j => coordinates p₂ j - coordinates p₀ j)
    (fun j => coordinates p₃ j - coordinates p₀ j)

theorem support35_data : support35.length = 30 ∧ support35.Nodup := by native_decide

theorem support53_data : support53.length = 32 ∧ support53.Nodup := by native_decide

theorem verticalFlat_data : verticalFlat.length = 8 ∧ verticalFlat.Nodup := by
  native_decide

theorem momentMasks_count : momentMasks.length = 130 := by native_decide

theorem lower_moments : ∀ mask : Fin 512, bitCount mask.val ≤ 2 →
    packedMoment support35 mask.val = false ∧
    packedMoment support53 mask.val = false ∧
    packedMoment verticalFlat mask.val = false := by native_decide

/-- These finite coefficients need a bridge to the trilinear moment form. -/
theorem trace_determinant_coefficients : ∀ i j k : Fin 9, i < j → j < k →
    packedMoment support35 (2 ^ i.val + 2 ^ j.val + 2 ^ k.val) =
      F8Scalar.traceBit (determinant (basisCovector i) (basisCovector j)
        (basisCovector k)) := by native_decide

theorem syndrome53_eq_35_xor_vertical : ∀ mask : Fin 512, bitCount mask.val ≤ 3 →
    packedMoment support53 mask.val =
      Bool.xor (packedMoment support35 mask.val) (packedMoment verticalFlat mask.val) := by
  native_decide

theorem vertical_syndrome : ∀ mask : Fin 512, bitCount mask.val ≤ 3 →
    packedMoment verticalFlat mask.val = (mask.val == 448) := by native_decide

theorem full_frame_points_mem :
    ∀ p ∈ ([35, 39, 26, 64, 136, 196] : List PackedPoint), p ∈ support35 := by
  native_decide

theorem full_frame_determinants :
    frameDeterminant 35 39 26 64 = F8Scalar.ofNat 1 ∧
    frameDeterminant 35 39 26 136 = F8Scalar.ofNat 2 ∧
    frameDeterminant 35 39 26 196 = F8Scalar.ofNat 3 := by native_decide

end Lemmata.RM59.FieldData
