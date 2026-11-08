module

public import Lemmata.RM59.Proof.TraceGeometry
public import Lemmata.RM59.Proof.FieldData
public import Lemmata.RM59.Proof.Packed
public meta import Lemmata.RM59.Proof.F8
public meta import Lemmata.RM59.Proof.FieldData
public meta import Lemmata.RM59.Proof.Packed

@[expose] public section

namespace Lemmata.RM59.FieldCoordinates

open scoped BigOperators

abbrev FieldPoint := TraceGeometry.FieldPoint

def encodeChunk (x : Fin 3 → Field) : F8Scalar :=
  F8Scalar.ofNat (∑ i, if x i = 1 then 2 ^ i.val else 0)

def decodeChunk (a : F8Scalar) : Fin 3 → Field :=
  fun i => Packed.bitField (a.bit i)

theorem encodeChunk_add : ∀ x y : Fin 3 → Field,
    encodeChunk (x + y) = encodeChunk x + encodeChunk y := by decide

@[simp] theorem encodeChunk_zero : encodeChunk 0 = 0 := by decide

theorem decode_encode : ∀ x : Fin 3 → Field, decodeChunk (encodeChunk x) = x := by decide

theorem encode_decode : ∀ a : F8Scalar, encodeChunk (decodeChunk a) = a := by decide

def chunkLinear : (Fin 3 → Field) →ₗ[Field] F8Scalar where
  toFun := encodeChunk
  map_add' := encodeChunk_add
  map_smul' r x := by
    rcases field_eq_zero_or_one r with rfl | rfl <;> simp

def chunkEquiv : (Fin 3 → Field) ≃ₗ[Field] F8Scalar where
  __ := chunkLinear
  invFun := decodeChunk
  left_inv := decode_encode
  right_inv := encode_decode

def blockIndex (j k : Fin 3) : Fin 9 :=
  ⟨(3 * j.val + k.val) % 9, Nat.mod_lt _ (by decide)⟩

def blockOf (i : Fin 9) : Fin 3 :=
  ⟨(i.val / 3) % 3, Nat.mod_lt _ (by decide)⟩

def indexInBlock (i : Fin 9) : Fin 3 :=
  ⟨i.val % 3, Nat.mod_lt _ (by decide)⟩

@[simp] theorem blockOf_blockIndex : ∀ j k : Fin 3, blockOf (blockIndex j k) = j := by
  decide

@[simp] theorem indexInBlock_blockIndex : ∀ j k : Fin 3,
    indexInBlock (blockIndex j k) = k := by decide

@[simp] theorem blockIndex_parts : ∀ i : Fin 9,
    blockIndex (blockOf i) (indexInBlock i) = i := by decide

def pointLinear : Point 9 →ₗ[Field] FieldPoint where
  toFun x j := chunkLinear (fun k => x (blockIndex j k))
  map_add' x y := funext fun j => chunkLinear.map_add
    (fun k => x (blockIndex j k)) (fun k => y (blockIndex j k))
  map_smul' r x := funext fun j => chunkLinear.map_smul r (fun k => x (blockIndex j k))

def inversePoint (x : FieldPoint) : Point 9 :=
  fun i => decodeChunk (x (blockOf i)) (indexInBlock i)

def pointEquiv : Point 9 ≃ₗ[Field] FieldPoint where
  __ := pointLinear
  invFun := inversePoint
  left_inv x := by
    funext i
    change decodeChunk (encodeChunk (fun k => x (blockIndex (blockOf i) k)))
      (indexInBlock i) = x i
    rw [decode_encode, blockIndex_parts]
  right_inv x := by
    funext j
    change encodeChunk (fun k => decodeChunk (x (blockOf (blockIndex j k)))
      (indexInBlock (blockIndex j k))) = x j
    simp only [blockOf_blockIndex, indexInBlock_blockIndex, encode_decode]

theorem packed_coordinates : ∀ x : Packed.PackedPoint,
    pointEquiv (Packed.decodePoint x) = FieldData.coordinates x := by native_decide

theorem traceDual_add : ∀ a b : F8Scalar,
    F8Scalar.traceDual (a + b) = F8Scalar.traceDual a + F8Scalar.traceDual b := by decide

@[simp] theorem traceDual_zero : F8Scalar.traceDual 0 = 0 := by decide

theorem traceDual_involution : ∀ a : F8Scalar,
    F8Scalar.traceDual (F8Scalar.traceDual a) = a := by decide

def traceDualLinear : F8Scalar →ₗ[Field] F8Scalar where
  toFun := F8Scalar.traceDual
  map_add' := traceDual_add
  map_smul' r a := by
    rcases field_eq_zero_or_one r with rfl | rfl <;> simp

def covectorLinear : Point 9 →ₗ[Field] FieldPoint where
  toFun x j := traceDualLinear (pointEquiv x j)
  map_add' x y := by
    funext j
    change traceDualLinear (pointEquiv (x + y) j) =
      traceDualLinear (pointEquiv x j) + traceDualLinear (pointEquiv y j)
    rw [map_add]
    exact traceDualLinear.map_add _ _
  map_smul' r x := by
    funext j
    change traceDualLinear (pointEquiv (r • x) j) = r • traceDualLinear (pointEquiv x j)
    rw [map_smul]
    exact traceDualLinear.map_smul r _

def covectorEquiv : Point 9 ≃ₗ[Field] FieldPoint where
  __ := covectorLinear
  invFun x := pointEquiv.symm (fun j => F8Scalar.traceDual (x j))
  left_inv x := by
    apply pointEquiv.injective
    change pointEquiv (pointEquiv.symm (fun j => F8Scalar.traceDual (covectorLinear x j))) =
      pointEquiv x
    rw [pointEquiv.apply_symm_apply]
    funext j
    exact traceDual_involution (pointEquiv x j)
  right_inv x := by
    change (fun j => F8Scalar.traceDual
      (pointEquiv (pointEquiv.symm (fun k => F8Scalar.traceDual (x k))) j)) = x
    rw [pointEquiv.apply_symm_apply]
    funext j
    exact traceDual_involution (x j)

theorem covector_basis : ∀ i : Fin 9,
    covectorLinear (Pi.single i 1) = FieldData.basisCovector i := by native_decide

end Lemmata.RM59.FieldCoordinates
