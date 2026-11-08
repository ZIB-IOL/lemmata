module

public import Lemmata.RM59.Proof.Model
public meta import Lemmata.RM59.Proof.Model
public meta import Lean.Elab.Tactic.Decide

@[expose] public section

namespace Lemmata.RM59.Packed

open scoped BigOperators

abbrev PackedPoint := Fin 512

def bitField (b : Bool) : Field := if b then 1 else 0

@[simp] theorem bitField_false : bitField false = 0 := rfl

@[simp] theorem bitField_true : bitField true = 1 := rfl

theorem bitField_xor (a b : Bool) :
    bitField (Bool.xor a b) = bitField a + bitField b := by
  cases a <;> cases b <;> decide

theorem bitField_injective : Function.Injective bitField := by
  intro a b h
  cases a <;> cases b <;> simp_all [bitField]

def decodePoint (x : PackedPoint) : Point 9 :=
  fun i => bitField (x.val.testBit i.val)

def encodePoint (x : Point 9) : PackedPoint :=
  ⟨(∑ i : Fin 9, if x i = 1 then 2 ^ i.val else 0) % 512,
    Nat.mod_lt _ (by decide)⟩

theorem encodePoint_decodePoint : ∀ x : PackedPoint,
    encodePoint (decodePoint x) = x := by native_decide

theorem decodePoint_encodePoint : ∀ x : Point 9,
    decodePoint (encodePoint x) = x := by native_decide

def pointEquiv : PackedPoint ≃ Point 9 where
  toFun := decodePoint
  invFun := encodePoint
  left_inv := encodePoint_decodePoint
  right_inv := decodePoint_encodePoint

theorem decodePoint_injective : Function.Injective decodePoint :=
  pointEquiv.injective

def decodeMask (mask : PackedPoint) : Finset (Fin 9) :=
  Finset.univ.filter fun i => mask.val.testBit i.val

def encodeMask (s : Finset (Fin 9)) : PackedPoint :=
  ⟨(∑ i ∈ s, 2 ^ i.val) % 512, Nat.mod_lt _ (by decide)⟩

theorem encodeMask_decodeMask : ∀ mask : PackedPoint,
    encodeMask (decodeMask mask) = mask := by native_decide

theorem decodeMask_encodeMask : ∀ s : Finset (Fin 9),
    decodeMask (encodeMask s) = s := by native_decide

def maskEquiv : PackedPoint ≃ Finset (Fin 9) where
  toFun := decodeMask
  invFun := encodeMask
  left_inv := encodeMask_decodeMask
  right_inv := decodeMask_encodeMask

def bitCount (mask : Nat) : Nat :=
  (List.range 9).countP fun i => mask.testBit i

theorem decodeMask_card : ∀ mask : PackedPoint,
    (decodeMask mask).card = bitCount mask.val := by native_decide

theorem bitCount_encodeMask (s : Finset (Fin 9)) :
    bitCount (encodeMask s).val = s.card := by
  rw [← decodeMask_card, decodeMask_encodeMask]

theorem monomial_decode : ∀ x mask : PackedPoint,
    monomial (decodeMask mask) (decodePoint x) =
      bitField (Nat.land x.val mask.val == mask.val) := by native_decide

def packedMoment (word : List PackedPoint) (mask : Nat) : Bool :=
  word.foldl (fun value x => Bool.xor value (Nat.land x.val mask == mask)) false

def decodeWord (word : List PackedPoint) : Finset (Point 9) :=
  (word.map decodePoint).toFinset

private theorem bitField_foldl (word : List PackedPoint) (mask : Nat) (start : Bool) :
    bitField (word.foldl
      (fun value x => Bool.xor value (Nat.land x.val mask == mask)) start) =
      bitField start +
        (word.map fun x => bitField (Nat.land x.val mask == mask)).sum := by
  induction word generalizing start with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [ih, bitField_xor, add_assoc]

theorem bitField_packedMoment (word : List PackedPoint) (mask : Nat) :
    bitField (packedMoment word mask) =
      (word.map fun x => bitField (Nat.land x.val mask == mask)).sum := by
  simpa only [packedMoment, bitField_false, zero_add] using
    bitField_foldl word mask false

theorem decodeWord_card (word : List PackedPoint) (hword : word.Nodup) :
    (decodeWord word).card = word.length := by
  rw [decodeWord, List.toFinset_card_of_nodup
    (List.Nodup.map decodePoint_injective hword), List.length_map]

theorem packedMoment_decodeWord (word : List PackedPoint) (hword : word.Nodup)
    (mask : PackedPoint) :
    bitField (packedMoment word mask.val) =
      supportMoment (decodeWord word) (decodeMask mask) := by
  rw [bitField_packedMoment, supportMoment, decodeWord,
    List.sum_toFinset _ (List.Nodup.map decodePoint_injective hword)]
  simp only [List.map_map, Function.comp_def, monomial_decode]

theorem matchSupportMoments_of_packedMoments {d : Nat}
    (word word' : List PackedPoint) (hword : word.Nodup) (hword' : word'.Nodup)
    (h : ∀ mask : PackedPoint, bitCount mask.val ≤ d →
      packedMoment word mask.val = packedMoment word' mask.val) :
    MatchSupportMoments d (decodeWord word) (decodeWord word') := by
  intro s hs
  have heq := congrArg bitField (h (encodeMask s) (by
    rwa [bitCount_encodeMask]))
  simpa only [packedMoment_decodeWord word hword,
    packedMoment_decodeWord word' hword', decodeMask_encodeMask] using heq

theorem zero_supportMoments_of_packedMoments {d : Nat}
    (word : List PackedPoint) (hword : word.Nodup)
    (h : ∀ mask : PackedPoint, bitCount mask.val ≤ d →
      packedMoment word mask.val = false) :
    ∀ s, s.card ≤ d → supportMoment (decodeWord word) s = 0 := by
  intro s hs
  have heq := congrArg bitField (h (encodeMask s) (by
    rwa [bitCount_encodeMask]))
  simpa only [packedMoment_decodeWord word hword, decodeMask_encodeMask,
    bitField_false] using heq

end Lemmata.RM59.Packed
