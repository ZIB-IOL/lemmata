module

public import Lemmata.CocubicCovering.Compute.Linear
public meta import Lemmata.CocubicCovering.Compute.Linear
public import Lemmata.CocubicCovering.Proof.Coordinates
public meta import Lemmata.CocubicCovering.Proof.Coordinates
public import Lemmata.CocubicCovering.Proof.PackedPair
public meta import Lemmata.CocubicCovering.Proof.PackedPair
public import Lemmata.CocubicCovering.Proof.LevelSixReconstruction
public meta import Lemmata.CocubicCovering.Proof.LevelSixReconstruction

@[expose] public section

namespace Lemmata.CocubicCovering.CoveringLevelSixSystems

open CoveringQuotient CoveringCoordinates CoveringPackedPair CoveringPolynomial
open CoveringLevelSixReconstruction

def rankData0 : Nat := 0xa

def rankData1 : Nat := 0xa

def rankData2 : Nat := 0xa

def rankData3 : Nat := 0x8

def rankData4 : Nat := 0xa

def rankData5 : Nat := 0x8

def rankData6 : Nat := 0xa

def rankData7 : Nat := 0x8

def rankData8 : Nat := 0x8

def rankData9 : Nat := 0x6

def rankData10 : Nat := 0x6

def rankData11 : Nat := 0x0

def rankData12 : Nat := 0x0

def rankData : List Nat := [
  rankData0,
  rankData1,
  rankData2,
  rankData3,
  rankData4,
  rankData5,
  rankData6,
  rankData7,
  rankData8,
  rankData9,
  rankData10,
  rankData11,
  rankData12
]

def crossRankData0 : Nat := 0x0

def crossRankData1 : Nat := 0x0

def crossRankData2 : Nat := 0x0

def crossRankData3 : Nat := 0x1

def crossRankData4 : Nat := 0x0

def crossRankData5 : Nat := 0x1

def crossRankData6 : Nat := 0x0

def crossRankData7 : Nat := 0x1

def crossRankData8 : Nat := 0x1

def crossRankData9 : Nat := 0x2

def crossRankData10 : Nat := 0x2

def crossRankData11 : Nat := 0x5

def crossRankData12 : Nat := 0x5

def crossRankData : List Nat := [
  crossRankData0,
  crossRankData1,
  crossRankData2,
  crossRankData3,
  crossRankData4,
  crossRankData5,
  crossRankData6,
  crossRankData7,
  crossRankData8,
  crossRankData9,
  crossRankData10,
  crossRankData11,
  crossRankData12
]

def inverseData0 : List Nat := [0x40, 0x8, 0x200, 0x2, 0x100, 0x280, 0x1, 0x220, 0x210, 0x1a4]

def inverseData1 : List Nat := [0x342, 0xad, 0x322, 0x2, 0x200, 0x106, 0x1, 0x302, 0xa5, 0x95]

def inverseData2 : List Nat := [0x70, 0x338, 0x20, 0x2, 0x2a3, 0x297, 0x1, 0x30, 0x202, 0x132]

def inverseData3 : List Nat := [0xa2, 0x59, 0x40, 0x2, 0x82, 0x1, 0x86, 0x51]

def inverseData4 : List Nat := [0x170, 0x3a8, 0x80, 0x2, 0x201, 0x303, 0x1, 0x106, 0xa3, 0x32]

def inverseData5 : List Nat := [0xe4, 0x8, 0x21, 0x2, 0xa0, 0x95, 0x1, 0x31]

def inverseData6 : List Nat := [0x254, 0x8, 0x21, 0x2, 0x321, 0x314, 0x1, 0x100, 0x2b0, 0x131]

def inverseData7 : List Nat := [0xe4, 0x8, 0x21, 0x2, 0xa0, 0x95, 0x1, 0x31]

def inverseData8 : List Nat := [0xe4, 0x8, 0x21, 0x2, 0xa0, 0x95, 0x1, 0x31]

def inverseData9 : List Nat := [0x20, 0x8, 0x10, 0x2, 0x4, 0x1]

def inverseData10 : List Nat := [0x20, 0x8, 0x10, 0x2, 0x4, 0x1]

def inverseData11 : List Nat := []

def inverseData12 : List Nat := []

def inverseData : List (List Nat) := [
  inverseData0,
  inverseData1,
  inverseData2,
  inverseData3,
  inverseData4,
  inverseData5,
  inverseData6,
  inverseData7,
  inverseData8,
  inverseData9,
  inverseData10,
  inverseData11,
  inverseData12
]

def crossBasisData0 : List Nat := [0x1, 0x2, 0x4, 0x8, 0x10, 0x20, 0x200, 0x400, 0x800, 0x20000]

def crossBasisData1 : List Nat := [0x1, 0x2, 0x4, 0x8, 0x10, 0x20, 0x200, 0x400, 0x800, 0x10000]

def crossBasisData2 : List Nat := [0x1, 0x2, 0x4, 0x8, 0x10, 0x20, 0x200, 0x400, 0x800, 0x10000]

def crossBasisData3 : List Nat := [0x1, 0x2, 0x4, 0x8, 0x10, 0x200, 0x400, 0x800, 0x20a02]

def crossBasisData4 : List Nat := [0x1, 0x2, 0x4, 0x8, 0x10, 0x20, 0x200, 0x400, 0x800, 0x8000]

def crossBasisData5 : List Nat := [0x1, 0x2, 0x4, 0x8, 0x10, 0x20, 0x200, 0x400, 0x10021]

def crossBasisData6 : List Nat := [0x1, 0x2, 0x4, 0x8, 0x10, 0x20, 0x200, 0x400, 0x800, 0x10000]

def crossBasisData7 : List Nat := [0x1, 0x2, 0x4, 0x8, 0x10, 0x20, 0x200, 0x400, 0x831]

def crossBasisData8 : List Nat := [0x1, 0x2, 0x4, 0x8, 0x10, 0x20, 0x200, 0x400, 0x831]

def crossBasisData9 : List Nat := [0x1, 0x2, 0x4, 0x8, 0x10, 0x200, 0x10021, 0x802]

def crossBasisData10 : List Nat := [0x1, 0x2, 0x4, 0x8, 0x10, 0x200, 0x10021, 0x802]

def crossBasisData11 : List Nat := [0x1, 0x2, 0x4, 0x8, 0x20]

def crossBasisData12 : List Nat := [0x1, 0x4, 0x8, 0x10, 0x800]

def crossBasisData : List (List Nat) := [
  crossBasisData0,
  crossBasisData1,
  crossBasisData2,
  crossBasisData3,
  crossBasisData4,
  crossBasisData5,
  crossBasisData6,
  crossBasisData7,
  crossBasisData8,
  crossBasisData9,
  crossBasisData10,
  crossBasisData11,
  crossBasisData12
]

def outsideBasisData0 : List Nat := [0x40, 0x80, 0x100, 0x1000, 0x2000, 0x4000, 0x40000, 0x80000, 0x100000, 0x200000, 0x400000, 0x800000, 0x1000000, 0x2000000, 0x4000000]

def outsideBasisData1 : List Nat := [0x40, 0x80, 0x100, 0x1000, 0x2000, 0x4000, 0x40000, 0x80000, 0x100000, 0x200000, 0x400000, 0x800000, 0x1000000, 0x2000000, 0x4000000]

def outsideBasisData2 : List Nat := [0x40, 0x80, 0x100, 0x1000, 0x2000, 0x4000, 0x40000, 0x80000, 0x100000, 0x200000, 0x400000, 0x800000, 0x1000000, 0x2000000, 0x4000000]

def outsideBasisData3 : List Nat := [0x40, 0x80, 0x100, 0x1000, 0x2000, 0x4000, 0x40000, 0x80000, 0x100000, 0x200000, 0x400000, 0x800000, 0x1000000, 0x2000000, 0x4000000]

def outsideBasisData4 : List Nat := [0x40, 0x80, 0x100, 0x1000, 0x2000, 0x4000, 0x40000, 0x80000, 0x100000, 0x200000, 0x400000, 0x800000, 0x1000000, 0x2000000, 0x4000000]

def outsideBasisData5 : List Nat := [0x40, 0x80, 0x100, 0x1000, 0x2000, 0x4000, 0x40000, 0x80000, 0x100000, 0x200000, 0x400000, 0x800000, 0x1000000, 0x2000000, 0x4000000]

def outsideBasisData6 : List Nat := [0x40, 0x80, 0x100, 0x1000, 0x2000, 0x4000, 0x40000, 0x80000, 0x100000, 0x200000, 0x400000, 0x800000, 0x1000000, 0x2000000, 0x4000000]

def outsideBasisData7 : List Nat := [0x40, 0x80, 0x100, 0x1000, 0x2000, 0x4000, 0x40000, 0x80000, 0x100000, 0x200000, 0x400000, 0x800000, 0x1000000, 0x2000000, 0x4000000]

def outsideBasisData8 : List Nat := [0x40, 0x80, 0x100, 0x1000, 0x2000, 0x4000, 0x40000, 0x80000, 0x100000, 0x200000, 0x400000, 0x800000, 0x1000000, 0x2000000, 0x4000000]

def outsideBasisData9 : List Nat := [0x40, 0x80, 0x100, 0x1000, 0x2000, 0x4000, 0x40000, 0x80000, 0x100000, 0x200000, 0x400000, 0x800000, 0x1000000, 0x2000000, 0x4000000]

def outsideBasisData10 : List Nat := [0x40, 0x80, 0x100, 0x1000, 0x2000, 0x4000, 0x40000, 0x80000, 0x100000, 0x200000, 0x400000, 0x800000, 0x1000000, 0x2000000, 0x4000000]

def outsideBasisData11 : List Nat := [0x40, 0x80, 0x100, 0x1000, 0x2000, 0x4000, 0x40000, 0x80000, 0x100000, 0x200000, 0x400000, 0x800000, 0x1000000, 0x2000000, 0x4000000]

def outsideBasisData12 : List Nat := [0x40, 0x80, 0x100, 0x1000, 0x2000, 0x4000, 0x40000, 0x80000, 0x100000, 0x200000, 0x400000, 0x800000, 0x1000000, 0x2000000, 0x4000000]

def outsideBasisData : List (List Nat) := [
  outsideBasisData0,
  outsideBasisData1,
  outsideBasisData2,
  outsideBasisData3,
  outsideBasisData4,
  outsideBasisData5,
  outsideBasisData6,
  outsideBasisData7,
  outsideBasisData8,
  outsideBasisData9,
  outsideBasisData10,
  outsideBasisData11,
  outsideBasisData12
]

def pairData : List (Nat × Nat) := [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (0, 12), (0, 13), (0, 14), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (1, 12), (1, 13), (1, 14), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (2, 12), (2, 13), (2, 14), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (3, 12), (3, 13), (3, 14), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (4, 12), (4, 13), (4, 14), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (5, 12), (5, 13), (5, 14), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (6, 12), (6, 13), (6, 14), (7, 8), (7, 9), (7, 10), (7, 11), (7, 12), (7, 13), (7, 14), (8, 9), (8, 10), (8, 11), (8, 12), (8, 13), (8, 14), (9, 10), (9, 11), (9, 12), (9, 13), (9, 14), (10, 11), (10, 12), (10, 13), (10, 14), (11, 12), (11, 13), (11, 14), (12, 13), (12, 14), (13, 14)]


def localRank (s : Fin 13) : Nat := rankData[s.val]?.getD 0

def crossRank (s : Fin 13) : Nat := crossRankData[s.val]?.getD 0

def pairs (s : Fin 13) : Nat := (10 - localRank s) / 2

def inverse (s : Fin 13) (i j : Fin (localRank s)) : Bool :=
  ((inverseData[s.val]?.getD [])[i.val]?.getD 0).testBit j.val

def crossBasis (s : Fin 13) (i : Fin (localRank s + crossRank s)) : Nat :=
  (crossBasisData[s.val]?.getD [])[i.val]?.getD 0

def outsideBasis (s : Fin 13) (j : Fin 15) : Nat :=
  (outsideBasisData[s.val]?.getD [])[j.val]?.getD 0

def pairFirst (pair : Fin 105) : Fin 15 :=
  Fin.ofNat 15 (pairData[pair.val]?.getD (0, 0)).1

def pairSecond (pair : Fin 105) : Fin 15 :=
  Fin.ofNat 15 (pairData[pair.val]?.getD (0, 0)).2

def affineBits (s : Fin 13) (left right : Nat) : Nat :=
  (List.finRange (crossCount s)).foldl (fun bits y =>
    if pairBit (cross s y) left right then bits ||| 2 ^ (y.val + 1) else bits)
    (if pairBit (base s) left right then 1 else 0)

def crossAffineData : Array (Array (Array Nat)) :=
  Array.ofFn fun s : Fin 13 => Array.ofFn fun i : Fin (localRank s + crossRank s) =>
    Array.ofFn fun j : Fin 15 => affineBits s (crossBasis s i) (outsideBasis s j)

def outsideAffineData : Array (Array (Array Nat)) :=
  Array.ofFn fun s : Fin 13 => Array.ofFn fun i : Fin 15 =>
    Array.ofFn fun j : Fin 15 => affineBits s (outsideBasis s i) (outsideBasis s j)

def crossAffine (s : Fin 13) (i : Fin (localRank s + crossRank s)) (j : Fin 15) : Nat :=
  ((crossAffineData[s.val]?.getD #[])[i.val]?.getD #[])[j.val]?.getD 0

def outsideAffine (s : Fin 13) (i j : Fin 15) : Nat :=
  ((outsideAffineData[s.val]?.getD #[])[i.val]?.getD #[])[j.val]?.getD 0

def quotientBases : Array (Array Nat) :=
  Array.ofFn fun s : Fin 13 => Lemmata.CocubicCovering.Compute.Linear.nullspace 105
    (Array.ofFn fun k : Fin (outsideCount s) =>
      (List.finRange 105).foldl (fun bits pair =>
        if pairBit (outside s k) (outsideBasis s (pairFirst pair))
          (outsideBasis s (pairSecond pair)) then bits ||| 2 ^ pair.val else bits) 0)

def keep (s : Fin 13) (target : Fin 87) (pair : Fin 105) : Bool :=
  ((quotientBases[s.val]?.getD #[])[target.val]?.getD 0).testBit pair.val

theorem crossRank_le_pairs (s : Fin 13) : crossRank s ≤ pairs s := by
  fin_cases s <;> decide


def crossPolynomial (s : Fin 13) (i : Fin (localRank s + crossRank s))
    (j : Fin 15) : CoveringIdeal.Polynomial :=
  affinePolynomial ((crossAffine s i j).testBit 0)
    (fun y : Fin (crossCount s) => (crossAffine s i j).testBit (y.val + 1))

def outsidePolynomial (s : Fin 13) (i j : Fin 15) : CoveringIdeal.Polynomial :=
  affinePolynomial ((outsideAffine s i j).testBit 0)
    (fun y : Fin (crossCount s) => (outsideAffine s i j).testBit (y.val + 1))

def nativeX (s : Fin 13) : Fin 15 → Fin (pairs s) → CoveringIdeal.Polynomial :=
  xPolynomial (y := crossCount s) (crossRank_le_pairs s)

def nativeY (s : Fin 13) : Fin 15 → Fin (pairs s) → CoveringIdeal.Polynomial :=
  yPolynomial (y := crossCount s) (crossRank_le_pairs s)
    (fun i => crossPolynomial s (Fin.natAdd (localRank s) i))

def raw (s : Fin 13) (pair : Fin 105) : CoveringIdeal.Polynomial :=
  rawPolynomial (inverse s) (fun i => crossPolynomial s (Fin.castAdd (crossRank s) i))
    (outsidePolynomial s) (nativeX s) (nativeY s) (pairFirst pair) (pairSecond pair)

def canonical (s : Fin 13) (target : Fin 87) : CoveringIdeal.Polynomial :=
  quotientPolynomial (keep s) (raw s) target



def input (s : Fin 13) (row : Fin 87) : CoveringIdeal.Polynomial :=
  CoveringIdeal.normalize (canonical s row)

def AffineChecked (s : Fin 13) : Prop :=
  (∀ (i : Fin (localRank s + crossRank s)) (j : Fin 15),
    (crossAffine s i j).testBit 0 = pairBit (base s) (crossBasis s i) (outsideBasis s j)) ∧
  (∀ (i : Fin (localRank s + crossRank s)) (j : Fin 15) (y : Fin (crossCount s)),
    (crossAffine s i j).testBit (y.val + 1) =
      pairBit (cross s y) (crossBasis s i) (outsideBasis s j)) ∧
  (∀ i j : Fin 15,
    (outsideAffine s i j).testBit 0 = pairBit (base s) (outsideBasis s i) (outsideBasis s j)) ∧
  (∀ (i j : Fin 15) (y : Fin (crossCount s)),
    (outsideAffine s i j).testBit (y.val + 1) =
      pairBit (cross s y) (outsideBasis s i) (outsideBasis s j))

def OutsideChecked (s : Fin 13) : Prop :=
  (∀ (k : Fin (outsideCount s)) (i : Fin (localRank s + crossRank s)) (j : Fin 15),
    pairBit (outside s k) (crossBasis s i) (outsideBasis s j) = false) ∧
  (∀ (k : Fin (outsideCount s)) (target : Fin 87),
    (List.finRange 105).foldr
      (fun pair value => Bool.xor
        (if keep s target pair then
          pairBit (outside s k) (outsideBasis s (pairFirst pair))
            (outsideBasis s (pairSecond pair)) else false) value) false = false)



end Lemmata.CocubicCovering.CoveringLevelSixSystems
