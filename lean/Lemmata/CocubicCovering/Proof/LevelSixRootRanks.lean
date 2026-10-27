module

public import Lemmata.CocubicCovering.Proof.LevelSixCoreData
public meta import Lemmata.CocubicCovering.Proof.LevelSixCoreData
public import Lemmata.CocubicCovering.Proof.LevelSixReduction
public meta import Lemmata.CocubicCovering.Proof.LevelSixReduction

@[expose] public section

set_option Elab.async false

namespace Lemmata.CocubicCovering.CoveringLevelSixRootRanks

open Module CoveringBits CoveringAffine CoveringCongruence CoveringWitness
open CoveringRankWitness CoveringPackedWitness CoveringLocalRanks
open CoveringLevelSixCoreData (roots rootRank)

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def matrixRows0 (i : Fin 12) : Nat :=
  (#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0][i.val]?).getD 0

def matrix0 : Matrix (Fin 12) (Fin 12) Field :=
  rowMatrix matrixRows0

def minorIndices0 (i : Fin 0) : Fin 12 :=
  Fin.ofNat 12 ((#[][i.val]?).getD 0)

def inverseRows0 (i : Fin 0) : Nat :=
  (#[][i.val]?).getD 0

def radicalMasks0 : List Nat := [1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

def radical0 (i : Fin 12) : Vector 12 :=
  decodeMask (radicalMasks0.get i)

def radicalDual0 (i : Fin 12) : Nat :=
  (#[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048][i.val]?).getD 0

def matrixRows1 (i : Fin 12) : Nat :=
  (#[0, 0, 0, 0, 0, 0, 2048, 1024, 512, 256, 128, 64][i.val]?).getD 0

def matrix1 : Matrix (Fin 12) (Fin 12) Field :=
  rowMatrix matrixRows1

def minorIndices1 (i : Fin 6) : Fin 12 :=
  Fin.ofNat 12 ((#[6, 7, 8, 9, 10, 11][i.val]?).getD 0)

def inverseRows1 (i : Fin 6) : Nat :=
  (#[32, 16, 8, 4, 2, 1][i.val]?).getD 0

def radicalMasks1 : List Nat := [1, 2, 4, 8, 16, 32]

def radical1 (i : Fin 6) : Vector 12 :=
  decodeMask (radicalMasks1.get i)

def radicalDual1 (i : Fin 6) : Nat :=
  (#[1, 2, 4, 8, 16, 32][i.val]?).getD 0

def matrixRows8 (i : Fin 12) : Nat :=
  (#[0, 0, 2048, 0, 256, 128, 0, 32, 16, 0, 0, 4][i.val]?).getD 0

def matrix8 : Matrix (Fin 12) (Fin 12) Field :=
  rowMatrix matrixRows8

def minorIndices8 (i : Fin 6) : Fin 12 :=
  Fin.ofNat 12 ((#[2, 4, 5, 7, 8, 11][i.val]?).getD 0)

def inverseRows8 (i : Fin 6) : Nat :=
  (#[32, 16, 8, 4, 2, 1][i.val]?).getD 0

def radicalMasks8 : List Nat := [1, 2, 8, 64, 512, 1024]

def radical8 (i : Fin 6) : Vector 12 :=
  decodeMask (radicalMasks8.get i)

def radicalDual8 (i : Fin 6) : Nat :=
  (#[1, 2, 8, 64, 512, 1024][i.val]?).getD 0

def matrixRows12 (i : Fin 12) : Nat :=
  (#[0, 0, 2048, 1024, 2816, 2176, 512, 2080, 1552, 336, 264, 180][i.val]?).getD 0

def matrix12 : Matrix (Fin 12) (Fin 12) Field :=
  rowMatrix matrixRows12

def minorIndices12 (i : Fin 10) : Fin 12 :=
  Fin.ofNat 12 ((#[2, 3, 4, 5, 6, 7, 8, 9, 10, 11][i.val]?).getD 0)

def inverseRows12 (i : Fin 10) : Nat :=
  (#[634, 277, 82, 33, 199, 9, 21, 16, 2, 1][i.val]?).getD 0

def radicalMasks12 : List Nat := [1, 2]

def radical12 (i : Fin 2) : Vector 12 :=
  decodeMask (radicalMasks12.get i)

def radicalDual12 (i : Fin 2) : Nat :=
  (#[1, 2][i.val]?).getD 0

def matrixRows80 (i : Fin 12) : Nat :=
  (#[0, 2048, 1024, 0, 128, 64, 160, 336, 128, 0, 4, 2][i.val]?).getD 0

def matrix80 : Matrix (Fin 12) (Fin 12) Field :=
  rowMatrix matrixRows80

def minorIndices80 (i : Fin 8) : Fin 12 :=
  Fin.ofNat 12 ((#[1, 2, 4, 5, 6, 7, 10, 11][i.val]?).getD 0)

def inverseRows80 (i : Fin 8) : Nat :=
  (#[128, 64, 40, 20, 8, 4, 2, 1][i.val]?).getD 0

def radicalMasks80 : List Nat := [1, 8, 272, 512]

def radical80 (i : Fin 4) : Vector 12 :=
  decodeMask (radicalMasks80.get i)

def radicalDual80 (i : Fin 4) : Nat :=
  (#[1, 8, 16, 512][i.val]?).getD 0

def matrixRows81 (i : Fin 12) : Nat :=
  (#[0, 2048, 1024, 0, 128, 64, 2208, 1360, 640, 256, 132, 66][i.val]?).getD 0

def matrix81 : Matrix (Fin 12) (Fin 12) Field :=
  rowMatrix matrixRows81

def minorIndices81 (i : Fin 10) : Fin 12 :=
  Fin.ofNat 12 ((#[1, 2, 4, 5, 6, 7, 8, 9, 10, 11][i.val]?).getD 0)

def inverseRows81 (i : Fin 10) : Nat :=
  (#[520, 260, 170, 21, 8, 4, 128, 68, 2, 1][i.val]?).getD 0

def radicalMasks81 : List Nat := [1, 8]

def radical81 (i : Fin 2) : Vector 12 :=
  decodeMask (radicalMasks81.get i)

def radicalDual81 (i : Fin 2) : Nat :=
  (#[1, 8][i.val]?).getD 0

def matrixRows88 (i : Fin 12) : Nat :=
  (#[0, 2048, 3072, 0, 384, 192, 160, 368, 144, 0, 4, 6][i.val]?).getD 0

def matrix88 : Matrix (Fin 12) (Fin 12) Field :=
  rowMatrix matrixRows88

def minorIndices88 (i : Fin 8) : Fin 12 :=
  Fin.ofNat 12 ((#[1, 2, 4, 5, 6, 7, 10, 11][i.val]?).getD 0)

def inverseRows88 (i : Fin 8) : Nat :=
  (#[192, 64, 56, 20, 12, 4, 3, 1][i.val]?).getD 0

def radicalMasks88 : List Nat := [1, 8, 496, 512]

def radical88 (i : Fin 4) : Vector 12 :=
  decodeMask (radicalMasks88.get i)

def radicalDual88 (i : Fin 4) : Nat :=
  (#[1, 8, 16, 512][i.val]?).getD 0

def matrixRows89 (i : Fin 12) : Nat :=
  (#[0, 2048, 3072, 0, 384, 192, 2208, 1392, 656, 256, 132, 70][i.val]?).getD 0

def matrix89 : Matrix (Fin 12) (Fin 12) Field :=
  rowMatrix matrixRows89

def minorIndices89 (i : Fin 10) : Fin 12 :=
  Fin.ofNat 12 ((#[1, 2, 4, 5, 6, 7, 8, 9, 10, 11][i.val]?).getD 0)

def inverseRows89 (i : Fin 10) : Nat :=
  (#[776, 388, 186, 149, 140, 132, 128, 126, 3, 1][i.val]?).getD 0

def radicalMasks89 : List Nat := [1, 8]

def radical89 (i : Fin 2) : Vector 12 :=
  decodeMask (radicalMasks89.get i)

def radicalDual89 (i : Fin 2) : Nat :=
  (#[1, 8][i.val]?).getD 0

def matrixRows104 (i : Fin 12) : Nat :=
  (#[2048, 0, 3072, 288, 64, 456, 48, 32, 40, 0, 4, 5][i.val]?).getD 0

def matrix104 : Matrix (Fin 12) (Fin 12) Field :=
  rowMatrix matrixRows104

def minorIndices104 (i : Fin 10) : Fin 12 :=
  Fin.ofNat 12 ((#[0, 2, 3, 4, 5, 6, 7, 8, 10, 11][i.val]?).getD 0)

def inverseRows104 (i : Fin 10) : Nat :=
  (#[768, 256, 192, 96, 64, 8, 156, 68, 3, 1][i.val]?).getD 0

def radicalMasks104 : List Nat := [2, 512]

def radical104 (i : Fin 2) : Vector 12 :=
  decodeMask (radicalMasks104.get i)

def radicalDual104 (i : Fin 2) : Nat :=
  (#[2, 512][i.val]?).getD 0

def matrixRows522 (i : Fin 12) : Nat :=
  (#[256, 32, 2384, 2048, 1284, 642, 4, 32, 21, 32, 16, 12][i.val]?).getD 0

def matrix522 : Matrix (Fin 12) (Fin 12) Field :=
  rowMatrix matrixRows522

def minorIndices522 (i : Fin 10) : Fin 12 :=
  Fin.ofNat 12 ((#[0, 1, 2, 3, 4, 5, 6, 8, 10, 11][i.val]?).getD 0)

def inverseRows522 (i : Fin 10) : Nat :=
  (#[448, 32, 64, 576, 256, 2, 269, 1, 81, 8][i.val]?).getD 0

def radicalMasks522 : List Nat := [514, 640]

def radical522 (i : Fin 2) : Vector 12 :=
  decodeMask (radicalMasks522.get i)

def radicalDual522 (i : Fin 2) : Nat :=
  (#[2, 128][i.val]?).getD 0

def matrixRows1400 (i : Fin 12) : Nat :=
  (#[3072, 2048, 3584, 496, 168, 344, 168, 344, 168, 4, 5, 7][i.val]?).getD 0

def matrix1400 : Matrix (Fin 12) (Fin 12) Field :=
  rowMatrix matrixRows1400

def minorIndices1400 (i : Fin 8) : Fin 12 :=
  Fin.ofNat 12 ((#[0, 1, 2, 3, 4, 9, 10, 11][i.val]?).getD 0)

def inverseRows1400 (i : Fin 8) : Nat :=
  (#[96, 192, 32, 16, 8, 5, 3, 2][i.val]?).getD 0

def radicalMasks1400 : List Nat := [392, 272, 160, 320]

def radical1400 (i : Fin 4) : Vector 12 :=
  decodeMask (radicalMasks1400.get i)

def radicalDual1400 (i : Fin 4) : Nat :=
  (#[8, 16, 32, 64][i.val]?).getD 0

def matrixRows1550 (i : Fin 12) : Nat :=
  (#[256, 32, 2896, 3200, 3908, 2690, 532, 2088, 1557, 372, 280, 188][i.val]?).getD 0

def matrix1550 : Matrix (Fin 12) (Fin 12) Field :=
  rowMatrix matrixRows1550

def minorIndices1550 (i : Fin 10) : Fin 12 :=
  Fin.ofNat 12 ((#[0, 1, 2, 3, 4, 5, 6, 7, 8, 9][i.val]?).getD 0)

def inverseRows1550 (i : Fin 10) : Nat :=
  (#[320, 124, 594, 130, 582, 2, 535, 8, 1, 84][i.val]?).getD 0

def radicalMasks1550 : List Nat := [3673, 2204]

def radical1550 (i : Fin 2) : Vector 12 :=
  decodeMask (radicalMasks1550.get i)

def radicalDual1550 (i : Fin 2) : Nat :=
  (#[1, 4][i.val]?).getD 0

def matrixRows1573 (i : Fin 12) : Nat :=
  (#[2304, 32, 848, 1184, 2820, 2314, 2564, 3080, 1077, 84, 392, 241][i.val]?).getD 0

def matrix1573 : Matrix (Fin 12) (Fin 12) Field :=
  rowMatrix matrixRows1573

def minorIndices1573 (i : Fin 10) : Fin 12 :=
  Fin.ofNat 12 ((#[0, 1, 2, 3, 4, 5, 6, 7, 8, 11][i.val]?).getD 0)

def inverseRows1573 (i : Fin 10) : Nat :=
  (#[604, 240, 17, 209, 847, 2, 795, 10, 80, 81][i.val]?).getD 0

def radicalMasks1573 : List Nat := [581, 1742]

def radical1573 (i : Fin 2) : Vector 12 :=
  decodeMask (radicalMasks1573.get i)

def radicalDual1573 (i : Fin 2) : Nat :=
  (#[1, 2][i.val]?).getD 0

def matrixRows1580 (i : Fin 12) : Nat :=
  (#[2304, 32, 2896, 1184, 2564, 2442, 516, 2088, 1573, 340, 264, 181][i.val]?).getD 0

def matrix1580 : Matrix (Fin 12) (Fin 12) Field :=
  rowMatrix matrixRows1580

def minorIndices1580 (i : Fin 10) : Fin 12 :=
  Fin.ofNat 12 ((#[0, 1, 2, 3, 4, 5, 6, 7, 8, 11][i.val]?).getD 0)

def inverseRows1580 (i : Fin 10) : Nat :=
  (#[322, 249, 64, 210, 778, 2, 783, 10, 81, 80][i.val]?).getD 0

def radicalMasks1580 : List Nat := [1155, 532]

def radical1580 (i : Fin 2) : Vector 12 :=
  decodeMask (radicalMasks1580.get i)

def radicalDual1580 (i : Fin 2) : Nat :=
  (#[1, 4][i.val]?).getD 0

def matrixRows16392 (i : Fin 12) : Nat :=
  (#[64, 8, 2224, 2, 260, 132, 1, 36, 16, 0, 0, 4][i.val]?).getD 0

def matrix16392 : Matrix (Fin 12) (Fin 12) Field :=
  rowMatrix matrixRows16392

def minorIndices16392 (i : Fin 10) : Fin 12 :=
  Fin.ofNat 12 ((#[0, 1, 2, 3, 4, 5, 6, 7, 8, 11][i.val]?).getD 0)

def inverseRows16392 (i : Fin 10) : Nat :=
  (#[64, 8, 512, 2, 256, 640, 1, 544, 528, 420][i.val]?).getD 0

def radicalMasks16392 : List Nat := [512, 1024]

def radical16392 (i : Fin 2) : Vector 12 :=
  decodeMask (radicalMasks16392.get i)

def radicalDual16392 (i : Fin 2) : Nat :=
  (#[512, 1024][i.val]?).getD 0

def matrixRows16410 (i : Fin 12) : Nat :=
  (#[64, 2056, 2224, 2306, 1412, 644, 129, 372, 152, 32, 16, 14][i.val]?).getD 0

def matrix16410 : Matrix (Fin 12) (Fin 12) Field :=
  rowMatrix matrixRows16410

def minorIndices16410 (i : Fin 10) : Fin 12 :=
  Fin.ofNat 12 ((#[0, 1, 2, 3, 4, 5, 6, 7, 8, 10][i.val]?).getD 0)

def inverseRows16410 (i : Fin 10) : Nat :=
  (#[834, 173, 802, 2, 512, 262, 1, 770, 165, 149][i.val]?).getD 0

def radicalMasks16410 : List Nat := [3469, 774]

def radical16410 (i : Fin 2) : Vector 12 :=
  decodeMask (radicalMasks16410.get i)

def radicalDual16410 (i : Fin 2) : Nat :=
  (#[1, 2][i.val]?).getD 0

def matrixRows16404 (i : Fin 12) : Nat :=
  (#[64, 2056, 176, 1282, 2692, 2052, 641, 2388, 1672, 336, 264, 178][i.val]?).getD 0

def matrix16404 : Matrix (Fin 12) (Fin 12) Field :=
  rowMatrix matrixRows16404

def minorIndices16404 (i : Fin 10) : Fin 12 :=
  Fin.ofNat 12 ((#[0, 1, 2, 3, 4, 5, 6, 7, 8, 10][i.val]?).getD 0)

def inverseRows16404 (i : Fin 10) : Nat :=
  (#[112, 824, 32, 2, 675, 663, 1, 48, 514, 306][i.val]?).getD 0

def radicalMasks16404 : List Nat := [3996, 672]

def radical16404 (i : Fin 2) : Vector 12 :=
  decodeMask (radicalMasks16404.get i)

def radicalDual16404 (i : Fin 2) : Nat :=
  (#[4, 32][i.val]?).getD 0

def matrixRows16480 (i : Fin 12) : Nat :=
  (#[2112, 8, 1200, 290, 324, 332, 49, 4, 56, 0, 4, 1][i.val]?).getD 0

def matrix16480 : Matrix (Fin 12) (Fin 12) Field :=
  rowMatrix matrixRows16480

def minorIndices16480 (i : Fin 8) : Fin 12 :=
  Fin.ofNat 12 ((#[0, 1, 2, 3, 4, 6, 7, 8][i.val]?).getD 0)

def inverseRows16480 (i : Fin 8) : Nat :=
  (#[162, 89, 64, 2, 130, 1, 134, 81][i.val]?).getD 0

def radicalMasks16480 : List Nat := [2370, 2416, 1152, 512]

def radical16480 (i : Fin 4) : Vector 12 :=
  decodeMask (radicalMasks16480.get i)

def radicalDual16480 (i : Fin 4) : Nat :=
  (#[2, 16, 128, 512][i.val]?).getD 0

def matrixRows16485 (i : Fin 12) : Nat :=
  (#[2112, 8, 1200, 1314, 2884, 2380, 2609, 3076, 1080, 80, 396, 241][i.val]?).getD 0

def matrix16485 : Matrix (Fin 12) (Fin 12) Field :=
  rowMatrix matrixRows16485

def minorIndices16485 (i : Fin 10) : Fin 12 :=
  Fin.ofNat 12 ((#[0, 1, 2, 3, 4, 5, 6, 7, 8, 9][i.val]?).getD 0)

def inverseRows16485 (i : Fin 10) : Nat :=
  (#[368, 936, 128, 2, 513, 771, 1, 262, 163, 50][i.val]?).getD 0

def radicalMasks16485 : List Nat := [2421, 3154]

def radical16485 (i : Fin 2) : Vector 12 :=
  decodeMask (radicalMasks16485.get i)

def radicalDual16485 (i : Fin 2) : Nat :=
  (#[1, 2][i.val]?).getD 0

def matrixRows16464 (i : Fin 12) : Nat :=
  (#[64, 2056, 1200, 2, 132, 68, 161, 340, 128, 0, 4, 2][i.val]?).getD 0

def matrix16464 : Matrix (Fin 12) (Fin 12) Field :=
  rowMatrix matrixRows16464

def minorIndices16464 (i : Fin 8) : Fin 12 :=
  Fin.ofNat 12 ((#[0, 1, 2, 3, 4, 5, 6, 7][i.val]?).getD 0)

def inverseRows16464 (i : Fin 8) : Nat :=
  (#[228, 8, 33, 2, 160, 149, 1, 49][i.val]?).getD 0

def radicalMasks16464 : List Nat := [1057, 2056, 1296, 512]

def radical16464 (i : Fin 4) : Vector 12 :=
  decodeMask (radicalMasks16464.get i)

def radicalDual16464 (i : Fin 4) : Nat :=
  (#[1, 8, 16, 512][i.val]?).getD 0

def matrixRows16467 (i : Fin 12) : Nat :=
  (#[64, 2056, 1200, 2050, 1156, 580, 2209, 1364, 640, 288, 148, 74][i.val]?).getD 0

def matrix16467 : Matrix (Fin 12) (Fin 12) Field :=
  rowMatrix matrixRows16467

def minorIndices16467 (i : Fin 10) : Fin 12 :=
  Fin.ofNat 12 ((#[0, 1, 2, 3, 4, 5, 6, 7, 8, 10][i.val]?).getD 0)

def inverseRows16467 (i : Fin 10) : Nat :=
  (#[596, 8, 33, 2, 801, 788, 1, 256, 688, 305][i.val]?).getD 0

def radicalMasks16467 : List Nat := [2059, 932]

def radical16467 (i : Fin 2) : Vector 12 :=
  decodeMask (radicalMasks16467.get i)

def radicalDual16467 (i : Fin 2) : Nat :=
  (#[1, 4][i.val]?).getD 0

def matrixRows16471 (i : Fin 12) : Nat :=
  (#[64, 2056, 1200, 3074, 3716, 2628, 2721, 3412, 1152, 112, 412, 250][i.val]?).getD 0

def matrix16471 : Matrix (Fin 12) (Fin 12) Field :=
  rowMatrix matrixRows16471

def minorIndices16471 (i : Fin 8) : Fin 12 :=
  Fin.ofNat 12 ((#[0, 1, 2, 3, 4, 5, 6, 7][i.val]?).getD 0)

def inverseRows16471 (i : Fin 8) : Nat :=
  (#[228, 8, 33, 2, 160, 149, 1, 49][i.val]?).getD 0

def radicalMasks16471 : List Nat := [305, 1202, 564, 4024]

def radical16471 (i : Fin 4) : Vector 12 :=
  decodeMask (radicalMasks16471.get i)

def radicalDual16471 (i : Fin 4) : Nat :=
  (#[1, 2, 4, 8][i.val]?).getD 0

def matrixRows16448 (i : Fin 12) : Nat :=
  (#[64, 8, 1200, 258, 4, 68, 33, 4, 8, 0, 4, 0][i.val]?).getD 0

def matrix16448 : Matrix (Fin 12) (Fin 12) Field :=
  rowMatrix matrixRows16448

def minorIndices16448 (i : Fin 6) : Fin 12 :=
  Fin.ofNat 12 ((#[0, 1, 2, 3, 4, 6][i.val]?).getD 0)

def inverseRows16448 (i : Fin 6) : Nat :=
  (#[32, 8, 16, 2, 4, 1][i.val]?).getD 0

def radicalMasks16448 : List Nat := [1057, 258, 1040, 1152, 512, 2048]

def radical16448 (i : Fin 6) : Vector 12 :=
  decodeMask (radicalMasks16448.get i)

def radicalDual16448 (i : Fin 6) : Nat :=
  (#[1, 2, 16, 128, 512, 2048][i.val]?).getD 0

structure RootCertificate where
  root : Nat
  minorSize : Nat
  radicalSize : Nat
  matrix : Matrix (Fin 12) (Fin 12) Field
  minorIndices : Fin minorSize → Fin 12
  inverseRows : Fin minorSize → Nat
  radical : Fin radicalSize → Vector 12
  radicalDual : Fin radicalSize → Nat

def RootCertificate.Valid (c : RootCertificate) : Prop :=
  c.matrix = rootMatrix c.root ∧
    (rowMatrix c.inverseRows : Matrix (Fin c.minorSize) (Fin c.minorSize) Field) *
      c.matrix.submatrix c.minorIndices c.minorIndices = 1 ∧
    ((∀ i, rowMap c.radicalDual (c.radical i) = Pi.single i 1) ∧
      (∀ i, c.matrix.mulVecLin (c.radical i) = 0)) ∧
    c.matrix.transpose = c.matrix

def rootCertificateDecision (c : RootCertificate) : Decidable c.Valid := by
  unfold RootCertificate.Valid
  infer_instance

@[noinline, never_extract]
def rootCertificateCheck (c : RootCertificate) : Bool :=
  @decide c.Valid (rootCertificateDecision c)

theorem rootCertificateCheck_sound (c : RootCertificate)
    (computed : rootCertificateCheck c = true) : c.Valid := by
  unfold rootCertificateCheck at computed
  exact @of_decide_eq_true c.Valid (rootCertificateDecision c) computed

@[noinline, never_extract]
def rootCertificatesCheck (certificates : List RootCertificate) : Bool :=
  certificates.all rootCertificateCheck

def certificate0 : RootCertificate :=
  ⟨0, 0, 12, matrix0,
    minorIndices0, inverseRows0, radical0, radicalDual0⟩

def certificate1 : RootCertificate :=
  ⟨1, 6, 6, matrix1,
    minorIndices1, inverseRows1, radical1, radicalDual1⟩

def certificate8 : RootCertificate :=
  ⟨8, 6, 6, matrix8,
    minorIndices8, inverseRows8, radical8, radicalDual8⟩

def certificate12 : RootCertificate :=
  ⟨12, 10, 2, matrix12,
    minorIndices12, inverseRows12, radical12, radicalDual12⟩

def certificate80 : RootCertificate :=
  ⟨80, 8, 4, matrix80,
    minorIndices80, inverseRows80, radical80, radicalDual80⟩

def certificate81 : RootCertificate :=
  ⟨81, 10, 2, matrix81,
    minorIndices81, inverseRows81, radical81, radicalDual81⟩

def certificate88 : RootCertificate :=
  ⟨88, 8, 4, matrix88,
    minorIndices88, inverseRows88, radical88, radicalDual88⟩

def certificate89 : RootCertificate :=
  ⟨89, 10, 2, matrix89,
    minorIndices89, inverseRows89, radical89, radicalDual89⟩

def certificate104 : RootCertificate :=
  ⟨104, 10, 2, matrix104,
    minorIndices104, inverseRows104, radical104, radicalDual104⟩

def certificate522 : RootCertificate :=
  ⟨522, 10, 2, matrix522,
    minorIndices522, inverseRows522, radical522, radicalDual522⟩

def certificate1400 : RootCertificate :=
  ⟨1400, 8, 4, matrix1400,
    minorIndices1400, inverseRows1400, radical1400, radicalDual1400⟩

def certificate1550 : RootCertificate :=
  ⟨1550, 10, 2, matrix1550,
    minorIndices1550, inverseRows1550, radical1550, radicalDual1550⟩

def certificate1573 : RootCertificate :=
  ⟨1573, 10, 2, matrix1573,
    minorIndices1573, inverseRows1573, radical1573, radicalDual1573⟩

def certificate1580 : RootCertificate :=
  ⟨1580, 10, 2, matrix1580,
    minorIndices1580, inverseRows1580, radical1580, radicalDual1580⟩

def certificate16392 : RootCertificate :=
  ⟨16392, 10, 2, matrix16392,
    minorIndices16392, inverseRows16392, radical16392, radicalDual16392⟩

def certificate16410 : RootCertificate :=
  ⟨16410, 10, 2, matrix16410,
    minorIndices16410, inverseRows16410, radical16410, radicalDual16410⟩

def certificate16404 : RootCertificate :=
  ⟨16404, 10, 2, matrix16404,
    minorIndices16404, inverseRows16404, radical16404, radicalDual16404⟩

def certificate16480 : RootCertificate :=
  ⟨16480, 8, 4, matrix16480,
    minorIndices16480, inverseRows16480, radical16480, radicalDual16480⟩

def certificate16485 : RootCertificate :=
  ⟨16485, 10, 2, matrix16485,
    minorIndices16485, inverseRows16485, radical16485, radicalDual16485⟩

def certificate16464 : RootCertificate :=
  ⟨16464, 8, 4, matrix16464,
    minorIndices16464, inverseRows16464, radical16464, radicalDual16464⟩

def certificate16467 : RootCertificate :=
  ⟨16467, 10, 2, matrix16467,
    minorIndices16467, inverseRows16467, radical16467, radicalDual16467⟩

def certificate16471 : RootCertificate :=
  ⟨16471, 8, 4, matrix16471,
    minorIndices16471, inverseRows16471, radical16471, radicalDual16471⟩

def certificate16448 : RootCertificate :=
  ⟨16448, 6, 6, matrix16448,
    minorIndices16448, inverseRows16448, radical16448, radicalDual16448⟩

def certificates : List RootCertificate :=
  [certificate0, certificate1, certificate8, certificate12, certificate80, certificate81, certificate88, certificate89, certificate104, certificate522, certificate1400, certificate1550, certificate1573, certificate1580, certificate16392, certificate16410, certificate16404, certificate16480, certificate16485, certificate16464, certificate16467, certificate16471, certificate16448]

private theorem certificatesChecked : rootCertificatesCheck certificates = true := by
  native_decide

private theorem certificate_valid (c : RootCertificate) (member : c ∈ certificates) : c.Valid := by
  have checked : rootCertificateCheck c = true :=
    (List.all_eq_true.mp certificatesChecked) c member
  exact rootCertificateCheck_sound c checked

private theorem certificate0_valid : certificate0.Valid :=
  certificate_valid _ (List.mem_iff_get.mpr ⟨⟨0, by decide⟩, rfl⟩)

private theorem certificate1_valid : certificate1.Valid :=
  certificate_valid _ (List.mem_iff_get.mpr ⟨⟨1, by decide⟩, rfl⟩)

private theorem certificate8_valid : certificate8.Valid :=
  certificate_valid _ (List.mem_iff_get.mpr ⟨⟨2, by decide⟩, rfl⟩)

private theorem certificate12_valid : certificate12.Valid :=
  certificate_valid _ (List.mem_iff_get.mpr ⟨⟨3, by decide⟩, rfl⟩)

private theorem certificate80_valid : certificate80.Valid :=
  certificate_valid _ (List.mem_iff_get.mpr ⟨⟨4, by decide⟩, rfl⟩)

private theorem certificate81_valid : certificate81.Valid :=
  certificate_valid _ (List.mem_iff_get.mpr ⟨⟨5, by decide⟩, rfl⟩)

private theorem certificate88_valid : certificate88.Valid :=
  certificate_valid _ (List.mem_iff_get.mpr ⟨⟨6, by decide⟩, rfl⟩)

private theorem certificate89_valid : certificate89.Valid :=
  certificate_valid _ (List.mem_iff_get.mpr ⟨⟨7, by decide⟩, rfl⟩)

private theorem certificate104_valid : certificate104.Valid :=
  certificate_valid _ (List.mem_iff_get.mpr ⟨⟨8, by decide⟩, rfl⟩)

private theorem certificate522_valid : certificate522.Valid :=
  certificate_valid _ (List.mem_iff_get.mpr ⟨⟨9, by decide⟩, rfl⟩)

private theorem certificate1400_valid : certificate1400.Valid :=
  certificate_valid _ (List.mem_iff_get.mpr ⟨⟨10, by decide⟩, rfl⟩)

private theorem certificate1550_valid : certificate1550.Valid :=
  certificate_valid _ (List.mem_iff_get.mpr ⟨⟨11, by decide⟩, rfl⟩)

private theorem certificate1573_valid : certificate1573.Valid :=
  certificate_valid _ (List.mem_iff_get.mpr ⟨⟨12, by decide⟩, rfl⟩)

private theorem certificate1580_valid : certificate1580.Valid :=
  certificate_valid _ (List.mem_iff_get.mpr ⟨⟨13, by decide⟩, rfl⟩)

private theorem certificate16392_valid : certificate16392.Valid :=
  certificate_valid _ (List.mem_iff_get.mpr ⟨⟨14, by decide⟩, rfl⟩)

private theorem certificate16410_valid : certificate16410.Valid :=
  certificate_valid _ (List.mem_iff_get.mpr ⟨⟨15, by decide⟩, rfl⟩)

private theorem certificate16404_valid : certificate16404.Valid :=
  certificate_valid _ (List.mem_iff_get.mpr ⟨⟨16, by decide⟩, rfl⟩)

private theorem certificate16480_valid : certificate16480.Valid :=
  certificate_valid _ (List.mem_iff_get.mpr ⟨⟨17, by decide⟩, rfl⟩)

private theorem certificate16485_valid : certificate16485.Valid :=
  certificate_valid _ (List.mem_iff_get.mpr ⟨⟨18, by decide⟩, rfl⟩)

private theorem certificate16464_valid : certificate16464.Valid :=
  certificate_valid _ (List.mem_iff_get.mpr ⟨⟨19, by decide⟩, rfl⟩)

private theorem certificate16467_valid : certificate16467.Valid :=
  certificate_valid _ (List.mem_iff_get.mpr ⟨⟨20, by decide⟩, rfl⟩)

private theorem certificate16471_valid : certificate16471.Valid :=
  certificate_valid _ (List.mem_iff_get.mpr ⟨⟨21, by decide⟩, rfl⟩)

private theorem certificate16448_valid : certificate16448.Valid :=
  certificate_valid _ (List.mem_iff_get.mpr ⟨⟨22, by decide⟩, rfl⟩)

private theorem matrix0_root : matrix0 = rootMatrix 0 := by
  exact certificate0_valid.1

private theorem minor0_checked :
    (rowMatrix inverseRows0 : Matrix (Fin 0) (Fin 0) Field) *
        matrix0.submatrix minorIndices0 minorIndices0 = 1 := by
  exact certificate0_valid.2.1

private theorem radical0_checked :
    (∀ i, rowMap radicalDual0 (radical0 i) = Pi.single i 1) ∧
      (∀ i, matrix0.mulVecLin (radical0 i) = 0) := by
  exact certificate0_valid.2.2.1

private theorem matrix0_rank : (rootMatrix 0).rank = 0 := by
  rw [← matrix0_root]
  exact matrix_rank_eq_of_minor_and_radical matrix0
    minorIndices0 minorIndices0 (rowMatrix inverseRows0)
    radical0 radicalDual0 (by decide) minor0_checked
    radical0_checked.1 radical0_checked.2

private theorem matrix0_kernel :
    LinearMap.ker (Matrix.toBilin' (rootMatrix 0)) =
      familySpan radical0 := by
  rw [← matrix0_root, toBilin_kernel]
  have hs : matrix0.transpose = matrix0 := certificate0_valid.2.2.2
  rw [hs]
  apply kernel_eq_familySpan matrix0.mulVecLin radical0
  · exact (packed_dual_witness radical0 radicalDual0
      radical0_checked.1).1
  · exact radical0_checked.2
  · change matrix0.rank + 12 = 12
    rw [matrix0_root, matrix0_rank]

private theorem radical0_dimension :
    finrank Field (familySpan radical0) = 12 :=
  (packed_dual_witness radical0 radicalDual0
    radical0_checked.1).2

private theorem matrix1_root : matrix1 = rootMatrix 1 := by
  exact certificate1_valid.1

private theorem minor1_checked :
    (rowMatrix inverseRows1 : Matrix (Fin 6) (Fin 6) Field) *
        matrix1.submatrix minorIndices1 minorIndices1 = 1 := by
  exact certificate1_valid.2.1

private theorem radical1_checked :
    (∀ i, rowMap radicalDual1 (radical1 i) = Pi.single i 1) ∧
      (∀ i, matrix1.mulVecLin (radical1 i) = 0) := by
  exact certificate1_valid.2.2.1

private theorem matrix1_rank : (rootMatrix 1).rank = 6 := by
  rw [← matrix1_root]
  exact matrix_rank_eq_of_minor_and_radical matrix1
    minorIndices1 minorIndices1 (rowMatrix inverseRows1)
    radical1 radicalDual1 (by decide) minor1_checked
    radical1_checked.1 radical1_checked.2

private theorem matrix1_kernel :
    LinearMap.ker (Matrix.toBilin' (rootMatrix 1)) =
      familySpan radical1 := by
  rw [← matrix1_root, toBilin_kernel]
  have hs : matrix1.transpose = matrix1 := certificate1_valid.2.2.2
  rw [hs]
  apply kernel_eq_familySpan matrix1.mulVecLin radical1
  · exact (packed_dual_witness radical1 radicalDual1
      radical1_checked.1).1
  · exact radical1_checked.2
  · change matrix1.rank + 6 = 12
    rw [matrix1_root, matrix1_rank]

private theorem radical1_dimension :
    finrank Field (familySpan radical1) = 6 :=
  (packed_dual_witness radical1 radicalDual1
    radical1_checked.1).2

private theorem matrix8_root : matrix8 = rootMatrix 8 := by
  exact certificate8_valid.1

private theorem minor8_checked :
    (rowMatrix inverseRows8 : Matrix (Fin 6) (Fin 6) Field) *
        matrix8.submatrix minorIndices8 minorIndices8 = 1 := by
  exact certificate8_valid.2.1

private theorem radical8_checked :
    (∀ i, rowMap radicalDual8 (radical8 i) = Pi.single i 1) ∧
      (∀ i, matrix8.mulVecLin (radical8 i) = 0) := by
  exact certificate8_valid.2.2.1

private theorem matrix8_rank : (rootMatrix 8).rank = 6 := by
  rw [← matrix8_root]
  exact matrix_rank_eq_of_minor_and_radical matrix8
    minorIndices8 minorIndices8 (rowMatrix inverseRows8)
    radical8 radicalDual8 (by decide) minor8_checked
    radical8_checked.1 radical8_checked.2

private theorem matrix8_kernel :
    LinearMap.ker (Matrix.toBilin' (rootMatrix 8)) =
      familySpan radical8 := by
  rw [← matrix8_root, toBilin_kernel]
  have hs : matrix8.transpose = matrix8 := certificate8_valid.2.2.2
  rw [hs]
  apply kernel_eq_familySpan matrix8.mulVecLin radical8
  · exact (packed_dual_witness radical8 radicalDual8
      radical8_checked.1).1
  · exact radical8_checked.2
  · change matrix8.rank + 6 = 12
    rw [matrix8_root, matrix8_rank]

private theorem radical8_dimension :
    finrank Field (familySpan radical8) = 6 :=
  (packed_dual_witness radical8 radicalDual8
    radical8_checked.1).2

private theorem matrix12_root : matrix12 = rootMatrix 12 := by
  exact certificate12_valid.1

private theorem minor12_checked :
    (rowMatrix inverseRows12 : Matrix (Fin 10) (Fin 10) Field) *
        matrix12.submatrix minorIndices12 minorIndices12 = 1 := by
  exact certificate12_valid.2.1

private theorem radical12_checked :
    (∀ i, rowMap radicalDual12 (radical12 i) = Pi.single i 1) ∧
      (∀ i, matrix12.mulVecLin (radical12 i) = 0) := by
  exact certificate12_valid.2.2.1

private theorem matrix12_rank : (rootMatrix 12).rank = 10 := by
  rw [← matrix12_root]
  exact matrix_rank_eq_of_minor_and_radical matrix12
    minorIndices12 minorIndices12 (rowMatrix inverseRows12)
    radical12 radicalDual12 (by decide) minor12_checked
    radical12_checked.1 radical12_checked.2

private theorem matrix12_kernel :
    LinearMap.ker (Matrix.toBilin' (rootMatrix 12)) =
      familySpan radical12 := by
  rw [← matrix12_root, toBilin_kernel]
  have hs : matrix12.transpose = matrix12 := certificate12_valid.2.2.2
  rw [hs]
  apply kernel_eq_familySpan matrix12.mulVecLin radical12
  · exact (packed_dual_witness radical12 radicalDual12
      radical12_checked.1).1
  · exact radical12_checked.2
  · change matrix12.rank + 2 = 12
    rw [matrix12_root, matrix12_rank]

private theorem radical12_dimension :
    finrank Field (familySpan radical12) = 2 :=
  (packed_dual_witness radical12 radicalDual12
    radical12_checked.1).2

private theorem matrix80_root : matrix80 = rootMatrix 80 := by
  exact certificate80_valid.1

private theorem minor80_checked :
    (rowMatrix inverseRows80 : Matrix (Fin 8) (Fin 8) Field) *
        matrix80.submatrix minorIndices80 minorIndices80 = 1 := by
  exact certificate80_valid.2.1

private theorem radical80_checked :
    (∀ i, rowMap radicalDual80 (radical80 i) = Pi.single i 1) ∧
      (∀ i, matrix80.mulVecLin (radical80 i) = 0) := by
  exact certificate80_valid.2.2.1

private theorem matrix80_rank : (rootMatrix 80).rank = 8 := by
  rw [← matrix80_root]
  exact matrix_rank_eq_of_minor_and_radical matrix80
    minorIndices80 minorIndices80 (rowMatrix inverseRows80)
    radical80 radicalDual80 (by decide) minor80_checked
    radical80_checked.1 radical80_checked.2

private theorem matrix80_kernel :
    LinearMap.ker (Matrix.toBilin' (rootMatrix 80)) =
      familySpan radical80 := by
  rw [← matrix80_root, toBilin_kernel]
  have hs : matrix80.transpose = matrix80 := certificate80_valid.2.2.2
  rw [hs]
  apply kernel_eq_familySpan matrix80.mulVecLin radical80
  · exact (packed_dual_witness radical80 radicalDual80
      radical80_checked.1).1
  · exact radical80_checked.2
  · change matrix80.rank + 4 = 12
    rw [matrix80_root, matrix80_rank]

private theorem radical80_dimension :
    finrank Field (familySpan radical80) = 4 :=
  (packed_dual_witness radical80 radicalDual80
    radical80_checked.1).2

private theorem matrix81_root : matrix81 = rootMatrix 81 := by
  exact certificate81_valid.1

private theorem minor81_checked :
    (rowMatrix inverseRows81 : Matrix (Fin 10) (Fin 10) Field) *
        matrix81.submatrix minorIndices81 minorIndices81 = 1 := by
  exact certificate81_valid.2.1

private theorem radical81_checked :
    (∀ i, rowMap radicalDual81 (radical81 i) = Pi.single i 1) ∧
      (∀ i, matrix81.mulVecLin (radical81 i) = 0) := by
  exact certificate81_valid.2.2.1

private theorem matrix81_rank : (rootMatrix 81).rank = 10 := by
  rw [← matrix81_root]
  exact matrix_rank_eq_of_minor_and_radical matrix81
    minorIndices81 minorIndices81 (rowMatrix inverseRows81)
    radical81 radicalDual81 (by decide) minor81_checked
    radical81_checked.1 radical81_checked.2

private theorem matrix81_kernel :
    LinearMap.ker (Matrix.toBilin' (rootMatrix 81)) =
      familySpan radical81 := by
  rw [← matrix81_root, toBilin_kernel]
  have hs : matrix81.transpose = matrix81 := certificate81_valid.2.2.2
  rw [hs]
  apply kernel_eq_familySpan matrix81.mulVecLin radical81
  · exact (packed_dual_witness radical81 radicalDual81
      radical81_checked.1).1
  · exact radical81_checked.2
  · change matrix81.rank + 2 = 12
    rw [matrix81_root, matrix81_rank]

private theorem radical81_dimension :
    finrank Field (familySpan radical81) = 2 :=
  (packed_dual_witness radical81 radicalDual81
    radical81_checked.1).2

private theorem matrix88_root : matrix88 = rootMatrix 88 := by
  exact certificate88_valid.1

private theorem minor88_checked :
    (rowMatrix inverseRows88 : Matrix (Fin 8) (Fin 8) Field) *
        matrix88.submatrix minorIndices88 minorIndices88 = 1 := by
  exact certificate88_valid.2.1

private theorem radical88_checked :
    (∀ i, rowMap radicalDual88 (radical88 i) = Pi.single i 1) ∧
      (∀ i, matrix88.mulVecLin (radical88 i) = 0) := by
  exact certificate88_valid.2.2.1

private theorem matrix88_rank : (rootMatrix 88).rank = 8 := by
  rw [← matrix88_root]
  exact matrix_rank_eq_of_minor_and_radical matrix88
    minorIndices88 minorIndices88 (rowMatrix inverseRows88)
    radical88 radicalDual88 (by decide) minor88_checked
    radical88_checked.1 radical88_checked.2

private theorem matrix88_kernel :
    LinearMap.ker (Matrix.toBilin' (rootMatrix 88)) =
      familySpan radical88 := by
  rw [← matrix88_root, toBilin_kernel]
  have hs : matrix88.transpose = matrix88 := certificate88_valid.2.2.2
  rw [hs]
  apply kernel_eq_familySpan matrix88.mulVecLin radical88
  · exact (packed_dual_witness radical88 radicalDual88
      radical88_checked.1).1
  · exact radical88_checked.2
  · change matrix88.rank + 4 = 12
    rw [matrix88_root, matrix88_rank]

private theorem radical88_dimension :
    finrank Field (familySpan radical88) = 4 :=
  (packed_dual_witness radical88 radicalDual88
    radical88_checked.1).2

private theorem matrix89_root : matrix89 = rootMatrix 89 := by
  exact certificate89_valid.1

private theorem minor89_checked :
    (rowMatrix inverseRows89 : Matrix (Fin 10) (Fin 10) Field) *
        matrix89.submatrix minorIndices89 minorIndices89 = 1 := by
  exact certificate89_valid.2.1

private theorem radical89_checked :
    (∀ i, rowMap radicalDual89 (radical89 i) = Pi.single i 1) ∧
      (∀ i, matrix89.mulVecLin (radical89 i) = 0) := by
  exact certificate89_valid.2.2.1

private theorem matrix89_rank : (rootMatrix 89).rank = 10 := by
  rw [← matrix89_root]
  exact matrix_rank_eq_of_minor_and_radical matrix89
    minorIndices89 minorIndices89 (rowMatrix inverseRows89)
    radical89 radicalDual89 (by decide) minor89_checked
    radical89_checked.1 radical89_checked.2

private theorem matrix89_kernel :
    LinearMap.ker (Matrix.toBilin' (rootMatrix 89)) =
      familySpan radical89 := by
  rw [← matrix89_root, toBilin_kernel]
  have hs : matrix89.transpose = matrix89 := certificate89_valid.2.2.2
  rw [hs]
  apply kernel_eq_familySpan matrix89.mulVecLin radical89
  · exact (packed_dual_witness radical89 radicalDual89
      radical89_checked.1).1
  · exact radical89_checked.2
  · change matrix89.rank + 2 = 12
    rw [matrix89_root, matrix89_rank]

private theorem radical89_dimension :
    finrank Field (familySpan radical89) = 2 :=
  (packed_dual_witness radical89 radicalDual89
    radical89_checked.1).2

private theorem matrix104_root : matrix104 = rootMatrix 104 := by
  exact certificate104_valid.1

private theorem minor104_checked :
    (rowMatrix inverseRows104 : Matrix (Fin 10) (Fin 10) Field) *
        matrix104.submatrix minorIndices104 minorIndices104 = 1 := by
  exact certificate104_valid.2.1

private theorem radical104_checked :
    (∀ i, rowMap radicalDual104 (radical104 i) = Pi.single i 1) ∧
      (∀ i, matrix104.mulVecLin (radical104 i) = 0) := by
  exact certificate104_valid.2.2.1

private theorem matrix104_rank : (rootMatrix 104).rank = 10 := by
  rw [← matrix104_root]
  exact matrix_rank_eq_of_minor_and_radical matrix104
    minorIndices104 minorIndices104 (rowMatrix inverseRows104)
    radical104 radicalDual104 (by decide) minor104_checked
    radical104_checked.1 radical104_checked.2

private theorem matrix104_kernel :
    LinearMap.ker (Matrix.toBilin' (rootMatrix 104)) =
      familySpan radical104 := by
  rw [← matrix104_root, toBilin_kernel]
  have hs : matrix104.transpose = matrix104 := certificate104_valid.2.2.2
  rw [hs]
  apply kernel_eq_familySpan matrix104.mulVecLin radical104
  · exact (packed_dual_witness radical104 radicalDual104
      radical104_checked.1).1
  · exact radical104_checked.2
  · change matrix104.rank + 2 = 12
    rw [matrix104_root, matrix104_rank]

private theorem radical104_dimension :
    finrank Field (familySpan radical104) = 2 :=
  (packed_dual_witness radical104 radicalDual104
    radical104_checked.1).2

private theorem matrix522_root : matrix522 = rootMatrix 522 := by
  exact certificate522_valid.1

private theorem minor522_checked :
    (rowMatrix inverseRows522 : Matrix (Fin 10) (Fin 10) Field) *
        matrix522.submatrix minorIndices522 minorIndices522 = 1 := by
  exact certificate522_valid.2.1

private theorem radical522_checked :
    (∀ i, rowMap radicalDual522 (radical522 i) = Pi.single i 1) ∧
      (∀ i, matrix522.mulVecLin (radical522 i) = 0) := by
  exact certificate522_valid.2.2.1

private theorem matrix522_rank : (rootMatrix 522).rank = 10 := by
  rw [← matrix522_root]
  exact matrix_rank_eq_of_minor_and_radical matrix522
    minorIndices522 minorIndices522 (rowMatrix inverseRows522)
    radical522 radicalDual522 (by decide) minor522_checked
    radical522_checked.1 radical522_checked.2

private theorem matrix522_kernel :
    LinearMap.ker (Matrix.toBilin' (rootMatrix 522)) =
      familySpan radical522 := by
  rw [← matrix522_root, toBilin_kernel]
  have hs : matrix522.transpose = matrix522 := certificate522_valid.2.2.2
  rw [hs]
  apply kernel_eq_familySpan matrix522.mulVecLin radical522
  · exact (packed_dual_witness radical522 radicalDual522
      radical522_checked.1).1
  · exact radical522_checked.2
  · change matrix522.rank + 2 = 12
    rw [matrix522_root, matrix522_rank]

private theorem radical522_dimension :
    finrank Field (familySpan radical522) = 2 :=
  (packed_dual_witness radical522 radicalDual522
    radical522_checked.1).2

private theorem matrix1400_root : matrix1400 = rootMatrix 1400 := by
  exact certificate1400_valid.1

private theorem minor1400_checked :
    (rowMatrix inverseRows1400 : Matrix (Fin 8) (Fin 8) Field) *
        matrix1400.submatrix minorIndices1400 minorIndices1400 = 1 := by
  exact certificate1400_valid.2.1

private theorem radical1400_checked :
    (∀ i, rowMap radicalDual1400 (radical1400 i) = Pi.single i 1) ∧
      (∀ i, matrix1400.mulVecLin (radical1400 i) = 0) := by
  exact certificate1400_valid.2.2.1

private theorem matrix1400_rank : (rootMatrix 1400).rank = 8 := by
  rw [← matrix1400_root]
  exact matrix_rank_eq_of_minor_and_radical matrix1400
    minorIndices1400 minorIndices1400 (rowMatrix inverseRows1400)
    radical1400 radicalDual1400 (by decide) minor1400_checked
    radical1400_checked.1 radical1400_checked.2

private theorem matrix1400_kernel :
    LinearMap.ker (Matrix.toBilin' (rootMatrix 1400)) =
      familySpan radical1400 := by
  rw [← matrix1400_root, toBilin_kernel]
  have hs : matrix1400.transpose = matrix1400 := certificate1400_valid.2.2.2
  rw [hs]
  apply kernel_eq_familySpan matrix1400.mulVecLin radical1400
  · exact (packed_dual_witness radical1400 radicalDual1400
      radical1400_checked.1).1
  · exact radical1400_checked.2
  · change matrix1400.rank + 4 = 12
    rw [matrix1400_root, matrix1400_rank]

private theorem radical1400_dimension :
    finrank Field (familySpan radical1400) = 4 :=
  (packed_dual_witness radical1400 radicalDual1400
    radical1400_checked.1).2

private theorem matrix1550_root : matrix1550 = rootMatrix 1550 := by
  exact certificate1550_valid.1

private theorem minor1550_checked :
    (rowMatrix inverseRows1550 : Matrix (Fin 10) (Fin 10) Field) *
        matrix1550.submatrix minorIndices1550 minorIndices1550 = 1 := by
  exact certificate1550_valid.2.1

private theorem radical1550_checked :
    (∀ i, rowMap radicalDual1550 (radical1550 i) = Pi.single i 1) ∧
      (∀ i, matrix1550.mulVecLin (radical1550 i) = 0) := by
  exact certificate1550_valid.2.2.1

private theorem matrix1550_rank : (rootMatrix 1550).rank = 10 := by
  rw [← matrix1550_root]
  exact matrix_rank_eq_of_minor_and_radical matrix1550
    minorIndices1550 minorIndices1550 (rowMatrix inverseRows1550)
    radical1550 radicalDual1550 (by decide) minor1550_checked
    radical1550_checked.1 radical1550_checked.2

private theorem matrix1550_kernel :
    LinearMap.ker (Matrix.toBilin' (rootMatrix 1550)) =
      familySpan radical1550 := by
  rw [← matrix1550_root, toBilin_kernel]
  have hs : matrix1550.transpose = matrix1550 := certificate1550_valid.2.2.2
  rw [hs]
  apply kernel_eq_familySpan matrix1550.mulVecLin radical1550
  · exact (packed_dual_witness radical1550 radicalDual1550
      radical1550_checked.1).1
  · exact radical1550_checked.2
  · change matrix1550.rank + 2 = 12
    rw [matrix1550_root, matrix1550_rank]

private theorem radical1550_dimension :
    finrank Field (familySpan radical1550) = 2 :=
  (packed_dual_witness radical1550 radicalDual1550
    radical1550_checked.1).2

private theorem matrix1573_root : matrix1573 = rootMatrix 1573 := by
  exact certificate1573_valid.1

private theorem minor1573_checked :
    (rowMatrix inverseRows1573 : Matrix (Fin 10) (Fin 10) Field) *
        matrix1573.submatrix minorIndices1573 minorIndices1573 = 1 := by
  exact certificate1573_valid.2.1

private theorem radical1573_checked :
    (∀ i, rowMap radicalDual1573 (radical1573 i) = Pi.single i 1) ∧
      (∀ i, matrix1573.mulVecLin (radical1573 i) = 0) := by
  exact certificate1573_valid.2.2.1

private theorem matrix1573_rank : (rootMatrix 1573).rank = 10 := by
  rw [← matrix1573_root]
  exact matrix_rank_eq_of_minor_and_radical matrix1573
    minorIndices1573 minorIndices1573 (rowMatrix inverseRows1573)
    radical1573 radicalDual1573 (by decide) minor1573_checked
    radical1573_checked.1 radical1573_checked.2

private theorem matrix1573_kernel :
    LinearMap.ker (Matrix.toBilin' (rootMatrix 1573)) =
      familySpan radical1573 := by
  rw [← matrix1573_root, toBilin_kernel]
  have hs : matrix1573.transpose = matrix1573 := certificate1573_valid.2.2.2
  rw [hs]
  apply kernel_eq_familySpan matrix1573.mulVecLin radical1573
  · exact (packed_dual_witness radical1573 radicalDual1573
      radical1573_checked.1).1
  · exact radical1573_checked.2
  · change matrix1573.rank + 2 = 12
    rw [matrix1573_root, matrix1573_rank]

private theorem radical1573_dimension :
    finrank Field (familySpan radical1573) = 2 :=
  (packed_dual_witness radical1573 radicalDual1573
    radical1573_checked.1).2

private theorem matrix1580_root : matrix1580 = rootMatrix 1580 := by
  exact certificate1580_valid.1

private theorem minor1580_checked :
    (rowMatrix inverseRows1580 : Matrix (Fin 10) (Fin 10) Field) *
        matrix1580.submatrix minorIndices1580 minorIndices1580 = 1 := by
  exact certificate1580_valid.2.1

private theorem radical1580_checked :
    (∀ i, rowMap radicalDual1580 (radical1580 i) = Pi.single i 1) ∧
      (∀ i, matrix1580.mulVecLin (radical1580 i) = 0) := by
  exact certificate1580_valid.2.2.1

private theorem matrix1580_rank : (rootMatrix 1580).rank = 10 := by
  rw [← matrix1580_root]
  exact matrix_rank_eq_of_minor_and_radical matrix1580
    minorIndices1580 minorIndices1580 (rowMatrix inverseRows1580)
    radical1580 radicalDual1580 (by decide) minor1580_checked
    radical1580_checked.1 radical1580_checked.2

private theorem matrix1580_kernel :
    LinearMap.ker (Matrix.toBilin' (rootMatrix 1580)) =
      familySpan radical1580 := by
  rw [← matrix1580_root, toBilin_kernel]
  have hs : matrix1580.transpose = matrix1580 := certificate1580_valid.2.2.2
  rw [hs]
  apply kernel_eq_familySpan matrix1580.mulVecLin radical1580
  · exact (packed_dual_witness radical1580 radicalDual1580
      radical1580_checked.1).1
  · exact radical1580_checked.2
  · change matrix1580.rank + 2 = 12
    rw [matrix1580_root, matrix1580_rank]

private theorem radical1580_dimension :
    finrank Field (familySpan radical1580) = 2 :=
  (packed_dual_witness radical1580 radicalDual1580
    radical1580_checked.1).2

private theorem matrix16392_root : matrix16392 = rootMatrix 16392 := by
  exact certificate16392_valid.1

private theorem minor16392_checked :
    (rowMatrix inverseRows16392 : Matrix (Fin 10) (Fin 10) Field) *
        matrix16392.submatrix minorIndices16392 minorIndices16392 = 1 := by
  exact certificate16392_valid.2.1

private theorem radical16392_checked :
    (∀ i, rowMap radicalDual16392 (radical16392 i) = Pi.single i 1) ∧
      (∀ i, matrix16392.mulVecLin (radical16392 i) = 0) := by
  exact certificate16392_valid.2.2.1

private theorem matrix16392_rank : (rootMatrix 16392).rank = 10 := by
  rw [← matrix16392_root]
  exact matrix_rank_eq_of_minor_and_radical matrix16392
    minorIndices16392 minorIndices16392 (rowMatrix inverseRows16392)
    radical16392 radicalDual16392 (by decide) minor16392_checked
    radical16392_checked.1 radical16392_checked.2

private theorem matrix16392_kernel :
    LinearMap.ker (Matrix.toBilin' (rootMatrix 16392)) =
      familySpan radical16392 := by
  rw [← matrix16392_root, toBilin_kernel]
  have hs : matrix16392.transpose = matrix16392 := certificate16392_valid.2.2.2
  rw [hs]
  apply kernel_eq_familySpan matrix16392.mulVecLin radical16392
  · exact (packed_dual_witness radical16392 radicalDual16392
      radical16392_checked.1).1
  · exact radical16392_checked.2
  · change matrix16392.rank + 2 = 12
    rw [matrix16392_root, matrix16392_rank]

private theorem radical16392_dimension :
    finrank Field (familySpan radical16392) = 2 :=
  (packed_dual_witness radical16392 radicalDual16392
    radical16392_checked.1).2

private theorem matrix16410_root : matrix16410 = rootMatrix 16410 := by
  exact certificate16410_valid.1

private theorem minor16410_checked :
    (rowMatrix inverseRows16410 : Matrix (Fin 10) (Fin 10) Field) *
        matrix16410.submatrix minorIndices16410 minorIndices16410 = 1 := by
  exact certificate16410_valid.2.1

private theorem radical16410_checked :
    (∀ i, rowMap radicalDual16410 (radical16410 i) = Pi.single i 1) ∧
      (∀ i, matrix16410.mulVecLin (radical16410 i) = 0) := by
  exact certificate16410_valid.2.2.1

private theorem matrix16410_rank : (rootMatrix 16410).rank = 10 := by
  rw [← matrix16410_root]
  exact matrix_rank_eq_of_minor_and_radical matrix16410
    minorIndices16410 minorIndices16410 (rowMatrix inverseRows16410)
    radical16410 radicalDual16410 (by decide) minor16410_checked
    radical16410_checked.1 radical16410_checked.2

private theorem matrix16410_kernel :
    LinearMap.ker (Matrix.toBilin' (rootMatrix 16410)) =
      familySpan radical16410 := by
  rw [← matrix16410_root, toBilin_kernel]
  have hs : matrix16410.transpose = matrix16410 := certificate16410_valid.2.2.2
  rw [hs]
  apply kernel_eq_familySpan matrix16410.mulVecLin radical16410
  · exact (packed_dual_witness radical16410 radicalDual16410
      radical16410_checked.1).1
  · exact radical16410_checked.2
  · change matrix16410.rank + 2 = 12
    rw [matrix16410_root, matrix16410_rank]

private theorem radical16410_dimension :
    finrank Field (familySpan radical16410) = 2 :=
  (packed_dual_witness radical16410 radicalDual16410
    radical16410_checked.1).2

private theorem matrix16404_root : matrix16404 = rootMatrix 16404 := by
  exact certificate16404_valid.1

private theorem minor16404_checked :
    (rowMatrix inverseRows16404 : Matrix (Fin 10) (Fin 10) Field) *
        matrix16404.submatrix minorIndices16404 minorIndices16404 = 1 := by
  exact certificate16404_valid.2.1

private theorem radical16404_checked :
    (∀ i, rowMap radicalDual16404 (radical16404 i) = Pi.single i 1) ∧
      (∀ i, matrix16404.mulVecLin (radical16404 i) = 0) := by
  exact certificate16404_valid.2.2.1

private theorem matrix16404_rank : (rootMatrix 16404).rank = 10 := by
  rw [← matrix16404_root]
  exact matrix_rank_eq_of_minor_and_radical matrix16404
    minorIndices16404 minorIndices16404 (rowMatrix inverseRows16404)
    radical16404 radicalDual16404 (by decide) minor16404_checked
    radical16404_checked.1 radical16404_checked.2

private theorem matrix16404_kernel :
    LinearMap.ker (Matrix.toBilin' (rootMatrix 16404)) =
      familySpan radical16404 := by
  rw [← matrix16404_root, toBilin_kernel]
  have hs : matrix16404.transpose = matrix16404 := certificate16404_valid.2.2.2
  rw [hs]
  apply kernel_eq_familySpan matrix16404.mulVecLin radical16404
  · exact (packed_dual_witness radical16404 radicalDual16404
      radical16404_checked.1).1
  · exact radical16404_checked.2
  · change matrix16404.rank + 2 = 12
    rw [matrix16404_root, matrix16404_rank]

private theorem radical16404_dimension :
    finrank Field (familySpan radical16404) = 2 :=
  (packed_dual_witness radical16404 radicalDual16404
    radical16404_checked.1).2

private theorem matrix16480_root : matrix16480 = rootMatrix 16480 := by
  exact certificate16480_valid.1

private theorem minor16480_checked :
    (rowMatrix inverseRows16480 : Matrix (Fin 8) (Fin 8) Field) *
        matrix16480.submatrix minorIndices16480 minorIndices16480 = 1 := by
  exact certificate16480_valid.2.1

private theorem radical16480_checked :
    (∀ i, rowMap radicalDual16480 (radical16480 i) = Pi.single i 1) ∧
      (∀ i, matrix16480.mulVecLin (radical16480 i) = 0) := by
  exact certificate16480_valid.2.2.1

private theorem matrix16480_rank : (rootMatrix 16480).rank = 8 := by
  rw [← matrix16480_root]
  exact matrix_rank_eq_of_minor_and_radical matrix16480
    minorIndices16480 minorIndices16480 (rowMatrix inverseRows16480)
    radical16480 radicalDual16480 (by decide) minor16480_checked
    radical16480_checked.1 radical16480_checked.2

private theorem matrix16480_kernel :
    LinearMap.ker (Matrix.toBilin' (rootMatrix 16480)) =
      familySpan radical16480 := by
  rw [← matrix16480_root, toBilin_kernel]
  have hs : matrix16480.transpose = matrix16480 := certificate16480_valid.2.2.2
  rw [hs]
  apply kernel_eq_familySpan matrix16480.mulVecLin radical16480
  · exact (packed_dual_witness radical16480 radicalDual16480
      radical16480_checked.1).1
  · exact radical16480_checked.2
  · change matrix16480.rank + 4 = 12
    rw [matrix16480_root, matrix16480_rank]

private theorem radical16480_dimension :
    finrank Field (familySpan radical16480) = 4 :=
  (packed_dual_witness radical16480 radicalDual16480
    radical16480_checked.1).2

private theorem matrix16485_root : matrix16485 = rootMatrix 16485 := by
  exact certificate16485_valid.1

private theorem minor16485_checked :
    (rowMatrix inverseRows16485 : Matrix (Fin 10) (Fin 10) Field) *
        matrix16485.submatrix minorIndices16485 minorIndices16485 = 1 := by
  exact certificate16485_valid.2.1

private theorem radical16485_checked :
    (∀ i, rowMap radicalDual16485 (radical16485 i) = Pi.single i 1) ∧
      (∀ i, matrix16485.mulVecLin (radical16485 i) = 0) := by
  exact certificate16485_valid.2.2.1

private theorem matrix16485_rank : (rootMatrix 16485).rank = 10 := by
  rw [← matrix16485_root]
  exact matrix_rank_eq_of_minor_and_radical matrix16485
    minorIndices16485 minorIndices16485 (rowMatrix inverseRows16485)
    radical16485 radicalDual16485 (by decide) minor16485_checked
    radical16485_checked.1 radical16485_checked.2

private theorem matrix16485_kernel :
    LinearMap.ker (Matrix.toBilin' (rootMatrix 16485)) =
      familySpan radical16485 := by
  rw [← matrix16485_root, toBilin_kernel]
  have hs : matrix16485.transpose = matrix16485 := certificate16485_valid.2.2.2
  rw [hs]
  apply kernel_eq_familySpan matrix16485.mulVecLin radical16485
  · exact (packed_dual_witness radical16485 radicalDual16485
      radical16485_checked.1).1
  · exact radical16485_checked.2
  · change matrix16485.rank + 2 = 12
    rw [matrix16485_root, matrix16485_rank]

private theorem radical16485_dimension :
    finrank Field (familySpan radical16485) = 2 :=
  (packed_dual_witness radical16485 radicalDual16485
    radical16485_checked.1).2

private theorem matrix16464_root : matrix16464 = rootMatrix 16464 := by
  exact certificate16464_valid.1

private theorem minor16464_checked :
    (rowMatrix inverseRows16464 : Matrix (Fin 8) (Fin 8) Field) *
        matrix16464.submatrix minorIndices16464 minorIndices16464 = 1 := by
  exact certificate16464_valid.2.1

private theorem radical16464_checked :
    (∀ i, rowMap radicalDual16464 (radical16464 i) = Pi.single i 1) ∧
      (∀ i, matrix16464.mulVecLin (radical16464 i) = 0) := by
  exact certificate16464_valid.2.2.1

private theorem matrix16464_rank : (rootMatrix 16464).rank = 8 := by
  rw [← matrix16464_root]
  exact matrix_rank_eq_of_minor_and_radical matrix16464
    minorIndices16464 minorIndices16464 (rowMatrix inverseRows16464)
    radical16464 radicalDual16464 (by decide) minor16464_checked
    radical16464_checked.1 radical16464_checked.2

private theorem matrix16464_kernel :
    LinearMap.ker (Matrix.toBilin' (rootMatrix 16464)) =
      familySpan radical16464 := by
  rw [← matrix16464_root, toBilin_kernel]
  have hs : matrix16464.transpose = matrix16464 := certificate16464_valid.2.2.2
  rw [hs]
  apply kernel_eq_familySpan matrix16464.mulVecLin radical16464
  · exact (packed_dual_witness radical16464 radicalDual16464
      radical16464_checked.1).1
  · exact radical16464_checked.2
  · change matrix16464.rank + 4 = 12
    rw [matrix16464_root, matrix16464_rank]

private theorem radical16464_dimension :
    finrank Field (familySpan radical16464) = 4 :=
  (packed_dual_witness radical16464 radicalDual16464
    radical16464_checked.1).2

private theorem matrix16467_root : matrix16467 = rootMatrix 16467 := by
  exact certificate16467_valid.1

private theorem minor16467_checked :
    (rowMatrix inverseRows16467 : Matrix (Fin 10) (Fin 10) Field) *
        matrix16467.submatrix minorIndices16467 minorIndices16467 = 1 := by
  exact certificate16467_valid.2.1

private theorem radical16467_checked :
    (∀ i, rowMap radicalDual16467 (radical16467 i) = Pi.single i 1) ∧
      (∀ i, matrix16467.mulVecLin (radical16467 i) = 0) := by
  exact certificate16467_valid.2.2.1

private theorem matrix16467_rank : (rootMatrix 16467).rank = 10 := by
  rw [← matrix16467_root]
  exact matrix_rank_eq_of_minor_and_radical matrix16467
    minorIndices16467 minorIndices16467 (rowMatrix inverseRows16467)
    radical16467 radicalDual16467 (by decide) minor16467_checked
    radical16467_checked.1 radical16467_checked.2

private theorem matrix16467_kernel :
    LinearMap.ker (Matrix.toBilin' (rootMatrix 16467)) =
      familySpan radical16467 := by
  rw [← matrix16467_root, toBilin_kernel]
  have hs : matrix16467.transpose = matrix16467 := certificate16467_valid.2.2.2
  rw [hs]
  apply kernel_eq_familySpan matrix16467.mulVecLin radical16467
  · exact (packed_dual_witness radical16467 radicalDual16467
      radical16467_checked.1).1
  · exact radical16467_checked.2
  · change matrix16467.rank + 2 = 12
    rw [matrix16467_root, matrix16467_rank]

private theorem radical16467_dimension :
    finrank Field (familySpan radical16467) = 2 :=
  (packed_dual_witness radical16467 radicalDual16467
    radical16467_checked.1).2

private theorem matrix16471_root : matrix16471 = rootMatrix 16471 := by
  exact certificate16471_valid.1

private theorem minor16471_checked :
    (rowMatrix inverseRows16471 : Matrix (Fin 8) (Fin 8) Field) *
        matrix16471.submatrix minorIndices16471 minorIndices16471 = 1 := by
  exact certificate16471_valid.2.1

private theorem radical16471_checked :
    (∀ i, rowMap radicalDual16471 (radical16471 i) = Pi.single i 1) ∧
      (∀ i, matrix16471.mulVecLin (radical16471 i) = 0) := by
  exact certificate16471_valid.2.2.1

private theorem matrix16471_rank : (rootMatrix 16471).rank = 8 := by
  rw [← matrix16471_root]
  exact matrix_rank_eq_of_minor_and_radical matrix16471
    minorIndices16471 minorIndices16471 (rowMatrix inverseRows16471)
    radical16471 radicalDual16471 (by decide) minor16471_checked
    radical16471_checked.1 radical16471_checked.2

private theorem matrix16471_kernel :
    LinearMap.ker (Matrix.toBilin' (rootMatrix 16471)) =
      familySpan radical16471 := by
  rw [← matrix16471_root, toBilin_kernel]
  have hs : matrix16471.transpose = matrix16471 := certificate16471_valid.2.2.2
  rw [hs]
  apply kernel_eq_familySpan matrix16471.mulVecLin radical16471
  · exact (packed_dual_witness radical16471 radicalDual16471
      radical16471_checked.1).1
  · exact radical16471_checked.2
  · change matrix16471.rank + 4 = 12
    rw [matrix16471_root, matrix16471_rank]

private theorem radical16471_dimension :
    finrank Field (familySpan radical16471) = 4 :=
  (packed_dual_witness radical16471 radicalDual16471
    radical16471_checked.1).2

private theorem matrix16448_root : matrix16448 = rootMatrix 16448 := by
  exact certificate16448_valid.1

private theorem minor16448_checked :
    (rowMatrix inverseRows16448 : Matrix (Fin 6) (Fin 6) Field) *
        matrix16448.submatrix minorIndices16448 minorIndices16448 = 1 := by
  exact certificate16448_valid.2.1

private theorem radical16448_checked :
    (∀ i, rowMap radicalDual16448 (radical16448 i) = Pi.single i 1) ∧
      (∀ i, matrix16448.mulVecLin (radical16448 i) = 0) := by
  exact certificate16448_valid.2.2.1

private theorem matrix16448_rank : (rootMatrix 16448).rank = 6 := by
  rw [← matrix16448_root]
  exact matrix_rank_eq_of_minor_and_radical matrix16448
    minorIndices16448 minorIndices16448 (rowMatrix inverseRows16448)
    radical16448 radicalDual16448 (by decide) minor16448_checked
    radical16448_checked.1 radical16448_checked.2

private theorem matrix16448_kernel :
    LinearMap.ker (Matrix.toBilin' (rootMatrix 16448)) =
      familySpan radical16448 := by
  rw [← matrix16448_root, toBilin_kernel]
  have hs : matrix16448.transpose = matrix16448 := certificate16448_valid.2.2.2
  rw [hs]
  apply kernel_eq_familySpan matrix16448.mulVecLin radical16448
  · exact (packed_dual_witness radical16448 radicalDual16448
      radical16448_checked.1).1
  · exact radical16448_checked.2
  · change matrix16448.rank + 6 = 12
    rw [matrix16448_root, matrix16448_rank]

private theorem radical16448_dimension :
    finrank Field (familySpan radical16448) = 6 :=
  (packed_dual_witness radical16448 radicalDual16448
    radical16448_checked.1).2

theorem matrix_rank (root : Fin 30) :
    (rootMatrix (roots root).assignment).rank = rootRank root := by
  fin_cases root
  · change (rootMatrix 0).rank = 0
    exact matrix0_rank
  · change (rootMatrix 1).rank = 6
    exact matrix1_rank
  · change (rootMatrix 1).rank = 6
    exact matrix1_rank
  · change (rootMatrix 1).rank = 6
    exact matrix1_rank
  · change (rootMatrix 8).rank = 6
    exact matrix8_rank
  · change (rootMatrix 8).rank = 6
    exact matrix8_rank
  · change (rootMatrix 8).rank = 6
    exact matrix8_rank
  · change (rootMatrix 12).rank = 10
    exact matrix12_rank
  · change (rootMatrix 80).rank = 8
    exact matrix80_rank
  · change (rootMatrix 80).rank = 8
    exact matrix80_rank
  · change (rootMatrix 81).rank = 10
    exact matrix81_rank
  · change (rootMatrix 88).rank = 8
    exact matrix88_rank
  · change (rootMatrix 88).rank = 8
    exact matrix88_rank
  · change (rootMatrix 89).rank = 10
    exact matrix89_rank
  · change (rootMatrix 104).rank = 10
    exact matrix104_rank
  · change (rootMatrix 522).rank = 10
    exact matrix522_rank
  · change (rootMatrix 1400).rank = 8
    exact matrix1400_rank
  · change (rootMatrix 1400).rank = 8
    exact matrix1400_rank
  · change (rootMatrix 1550).rank = 10
    exact matrix1550_rank
  · change (rootMatrix 1573).rank = 10
    exact matrix1573_rank
  · change (rootMatrix 1580).rank = 10
    exact matrix1580_rank
  · change (rootMatrix 16392).rank = 10
    exact matrix16392_rank
  · change (rootMatrix 16410).rank = 10
    exact matrix16410_rank
  · change (rootMatrix 16404).rank = 10
    exact matrix16404_rank
  · change (rootMatrix 16480).rank = 8
    exact matrix16480_rank
  · change (rootMatrix 16485).rank = 10
    exact matrix16485_rank
  · change (rootMatrix 16464).rank = 8
    exact matrix16464_rank
  · change (rootMatrix 16467).rank = 10
    exact matrix16467_rank
  · change (rootMatrix 16471).rank = 8
    exact matrix16471_rank
  · change (rootMatrix 16448).rank = 6
    exact matrix16448_rank

theorem matrix_kernel (root : Fin 30) :
    LinearMap.ker (Matrix.toBilin' (rootMatrix (roots root).assignment)) =
      familySpan (decoded (n := 12) (listColumns (roots root).radical)) := by
  fin_cases root
  · change LinearMap.ker (Matrix.toBilin' (rootMatrix 0)) =
      familySpan radical0
    exact matrix0_kernel
  · change LinearMap.ker (Matrix.toBilin' (rootMatrix 1)) =
      familySpan radical1
    exact matrix1_kernel
  · change LinearMap.ker (Matrix.toBilin' (rootMatrix 1)) =
      familySpan radical1
    exact matrix1_kernel
  · change LinearMap.ker (Matrix.toBilin' (rootMatrix 1)) =
      familySpan radical1
    exact matrix1_kernel
  · change LinearMap.ker (Matrix.toBilin' (rootMatrix 8)) =
      familySpan radical8
    exact matrix8_kernel
  · change LinearMap.ker (Matrix.toBilin' (rootMatrix 8)) =
      familySpan radical8
    exact matrix8_kernel
  · change LinearMap.ker (Matrix.toBilin' (rootMatrix 8)) =
      familySpan radical8
    exact matrix8_kernel
  · change LinearMap.ker (Matrix.toBilin' (rootMatrix 12)) =
      familySpan radical12
    exact matrix12_kernel
  · change LinearMap.ker (Matrix.toBilin' (rootMatrix 80)) =
      familySpan radical80
    exact matrix80_kernel
  · change LinearMap.ker (Matrix.toBilin' (rootMatrix 80)) =
      familySpan radical80
    exact matrix80_kernel
  · change LinearMap.ker (Matrix.toBilin' (rootMatrix 81)) =
      familySpan radical81
    exact matrix81_kernel
  · change LinearMap.ker (Matrix.toBilin' (rootMatrix 88)) =
      familySpan radical88
    exact matrix88_kernel
  · change LinearMap.ker (Matrix.toBilin' (rootMatrix 88)) =
      familySpan radical88
    exact matrix88_kernel
  · change LinearMap.ker (Matrix.toBilin' (rootMatrix 89)) =
      familySpan radical89
    exact matrix89_kernel
  · change LinearMap.ker (Matrix.toBilin' (rootMatrix 104)) =
      familySpan radical104
    exact matrix104_kernel
  · change LinearMap.ker (Matrix.toBilin' (rootMatrix 522)) =
      familySpan radical522
    exact matrix522_kernel
  · change LinearMap.ker (Matrix.toBilin' (rootMatrix 1400)) =
      familySpan radical1400
    exact matrix1400_kernel
  · change LinearMap.ker (Matrix.toBilin' (rootMatrix 1400)) =
      familySpan radical1400
    exact matrix1400_kernel
  · change LinearMap.ker (Matrix.toBilin' (rootMatrix 1550)) =
      familySpan radical1550
    exact matrix1550_kernel
  · change LinearMap.ker (Matrix.toBilin' (rootMatrix 1573)) =
      familySpan radical1573
    exact matrix1573_kernel
  · change LinearMap.ker (Matrix.toBilin' (rootMatrix 1580)) =
      familySpan radical1580
    exact matrix1580_kernel
  · change LinearMap.ker (Matrix.toBilin' (rootMatrix 16392)) =
      familySpan radical16392
    exact matrix16392_kernel
  · change LinearMap.ker (Matrix.toBilin' (rootMatrix 16410)) =
      familySpan radical16410
    exact matrix16410_kernel
  · change LinearMap.ker (Matrix.toBilin' (rootMatrix 16404)) =
      familySpan radical16404
    exact matrix16404_kernel
  · change LinearMap.ker (Matrix.toBilin' (rootMatrix 16480)) =
      familySpan radical16480
    exact matrix16480_kernel
  · change LinearMap.ker (Matrix.toBilin' (rootMatrix 16485)) =
      familySpan radical16485
    exact matrix16485_kernel
  · change LinearMap.ker (Matrix.toBilin' (rootMatrix 16464)) =
      familySpan radical16464
    exact matrix16464_kernel
  · change LinearMap.ker (Matrix.toBilin' (rootMatrix 16467)) =
      familySpan radical16467
    exact matrix16467_kernel
  · change LinearMap.ker (Matrix.toBilin' (rootMatrix 16471)) =
      familySpan radical16471
    exact matrix16471_kernel
  · change LinearMap.ker (Matrix.toBilin' (rootMatrix 16448)) =
      familySpan radical16448
    exact matrix16448_kernel

theorem radical_dimension (root : Fin 30) :
    finrank Field (familySpan (decoded (n := 12) (listColumns (roots root).radical))) =
      (roots root).radical.length := by
  fin_cases root
  · change finrank Field (familySpan radical0) = 12
    exact radical0_dimension
  · change finrank Field (familySpan radical1) = 6
    exact radical1_dimension
  · change finrank Field (familySpan radical1) = 6
    exact radical1_dimension
  · change finrank Field (familySpan radical1) = 6
    exact radical1_dimension
  · change finrank Field (familySpan radical8) = 6
    exact radical8_dimension
  · change finrank Field (familySpan radical8) = 6
    exact radical8_dimension
  · change finrank Field (familySpan radical8) = 6
    exact radical8_dimension
  · change finrank Field (familySpan radical12) = 2
    exact radical12_dimension
  · change finrank Field (familySpan radical80) = 4
    exact radical80_dimension
  · change finrank Field (familySpan radical80) = 4
    exact radical80_dimension
  · change finrank Field (familySpan radical81) = 2
    exact radical81_dimension
  · change finrank Field (familySpan radical88) = 4
    exact radical88_dimension
  · change finrank Field (familySpan radical88) = 4
    exact radical88_dimension
  · change finrank Field (familySpan radical89) = 2
    exact radical89_dimension
  · change finrank Field (familySpan radical104) = 2
    exact radical104_dimension
  · change finrank Field (familySpan radical522) = 2
    exact radical522_dimension
  · change finrank Field (familySpan radical1400) = 4
    exact radical1400_dimension
  · change finrank Field (familySpan radical1400) = 4
    exact radical1400_dimension
  · change finrank Field (familySpan radical1550) = 2
    exact radical1550_dimension
  · change finrank Field (familySpan radical1573) = 2
    exact radical1573_dimension
  · change finrank Field (familySpan radical1580) = 2
    exact radical1580_dimension
  · change finrank Field (familySpan radical16392) = 2
    exact radical16392_dimension
  · change finrank Field (familySpan radical16410) = 2
    exact radical16410_dimension
  · change finrank Field (familySpan radical16404) = 2
    exact radical16404_dimension
  · change finrank Field (familySpan radical16480) = 4
    exact radical16480_dimension
  · change finrank Field (familySpan radical16485) = 2
    exact radical16485_dimension
  · change finrank Field (familySpan radical16464) = 4
    exact radical16464_dimension
  · change finrank Field (familySpan radical16467) = 2
    exact radical16467_dimension
  · change finrank Field (familySpan radical16471) = 4
    exact radical16471_dimension
  · change finrank Field (familySpan radical16448) = 6
    exact radical16448_dimension

private theorem projection_rows :
    localParameterRows = CoveringSymmetry.projectionRows := by
  native_decide

theorem localRadical (root : Fin 30) (v : Vector 127)
    (hroot : CoveringSymmetry.localParameterProjection v =
      (decodeMask (roots root).assignment : Vector 15)) :
    CoveringLocal.localRadical (CoveringSymmetry.fullForm v) =
      familySpan (decoded (n := 12) (listColumns (roots root).radical)) := by
  have hprojection : rowMap localParameterRows v =
      (decodeMask (roots root).assignment : Vector 15) := by
    rw [projection_rows]
    exact hroot
  change LinearMap.ker (CoveringLocal.localForm
    (Matrix.toBilin' (coefficientMatrix CoveringCovarianceData.matrixRows v))) = _
  rw [localForm_root (roots root).assignment v hprojection]
  exact matrix_kernel root

theorem fullKernel_le_radical (root : Fin 30) (v : Vector 127)
    (hroot : CoveringSymmetry.localParameterProjection v =
      (decodeMask (roots root).assignment : Vector 15)) :
    CoveringLevelSixReduction.fullKernel v ≤
      familySpan (decoded (n := 12) (listColumns (roots root).radical)) := by
  exact (CoveringLevelSixReduction.fullKernel_le_common v).trans
    ((CoveringLocal.fullKernel_le_localRadical (CoveringSymmetry.fullForm v)).trans
      (le_of_eq (localRadical root v hroot)))

theorem local_rank (root : Fin 30) (v : Vector 127)
    (hroot : CoveringSymmetry.localParameterProjection v =
      (decodeMask (roots root).assignment : Vector 15)) :
    finrank Field (LinearMap.range (Covering.gram (CoveringLevelSixReduction.fullForm v)
      CoveringLevelSixReduction.localEmbedding)) = rootRank root := by
  have hprojection : rowMap localParameterRows v =
      (decodeMask (roots root).assignment : Vector 15) := by
    rw [projection_rows]
    exact hroot
  have he := CoveringLevelSixReduction.local_restriction v
  have hr := localForm_rank_root (roots root).assignment v hprojection
  exact (congrArg (fun B => finrank Field (LinearMap.range B)) he).trans
    (hr.trans (matrix_rank root))

end Lemmata.CocubicCovering.CoveringLevelSixRootRanks
