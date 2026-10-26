module

public import Lemmata.CocubicCovering.Proof.FiniteDAG
public meta import Lemmata.CocubicCovering.Proof.FiniteDAG
public import Lemmata.CocubicCovering.Proof.Symmetry
public meta import Lemmata.CocubicCovering.Proof.Symmetry

@[expose] public section

namespace Lemmata.CocubicCovering.CoveringLevelSixCoreData

open CoveringFiniteDAG (Root State)
open CoveringAffine

def rootData : Array Root := #[
  ⟨0, [1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048], 7⟩,
  ⟨1, [1, 2, 4, 8, 16, 32], 6⟩,
  ⟨1, [1, 2, 4, 8, 16, 32], 5⟩,
  ⟨1, [1, 2, 4, 8, 16, 32], 4⟩,
  ⟨8, [1, 2, 8, 64, 512, 1024], 6⟩,
  ⟨8, [1, 2, 8, 64, 512, 1024], 5⟩,
  ⟨8, [1, 2, 8, 64, 512, 1024], 4⟩,
  ⟨12, [1, 2], 2⟩,
  ⟨80, [1, 8, 272, 512], 4⟩,
  ⟨80, [1, 8, 272, 512], 3⟩,
  ⟨81, [1, 8], 2⟩,
  ⟨88, [1, 8, 496, 512], 4⟩,
  ⟨88, [1, 8, 496, 512], 3⟩,
  ⟨89, [1, 8], 2⟩,
  ⟨104, [2, 512], 2⟩,
  ⟨522, [514, 640], 2⟩,
  ⟨1400, [392, 272, 160, 320], 4⟩,
  ⟨1400, [392, 272, 160, 320], 3⟩,
  ⟨1550, [3673, 2204], 2⟩,
  ⟨1573, [581, 1742], 2⟩,
  ⟨1580, [1155, 532], 2⟩,
  ⟨16392, [512, 1024], 2⟩,
  ⟨16410, [3469, 774], 2⟩,
  ⟨16404, [3996, 672], 2⟩,
  ⟨16480, [2370, 2416, 1152, 512], 3⟩,
  ⟨16485, [2421, 3154], 2⟩,
  ⟨16464, [1057, 2056, 1296, 512], 3⟩,
  ⟨16467, [2059, 932], 2⟩,
  ⟨16471, [305, 1202, 564, 4024], 3⟩,
  ⟨16448, [1057, 258, 1040, 1152, 512, 2048], 4⟩,
]

def roots (i : Fin 30) : Root := rootData[i.val]?.getD ⟨0, [], 0⟩

def rootRank (i : Fin 30) : Nat :=
  (#[0, 6, 6, 6, 6, 6, 6, 10, 8, 8, 10, 8, 8, 10, 10, 10, 8, 8, 10, 10, 10, 10, 10, 10, 8, 10, 8, 10, 8, 6][i.val]?).getD 0

def rootCrossRank (i : Fin 30) : Nat :=
  (#[5, 0, 1, 2, 0, 1, 2, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 2][i.val]?).getD 0

def searchRoot (i : Fin 21) : Fin 30 := Fin.ofNat 30 i.val
def entries (i : Fin 21) : Fin 21 := i
def states (i : Fin 21) : State 30 := ⟨searchRoot i, []⟩

theorem entry_roots (i : Fin 21) : (states (entries i)).root = searchRoot i := rfl
theorem entry_cores (i : Fin 21) : (states (entries i)).core = [] := rfl

def terminalData : Array (State 30) := #[
  ⟨21, [1024, 512]⟩,
  ⟨22, [3469, 774]⟩,
  ⟨23, [3388, 672]⟩,
  ⟨24, [3522, 512, 50]⟩,
  ⟨25, [2421, 1319]⟩,
  ⟨26, [2361, 1296, 512]⟩,
  ⟨27, [2059, 932]⟩,
  ⟨28, [2063, 1411, 773]⟩,
  ⟨28, [2366, 1411, 773]⟩,
  ⟨29, [2097, 1152, 561, 307]⟩,
  ⟨29, [2048, 1410, 512, 49]⟩,
  ⟨0, [2048, 1024, 513, 270, 142, 66, 29]⟩,
  ⟨0, [2048, 1024, 512, 129, 85, 49, 3]⟩,
]

def terminals (i : Fin 13) : State 30 := terminalData[i.val]?.getD ⟨0, []⟩

abbrev elementaryColumns := CoveringSymmetry.unitCoreColumns

def elementaryLocalColumns (step : Fin 8) (j : Fin 15) : Nat :=
  xorRows ((List.finRange 15).map fun i =>
    if (CoveringSymmetry.unitLocalRows step i).testBit j.val then 2 ^ i.val else 0)

def applyWord (steps : List (Fin 8)) (mask : Nat) : Nat :=
  steps.foldl (fun value step => composeRow value (elementaryColumns step)) mask

def applyLocalWord (steps : List (Fin 8)) (mask : Nat) : Nat :=
  steps.foldl (fun value step => composeRow value (elementaryLocalColumns step)) mask

end Lemmata.CocubicCovering.CoveringLevelSixCoreData
