module

public import Lemmata.CocubicCovering.Proof.Bits
public meta import Lemmata.CocubicCovering.Proof.Bits
public import Lemmata.CocubicCovering.Proof.RankWitness
public meta import Lemmata.CocubicCovering.Proof.RankWitness
public import Lemmata.CocubicCovering.Proof.CovarianceData
public meta import Lemmata.CocubicCovering.Proof.CovarianceData
public import Lemmata.CocubicCovering.Proof.Local
public meta import Lemmata.CocubicCovering.Proof.Local

@[expose] public section

set_option Elab.async false

namespace Lemmata.CocubicCovering.CoveringLocalRanks

open CoveringBits CoveringAffine CoveringCongruence CoveringCovarianceData
open Module CoveringRankWitness CoveringWitness

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def localRowData : Array (Array Nat) :=
  #[
    #[0, 0, 0, 0, 0, 0, 16384, 8192, 512, 4096, 256, 32],
    #[0, 0, 0, 16384, 8192, 512, 0, 0, 0, 2048, 128, 16],
    #[0, 0, 0, 8192, 16896, 16384, 512, 16384, 8704, 1024, 64, 8],
    #[0, 16384, 8192, 0, 256, 32, 2304, 1024, 4432, 0, 4, 2],
    #[0, 8192, 16896, 256, 0, 4352, 1184, 6160, 168, 4, 2, 4],
    #[0, 512, 16384, 32, 4352, 0, 64, 2312, 160, 2, 0, 4],
    #[16384, 0, 512, 2304, 1184, 64, 0, 16, 2176, 4, 0, 1],
    #[8192, 0, 16384, 1024, 6160, 2312, 16, 0, 144, 0, 1, 4],
    #[512, 0, 8704, 4432, 168, 160, 2176, 144, 0, 5, 4, 0],
    #[4096, 2048, 1024, 0, 4, 2, 4, 0, 5, 0, 0, 0],
    #[256, 128, 64, 4, 2, 0, 0, 1, 4, 0, 0, 0],
    #[32, 16, 8, 2, 4, 4, 1, 4, 0, 0, 0, 0],
  ]

def localRows (i j : Fin 12) : Nat :=
  (localRowData[i.val]?.getD #[])[j.val]?.getD 0

def localParameterData : Array Nat :=
  #[2596148429267413814265248164610048, 5192296858534827628530496329220096, 10384593717069655257060992658440192, 20769187434139310514121985316880384, 41538374868278621028243970633760768, 83076749736557242056487941267521536, 166153499473114484112975882535043072, 332306998946228968225951765070086144, 664613997892457936451903530140172288, 1329227995784915872903807060280344576, 2658455991569831745807614120560689152, 5316911983139663491615228241121378304, 10633823966279326983230456482242756608, 21267647932558653966460912964485513216, 42535295865117307932921825928971026432]

def localParameterRows (i : Fin 15) : Nat := localParameterData[i.val]?.getD 0

theorem localRows_encoded : ∀ i j : Fin 12,
    composeRow (localRows i j) localParameterRows =
      matrixRows (CoveringMatrix.localInclusion i) (CoveringMatrix.localInclusion j) := by
  native_decide

theorem local_submatrix (v : Vector 127) :
    (coefficientMatrix matrixRows v).submatrix
        CoveringMatrix.localInclusion CoveringMatrix.localInclusion =
      coefficientMatrix localRows (rowMap localParameterRows v) := by
  ext i j
  change evalRow (matrixRows _ _) v =
    evalRow (localRows i j) (rowMap localParameterRows v)
  rw [← evalRow_composeRow, localRows_encoded]

theorem localForm_submatrix (A : Matrix (Fin 24) (Fin 24) Field) :
    CoveringLocal.localForm (Matrix.toBilin' A) = Matrix.toBilin'
      (A.submatrix CoveringMatrix.localInclusion CoveringMatrix.localInclusion) := by
  apply (Pi.basisFun Field (Fin 12)).ext
  intro i
  apply (Pi.basisFun Field (Fin 12)).ext
  intro j
  simp only [Pi.basisFun_apply, CoveringLocal.localForm_basis, Matrix.toBilin'_single,
    Matrix.submatrix_apply]

def rowMatrix {m n : Nat} (rows : Fin m → Nat) : Matrix (Fin m) (Fin n) Field :=
  fun i j => CoveringPolynomial.ofBool ((rows i).testBit j.val)

def localArows (root : Nat) (i : Fin 12) : Nat :=
  match root with
  | 0 => (#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0][i.val]?).getD 0
  | 1 => (#[0, 0, 0, 0, 0, 0, 2048, 1024, 512, 256, 128, 64][i.val]?).getD 0
  | 8 => (#[0, 0, 2048, 0, 256, 128, 0, 32, 16, 0, 0, 4][i.val]?).getD 0
  | 12 => (#[0, 0, 2048, 1024, 2816, 2176, 512, 2080, 1552, 336, 264, 180][i.val]?).getD 0
  | 80 => (#[0, 2048, 1024, 0, 128, 64, 160, 336, 128, 0, 4, 2][i.val]?).getD 0
  | 81 => (#[0, 2048, 1024, 0, 128, 64, 2208, 1360, 640, 256, 132, 66][i.val]?).getD 0
  | 88 => (#[0, 2048, 3072, 0, 384, 192, 160, 368, 144, 0, 4, 6][i.val]?).getD 0
  | 89 => (#[0, 2048, 3072, 0, 384, 192, 2208, 1392, 656, 256, 132, 70][i.val]?).getD 0
  | 104 => (#[2048, 0, 3072, 288, 64, 456, 48, 32, 40, 0, 4, 5][i.val]?).getD 0
  | 522 => (#[256, 32, 2384, 2048, 1284, 642, 4, 32, 21, 32, 16, 12][i.val]?).getD 0
  | 1184 => (#[2048, 1024, 512, 160, 64, 8, 272, 264, 192, 4, 2, 1][i.val]?).getD 0
  | 1188 => (#[2048, 1024, 512, 1184, 2624, 2056, 784, 2312, 1728, 340, 266, 177][i.val]?).getD 0
  | 1192 => (#[2048, 1024, 2560, 160, 320, 136, 272, 296, 208, 4, 2, 5][i.val]?).getD 0
  | 1193 => (#[2048, 1024, 2560, 160, 320, 136, 2320, 1320, 720, 260, 130, 69][i.val]?).getD 0
  | 1400 => (#[3072, 2048, 3584, 496, 168, 344, 168, 344, 168, 4, 5, 7][i.val]?).getD 0
  | 1550 => (#[256, 32, 2896, 3200, 3908, 2690, 532, 2088, 1557, 372, 280, 188][i.val]?).getD 0
  | 1573 => (#[2304, 32, 848, 1184, 2820, 2314, 2564, 3080, 1077, 84, 392, 241][i.val]?).getD 0
  | 1580 => (#[2304, 32, 2896, 1184, 2564, 2442, 516, 2088, 1573, 340, 264, 181][i.val]?).getD 0
  | _ => 0

def localMatrix (root : Nat) : Matrix (Fin 12) (Fin 12) Field :=
  rowMatrix (localArows root)

def rootMatrix (root : Nat) : Matrix (Fin 12) (Fin 12) Field :=
  coefficientMatrix localRows (decodeMask root : Vector 15)

theorem localForm_root (root : Nat) (v : Vector 127)
    (hroot : rowMap localParameterRows v = (decodeMask root : Vector 15)) :
    CoveringLocal.localForm (Matrix.toBilin' (coefficientMatrix matrixRows v)) =
      Matrix.toBilin' (rootMatrix root) := by
  change CoveringLocal.localForm (Matrix.toBilin' (coefficientMatrix matrixRows v)) =
    Matrix.toBilin' (coefficientMatrix localRows (decodeMask root : Vector 15))
  rw [localForm_submatrix, local_submatrix, hroot]

theorem localForm_rank_root (root : Nat) (v : Vector 127)
    (hroot : rowMap localParameterRows v = (decodeMask root : Vector 15)) :
    finrank Field (LinearMap.range (CoveringLocal.localForm
      (Matrix.toBilin' (coefficientMatrix matrixRows v)))) = (rootMatrix root).rank := by
  rw [localForm_root root v hroot, toBilin_rank]

theorem root0_matrix : localMatrix 0 = rootMatrix 0 := by
  native_decide

def minorIndices0 (i : Fin 0) : Fin 12 :=
  Fin.ofNat 12 ((#[][i.val]?).getD 0)

def inverseRows0 (i : Fin 0) : Nat :=
  (#[][i.val]?).getD 0

private theorem minor0_checked :
    (rowMatrix (inverseRows0) : Matrix (Fin 0) (Fin 0) Field) *
        (localMatrix 0).submatrix minorIndices0 minorIndices0 = 1 := by
  native_decide

def radical0 (i : Fin 12) : Vector 12 :=
  decodeMask ((#[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048][i.val]?).getD 0)

def radicalDual0 (i : Fin 12) : Nat :=
  (#[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048][i.val]?).getD 0

theorem radical0_checked :
    (∀ i, rowMap radicalDual0 (radical0 i) = Pi.single i 1) ∧
      (∀ i, (localMatrix 0).mulVecLin (radical0 i) = 0) := by
  native_decide

theorem root0_rank : (rootMatrix 0).rank = 0 := by
  rw [← root0_matrix]
  exact matrix_rank_eq_of_minor_and_radical (localMatrix 0)
    minorIndices0 minorIndices0 (rowMatrix (inverseRows0))
    radical0 radicalDual0 (by decide) minor0_checked
    radical0_checked.1 radical0_checked.2

theorem radical0_kernel :
    LinearMap.ker (Matrix.toBilin' (rootMatrix 0)) = familySpan radical0 := by
  rw [← root0_matrix, toBilin_kernel]
  have hs : (localMatrix 0).transpose = localMatrix 0 := by native_decide
  rw [hs]
  apply kernel_eq_familySpan (localMatrix 0).mulVecLin radical0
  · exact (packed_dual_witness radical0 radicalDual0 radical0_checked.1).1
  · exact radical0_checked.2
  · change (localMatrix 0).rank + 12 = 12
    rw [root0_matrix, root0_rank]

theorem radical0_dimension : finrank Field (familySpan radical0) = 12 :=
  (packed_dual_witness radical0 radicalDual0 radical0_checked.1).2

theorem localRadical_root0 (v : Vector 127)
    (hroot : rowMap localParameterRows v = (decodeMask 0 : Vector 15)) :
    CoveringLocal.localRadical (Matrix.toBilin' (coefficientMatrix matrixRows v)) =
      familySpan radical0 := by
  change LinearMap.ker (CoveringLocal.localForm
    (Matrix.toBilin' (coefficientMatrix matrixRows v))) = _
  rw [localForm_root 0 v hroot]
  exact radical0_kernel

theorem localRadical_root0_finrank (v : Vector 127)
    (hroot : rowMap localParameterRows v = (decodeMask 0 : Vector 15)) :
    finrank Field (CoveringLocal.localRadical
      (Matrix.toBilin' (coefficientMatrix matrixRows v))) = 12 := by
  rw [localRadical_root0 v hroot]
  exact radical0_dimension

theorem root1_matrix : localMatrix 1 = rootMatrix 1 := by
  native_decide

def minorIndices1 (i : Fin 6) : Fin 12 :=
  Fin.ofNat 12 ((#[6, 7, 8, 9, 10, 11][i.val]?).getD 0)

def inverseRows1 (i : Fin 6) : Nat :=
  (#[32, 16, 8, 4, 2, 1][i.val]?).getD 0

private theorem minor1_checked :
    (rowMatrix (inverseRows1) : Matrix (Fin 6) (Fin 6) Field) *
        (localMatrix 1).submatrix minorIndices1 minorIndices1 = 1 := by
  native_decide

def radical1 (i : Fin 6) : Vector 12 :=
  decodeMask ((#[1, 2, 4, 8, 16, 32][i.val]?).getD 0)

def radicalDual1 (i : Fin 6) : Nat :=
  (#[1, 2, 4, 8, 16, 32][i.val]?).getD 0

theorem radical1_checked :
    (∀ i, rowMap radicalDual1 (radical1 i) = Pi.single i 1) ∧
      (∀ i, (localMatrix 1).mulVecLin (radical1 i) = 0) := by
  native_decide

theorem root1_rank : (rootMatrix 1).rank = 6 := by
  rw [← root1_matrix]
  exact matrix_rank_eq_of_minor_and_radical (localMatrix 1)
    minorIndices1 minorIndices1 (rowMatrix (inverseRows1))
    radical1 radicalDual1 (by decide) minor1_checked
    radical1_checked.1 radical1_checked.2

theorem radical1_kernel :
    LinearMap.ker (Matrix.toBilin' (rootMatrix 1)) = familySpan radical1 := by
  rw [← root1_matrix, toBilin_kernel]
  have hs : (localMatrix 1).transpose = localMatrix 1 := by native_decide
  rw [hs]
  apply kernel_eq_familySpan (localMatrix 1).mulVecLin radical1
  · exact (packed_dual_witness radical1 radicalDual1 radical1_checked.1).1
  · exact radical1_checked.2
  · change (localMatrix 1).rank + 6 = 12
    rw [root1_matrix, root1_rank]

theorem radical1_dimension : finrank Field (familySpan radical1) = 6 :=
  (packed_dual_witness radical1 radicalDual1 radical1_checked.1).2

theorem localRadical_root1 (v : Vector 127)
    (hroot : rowMap localParameterRows v = (decodeMask 1 : Vector 15)) :
    CoveringLocal.localRadical (Matrix.toBilin' (coefficientMatrix matrixRows v)) =
      familySpan radical1 := by
  change LinearMap.ker (CoveringLocal.localForm
    (Matrix.toBilin' (coefficientMatrix matrixRows v))) = _
  rw [localForm_root 1 v hroot]
  exact radical1_kernel

theorem localRadical_root1_finrank (v : Vector 127)
    (hroot : rowMap localParameterRows v = (decodeMask 1 : Vector 15)) :
    finrank Field (CoveringLocal.localRadical
      (Matrix.toBilin' (coefficientMatrix matrixRows v))) = 6 := by
  rw [localRadical_root1 v hroot]
  exact radical1_dimension

theorem root8_matrix : localMatrix 8 = rootMatrix 8 := by
  native_decide

def minorIndices8 (i : Fin 6) : Fin 12 :=
  Fin.ofNat 12 ((#[2, 4, 5, 7, 8, 11][i.val]?).getD 0)

def inverseRows8 (i : Fin 6) : Nat :=
  (#[32, 16, 8, 4, 2, 1][i.val]?).getD 0

private theorem minor8_checked :
    (rowMatrix (inverseRows8) : Matrix (Fin 6) (Fin 6) Field) *
        (localMatrix 8).submatrix minorIndices8 minorIndices8 = 1 := by
  native_decide

def radical8 (i : Fin 6) : Vector 12 :=
  decodeMask ((#[1, 2, 8, 64, 512, 1024][i.val]?).getD 0)

def radicalDual8 (i : Fin 6) : Nat :=
  (#[1, 2, 8, 64, 512, 1024][i.val]?).getD 0

theorem radical8_checked :
    (∀ i, rowMap radicalDual8 (radical8 i) = Pi.single i 1) ∧
      (∀ i, (localMatrix 8).mulVecLin (radical8 i) = 0) := by
  native_decide

theorem root8_rank : (rootMatrix 8).rank = 6 := by
  rw [← root8_matrix]
  exact matrix_rank_eq_of_minor_and_radical (localMatrix 8)
    minorIndices8 minorIndices8 (rowMatrix (inverseRows8))
    radical8 radicalDual8 (by decide) minor8_checked
    radical8_checked.1 radical8_checked.2

theorem radical8_kernel :
    LinearMap.ker (Matrix.toBilin' (rootMatrix 8)) = familySpan radical8 := by
  rw [← root8_matrix, toBilin_kernel]
  have hs : (localMatrix 8).transpose = localMatrix 8 := by native_decide
  rw [hs]
  apply kernel_eq_familySpan (localMatrix 8).mulVecLin radical8
  · exact (packed_dual_witness radical8 radicalDual8 radical8_checked.1).1
  · exact radical8_checked.2
  · change (localMatrix 8).rank + 6 = 12
    rw [root8_matrix, root8_rank]

theorem radical8_dimension : finrank Field (familySpan radical8) = 6 :=
  (packed_dual_witness radical8 radicalDual8 radical8_checked.1).2

theorem localRadical_root8 (v : Vector 127)
    (hroot : rowMap localParameterRows v = (decodeMask 8 : Vector 15)) :
    CoveringLocal.localRadical (Matrix.toBilin' (coefficientMatrix matrixRows v)) =
      familySpan radical8 := by
  change LinearMap.ker (CoveringLocal.localForm
    (Matrix.toBilin' (coefficientMatrix matrixRows v))) = _
  rw [localForm_root 8 v hroot]
  exact radical8_kernel

theorem localRadical_root8_finrank (v : Vector 127)
    (hroot : rowMap localParameterRows v = (decodeMask 8 : Vector 15)) :
    finrank Field (CoveringLocal.localRadical
      (Matrix.toBilin' (coefficientMatrix matrixRows v))) = 6 := by
  rw [localRadical_root8 v hroot]
  exact radical8_dimension

theorem root12_matrix : localMatrix 12 = rootMatrix 12 := by
  native_decide

def minorIndices12 (i : Fin 10) : Fin 12 :=
  Fin.ofNat 12 ((#[2, 3, 4, 5, 6, 7, 8, 9, 10, 11][i.val]?).getD 0)

def inverseRows12 (i : Fin 10) : Nat :=
  (#[634, 277, 82, 33, 199, 9, 21, 16, 2, 1][i.val]?).getD 0

private theorem minor12_checked :
    (rowMatrix (inverseRows12) : Matrix (Fin 10) (Fin 10) Field) *
        (localMatrix 12).submatrix minorIndices12 minorIndices12 = 1 := by
  native_decide

theorem root12_rank_lower : 10 ≤ (rootMatrix 12).rank := by
  rw [← root12_matrix]
  exact matrix_rank_lower_of_minor (localMatrix 12)
    minorIndices12 minorIndices12 (rowMatrix (inverseRows12))
    minor12_checked

theorem root80_matrix : localMatrix 80 = rootMatrix 80 := by
  native_decide

def minorIndices80 (i : Fin 8) : Fin 12 :=
  Fin.ofNat 12 ((#[1, 2, 4, 5, 6, 7, 10, 11][i.val]?).getD 0)

def inverseRows80 (i : Fin 8) : Nat :=
  (#[128, 64, 40, 20, 8, 4, 2, 1][i.val]?).getD 0

private theorem minor80_checked :
    (rowMatrix (inverseRows80) : Matrix (Fin 8) (Fin 8) Field) *
        (localMatrix 80).submatrix minorIndices80 minorIndices80 = 1 := by
  native_decide

def radical80 (i : Fin 4) : Vector 12 :=
  decodeMask ((#[1, 8, 272, 512][i.val]?).getD 0)

def radicalDual80 (i : Fin 4) : Nat :=
  (#[1, 8, 16, 512][i.val]?).getD 0

theorem radical80_checked :
    (∀ i, rowMap radicalDual80 (radical80 i) = Pi.single i 1) ∧
      (∀ i, (localMatrix 80).mulVecLin (radical80 i) = 0) := by
  native_decide

theorem root80_rank : (rootMatrix 80).rank = 8 := by
  rw [← root80_matrix]
  exact matrix_rank_eq_of_minor_and_radical (localMatrix 80)
    minorIndices80 minorIndices80 (rowMatrix (inverseRows80))
    radical80 radicalDual80 (by decide) minor80_checked
    radical80_checked.1 radical80_checked.2

theorem radical80_kernel :
    LinearMap.ker (Matrix.toBilin' (rootMatrix 80)) = familySpan radical80 := by
  rw [← root80_matrix, toBilin_kernel]
  have hs : (localMatrix 80).transpose = localMatrix 80 := by native_decide
  rw [hs]
  apply kernel_eq_familySpan (localMatrix 80).mulVecLin radical80
  · exact (packed_dual_witness radical80 radicalDual80 radical80_checked.1).1
  · exact radical80_checked.2
  · change (localMatrix 80).rank + 4 = 12
    rw [root80_matrix, root80_rank]

theorem radical80_dimension : finrank Field (familySpan radical80) = 4 :=
  (packed_dual_witness radical80 radicalDual80 radical80_checked.1).2

theorem localRadical_root80 (v : Vector 127)
    (hroot : rowMap localParameterRows v = (decodeMask 80 : Vector 15)) :
    CoveringLocal.localRadical (Matrix.toBilin' (coefficientMatrix matrixRows v)) =
      familySpan radical80 := by
  change LinearMap.ker (CoveringLocal.localForm
    (Matrix.toBilin' (coefficientMatrix matrixRows v))) = _
  rw [localForm_root 80 v hroot]
  exact radical80_kernel

theorem localRadical_root80_finrank (v : Vector 127)
    (hroot : rowMap localParameterRows v = (decodeMask 80 : Vector 15)) :
    finrank Field (CoveringLocal.localRadical
      (Matrix.toBilin' (coefficientMatrix matrixRows v))) = 4 := by
  rw [localRadical_root80 v hroot]
  exact radical80_dimension

theorem root81_matrix : localMatrix 81 = rootMatrix 81 := by
  native_decide

def minorIndices81 (i : Fin 10) : Fin 12 :=
  Fin.ofNat 12 ((#[1, 2, 4, 5, 6, 7, 8, 9, 10, 11][i.val]?).getD 0)

def inverseRows81 (i : Fin 10) : Nat :=
  (#[520, 260, 170, 21, 8, 4, 128, 68, 2, 1][i.val]?).getD 0

private theorem minor81_checked :
    (rowMatrix (inverseRows81) : Matrix (Fin 10) (Fin 10) Field) *
        (localMatrix 81).submatrix minorIndices81 minorIndices81 = 1 := by
  native_decide

theorem root81_rank_lower : 10 ≤ (rootMatrix 81).rank := by
  rw [← root81_matrix]
  exact matrix_rank_lower_of_minor (localMatrix 81)
    minorIndices81 minorIndices81 (rowMatrix (inverseRows81))
    minor81_checked

theorem root88_matrix : localMatrix 88 = rootMatrix 88 := by
  native_decide

def minorIndices88 (i : Fin 8) : Fin 12 :=
  Fin.ofNat 12 ((#[1, 2, 4, 5, 6, 7, 10, 11][i.val]?).getD 0)

def inverseRows88 (i : Fin 8) : Nat :=
  (#[192, 64, 56, 20, 12, 4, 3, 1][i.val]?).getD 0

private theorem minor88_checked :
    (rowMatrix (inverseRows88) : Matrix (Fin 8) (Fin 8) Field) *
        (localMatrix 88).submatrix minorIndices88 minorIndices88 = 1 := by
  native_decide

def radical88 (i : Fin 4) : Vector 12 :=
  decodeMask ((#[1, 8, 496, 512][i.val]?).getD 0)

def radicalDual88 (i : Fin 4) : Nat :=
  (#[1, 8, 16, 512][i.val]?).getD 0

theorem radical88_checked :
    (∀ i, rowMap radicalDual88 (radical88 i) = Pi.single i 1) ∧
      (∀ i, (localMatrix 88).mulVecLin (radical88 i) = 0) := by
  native_decide

theorem root88_rank : (rootMatrix 88).rank = 8 := by
  rw [← root88_matrix]
  exact matrix_rank_eq_of_minor_and_radical (localMatrix 88)
    minorIndices88 minorIndices88 (rowMatrix (inverseRows88))
    radical88 radicalDual88 (by decide) minor88_checked
    radical88_checked.1 radical88_checked.2

theorem radical88_kernel :
    LinearMap.ker (Matrix.toBilin' (rootMatrix 88)) = familySpan radical88 := by
  rw [← root88_matrix, toBilin_kernel]
  have hs : (localMatrix 88).transpose = localMatrix 88 := by native_decide
  rw [hs]
  apply kernel_eq_familySpan (localMatrix 88).mulVecLin radical88
  · exact (packed_dual_witness radical88 radicalDual88 radical88_checked.1).1
  · exact radical88_checked.2
  · change (localMatrix 88).rank + 4 = 12
    rw [root88_matrix, root88_rank]

theorem radical88_dimension : finrank Field (familySpan radical88) = 4 :=
  (packed_dual_witness radical88 radicalDual88 radical88_checked.1).2

theorem localRadical_root88 (v : Vector 127)
    (hroot : rowMap localParameterRows v = (decodeMask 88 : Vector 15)) :
    CoveringLocal.localRadical (Matrix.toBilin' (coefficientMatrix matrixRows v)) =
      familySpan radical88 := by
  change LinearMap.ker (CoveringLocal.localForm
    (Matrix.toBilin' (coefficientMatrix matrixRows v))) = _
  rw [localForm_root 88 v hroot]
  exact radical88_kernel

theorem localRadical_root88_finrank (v : Vector 127)
    (hroot : rowMap localParameterRows v = (decodeMask 88 : Vector 15)) :
    finrank Field (CoveringLocal.localRadical
      (Matrix.toBilin' (coefficientMatrix matrixRows v))) = 4 := by
  rw [localRadical_root88 v hroot]
  exact radical88_dimension

theorem root89_matrix : localMatrix 89 = rootMatrix 89 := by
  native_decide

def minorIndices89 (i : Fin 10) : Fin 12 :=
  Fin.ofNat 12 ((#[1, 2, 4, 5, 6, 7, 8, 9, 10, 11][i.val]?).getD 0)

def inverseRows89 (i : Fin 10) : Nat :=
  (#[776, 388, 186, 149, 140, 132, 128, 126, 3, 1][i.val]?).getD 0

private theorem minor89_checked :
    (rowMatrix (inverseRows89) : Matrix (Fin 10) (Fin 10) Field) *
        (localMatrix 89).submatrix minorIndices89 minorIndices89 = 1 := by
  native_decide

theorem root89_rank_lower : 10 ≤ (rootMatrix 89).rank := by
  rw [← root89_matrix]
  exact matrix_rank_lower_of_minor (localMatrix 89)
    minorIndices89 minorIndices89 (rowMatrix (inverseRows89))
    minor89_checked

theorem root104_matrix : localMatrix 104 = rootMatrix 104 := by
  native_decide

def minorIndices104 (i : Fin 10) : Fin 12 :=
  Fin.ofNat 12 ((#[0, 2, 3, 4, 5, 6, 7, 8, 10, 11][i.val]?).getD 0)

def inverseRows104 (i : Fin 10) : Nat :=
  (#[768, 256, 192, 96, 64, 8, 156, 68, 3, 1][i.val]?).getD 0

private theorem minor104_checked :
    (rowMatrix (inverseRows104) : Matrix (Fin 10) (Fin 10) Field) *
        (localMatrix 104).submatrix minorIndices104 minorIndices104 = 1 := by
  native_decide

theorem root104_rank_lower : 10 ≤ (rootMatrix 104).rank := by
  rw [← root104_matrix]
  exact matrix_rank_lower_of_minor (localMatrix 104)
    minorIndices104 minorIndices104 (rowMatrix (inverseRows104))
    minor104_checked

theorem root522_matrix : localMatrix 522 = rootMatrix 522 := by
  native_decide

def minorIndices522 (i : Fin 10) : Fin 12 :=
  Fin.ofNat 12 ((#[0, 1, 2, 3, 4, 5, 6, 8, 10, 11][i.val]?).getD 0)

def inverseRows522 (i : Fin 10) : Nat :=
  (#[448, 32, 64, 576, 256, 2, 269, 1, 81, 8][i.val]?).getD 0

private theorem minor522_checked :
    (rowMatrix (inverseRows522) : Matrix (Fin 10) (Fin 10) Field) *
        (localMatrix 522).submatrix minorIndices522 minorIndices522 = 1 := by
  native_decide

theorem root522_rank_lower : 10 ≤ (rootMatrix 522).rank := by
  rw [← root522_matrix]
  exact matrix_rank_lower_of_minor (localMatrix 522)
    minorIndices522 minorIndices522 (rowMatrix (inverseRows522))
    minor522_checked

theorem root1184_matrix : localMatrix 1184 = rootMatrix 1184 := by
  native_decide

def minorIndices1184 (i : Fin 10) : Fin 12 :=
  Fin.ofNat 12 ((#[0, 1, 2, 3, 4, 5, 6, 9, 10, 11][i.val]?).getD 0)

def inverseRows1184 (i : Fin 10) : Nat :=
  (#[512, 256, 128, 32, 64, 8, 16, 4, 2, 1][i.val]?).getD 0

private theorem minor1184_checked :
    (rowMatrix (inverseRows1184) : Matrix (Fin 10) (Fin 10) Field) *
        (localMatrix 1184).submatrix minorIndices1184 minorIndices1184 = 1 := by
  native_decide

theorem root1184_rank_lower : 10 ≤ (rootMatrix 1184).rank := by
  rw [← root1184_matrix]
  exact matrix_rank_lower_of_minor (localMatrix 1184)
    minorIndices1184 minorIndices1184 (rowMatrix (inverseRows1184))
    minor1184_checked

theorem root1188_matrix : localMatrix 1188 = rootMatrix 1188 := by
  native_decide

def minorIndices1188 (i : Fin 10) : Fin 12 :=
  Fin.ofNat 12 ((#[0, 1, 2, 3, 4, 5, 6, 9, 10, 11][i.val]?).getD 0)

def inverseRows1188 (i : Fin 10) : Nat :=
  (#[590, 289, 209, 33, 68, 10, 21, 4, 2, 1][i.val]?).getD 0

private theorem minor1188_checked :
    (rowMatrix (inverseRows1188) : Matrix (Fin 10) (Fin 10) Field) *
        (localMatrix 1188).submatrix minorIndices1188 minorIndices1188 = 1 := by
  native_decide

theorem root1188_rank_lower : 10 ≤ (rootMatrix 1188).rank := by
  rw [← root1188_matrix]
  exact matrix_rank_lower_of_minor (localMatrix 1188)
    minorIndices1188 minorIndices1188 (rowMatrix (inverseRows1188))
    minor1188_checked

theorem root1192_matrix : localMatrix 1192 = rootMatrix 1192 := by
  native_decide

def minorIndices1192 (i : Fin 10) : Fin 12 :=
  Fin.ofNat 12 ((#[0, 1, 2, 3, 4, 5, 6, 9, 10, 11][i.val]?).getD 0)

def inverseRows1192 (i : Fin 10) : Nat :=
  (#[640, 256, 128, 32, 64, 8, 16, 5, 2, 1][i.val]?).getD 0

private theorem minor1192_checked :
    (rowMatrix (inverseRows1192) : Matrix (Fin 10) (Fin 10) Field) *
        (localMatrix 1192).submatrix minorIndices1192 minorIndices1192 = 1 := by
  native_decide

theorem root1192_rank_lower : 10 ≤ (rootMatrix 1192).rank := by
  rw [← root1192_matrix]
  exact matrix_rank_lower_of_minor (localMatrix 1192)
    minorIndices1192 minorIndices1192 (rowMatrix (inverseRows1192))
    minor1192_checked

theorem root1193_matrix : localMatrix 1193 = rootMatrix 1193 := by
  native_decide

def minorIndices1193 (i : Fin 10) : Fin 12 :=
  Fin.ofNat 12 ((#[0, 1, 2, 3, 4, 5, 6, 9, 10, 11][i.val]?).getD 0)

def inverseRows1193 (i : Fin 10) : Nat :=
  (#[656, 256, 128, 32, 65, 8, 16, 5, 2, 1][i.val]?).getD 0

private theorem minor1193_checked :
    (rowMatrix (inverseRows1193) : Matrix (Fin 10) (Fin 10) Field) *
        (localMatrix 1193).submatrix minorIndices1193 minorIndices1193 = 1 := by
  native_decide

theorem root1193_rank_lower : 10 ≤ (rootMatrix 1193).rank := by
  rw [← root1193_matrix]
  exact matrix_rank_lower_of_minor (localMatrix 1193)
    minorIndices1193 minorIndices1193 (rowMatrix (inverseRows1193))
    minor1193_checked

theorem root1400_matrix : localMatrix 1400 = rootMatrix 1400 := by
  native_decide

def minorIndices1400 (i : Fin 8) : Fin 12 :=
  Fin.ofNat 12 ((#[0, 1, 2, 3, 4, 9, 10, 11][i.val]?).getD 0)

def inverseRows1400 (i : Fin 8) : Nat :=
  (#[96, 192, 32, 16, 8, 5, 3, 2][i.val]?).getD 0

private theorem minor1400_checked :
    (rowMatrix (inverseRows1400) : Matrix (Fin 8) (Fin 8) Field) *
        (localMatrix 1400).submatrix minorIndices1400 minorIndices1400 = 1 := by
  native_decide

def radical1400 (i : Fin 4) : Vector 12 :=
  decodeMask ((#[392, 272, 160, 320][i.val]?).getD 0)

def radicalDual1400 (i : Fin 4) : Nat :=
  (#[8, 16, 32, 64][i.val]?).getD 0

theorem radical1400_checked :
    (∀ i, rowMap radicalDual1400 (radical1400 i) = Pi.single i 1) ∧
      (∀ i, (localMatrix 1400).mulVecLin (radical1400 i) = 0) := by
  native_decide

theorem root1400_rank : (rootMatrix 1400).rank = 8 := by
  rw [← root1400_matrix]
  exact matrix_rank_eq_of_minor_and_radical (localMatrix 1400)
    minorIndices1400 minorIndices1400 (rowMatrix (inverseRows1400))
    radical1400 radicalDual1400 (by decide) minor1400_checked
    radical1400_checked.1 radical1400_checked.2

theorem radical1400_kernel :
    LinearMap.ker (Matrix.toBilin' (rootMatrix 1400)) = familySpan radical1400 := by
  rw [← root1400_matrix, toBilin_kernel]
  have hs : (localMatrix 1400).transpose = localMatrix 1400 := by native_decide
  rw [hs]
  apply kernel_eq_familySpan (localMatrix 1400).mulVecLin radical1400
  · exact (packed_dual_witness radical1400 radicalDual1400 radical1400_checked.1).1
  · exact radical1400_checked.2
  · change (localMatrix 1400).rank + 4 = 12
    rw [root1400_matrix, root1400_rank]

theorem radical1400_dimension : finrank Field (familySpan radical1400) = 4 :=
  (packed_dual_witness radical1400 radicalDual1400 radical1400_checked.1).2

theorem localRadical_root1400 (v : Vector 127)
    (hroot : rowMap localParameterRows v = (decodeMask 1400 : Vector 15)) :
    CoveringLocal.localRadical (Matrix.toBilin' (coefficientMatrix matrixRows v)) =
      familySpan radical1400 := by
  change LinearMap.ker (CoveringLocal.localForm
    (Matrix.toBilin' (coefficientMatrix matrixRows v))) = _
  rw [localForm_root 1400 v hroot]
  exact radical1400_kernel

theorem localRadical_root1400_finrank (v : Vector 127)
    (hroot : rowMap localParameterRows v = (decodeMask 1400 : Vector 15)) :
    finrank Field (CoveringLocal.localRadical
      (Matrix.toBilin' (coefficientMatrix matrixRows v))) = 4 := by
  rw [localRadical_root1400 v hroot]
  exact radical1400_dimension

theorem root1550_matrix : localMatrix 1550 = rootMatrix 1550 := by
  native_decide

def minorIndices1550 (i : Fin 10) : Fin 12 :=
  Fin.ofNat 12 ((#[0, 1, 2, 3, 4, 5, 6, 7, 8, 9][i.val]?).getD 0)

def inverseRows1550 (i : Fin 10) : Nat :=
  (#[320, 124, 594, 130, 582, 2, 535, 8, 1, 84][i.val]?).getD 0

private theorem minor1550_checked :
    (rowMatrix (inverseRows1550) : Matrix (Fin 10) (Fin 10) Field) *
        (localMatrix 1550).submatrix minorIndices1550 minorIndices1550 = 1 := by
  native_decide

theorem root1550_rank_lower : 10 ≤ (rootMatrix 1550).rank := by
  rw [← root1550_matrix]
  exact matrix_rank_lower_of_minor (localMatrix 1550)
    minorIndices1550 minorIndices1550 (rowMatrix (inverseRows1550))
    minor1550_checked

theorem root1573_matrix : localMatrix 1573 = rootMatrix 1573 := by
  native_decide

def minorIndices1573 (i : Fin 10) : Fin 12 :=
  Fin.ofNat 12 ((#[0, 1, 2, 3, 4, 5, 6, 7, 8, 11][i.val]?).getD 0)

def inverseRows1573 (i : Fin 10) : Nat :=
  (#[604, 240, 17, 209, 847, 2, 795, 10, 80, 81][i.val]?).getD 0

private theorem minor1573_checked :
    (rowMatrix (inverseRows1573) : Matrix (Fin 10) (Fin 10) Field) *
        (localMatrix 1573).submatrix minorIndices1573 minorIndices1573 = 1 := by
  native_decide

theorem root1573_rank_lower : 10 ≤ (rootMatrix 1573).rank := by
  rw [← root1573_matrix]
  exact matrix_rank_lower_of_minor (localMatrix 1573)
    minorIndices1573 minorIndices1573 (rowMatrix (inverseRows1573))
    minor1573_checked

theorem root1580_matrix : localMatrix 1580 = rootMatrix 1580 := by
  native_decide

def minorIndices1580 (i : Fin 10) : Fin 12 :=
  Fin.ofNat 12 ((#[0, 1, 2, 3, 4, 5, 6, 7, 8, 11][i.val]?).getD 0)

def inverseRows1580 (i : Fin 10) : Nat :=
  (#[322, 249, 64, 210, 778, 2, 783, 10, 81, 80][i.val]?).getD 0

private theorem minor1580_checked :
    (rowMatrix (inverseRows1580) : Matrix (Fin 10) (Fin 10) Field) *
        (localMatrix 1580).submatrix minorIndices1580 minorIndices1580 = 1 := by
  native_decide

theorem root1580_rank_lower : 10 ≤ (rootMatrix 1580).rank := by
  rw [← root1580_matrix]
  exact matrix_rank_lower_of_minor (localMatrix 1580)
    minorIndices1580 minorIndices1580 (rowMatrix (inverseRows1580))
    minor1580_checked

def representatives : List Nat := [0, 1, 8, 12, 80, 81, 88, 89, 104, 522, 1184, 1188, 1192, 1193, 1400, 1550, 1573, 1580]

def lowRepresentatives : List Nat := [0, 1, 8, 80, 88, 1400]

def highRepresentatives : List Nat := [12, 81, 89, 104, 522, 1184, 1188, 1192, 1193, 1550, 1573, 1580]

theorem matrices_correct (root : Nat) (hroot : root ∈ representatives) :
    localMatrix root = rootMatrix root := by
  simp only [representatives, List.mem_cons, List.mem_nil_iff, or_false] at hroot
  rcases hroot with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact root0_matrix
  · exact root1_matrix
  · exact root8_matrix
  · exact root12_matrix
  · exact root80_matrix
  · exact root81_matrix
  · exact root88_matrix
  · exact root89_matrix
  · exact root104_matrix
  · exact root522_matrix
  · exact root1184_matrix
  · exact root1188_matrix
  · exact root1192_matrix
  · exact root1193_matrix
  · exact root1400_matrix
  · exact root1550_matrix
  · exact root1573_matrix
  · exact root1580_matrix

theorem high_ranks (root : Nat) (hroot : root ∈ highRepresentatives) :
    10 ≤ (rootMatrix root).rank := by
  simp only [highRepresentatives, List.mem_cons, List.mem_nil_iff, or_false] at hroot
  rcases hroot with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact root12_rank_lower
  · exact root81_rank_lower
  · exact root89_rank_lower
  · exact root104_rank_lower
  · exact root522_rank_lower
  · exact root1184_rank_lower
  · exact root1188_rank_lower
  · exact root1192_rank_lower
  · exact root1193_rank_lower
  · exact root1550_rank_lower
  · exact root1573_rank_lower
  · exact root1580_rank_lower

end Lemmata.CocubicCovering.CoveringLocalRanks
