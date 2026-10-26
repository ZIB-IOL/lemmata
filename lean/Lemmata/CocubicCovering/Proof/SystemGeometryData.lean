module

public import Lemmata.CocubicCovering.Proof.LevelSixSystemData
public meta import Lemmata.CocubicCovering.Proof.LevelSixSystemData
public import Lemmata.CocubicCovering.Proof.LevelSixReduction
public meta import Lemmata.CocubicCovering.Proof.LevelSixReduction
public import Lemmata.CocubicCovering.Proof.RankWitness
public meta import Lemmata.CocubicCovering.Proof.RankWitness

@[expose] public section

set_option Elab.async false

namespace Lemmata.CocubicCovering.CoveringSystemGeometryData

open Module Covering CoveringAffine CoveringBits CoveringCongruence CoveringPolynomial
open CoveringWitness CoveringPackedAction CoveringPackedPair
open CoveringLevelSixReconstruction CoveringLevelSixSystems
open scoped BigOperators

def nondegenerateData : List (List Nat) := [
  [0x1, 0x2, 0x4, 0x8, 0x10, 0x20, 0x40, 0x80, 0x100, 0x800],
  [0x1, 0x2, 0x4, 0x8, 0x10, 0x20, 0x40, 0x80, 0x100, 0x400],
  [0x1, 0x2, 0x4, 0x8, 0x10, 0x20, 0x40, 0x80, 0x100, 0x400],
  [0x1, 0x2, 0x4, 0x8, 0x10, 0x40, 0x80, 0x100],
  [0x1, 0x2, 0x4, 0x8, 0x10, 0x20, 0x40, 0x80, 0x100, 0x200],
  [0x1, 0x2, 0x4, 0x8, 0x10, 0x20, 0x40, 0x80],
  [0x1, 0x2, 0x4, 0x8, 0x10, 0x20, 0x40, 0x80, 0x100, 0x400],
  [0x1, 0x2, 0x4, 0x8, 0x10, 0x20, 0x40, 0x80],
  [0x1, 0x2, 0x4, 0x8, 0x10, 0x20, 0x40, 0x80],
  [0x1, 0x2, 0x4, 0x8, 0x10, 0x40],
  [0x1, 0x2, 0x4, 0x8, 0x10, 0x40],
  [],
  []
]

def complementData : List (List Nat) := [
  [],
  [],
  [],
  [0x942],
  [],
  [0x421],
  [],
  [0x131],
  [0x131],
  [0x421, 0x102],
  [0x421, 0x102],
  [0x1, 0x2, 0x4, 0x8, 0x20],
  [0x1, 0x4, 0x8, 0x10, 0x100]
]

def dualData : List (List Nat) := [
  [0x10000, 0x8000],
  [0x20000, 0x8000],
  [0x20000, 0x8000],
  [0x10000, 0x8000, 0x20, 0x30000],
  [0x20000, 0x10000],
  [0x20000, 0x20800, 0x8000, 0x30800],
  [0x20000, 0x8000],
  [0x20000, 0x10000, 0x8000, 0x18800],
  [0x20000, 0x10000, 0x8000, 0x38800],
  [0x20000, 0x400, 0x8000, 0x38420, 0x10400, 0x38c20],
  [0x20000, 0x400, 0x8000, 0x10420, 0x10400, 0xc00],
  [0x20000, 0x10000, 0x8000, 0x800, 0x400, 0x200, 0x10, 0x8011, 0xe02, 0xc14, 0xc18, 0x20],
  [0x20000, 0x10000, 0x8000, 0x400, 0x200, 0x20, 0x2, 0x623, 0x204, 0x8, 0x230, 0x800]
]

def spanningData : List (List Nat) := [
  [0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0xc, 0xd, 0xe, 0x6, 0x7, 0x8, 0xf, 0x10, 0x11, 0x9, 0xa, 0xb, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19, 0x1a],
  [0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0xc, 0xd, 0xe, 0x6, 0x7, 0x8, 0xf, 0x10, 0x11, 0x9, 0xa, 0xb, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19, 0x1a],
  [0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0xc, 0xd, 0xe, 0x6, 0x7, 0x8, 0xf, 0x10, 0x11, 0x9, 0xa, 0xb, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19, 0x1a],
  [0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0xc, 0xd, 0xe, 0x6, 0x7, 0x8, 0xf, 0x10, 0x11, 0x9, 0xa, 0xb, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19, 0x1a],
  [0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0xc, 0xd, 0xe, 0x6, 0x7, 0x8, 0xf, 0x10, 0x11, 0x9, 0xa, 0xb, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19, 0x1a],
  [0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0xc, 0xd, 0xe, 0x6, 0x7, 0x8, 0xf, 0x10, 0x11, 0x9, 0xa, 0xb, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19, 0x1a],
  [0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0xc, 0xd, 0xe, 0x6, 0x7, 0x8, 0xf, 0x10, 0x11, 0x9, 0xa, 0xb, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19, 0x1a],
  [0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0xc, 0xd, 0xe, 0x6, 0x7, 0x8, 0xf, 0x10, 0x11, 0x9, 0xa, 0xb, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19, 0x1a],
  [0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0xc, 0xd, 0xe, 0x6, 0x7, 0x8, 0xf, 0x10, 0x11, 0x9, 0xa, 0xb, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19, 0x1a],
  [0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0xc, 0xd, 0xe, 0x6, 0x7, 0x8, 0xf, 0x10, 0x11, 0x9, 0xa, 0xb, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19, 0x1a],
  [0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0xc, 0xd, 0xe, 0x6, 0x7, 0x8, 0xf, 0x10, 0x11, 0x9, 0xa, 0xb, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19, 0x1a],
  [0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0xc, 0xd, 0xe, 0x6, 0x7, 0x8, 0xf, 0x10, 0x11, 0x9, 0xa, 0xb, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19, 0x1a],
  [0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0xc, 0xd, 0xe, 0x6, 0x7, 0x8, 0xf, 0x10, 0x11, 0x9, 0xa, 0xb, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19, 0x1a]
]

def localData : List (List Nat) := [
  [0x40, 0x8, 0x8b0, 0x2, 0x104, 0x84, 0x1, 0x24, 0x10, 0x0, 0x0, 0x4],
  [0x40, 0x808, 0x8b0, 0x902, 0x584, 0x284, 0x81, 0x174, 0x98, 0x20, 0x10, 0xe],
  [0x40, 0x808, 0xb0, 0x502, 0xa84, 0x804, 0x281, 0x954, 0x688, 0x150, 0x108, 0xb2],
  [0x840, 0x8, 0x4b0, 0x122, 0x144, 0x14c, 0x31, 0x4, 0x38, 0x0, 0x4, 0x1],
  [0x840, 0x8, 0x4b0, 0x522, 0xb44, 0x94c, 0xa31, 0xc04, 0x438, 0x50, 0x18c, 0xf1],
  [0x40, 0x808, 0x4b0, 0x2, 0x84, 0x44, 0xa1, 0x154, 0x80, 0x0, 0x4, 0x2],
  [0x40, 0x808, 0x4b0, 0x802, 0x484, 0x244, 0x8a1, 0x554, 0x280, 0x120, 0x94, 0x4a],
  [0x40, 0x808, 0x4b0, 0xc02, 0xe84, 0xa44, 0xaa1, 0xd54, 0x480, 0x70, 0x19c, 0xfa],
  [0x40, 0x808, 0x4b0, 0xc02, 0xe84, 0xa44, 0xaa1, 0xd54, 0x480, 0x70, 0x19c, 0xfa],
  [0x40, 0x8, 0x4b0, 0x102, 0x4, 0x44, 0x21, 0x4, 0x8, 0x0, 0x4, 0x0],
  [0x40, 0x8, 0x4b0, 0x102, 0x4, 0x44, 0x21, 0x4, 0x8, 0x0, 0x4, 0x0],
  [0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0],
  [0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0]
]

def coreCount (s : Fin 13) : Nat := (core s).length
def coreMask (s : Fin 13) (i : Fin (coreCount s)) : Nat := (core s).get i
def nondegenerate (s : Fin 13) (i : Fin (localRank s)) : Nat :=
  (nondegenerateData[s.val]?.getD [])[i.val]?.getD 0
def complement (s : Fin 13) (i : Fin (crossRank s)) : Nat :=
  (complementData[s.val]?.getD [])[i.val]?.getD 0
def localRows (s : Fin 13) (i : Fin 12) : Nat := (localData[s.val]?.getD [])[i.val]?.getD 0

def embed (mask : Nat) : Vector 27 := decodeMask (composeRow mask wCoordinates)
def coreVector (s : Fin 13) (i : Fin (coreCount s)) : Vector 27 := embed (coreMask s i)
def complementVector (s : Fin 13) (i : Fin (crossRank s)) : Vector 27 := embed (complement s i)
def nondegenerateVector (s : Fin 13) (i : Fin (localRank s)) : Vector 27 := embed (nondegenerate s i)
def outsideVector (s : Fin 13) (i : Fin 15) : Vector 27 := decodeMask (outsideBasis s i)

def W : Submodule Field (Vector 27) := LinearMap.range CoveringLevelSixReduction.localEmbedding
def coreSpace (s : Fin 13) : Submodule Field (Vector 27) := familySpan (coreVector s)
def H (s : Fin 13) : Submodule Field (Vector 27) := familySpan (complementVector s)

def combinedVector (s : Fin 13) : Fin (coreCount s) ⊕ Fin (crossRank s) → Vector 27 :=
  Sum.elim (coreVector s) (complementVector s)

def dualRow (s : Fin 13) (i : Fin (coreCount s) ⊕ Fin (crossRank s)) : Nat :=
  (dualData[s.val]?.getD [])[(finSumFinEquiv i).val]?.getD 0

def combinedDual (s : Fin 13) : Vector 27 →ₗ[Field] (Fin (coreCount s) ⊕ Fin (crossRank s) → Field) where
  toFun v i := evalRow (dualRow s i) v
  map_add' v w := by funext i; exact evalRow_add (dualRow s i) v w
  map_smul' a v := by funext i; exact evalRow_smul (dualRow s i) a v

def localBlock (s : Fin 13) : Matrix (Fin (localRank s)) (Fin (localRank s)) Field :=
  fun i j => ofBool (pairBit (localRows s) (nondegenerate s i) (nondegenerate s j))

def inverseMatrix (s : Fin 13) : Matrix (Fin (localRank s)) (Fin (localRank s)) Field :=
  fun i j => ofBool (inverse s i j)

def spanningIndex (s : Fin 13) (i : Fin 27) : Fin 12 ⊕ Fin 15 :=
  finSumFinEquiv.symm (Fin.ofNat 27 ((spanningData[s.val]?.getD [])[i.val]?.getD 0))

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

private theorem embedding_basis : ∀ i : Fin 12,
    CoveringLevelSixReduction.localEmbedding (Pi.single i 1) = decodeMask (wCoordinates i) := by
  native_decide

theorem localEmbedding_eq_family : CoveringLevelSixReduction.localEmbedding =
    familyLinear (fun i : Fin 12 => (decodeMask (wCoordinates i) : Vector 27)) := by
  apply (Pi.basisFun Field (Fin 12)).ext
  intro i
  simpa only [Pi.basisFun_apply, familyLinear, Fintype.linearCombination_apply_single, one_smul]
    using embedding_basis i

theorem embedding_mask (mask : Nat) :
    CoveringLevelSixReduction.localEmbedding (decodeMask mask) = embed mask := by
  rw [localEmbedding_eq_family, embed, decodeMask_composeRow_familyLinear]

theorem embed_mem_W (mask : Nat) : embed mask ∈ W :=
  ⟨decodeMask mask, embedding_mask mask⟩

def Checked (s : Fin 13) : Prop :=
  (∀ i, combinedDual s (combinedVector s i) = Pi.single i 1) ∧
  (bitMatrix (localRows s) = CoveringLocalRanks.rootMatrix (restriction s)) ∧
  (inverseMatrix s * localBlock s = 1) ∧ (localBlock s * inverseMatrix s = 1) ∧
  (∀ (i : Fin (crossRank s)) (j : Fin 12),
    pairBit (localRows s) (complement s i) (2 ^ j.val) = false) ∧
  (∀ i : Fin (localRank s), decodeMask (crossBasis s (Fin.castAdd (crossRank s) i)) =
    nondegenerateVector s i) ∧
  (∀ i : Fin (crossRank s), decodeMask (crossBasis s (Fin.natAdd (localRank s) i)) =
    complementVector s i) ∧
  (∀ i : Fin 27, Sum.elim (fun j : Fin 12 =>
    CoveringLevelSixReduction.localEmbedding (Pi.single j 1)) (outsideVector s)
      (spanningIndex s i) = Pi.single i 1)

private theorem checked0 : Checked 0 := by
  unfold Checked
  native_decide

private theorem checked1 : Checked 1 := by
  unfold Checked
  native_decide

private theorem checked2 : Checked 2 := by
  unfold Checked
  native_decide

private theorem checked3 : Checked 3 := by
  unfold Checked
  native_decide

private theorem checked4 : Checked 4 := by
  unfold Checked
  native_decide

private theorem checked5 : Checked 5 := by
  unfold Checked
  native_decide

private theorem checked6 : Checked 6 := by
  unfold Checked
  native_decide

private theorem checked7 : Checked 7 := by
  unfold Checked
  native_decide

private theorem checked8 : Checked 8 := by
  unfold Checked
  native_decide

private theorem checked9 : Checked 9 := by
  unfold Checked
  native_decide

private theorem checked10 : Checked 10 := by
  unfold Checked
  native_decide

private theorem checked11 : Checked 11 := by
  unfold Checked
  native_decide

private theorem checked12 : Checked 12 := by
  unfold Checked
  native_decide

theorem checked (s : Fin 13) : Checked s := by
  fin_cases s
  · exact checked0
  · exact checked1
  · exact checked2
  · exact checked3
  · exact checked4
  · exact checked5
  · exact checked6
  · exact checked7
  · exact checked8
  · exact checked9
  · exact checked10
  · exact checked11
  · exact checked12

theorem combined_injective (s : Fin 13) : Function.Injective (familyLinear (combinedVector s)) :=
  injective_of_dual (combinedVector s) (combinedDual s) (checked s).1

theorem complement_injective (s : Fin 13) : Function.Injective (familyLinear (complementVector s)) := by
  have hsum := (familyLinear_injective_iff (combinedVector s)).mp (combined_injective s)
  have hpart := (linearIndependent_sum.mp hsum).2.1
  apply (familyLinear_injective_iff (complementVector s)).mpr
  simpa only [combinedVector, Function.comp_def, Sum.elim_inr] using hpart

theorem complement_disjoint_core (s : Fin 13) : H s ⊓ coreSpace s = ⊥ :=
  (combined_family (coreVector s) (complementVector s) (combined_injective s)).1

theorem core_mem_W (s : Fin 13) (i : Fin (coreCount s)) : coreVector s i ∈ W :=
  embed_mem_W _

theorem complement_mem_W (s : Fin 13) (i : Fin (crossRank s)) : complementVector s i ∈ W :=
  embed_mem_W _

theorem W_outside_spanning (s : Fin 13) : W ⊔ familySpan (outsideVector s) = ⊤ := by
  have hunit : ∀ i : Fin 27, Pi.single i (1 : Field) ∈ W ⊔ familySpan (outsideVector s) := by
    intro i
    rw [← (checked s).2.2.2.2.2.2.2 i]
    cases spanningIndex s i with
    | inl j => exact Submodule.mem_sup_left ⟨Pi.single j 1, rfl⟩
    | inr j => exact Submodule.mem_sup_right (Submodule.subset_span ⟨j, rfl⟩)
  apply top_unique
  intro x hx
  rw [← (Pi.basisFun Field (Fin 27)).sum_repr x]
  apply Submodule.sum_mem
  intro i hi
  exact Submodule.smul_mem _ _ (by simpa only [Pi.basisFun_apply] using hunit i)

private theorem parameter_rows : ∀ i : Fin 15,
    CoveringLocalRanks.localParameterRows i = 2 ^ (111 + i.val) := by native_decide

theorem projection_of_local (s : Fin 13) (v : Vector 127)
    (hlocal : ∀ i : Fin 15, v ⟨111 + i.val, by omega⟩ = ofBool ((restriction s).testBit i.val)) :
    rowMap CoveringLocalRanks.localParameterRows v = (decodeMask (restriction s) : Vector 15) := by
  funext i
  change evalRow (CoveringLocalRanks.localParameterRows i) v = _
  rw [parameter_rows, CoveringEncoding.evalRow_two_pow ⟨111 + i.val, by omega⟩ v]
  exact hlocal i

theorem localGram (s : Fin 13) (v : Vector 127)
    (hlocal : ∀ i : Fin 15, v ⟨111 + i.val, by omega⟩ = ofBool ((restriction s).testBit i.val)) :
    gram (CoveringLevelSixReduction.fullForm v) CoveringLevelSixReduction.localEmbedding =
      Matrix.toBilin' (bitMatrix (localRows s)) := by
  change CoveringLocal.localForm
    (gram (CoveringLevelSixReduction.fullForm v) CoveringLevelSixReduction.commonEmbedding) = _
  rw [CoveringLevelSixReduction.common_restriction, (checked s).2.1]
  exact CoveringLocalRanks.localForm_root (restriction s) v (projection_of_local s v hlocal)

private theorem kernel_of_pairBit (rows : Fin 12 → Nat) (mask : Nat)
    (hzero : ∀ j : Fin 12, pairBit rows mask (2 ^ j.val) = false) :
    Matrix.toBilin' (bitMatrix rows) (decodeMask mask) = 0 := by
  apply (Pi.basisFun Field (Fin 12)).ext
  intro j
  have hsingle : (decodeMask (2 ^ j.val) : Vector 12) = Pi.single j 1 := by
    funext k
    by_cases h : j = k
    · subst k
      simp [decodeMask, Nat.testBit_two_pow, Pi.single_apply]
    · have hv : j.val ≠ k.val := fun he => h (Fin.ext he)
      simp [decodeMask, Nat.testBit_two_pow, Pi.single_apply, h, hv, Ne.symm h]
  have h := ofBool_pairBit rows mask (2 ^ j.val)
  rw [hzero j, ofBool_false, hsingle] at h
  simpa only [Pi.basisFun_apply, LinearMap.zero_apply] using h.symm

theorem complement_orthogonal_W (s : Fin 13) (v : Vector 127)
    (hlocal : ∀ i : Fin 15, v ⟨111 + i.val, by omega⟩ = ofBool ((restriction s).testBit i.val))
    (i : Fin (crossRank s)) (w : Vector 27) (hw : w ∈ W) :
    CoveringLevelSixReduction.fullForm v (complementVector s i) w = 0 := by
  obtain ⟨u, rfl⟩ := hw
  change CoveringLevelSixReduction.fullForm v (embed (complement s i))
    (CoveringLevelSixReduction.localEmbedding u) = 0
  rw [← embedding_mask]
  change gram (CoveringLevelSixReduction.fullForm v) CoveringLevelSixReduction.localEmbedding
    (decodeMask (complement s i)) u = 0
  rw [localGram s v hlocal]
  exact LinearMap.congr_fun
    (kernel_of_pairBit (localRows s) (complement s i) ((checked s).2.2.2.2.1 i)) u

theorem actual_localBlock (s : Fin 13) (v : Vector 127)
    (hlocal : ∀ i : Fin 15, v ⟨111 + i.val, by omega⟩ = ofBool ((restriction s).testBit i.val))
    (i j : Fin (localRank s)) :
    CoveringLevelSixReduction.fullForm v (nondegenerateVector s i) (nondegenerateVector s j) =
      localBlock s i j := by
  change CoveringLevelSixReduction.fullForm v (embed (nondegenerate s i)) (embed (nondegenerate s j)) = _
  rw [← embedding_mask, ← embedding_mask]
  change gram (CoveringLevelSixReduction.fullForm v) CoveringLevelSixReduction.localEmbedding
    (decodeMask (nondegenerate s i)) (decodeMask (nondegenerate s j)) = _
  rw [localGram s v hlocal]
  exact (ofBool_pairBit _ _ _).symm

theorem inverse_left (s : Fin 13) : inverseMatrix s * localBlock s = 1 := (checked s).2.2.1
theorem inverse_right (s : Fin 13) : localBlock s * inverseMatrix s = 1 := (checked s).2.2.2.1
theorem native_nondegenerate (s : Fin 13) (i : Fin (localRank s)) :
    decodeMask (crossBasis s (Fin.castAdd (crossRank s) i)) = nondegenerateVector s i :=
  (checked s).2.2.2.2.2.1 i
theorem native_complement (s : Fin 13) (i : Fin (crossRank s)) :
    decodeMask (crossBasis s (Fin.natAdd (localRank s) i)) = complementVector s i :=
  (checked s).2.2.2.2.2.2.1 i

theorem local_dimensions (s : Fin 13) : localRank s + coreCount s + crossRank s = 12 := by
  fin_cases s <;> native_decide

theorem core_local_radical (s : Fin 13) (i : Fin (coreCount s)) :
    Matrix.toBilin' (bitMatrix (localRows s)) (decodeMask (coreMask s i)) = 0 := by
  have hzero : ∀ (s : Fin 13) (i : Fin (coreCount s)) (j : Fin 12),
      pairBit (localRows s) (coreMask s i) (2 ^ j.val) = false := by
    intro s
    fin_cases s <;> native_decide
  exact kernel_of_pairBit (localRows s) (coreMask s i) (hzero s i)

end Lemmata.CocubicCovering.CoveringSystemGeometryData
