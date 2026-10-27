module

public import Lemmata.CocubicCovering.Proof.Affine
public meta import Lemmata.CocubicCovering.Proof.Affine
public import Lemmata.CocubicCovering.Proof.Encoding
public meta import Lemmata.CocubicCovering.Proof.Encoding
public import Lemmata.CocubicCovering.Proof.LevelSixReduction
public meta import Lemmata.CocubicCovering.Proof.LevelSixReduction

@[expose] public section

set_option Elab.async false

namespace Lemmata.CocubicCovering.CoveringLevelSixLeaf

open scoped BigOperators
open CoveringAffine CoveringEncoding CoveringPolynomial

def kernelRow (mask : ℕ) (column : Fin 27) : ℕ :=
  composeRow mask fun i : Fin 12 => CoveringLevelSix.matrixRows (Fin.castAdd 3 (CoveringMatrix.localInclusion i)) column

theorem localEmbedding_pairing (B : LinearMap.BilinForm Field (Vector 27))
    (a : Vector 12) (w : Vector 27) :
    B (CoveringLevelSixReduction.localEmbedding a) w =
      ∑ i : Fin 12, a i *
        B (Pi.single (Fin.castAdd 3 (CoveringMatrix.localInclusion i)) 1) w := by
  simp only [CoveringLevelSixReduction.localEmbedding, LinearMap.comp_apply,
    CoveringLocal.localEmbedding, Fintype.linearCombination_apply, map_sum, map_smul,
    LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    CoveringLevelSixReduction.commonEmbedding_basis]

theorem kernelRow_zero (v : Vector 127) (mask : ℕ)
    (hmask : CoveringBits.decodeMask mask ∈ CoveringLevelSixReduction.fullKernel v)
    (column : Fin 27) : evalRow (kernelRow mask column) v = 0 := by
  have he : evalRow (kernelRow mask column) v =
      CoveringLevelSixReduction.fullForm v
        (CoveringLevelSixReduction.localEmbedding (CoveringBits.decodeMask mask))
        (Pi.single column 1) := by
    rw [kernelRow, evalRow_composeRow, localEmbedding_pairing]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [CoveringLevelSixReduction.fullForm, Matrix.toBilin'_single,
      CoveringCongruence.coefficientMatrix, CoveringBits.decodeMask]
    cases (mask.testBit i.val) <;> simp <;> rfl
  rw [he]
  change CoveringLevelSixReduction.fullForm v
    (CoveringLevelSixReduction.localEmbedding (CoveringBits.decodeMask mask)) = 0 at hmask
  exact LinearMap.congr_fun hmask (Pi.single column 1)

def sourceRow (root : ℕ) (path : List ℕ) (source : ℕ) : ℕ :=
  if source < 15 then
    (2 ^ (111 + source)) ^^^ (if root.testBit source then 2 ^ 126 else 0)
  else
    match path[(source - 15) / 27]? with
    | none => 0
    | some mask => kernelRow mask ⟨(source - 15) % 27, Nat.mod_lt _ (by decide)⟩

def check (root : ℕ) (path selected : List ℕ) : Bool :=
  decide (xorRows (selected.map (sourceRow root path)) = 2 ^ 126)

theorem sourceRow_zero (root : ℕ) (path : List ℕ) (v : Vector 127)
    (hpoint : v (Fin.last 126) = 1)
    (hroot : ∀ i : Fin 15, v ⟨111 + i.val, by omega⟩ = ofBool (root.testBit i.val))
    (hpath : ∀ mask ∈ path, ∀ column, evalRow (kernelRow mask column) v = 0)
    (source : ℕ) : evalRow (sourceRow root path source) v = 0 := by
  by_cases hs : source < 15
  · simp only [sourceRow, hs, ↓reduceIte, evalRow_xor]
    have hparameter := hroot ⟨source, hs⟩
    have he : evalRow (2 ^ (111 + source)) v = ofBool (root.testBit source) := by
      rw [evalRow_two_pow (⟨111 + source, by omega⟩ : Fin 127)]
      exact hparameter
    rw [he]
    cases root.testBit source
    · change (0 : Field) + evalRow 0 v = 0
      rw [evalRow_zero]
      rfl
    · change (1 : Field) + evalRow (2 ^ 126) v = 0
      have hc : evalRow (2 ^ 126) v = 1 :=
        (evalRow_two_pow (Fin.last 126) v).trans hpoint
      rw [hc]
      decide
  · simp only [sourceRow, hs, ↓reduceIte]
    cases hp : path[(source - 15) / 27]? with
    | none => exact evalRow_zero v
    | some mask =>
        exact hpath mask (List.mem_of_getElem? hp) _

theorem check_sound (root : ℕ) (path selected : List ℕ)
    (accepted : check root path selected = true) :
    ¬∃ v : Vector 127, v (Fin.last 126) = 1 ∧
      (∀ i : Fin 15, v ⟨111 + i.val, by omega⟩ = ofBool (root.testBit i.val)) ∧
      (∀ mask ∈ path, ∀ column, evalRow (kernelRow mask column) v = 0) := by
  rintro ⟨v, hpoint, hroot, hpath⟩
  have he : xorRows (selected.map (sourceRow root path)) = 2 ^ 126 :=
    of_decide_eq_true accepted
  have hz : evalRow (xorRows (selected.map (sourceRow root path))) v = 0 := by
    rw [evalRow_xorRows, List.map_map]
    apply List.sum_eq_zero
    intro row hrow
    obtain ⟨source, _, rfl⟩ := List.mem_map.mp hrow
    exact sourceRow_zero root path v hpoint hroot hpath source
  rw [he] at hz
  have hc : evalRow (2 ^ 126) v = 1 :=
    (evalRow_two_pow (Fin.last 126) v).trans hpoint
  exact one_ne_zero (hc.symm.trans hz)

end Lemmata.CocubicCovering.CoveringLevelSixLeaf
