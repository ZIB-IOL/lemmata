module

public import Lemmata.CocubicCovering.Proof.Affine
public meta import Lemmata.CocubicCovering.Proof.Affine
public import Lemmata.CocubicCovering.Proof.Encoding
public meta import Lemmata.CocubicCovering.Proof.Encoding
public import Lemmata.CocubicCovering.Proof.Matrix
public meta import Lemmata.CocubicCovering.Proof.Matrix
public import Lemmata.CocubicCovering.Proof.CovarianceData
public meta import Lemmata.CocubicCovering.Proof.CovarianceData

@[expose] public section

set_option Elab.async false

namespace Lemmata.CocubicCovering.CoveringPackedLeaf

open CoveringAffine CoveringEncoding CoveringPolynomial CoveringCovarianceData

def kernelRow (mask : ℕ) (column : Fin 24) : ℕ :=
  composeRow mask fun i : Fin 12 => matrixRows (CoveringMatrix.localInclusion i) column

def sourceRow (root : ℕ) (path : List ℕ) (source : ℕ) : ℕ :=
  if source < 15 then
    (2 ^ (111 + source)) ^^^ (if root.testBit source then 2 ^ 126 else 0)
  else
    match path[(source - 15) / 24]? with
    | none => 0
    | some mask => kernelRow mask ⟨(source - 15) % 24, Nat.mod_lt _ (by decide)⟩

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
    cases hp : path[(source - 15) / 24]? with
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

end Lemmata.CocubicCovering.CoveringPackedLeaf
