module

public import Lemmata.RM59.Compute.BinaryValues
public meta import Lemmata.RM59.Compute.BinaryValues
public import Lemmata.RM59.Proof.CatalogCompute
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.List.Range
public import Init.Data.Array.OfFn
public import Lean.Elab.Tactic.Omega

@[expose] public section

namespace Lemmata.RM59.BinaryValues

theorem slowList_cons (c : ℕ) (columns : List ℕ) (w start : ℕ) :
    slowList (c :: columns) w start =
      slowList columns (w / 2) (if w.testBit 0 then Nat.xor start c else start) := by
  unfold slowList
  rw [List.length_cons, List.range_succ_eq_map, List.foldl_cons, List.foldl_map]
  simp only [List.getElem?_cons_zero, Option.getD_some, List.getElem?_cons_succ,
    Nat.testBit_succ]

theorem slowList_eq_xorValue (columns : List ℕ) (w start : ℕ) :
    slowList columns w start = Nat.xor start (xorValue columns w) := by
  induction columns generalizing w start with
  | nil => simp [slowList, xorValue]
  | cons c columns ih =>
    rw [slowList_cons, ih]
    cases h : w.testBit 0 <;> simp [xorValue, h, Nat.xor_assoc, Nat.xor_comm]
    rw [← Nat.xor_assoc, Nat.xor_comm c start, Nat.xor_assoc]

theorem xorValue_eq_contractPair (row : Array ℕ) (w : ℕ) :
    xorValue row.toList w = CatalogCompute.contractPair row w := by
  have h := slowList_eq_xorValue row.toList w 0
  simpa [slowList, CatalogCompute.contractPair] using h.symm

theorem values_size (columns : List ℕ) : (values columns).size = 2 ^ columns.length := by
  induction columns with
  | nil => simp [values]
  | cons c columns ih => simp [values, ih, Nat.pow_succ, Nat.mul_comm]

theorem values_get (columns : List ℕ) (w : ℕ) (hw : w < (values columns).size) :
    (values columns)[w] = xorValue columns w := by
  induction columns generalizing w with
  | nil =>
    have hw0 : w = 0 := by
      have : w < 1 := by simpa [values] using hw
      omega
    subst w
    simp [values, xorValue]
  | cons c columns ih =>
    have hbound : w < 2 * (values columns).size := by
      simpa only [values, Array.size_ofFn] using hw
    have hhalf : w / 2 < (values columns).size := by omega
    simp only [values, Array.getElem_ofFn, xorValue]
    simp only [ih (w / 2) hhalf]

theorem values_getD (columns : List ℕ) (w : ℕ) (hw : w < 2 ^ columns.length) :
    (values columns)[w]?.getD 0 = xorValue columns w := by
  have hbound : w < (values columns).size := by simpa only [values_size] using hw
  rw [Array.getElem?_eq_some_getElem _ _ hbound]
  simp only [Option.getD_some]
  exact values_get columns w hbound

theorem values_eq_ofFn (row : Array ℕ) :
    values row.toList = Array.ofFn (fun w : Fin (2 ^ row.size) =>
      CatalogCompute.contractPair row w.val) := by
  apply Array.ext
  · simp [values_size]
  · intro w hw₁ hw₂
    rw [Array.getElem_ofFn]
    exact (values_get row.toList w hw₁).trans (xorValue_eq_contractPair row w)

@[simp] theorem fastPairValues_size (table : Array (Array ℕ)) :
    (fastPairValues table).size = table.size := by
  simp [fastPairValues]

theorem fastPairValues_row_size (table : Array (Array ℕ)) (v : Fin table.size) :
    ((fastPairValues table)[v.val]'(by simp [v.isLt])).size = 2 ^ table[v.val].size := by
  simp [fastPairValues, values_size]

theorem fastPairValues_entry (table : Array (Array ℕ)) (v : Fin table.size) (w : ℕ)
    (hw : w < 2 ^ table[v.val].size) :
    (((fastPairValues table)[v.val]'(by simp [v.isLt]))[w]?.getD 0) =
      CatalogCompute.contractPair table[v.val] w := by
  simp only [fastPairValues, Array.getElem_map]
  exact (values_getD table[v.val].toList w (by simpa using hw)).trans
    (xorValue_eq_contractPair table[v.val] w)

theorem fastPairValues_eq_pairValues (table : Array (Array ℕ))
    (hshape : ∀ v : Fin table.size, 2 ^ table[v.val].size = table.size) :
    fastPairValues table = CatalogCompute.pairValues table := by
  apply Array.ext
  · simp [fastPairValues, CatalogCompute.pairValues]
  · intro v hv₁ hv₂
    have hv : v < table.size := by simpa [fastPairValues] using hv₁
    simp only [fastPairValues, CatalogCompute.pairValues, Array.getElem_map]
    rw [values_eq_ofFn]
    apply Array.ext
    · simpa only [Array.size_ofFn] using hshape ⟨v, hv⟩
    · intro w hw₁ hw₂
      simp only [Array.getElem_ofFn]

end Lemmata.RM59.BinaryValues
