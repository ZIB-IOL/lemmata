module

public import Lemmata.RM59.Proof.CatalogContractions

@[expose] public section

namespace Lemmata.RM59.CatalogGraph

open scoped Matrix CharTwo
open Packed CatalogCompute CatalogForms CatalogContractions

def BasisBound (basis : Array (Array ℕ)) : Prop :=
  ∀ i j : Fin 9, ((basis[i.val]?.getD #[])[j.val]?.getD 0) < 512

theorem xor_fold_lt (indices : List ℕ) (values : ℕ → ℕ) (selected : ℕ → Bool)
    (start : ℕ) (hstart : start < 512) (hvalues : ∀ i ∈ indices, values i < 512) :
    indices.foldl (fun value i => if selected i then Nat.xor value (values i) else value) start < 512 := by
  induction indices generalizing start with
  | nil => exact hstart
  | cons i indices ih =>
    have htail : ∀ j ∈ indices, values j < 512 := by
      intro j hj
      exact hvalues j (List.mem_cons.mpr (Or.inr hj))
    cases h : selected i
    · simpa [List.foldl_cons, h] using ih start hstart htail
    · have hnext : Nat.xor start (values i) < 512 := by
        simpa only [Nat.xor_eq] using Nat.xor_lt_two_pow (n := 9) hstart (hvalues i (by simp))
      simpa [List.foldl_cons, h] using ih (Nat.xor start (values i)) hnext htail

theorem contractionRow_bound (basis : Array (Array ℕ)) (hb : BasisBound basis)
    (x : PackedPoint) (j : Fin 9) : (contractionRow basis x)[j.val]?.getD 0 < 512 := by
  rw [contractionRow_entry]
  apply xor_fold_lt _ _ _ 0 (by decide)
  intro i hi
  exact hb ⟨i, List.mem_range.mp hi⟩ j

theorem pairValue_bound (basis : Array (Array ℕ)) (hb : BasisBound basis)
    (x y : PackedPoint) : pairValue basis x y < 512 := by
  rw [pairValue_eq, contractPair, contractionRow_size]
  apply xor_fold_lt _ _ _ 0 (by decide)
  intro j hj
  exact contractionRow_bound basis hb x ⟨j, List.mem_range.mp hj⟩

theorem natRow_eq_zero_iff (value : ℕ) (hvalue : value < 512) :
    natRow value = 0 ↔ value = 0 := by
  constructor
  · intro h
    have hp : (⟨value, hvalue⟩ : PackedPoint) = 0 :=
      natRow_injective_on_packed _ 0 (by simpa using h)
    exact congrArg Fin.val hp
  · rintro rfl
    exact natRow_zero

theorem pairValue_zero_iff (T : CubicForm) (basis : Array (Array ℕ))
    (hbasis : ∀ i j : Fin 9,
      natRow ((basis[i.val]?.getD #[])[j.val]?.getD 0) =
        contractionPoint T (basisPoint i) (basisPoint j))
    (hb : BasisBound basis) (x y : PackedPoint) :
    pairValue basis x y = 0 ↔ ∀ z, cubicFormValue T (decodePoint x) (decodePoint y) z = 0 := by
  have h := natRow_eq_zero_iff (pairValue basis x y) (pairValue_bound basis hb x y)
  rw [pairValue_semantic T basis hbasis, contractionPoint_zero_iff] at h
  exact h.symm

theorem family_basis_bound (family : Fin 348) : BasisBound (familyBasis family) := by
  let basis := familyBasis family
  have h := basis_data_checked family
  unfold basisDataCheck at h
  have hleft : basis.size == 9 &&
      basis.all (fun row => row.size == 9 && row.all (· < 512)) = true :=
    (Bool.and_eq_true_iff.mp h).1
  have hsize : basis.size = 9 := by
    simpa using (Bool.and_eq_true_iff.mp hleft).1
  have hall := (Bool.and_eq_true_iff.mp hleft).2
  intro i j
  have hi : i.val < basis.size := by simpa only [hsize] using i.isLt
  have hrow := Array.all_eq_true.mp hall i.val hi
  have hrowsize : basis[i.val].size = 9 := by
    simpa using (Bool.and_eq_true_iff.mp hrow).1
  have hrowall := (Bool.and_eq_true_iff.mp hrow).2
  have hj : j.val < basis[i.val].size := by simpa only [hrowsize] using j.isLt
  have hentry := Array.all_eq_true.mp hrowall j.val hj
  change ((basis[i.val]?.getD #[])[j.val]?.getD 0) < 512
  rw [Array.getElem?_eq_some_getElem basis i.val hi]
  simp only [Option.getD_some]
  rw [Array.getElem?_eq_some_getElem basis[i.val] j.val hj]
  simpa only [Option.getD_some, decide_eq_true_eq] using hentry

def adjacency (basis : Array (Array ℕ)) (x y : PackedPoint) : Bool :=
  x.val != 0 && y.val != 0 && x != y && pairValue basis x y == 0

theorem decodePoint_eq_zero_iff (x : PackedPoint) : decodePoint x = 0 ↔ x.val = 0 := by
  constructor
  · intro h
    have hx : x = 0 := decodePoint_injective (h.trans decodePoint_zero.symm)
    exact congrArg Fin.val hx
  · intro h
    have hx : x = 0 := Fin.ext h
    subst x
    exact decodePoint_zero

theorem adjacency_semantic (T : CubicForm) (basis : Array (Array ℕ))
    (hbasis : ∀ i j : Fin 9,
      natRow ((basis[i.val]?.getD #[])[j.val]?.getD 0) =
        contractionPoint T (basisPoint i) (basisPoint j))
    (hb : BasisBound basis) (x y : PackedPoint) :
    adjacency basis x y = CatalogInvariant.contractionAdjacency
      (cubicFormValue T) (decodePoint x) (decodePoint y) := by
  apply Bool.eq_iff_iff.mpr
  simp only [adjacency, CatalogInvariant.contractionAdjacency, Bool.and_eq_true_iff,
    bne_iff_ne, beq_iff_eq, decide_eq_true_eq, ne_eq, decodePoint_eq_zero_iff,
    decodePoint_injective.eq_iff, pairValue_zero_iff T basis hbasis hb x y, and_assoc]

theorem cubicFormValue_swap (T : CubicForm) (x y z : Point 9) :
    cubicFormValue T x y z = cubicFormValue T y x z := by
  have htuple : ![x, y, z] ∘ Equiv.swap (0 : Fin 3) 1 = ![y, x, z] := by
    funext i
    fin_cases i <;> simp [Function.comp_apply, Equiv.swap_apply_def]
  have h := T.map_swap ![x, y, z] (i := 0) (j := 1) (by decide)
  rw [htuple] at h
  change cubicFormValue T y x z = -cubicFormValue T x y z at h
  simpa only [CharTwo.neg_eq] using h.symm

theorem adjacency_symm (T : CubicForm) (basis : Array (Array ℕ))
    (hbasis : ∀ i j : Fin 9,
      natRow ((basis[i.val]?.getD #[])[j.val]?.getD 0) =
        contractionPoint T (basisPoint i) (basisPoint j))
    (hb : BasisBound basis) (x y : PackedPoint) : adjacency basis x y = adjacency basis y x := by
  rw [adjacency_semantic T basis hbasis hb x y, adjacency_semantic T basis hbasis hb y x]
  exact CatalogInvariant.contractionAdjacency_symm (cubicFormValue T)
    (cubicFormValue_swap T) (decodePoint x) (decodePoint y)

theorem family_adjacency_semantic (family : Fin 348) (x y : PackedPoint) :
    adjacency (familyBasis family) x y = CatalogInvariant.contractionAdjacency
      (cubicFormValue (representative family)) (decodePoint x) (decodePoint y) :=
  adjacency_semantic _ _ (family_basis_semantic family) (family_basis_bound family) x y

theorem family_adjacency_symm (family : Fin 348) (x y : PackedPoint) :
    adjacency (familyBasis family) x y = adjacency (familyBasis family) y x :=
  adjacency_symm _ _ (family_basis_semantic family) (family_basis_bound family) x y

end Lemmata.RM59.CatalogGraph
