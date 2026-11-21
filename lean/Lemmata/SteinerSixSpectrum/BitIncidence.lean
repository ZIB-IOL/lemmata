module

public import Lemmata.SteinerSixSpectrum.Statement
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Init.Data.Nat.Power2.Bitwise
import all Init.Data.Nat.Power2.Basic

public section

namespace Lemmata.SteinerSixSpectrum
namespace BitIncidence

/-- Build a candidate incidence matrix from a block list. Only its literal
entries are used by the proof, so the block generator can run before checking. -/
def masksOfRows (n : Nat) (rows : List (List Nat)) : List Nat := Id.run do
  let mut masks := Array.replicate n 0
  let mut blockNumber := 0
  for row in rows do
    let bit := 1 <<< blockNumber
    for x in row do
      masks := masks.modify x (· ||| bit)
    blockNumber := blockNumber + 1
  return masks.toList

/-- Bit `j` of the mask for point `x` records membership in block `j`.
`atLeast rows k` marks the blocks containing more than `k` points. -/
@[expose] def atLeast : List Nat → Nat → Nat
  | [], _ => 0
  | x :: xs, 0 => x ||| atLeast xs 0
  | x :: xs, k+1 => atLeast xs (k+1) ||| (x &&& atLeast xs k)

theorem atLeast_spec (xs : List Nat) (k j : Nat) :
    (atLeast xs k).testBit j = true ↔ k < xs.countP (·.testBit j) := by
  induction xs generalizing k with
  | nil => simp [atLeast]
  | cons x xs ih =>
    cases k <;> cases h : x.testBit j <;>
      simp [atLeast, h, Nat.testBit_or, Nat.testBit_and, Bool.or_eq_true, ih]
    omega

/-- Two points in different groups share exactly one block. Points in the same
group share none. The binary digits of their intersection give the witnesses. -/
@[expose] def pairOK (required : Bool) (a b : Nat) : Bool :=
  let common := a &&& b
  if required then common != 0 && (common &&& (common-1)) == 0 else common == 0

theorem pairOK_symm (e : Bool) (a b : Nat) : pairOK e a b = pairOK e b a := by
  simp only [pairOK, Nat.and_comm a b]

@[expose] def against (required : Nat → Bool) (a j : Nat) : List Nat → Bool
  | [] => true
  | b :: bs => pairOK (required j) a b && against required a (j+1) bs

@[expose] def pairs (required : Nat → Nat → Bool) (i : Nat) : List Nat → Bool
  | [] => true
  | a :: as => against (required i) a (i+1) as && pairs required (i+1) as

private theorem against_get {e : Nat → Bool} {a j : Nat} {xs : List Nat}
    (h : against e a j xs = true) (y : Fin xs.length) :
    pairOK (e (j+y.val)) a xs[y.val] = true := by
  induction xs generalizing j with
  | nil => exact Fin.elim0 y
  | cons b bs ih =>
    simp only [against, Bool.and_eq_true] at h
    refine Fin.cases ?_ (fun t => ?_) y
    · simpa using h.1
    · simpa [Nat.add_assoc, Nat.add_comm 1] using ih h.2 t

private theorem pairs_get {e : Nat → Nat → Bool} {i : Nat} {xs : List Nat}
    (h : pairs e i xs = true) (x y : Fin xs.length) (lt : x < y) :
    pairOK (e (i+x.val) (i+y.val)) xs[x.val] xs[y.val] = true := by
  induction xs generalizing i with
  | nil => exact Fin.elim0 x
  | cons a as ih =>
    simp only [pairs, Bool.and_eq_true] at h
    revert lt
    refine Fin.cases ?_ (fun s => ?_) x
    · refine Fin.cases (by simp) (fun t _ => ?_) y
      simpa [Nat.add_assoc, Nat.add_comm 1] using against_get h.1 t
    · refine Fin.cases (by simp) (fun t lt => ?_) y
      simpa [Nat.add_assoc, Nat.add_comm 1] using ih h.2 s t (Fin.succ_lt_succ_iff.mp lt)

private def block (xs : List Nat) (j : Nat) : Finset (Fin xs.length) :=
  Finset.univ.filter fun x => xs[x.val].testBit j = true

private theorem card_block (xs : List Nat) (j : Nat) :
    (block xs j).card = xs.countP (·.testBit j) := by
  classical
  rw [block, Finset.card_filter]
  induction xs with
  | nil => simp
  | cons x xs ih =>
    change (∑ i : Fin (xs.length+1), if (x::xs)[i.val].testBit j then 1 else 0) = _
    rw [Fin.sum_univ_succ]
    change (if x.testBit j then 1 else 0) +
      (∑ i : Fin xs.length, if xs[i.val].testBit j then 1 else 0) = _
    rw [ih, List.countP_cons]
    omega

/-- Every nonempty column has six entries. Intersections of two rows have the
prescribed multiplicity, so the columns give the required pair design. -/
def ofMasks (xs : List Nat) (e : Nat → Nat → Bool) (sym : ∀ x y, e x y = e y x)
    (six : atLeast xs 0 = atLeast xs 5) (seven : atLeast xs 6 = 0)
    (checked : pairs e 0 xs = true) :
    PairDesign (Fin xs.length) (fun x y => e x.val y.val = true) := by
  have card (j : Nat) (occupied : (block xs j).Nonempty) : (block xs j).card = 6 := by
    have h := Finset.card_pos.mpr occupied
    rw [card_block] at h ⊢
    have lo := (atLeast_spec xs 0 j).2 h
    rw [six, atLeast_spec] at lo
    have hi : ¬ 6 < xs.countP (·.testBit j) := by
      rw [← atLeast_spec, seven]
      simp
    omega
  have pair (x y : Fin xs.length) (ne : x ≠ y) :
      pairOK (e x.val y.val) xs[x.val] xs[y.val] = true := by
    rcases lt_or_gt_of_ne ne with h | h
    · simpa using pairs_get checked x y h
    · rw [sym, pairOK_symm]
      simpa using pairs_get checked y x h
  have mem (j : Nat) (x : Fin xs.length) :
      x ∈ block xs j ↔ xs[x.val].testBit j = true := by simp [block]
  refine ⟨{B | ∃ j, (block xs j).Nonempty ∧ block xs j = B}, ?_, ?_, ?_⟩
  · rintro B ⟨j, hj, rfl⟩
    exact card j hj
  · rintro B ⟨j, hj, rfl⟩ x hx y hy ne
    have hit : (xs[x.val] &&& xs[y.val]).testBit j = true := by
      simp [Nat.testBit_and, (mem j x).1 hx, (mem j y).1 hy]
    have ok := pair x y ne
    cases h : e x.val y.val with
    | true => rfl
    | false =>
      simp [pairOK, h] at ok
      simp [ok] at hit
  · intro x y ne req
    have ok := pair x y ne
    simp [pairOK, req] at ok
    obtain ⟨j, hj⟩ := (Nat.and_sub_one_eq_zero_iff_isPowerOfTwo ok.1).mp ok.2
    have incidence (t : Nat) : x ∈ block xs t ∧ y ∈ block xs t ↔ j = t := by
      rw [mem, mem, ← Bool.and_eq_true, ← Nat.testBit_and, hj, Nat.testBit_two_pow]
      simp
    obtain ⟨hx, hy⟩ := (incidence j).2 rfl
    refine ⟨block xs j, ⟨⟨j, ⟨x, hx⟩, rfl⟩, hx, hy⟩, ?_⟩
    rintro B ⟨⟨t, _, rfl⟩, hx', hy'⟩
    rw [(incidence t).1 ⟨hx', hy'⟩]

/-- A complete design requires every pair of different points. -/
def complete (xs : List Nat) (six : atLeast xs 0 = atLeast xs 5) (seven : atLeast xs 6 = 0)
    (checked : pairs (fun _ _ => true) 0 xs = true) : SteinerSystem (Fin xs.length) := by
  simpa only [eq_self] using ofMasks xs _ (fun _ _ => rfl) six seven checked

end BitIncidence
end Lemmata.SteinerSixSpectrum
