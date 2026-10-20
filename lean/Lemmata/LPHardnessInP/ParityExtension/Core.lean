module

public import Lemmata.LPHardnessInP.Parity.Main
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Finset.Card

@[expose] public section

namespace Lemmata.LPHardnessInP.ParityExtension

open scoped BigOperators
open Lemmata.LPHardnessInP.Parity

/-- The number of indices outside a set in the core. -/
theorem count_outside {h : ℕ} (S : Finset (Fin h)) :
    (∑ x : Fin h, if x ∉ S then 1 else 0 : ℕ) = h - S.card := by
  rw [Finset.sum_boole]
  have hfilter : Finset.univ.filter (fun x : Fin h => x ∉ S) = Finset.univ \ S := by
    ext x
    simp
  rw [hfilter, Finset.card_sdiff_of_subset (Finset.subset_univ S)]
  simp

/-- The two transposed edges are blue; every other edge is red. -/
def coreRed {h : ℕ} (i j x : Fin h) : Bool :=
  decide (x ∉ ({i, j} : Finset (Fin h)))

theorem coreRed_count {h : ℕ} (i j : Fin h) (hij : i ≠ j) :
    (∑ x : Fin h, if coreRed i j x then 1 else 0 : ℕ) = h - 2 := by
  simpa [coreRed, hij] using count_outside ({i, j} : Finset (Fin h))

theorem coreRed_parity {h : ℕ} (hodd : Odd h) (i j : Fin h) (hij : i ≠ j) :
    ∑ x : Fin h, bit (coreRed i j x) = 1 := by
  have hcard : 2 ≤ h := by
    have hle := Finset.card_le_card (Finset.subset_univ ({i, j} : Finset (Fin h)))
    simpa [hij] using hle
  have hredodd : Odd (h - 2) := by
    rw [Nat.odd_iff] at hodd ⊢
    omega
  have hcount := coreRed_count i j hij
  have hcast : ((∑ x : Fin h, if coreRed i j x then 1 else 0 : ℕ) : ZMod 2) = 1 := by
    rw [hcount]
    exact hredodd.natCast_zmod_two
  simpa only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, bit] using hcast

/-- The matching used by the new core swap: transpose two partners and color
exactly the two transposed edges blue. -/
def coreMatching {h : ℕ} (hodd : Odd h) (i j : Fin h) (hij : i ≠ j) :
    ParityMatching h where
  perm := Equiv.swap i j
  red := coreRed i j
  odd_red := coreRed_parity hodd i j hij

/-- The new labeling is one on the left and zero precisely on the three
specified right vertices. -/
def coreRight {h : ℕ} (H' : Finset (Fin h)) (x : Fin h) : Bool :=
  decide (x ∉ H')

theorem coreRight_count {h : ℕ} (H' : Finset (Fin h)) (hcard : H'.card = 3) :
    (∑ x : Fin h, if coreRight H' x then 1 else 0 : ℕ) = h - 3 := by
  simpa [coreRight, hcard] using count_outside H'

theorem coreRight_parity {h : ℕ} (hodd : Odd h)
    (H' : Finset (Fin h)) (hcard : H'.card = 3) :
    ∑ x : Fin h, bit (coreRight H' x) = 0 := by
  have hle : 3 ≤ h := by
    have hle := Finset.card_le_card (Finset.subset_univ H')
    simpa [hcard] using hle
  have hright_even : Even (h - 3) := by
    rw [Nat.even_iff]
    rw [Nat.odd_iff] at hodd
    omega
  have hcast : ((∑ x : Fin h, if coreRight H' x then 1 else 0 : ℕ) : ZMod 2) = 0 := by
    rw [coreRight_count H' hcard]
    exact hright_even.natCast_zmod_two
  simpa only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, bit] using hcast

def coreLabel {h : ℕ} (hodd : Odd h) (H' : Finset (Fin h)) (hcard : H'.card = 3) :
    ParityLabel h where
  left := fun _ => true
  right := coreRight H'
  label_parity := by
    rw [coreRight_parity hodd H' hcard]
    simp [bit]

theorem coreLabel_ones {h : ℕ} (hodd : Odd h)
    (H' : Finset (Fin h)) (hcard : H'.card = 3) :
    (∑ x : Fin h, if (coreLabel hodd H' hcard).left x then 1 else 0 : ℕ) +
      (∑ x : Fin h, if (coreLabel hodd H' hcard).right x then 1 else 0 : ℕ) =
        2 * h - 3 := by
  have hle : 3 ≤ h := by
    have hle := Finset.card_le_card (Finset.subset_univ H')
    simpa [hcard] using hle
  change (∑ _x : Fin h, 1 : ℕ) + (∑ x : Fin h, if coreRight H' x then 1 else 0 : ℕ) =
    2 * h - 3
  rw [coreRight_count H' hcard]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
  omega

theorem coreMatching_fixed {h : ℕ} (hodd : Odd h) (i j : Fin h) (hij : i ≠ j)
    (x : Fin h) (hxi : x ≠ i) (hxj : x ≠ j) :
    (coreMatching hodd i j hij).perm x = x ∧
      (coreMatching hodd i j hij).red x = true := by
  simp [coreMatching, coreRed, Equiv.swap_apply_of_ne_of_ne hxi hxj, hxi, hxj]

/-- The swapped matching agrees with the red identity on every witness core
that excludes the two swapped indices. -/
theorem coreMatching_agrees_on {h : ℕ} (hodd : Odd h) (i j : Fin h) (hij : i ≠ j)
    (H : Finset (Fin h)) (hi : i ∉ H) (hj : j ∉ H) :
    ∀ x ∈ H, (coreMatching hodd i j hij).perm x = x ∧
      (coreMatching hodd i j hij).red x = true := by
  intro x hx
  apply coreMatching_fixed hodd i j hij x
  · intro hxi
    exact hi (hxi ▸ hx)
  · intro hxj
    exact hj (hxj ▸ hx)

theorem coreLabel_on {h : ℕ} (hodd : Odd h) (H' : Finset (Fin h))
    (hcard : H'.card = 3) (x : Fin h) (hx : x ∈ H') :
    (coreLabel hodd H' hcard).left x = true ∧
      (coreLabel hodd H' hcard).right x = false := by
  simp [coreLabel, coreRight, hx]

theorem coreLabel_off {h : ℕ} (hodd : Odd h) (H' : Finset (Fin h))
    (hcard : H'.card = 3) (x : Fin h) (hx : x ∉ H') :
    (coreLabel hodd H' hcard).left x = true ∧
      (coreLabel hodd H' hcard).right x = true := by
  simp [coreLabel, coreRight, hx]

theorem core_violates_iff {h : ℕ} (hodd : Odd h)
    (H' : Finset (Fin h)) (hcard : H'.card = 3)
    (i j : Fin h) (hij : i ≠ j) (hi : i ∈ H') (hj : j ∈ H') (x : Fin h) :
    Violates (coreLabel hodd H' hcard) x
      ((coreMatching hodd i j hij).perm x) ((coreMatching hodd i j hij).red x) ↔
        x ∈ H' ∧ x ≠ i ∧ x ≠ j := by
  by_cases hxi : x = i
  · subst x
    simp [Violates, coreLabel, coreRight, coreMatching, coreRed, hi, hj]
  by_cases hxj : x = j
  · subst x
    simp [Violates, coreLabel, coreRight, coreMatching, coreRed, hi, hj]
  · simp [Violates, coreLabel, coreRight, coreMatching, coreRed,
      Equiv.swap_apply_of_ne_of_ne hxi hxj, hxi, hxj]

-- DOCS_BEGIN_MAIN
/-- The actual swapped matching and labeling have exactly one violation,
the sole element of the three-element core other than the swapped indices. -/
theorem core_violationCount {h : ℕ} (hodd : Odd h)
    (H' : Finset (Fin h)) (hcard : H'.card = 3)
    (i j : Fin h) (hij : i ≠ j) (hi : i ∈ H') (hj : j ∈ H') :
    violationCount (coreLabel hodd H' hcard) (coreMatching hodd i j hij) = 1 := by
  unfold violationCount
  simp only [core_violates_iff hodd H' hcard i j hij hi hj]
  rw [Finset.sum_boole]
  have hfilter :
      Finset.univ.filter (fun x : Fin h => x ∈ H' ∧ x ≠ i ∧ x ≠ j) =
        (H'.erase i).erase j := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    tauto
  rw [hfilter, Finset.card_erase_of_mem (by simp [hj, hij.symm]),
    Finset.card_erase_of_mem hi, hcard]
  norm_num

/-- Opposite labels at the two swapped indices make both blue edges
consistent. Every other edge remains red with equal endpoint labels. -/
theorem coreMatching_block_consistent {h : ℕ} (hodd : Odd h)
    (i j : Fin h) (hij : i ≠ j) (b : Fin h → Bool) (hb : b i ≠ b j) :
    ∀ x, ¬ (if (coreMatching hodd i j hij).red x
      then b x ≠ b ((coreMatching hodd i j hij).perm x)
      else b x = b ((coreMatching hodd i j hij).perm x)) := by
  intro x
  by_cases hxi : x = i
  · subst x
    simpa [coreMatching, coreRed] using hb
  by_cases hxj : x = j
  · subst x
    simpa [coreMatching, coreRed] using hb.symm
  · simp [coreMatching, coreRed, Equiv.swap_apply_of_ne_of_ne hxi hxj, hxi, hxj]

/-- The same consistency statement directly for an admissible labeling:
outside a witness core its endpoint pairs have equal labels, and the two
swapped pairs have opposite labels. -/
theorem coreMatching_consistent_off {h : ℕ} (hodd : Odd h)
    (i j : Fin h) (hij : i ≠ j) (L : ParityLabel h)
    (H : Finset (Fin h)) (hi : i ∉ H) (hj : j ∉ H)
    (hequal : ∀ x, x ∉ H → L.left x = L.right x)
    (hopposite : L.left i ≠ L.left j) :
    ∀ x, x ∉ H →
      ¬ Violates L x ((coreMatching hodd i j hij).perm x)
        ((coreMatching hodd i j hij).red x) := by
  intro x hx
  by_cases hxi : x = i
  · subst x
    simpa [Violates, coreMatching, coreRed, ← hequal j hj] using hopposite
  by_cases hxj : x = j
  · subst x
    simpa [Violates, coreMatching, coreRed, ← hequal i hi] using hopposite.symm
  · simp [Violates, coreMatching, coreRed, Equiv.swap_apply_of_ne_of_ne hxi hxj,
      hxi, hxj, hequal x hx]

/-- On the complement of the new three-element core every endpoint is one,
so any red edge in that complement is nonviolating. -/
theorem coreLabel_red_complement_consistent {h : ℕ} (hodd : Odd h)
    (H' : Finset (Fin h)) (hcard : H'.card = 3)
    (x y : Fin h) (_hx : x ∉ H') (hy : y ∉ H') :
    ¬ Violates (coreLabel hodd H' hcard) x y true := by
  simp [Violates, coreLabel, coreRight, hy]

/-- Any matching that is red and stays in the complement is consistent with
the new labeling on that complement; its internal permutation is arbitrary. -/
theorem coreLabel_consistent_off {h : ℕ} (hodd : Odd h)
    (H' : Finset (Fin h)) (hcard : H'.card = 3) (M : ParityMatching h)
    (hred : ∀ x, x ∉ H' → M.red x = true)
    (hperm : ∀ x, x ∉ H' → M.perm x ∉ H') :
    ∀ x, x ∉ H' → ¬ Violates (coreLabel hodd H' hcard) x (M.perm x) (M.red x) := by
  intro x hx
  rw [hred x hx]
  exact coreLabel_red_complement_consistent hodd H' hcard x (M.perm x) hx (hperm x hx)

-- DOCS_END_MAIN

end Lemmata.LPHardnessInP.ParityExtension
