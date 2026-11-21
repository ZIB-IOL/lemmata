module

public import Lemmata.SteinerSixSpectrum.BitIncidence

public section

namespace Lemmata.SteinerSixSpectrum.BitIncidence

/-- The kernel hashes a natural-number literal by its low 64 bits. Incidence
masks often agree there. Attach a varying low word and check only the bits
above it. The correctness proof works for every choice of low words. -/
private def lowWord (i : Nat) : Nat := Id.run do
  let a := i.toUInt64 + 0x9e3779b97f4a7c15
  let b := (a ^^^ (a >>> 30)) * 0xbf58476d1ce4e5b9
  let c := (b ^^^ (b >>> 27)) * 0x94d049bb133111eb
  return (c ^^^ (c >>> 31)).toNat

def taggedMasks (n : Nat) (rows : List (List Nat)) : List Nat :=
  (masksOfRows n rows).zipIdx.map fun (m,i) => (m <<< 64) + lowWord i

@[expose] def taggedPair (a b : Nat) : Bool :=
  let z := a &&& b
  decide (18446744073709551616 ≤ z) &&
    decide ((z &&& (z-18446744073709551616)) < 18446744073709551616)

private theorem untag_pair {a b : Nat} (h : taggedPair a b = true) :
    pairOK true (a >>> 64) (b >>> 64) = true := by
  let z := a &&& b
  change (decide (18446744073709551616 ≤ z) &&
    decide ((z &&& (z-18446744073709551616)) < 18446744073709551616)) = true at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  have div (x : Nat) : x >>> 64 = x / 18446744073709551616 := Nat.shiftRight_eq_div_pow x 64
  have one : (z >>> 64) ≠ 0 := by rw [div]; omega
  have sub : (z-18446744073709551616) >>> 64 = (z >>> 64)-1 := by
    simp only [div]; omega
  have zero : (z &&& (z-18446744073709551616)) >>> 64 = 0 := by rw [div]; omega
  rw [Nat.shiftRight_and_distrib, sub] at zero
  simpa [pairOK, ← Nat.shiftRight_and_distrib, z] using And.intro one zero

@[expose] def frontOK : Nat → List Nat → Bool
  | 0, _ | _, [] => true
  | k+1, a::xs => xs.all (taggedPair a) && frontOK k xs

def Suffix (xs : List Nat) (i : Nat) : Prop :=
  (xs.drop i).Pairwise (fun a b => taggedPair a b = true)

private theorem front_sound {xs : List Nat} {k : Nat} (h : frontOK k xs = true)
    (tail : (xs.drop k).Pairwise (fun a b => taggedPair a b = true)) :
    xs.Pairwise (fun a b => taggedPair a b = true) := by
  induction k generalizing xs with
  | zero => simpa using tail
  | succ k ih =>
    cases xs with
    | nil => simp
    | cons a xs =>
      simp only [frontOK, Bool.and_eq_true, List.all_eq_true] at h
      exact List.pairwise_cons.mpr ⟨h.1, ih h.2 tail⟩

theorem suffixStep {xs : List Nat} {i k : Nat} (h : frontOK k (xs.drop i) = true)
    (tail : Suffix xs (i+k)) : Suffix xs i :=
  front_sound h (by simpa [Suffix, List.drop_drop, Nat.add_comm] using tail)

theorem suffixEnd {xs : List Nat} {i : Nat} (h : xs.length ≤ i) : Suffix xs i := by
  simp [Suffix, List.drop_eq_nil_of_le h]

private theorem against_complete (a i : Nat) (xs : List Nat) :
    against (fun _ => true) a i xs = true ↔ ∀ b ∈ xs, pairOK true a b = true := by
  induction xs generalizing i <;> simp [against, *]

private theorem pairs_complete (i : Nat) (xs : List Nat) :
    pairs (fun _ _ => true) i xs = true ↔ xs.Pairwise (fun a b => pairOK true a b = true) := by
  induction xs generalizing i <;> simp [pairs, against_complete, List.pairwise_cons, *]

def completeTagged (xs : List Nat)
    (six : atLeast (xs.map (· >>> 64)) 0 = atLeast (xs.map (· >>> 64)) 5)
    (seven : atLeast (xs.map (· >>> 64)) 6 = 0) (checked : Suffix xs 0) :
    SteinerSystem (Fin (xs.map (· >>> 64)).length) := by
  apply complete _ six seven
  apply (pairs_complete ..).2
  rw [List.pairwise_map]
  have h : xs.Pairwise (fun a b => taggedPair a b = true) := by simpa [Suffix] using checked
  exact h.imp (fun h => untag_pair h)

end Lemmata.SteinerSixSpectrum.BitIncidence
