module

public import Lemmata.SteinerSixSpectrum.Statement
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.List.Nodup

public section

namespace Lemmata.SteinerSixSpectrum

/-- The earlier and later points in each pair of positions in a row. -/
@[expose] def rowPairs : List ℕ → List (ℕ × ℕ)
  | [] => []
  | x :: rest => rest.map (fun y => (x, y)) ++ rowPairs rest

private theorem mem_rowPairs {row : List ℕ} (hr : row.Pairwise (· < ·)) {x y : ℕ} :
    (x, y) ∈ rowPairs row ↔ x ∈ row ∧ y ∈ row ∧ x < y := by
  induction row with
  | nil => simp [rowPairs]
  | cons z rest ih =>
    have ⟨hz, hrest⟩ := List.pairwise_cons.mp hr
    simp only [rowPairs, List.mem_append, List.mem_map, Prod.mk.injEq, List.mem_cons,
      ih hrest]
    constructor
    · rintro (⟨w, hw, rfl, rfl⟩ | ⟨hx, hy, hlt⟩)
      · exact ⟨Or.inl rfl, Or.inr hw, hz w hw⟩
      · exact ⟨Or.inr hx, Or.inr hy, hlt⟩
    · rintro ⟨rfl | hx, rfl | hy, hlt⟩
      · exact False.elim (Nat.lt_irrefl _ hlt)
      · exact Or.inl ⟨_, hy, rfl, rfl⟩
      · exact False.elim (Nat.lt_asymm hlt (hz _ hx))
      · exact Or.inr ⟨hx, hy, hlt⟩

private theorem length_rowPairs (xs : List ℕ) :
    (rowPairs xs).length = (List.range xs.length).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [rowPairs, List.range_succ, ih, Nat.add_comm]

/-- Mark the index of each covered pair once. A collision or an out-of-range
index rejects the certificate. -/
@[expose] def markDistinct {α : Type*} (key : α → ℕ) : List α → Array Bool → Bool
  | [], _ => true
  | x :: xs, seen => seen[key x]? == some false &&
      markDistinct key xs (seen.setIfInBounds (key x) true)

private theorem markDistinct_sound {α : Type*} {key : α → ℕ} {xs : List α} {seen : Array Bool}
    (ok : markDistinct key xs seen = true) :
    xs.Nodup ∧ ∀ x ∈ xs, seen[key x]? = some false := by
  induction xs generalizing seen with
  | nil => simp
  | cons x xs ih =>
    simp only [markDistinct, Bool.and_eq_true, beq_iff_eq] at ok
    obtain ⟨unused, rest⟩ := ok
    obtain ⟨nd, fresh⟩ := ih rest
    have bound : key x < seen.size := (Array.getElem?_eq_some_iff.mp unused).1
    have other (y : α) (hy : y ∈ xs) : key y ≠ key x := by
      intro eq
      have h := fresh y hy
      simp [eq, bound] at h
    refine ⟨List.nodup_cons.mpr ⟨fun h => other x h rfl, nd⟩, ?_⟩
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact unused
    · simpa [Array.getElem?_setIfInBounds, Ne.symm (other y hy), other y hy] using fresh y hy

/-- Check row bounds and eligibility. Distinct covered pairs whose number
equals the number of required pairs certify exact coverage. -/
@[expose] def checkPairs (n required : ℕ) (eligible : ℕ → ℕ → Bool) (rows : List (List ℕ)) : Bool :=
  let pairs := rows.flatMap rowPairs
  rows.all (fun row =>
    decide (row.length = 6 ∧ row.Pairwise (· < ·)) &&
      row.all (fun x => decide (x < n))) &&
  pairs.all (fun p => eligible p.1 p.2) &&
  pairs.length == required &&
  markDistinct (fun (x,y) => y*(y-1)/2+x) pairs (Array.replicate (n*(n-1)/2) false)

@[expose] def checkDesign (n : ℕ) (eligible : ℕ → ℕ → Bool) (rows : List (List ℕ)) : Bool :=
  checkPairs n ((rowPairs (List.range n)).countP (fun p => eligible p.1 p.2)) eligible rows

/-- For a complete design the number of required pairs is 0 + 1 + ⋯ + (n−1). -/
@[expose] def checkComplete (n : ℕ) (rows : List (List ℕ)) : Bool :=
  checkPairs n (List.range n).sum (fun _ _ => true) rows

private def liftRow (n : ℕ) (row : List ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun x => x.val ∈ row)

private theorem card_liftRow {n : ℕ} {row : List ℕ}
    (hb : ∀ x ∈ row, x < n) (hd : row.Nodup) :
    (liftRow n row).card = row.length := by
  let emb : Fin n ↪ ℕ := ⟨Fin.val, Fin.val_injective⟩
  have he : (liftRow n row).map emb = row.toFinset := by
    ext x
    simp only [liftRow, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      List.mem_toFinset]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hb x hx⟩, hx, rfl⟩
  rw [← List.toFinset_card_of_nodup hd, ← he, Finset.card_map]

private theorem eq_of_mem_of_flatMap_nodup {α β : Type*} {f : α → List β}
    {as : List α} {a a' : α} {b : β} (hn : (as.flatMap f).Nodup)
    (ha : a ∈ as) (ha' : a' ∈ as) (hb : b ∈ f a) (hb' : b ∈ f a') :
    a = a' := by
  induction as with
  | nil => simp at ha
  | cons head tail ih =>
    simp only [List.flatMap_cons, List.nodup_append] at hn
    rcases List.mem_cons.mp ha with hh | ht
    · rcases List.mem_cons.mp ha' with hh' | ht'
      · exact hh.trans hh'.symm
      · exact False.elim (hn.2.2 _ (hh ▸ hb) _ (List.mem_flatMap.mpr ⟨_, ht', hb'⟩) rfl)
    · rcases List.mem_cons.mp ha' with hh' | ht'
      · exact False.elim (hn.2.2 _ (hh' ▸ hb') _ (List.mem_flatMap.mpr ⟨_, ht, hb⟩) rfl)
      · exact ih hn.2.1 ht ht'

/-- The finite computation certifies a block family with the mathematical pair property. -/
def ofCheck {n : ℕ} {eligible : ℕ → ℕ → Bool} {rows : List (List ℕ)}
    (symmetric : ∀ x y, eligible x y = eligible y x)
    (checked : checkDesign n eligible rows = true) :
    PairDesign (Fin n) (fun x y => eligible x.val y.val = true) := by
  simp only [checkDesign, checkPairs, List.countP_eq_length_filter, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    beq_iff_eq] at checked
  obtain ⟨⟨⟨valid, eligiblePairs⟩, count⟩, marks⟩ := checked
  have rangeOrder : (List.range n).Pairwise (· < ·) := List.pairwise_lt_range
  have nodup := (markDistinct_sound marks).1
  have subset : rows.flatMap rowPairs ⊆
      (rowPairs (List.range n)).filter (fun p => eligible p.1 p.2) := by
    rintro ⟨x,y⟩ hp
    obtain ⟨row, hr, hxy⟩ := List.mem_flatMap.mp hp
    obtain ⟨hx, hy, lt⟩ := (mem_rowPairs (valid row hr).1.2).mp hxy
    exact List.mem_filter.mpr ⟨(mem_rowPairs rangeOrder).mpr
      ⟨List.mem_range.mpr ((valid row hr).2 x hx), List.mem_range.mpr ((valid row hr).2 y hy), lt⟩,
      eligiblePairs _ hp⟩
  have perm := (List.subperm_of_subset nodup subset).perm_of_length_le (Nat.le_of_eq count.symm)
  have coverage (x y : Fin n) (hxy : x.val < y.val) :
      (x.val, y.val) ∈ rows.flatMap rowPairs ↔ eligible x.val y.val = true := by
    rw [perm.mem_iff, List.mem_filter, mem_rowPairs rangeOrder]
    simp [x.isLt, y.isLt, hxy]
  have memLift (row : List ℕ) (x : Fin n) : x ∈ liftRow n row ↔ x.val ∈ row := by
    simp [liftRow]
  refine {
    blocks := { B | ∃ row ∈ rows, liftRow n row = B }
    six := ?_
    eligible_of_mem := ?_
    cover := ?_ }
  · rintro B ⟨row, hrow, rfl⟩
    have ⟨⟨hlen, horder⟩, hbound⟩ := valid row hrow
    rw [card_liftRow hbound (horder.imp (fun h => Nat.ne_of_lt h)), hlen]
  · rintro B ⟨row, hrow, rfl⟩ x hx y hy hne
    have addPair (a b : Fin n) (ha : a.val ∈ row) (hb : b.val ∈ row)
        (hlt : a.val < b.val) : eligible a.val b.val = true :=
      (coverage a b hlt).mp (List.mem_flatMap.mpr
        ⟨row, hrow, (mem_rowPairs (valid row hrow).1.2).mpr ⟨ha, hb, hlt⟩⟩)
    have hne' : x.val ≠ y.val := fun h => hne (Fin.ext h)
    rcases lt_or_gt_of_ne hne' with h | h
    · exact addPair x y ((memLift row x).mp hx) ((memLift row y).mp hy) h
    · rw [symmetric]
      exact addPair y x ((memLift row y).mp hy) ((memLift row x).mp hx) h
  · intro x y hne h
    have ordered (a b : Fin n) (hlt : a.val < b.val) (hel : eligible a.val b.val = true) :
        ∃! B, (∃ row ∈ rows, liftRow n row = B) ∧ a ∈ B ∧ b ∈ B := by
      obtain ⟨row, hrow, hp⟩ := List.mem_flatMap.mp ((coverage a b hlt).mpr hel)
      have ⟨ha, hb, _⟩ := (mem_rowPairs (valid row hrow).1.2).mp hp
      refine ⟨liftRow n row, ⟨⟨row, hrow, rfl⟩, (memLift _ _).mpr ha, (memLift _ _).mpr hb⟩,
        ?_⟩
      rintro _ ⟨⟨other, hother, rfl⟩, hma, hmb⟩
      have hop := (mem_rowPairs (valid other hother).1.2).mpr
        ⟨(memLift _ _).mp hma, (memLift _ _).mp hmb, hlt⟩
      exact congrArg (liftRow n) (eq_of_mem_of_flatMap_nodup nodup hother hrow hop hp)
    have hne' : x.val ≠ y.val := fun h => hne (Fin.ext h)
    rcases lt_or_gt_of_ne hne' with hlt | hlt
    · exact ordered x y hlt h
    · rw [symmetric] at h
      simpa only [Set.mem_ofPred_eq, and_left_comm, and_assoc, and_comm] using ordered y x hlt h

/-- A verified complete block list gives a Steiner system. -/
def steinerOfCheck {n : ℕ} {rows : List (List ℕ)}
    (checked : checkComplete n rows = true) : SteinerSystem (Fin n) := by
  have ok : checkDesign n (fun _ _ => true) rows = true := by
    simpa [checkDesign, checkComplete, List.countP_eq_length_filter, length_rowPairs] using checked
  simpa only [eq_self] using ofCheck (fun _ _ => rfl) ok

end Lemmata.SteinerSixSpectrum
