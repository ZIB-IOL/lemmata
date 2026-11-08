module

public import Lemmata.RM59.Proof.BinarySpan9
public import Lemmata.RM59.Proof.CommonConfigurations
public import Mathlib.LinearAlgebra.LinearIndependent.Basic

@[expose] public section

namespace Lemmata.RM59.SimplexSearch

open Packed PlaneCertificates

def packedSpan (points : Finset PackedPoint) : Submodule Field (Point 9) :=
  Submodule.span Field (decodePoint '' (points : Set PackedPoint))

theorem packedSpan_mono {points other : Finset PackedPoint} (h : points ⊆ other) :
    packedSpan points ≤ packedSpan other := by
  apply Submodule.span_mono
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x, h hx, rfl⟩

theorem mem_packedSpan {points : Finset PackedPoint} {x : PackedPoint} (hx : x ∈ points) :
    decodePoint x ∈ packedSpan points := Submodule.subset_span ⟨x, hx, rfl⟩

def RowsIn (basis : BinarySpan9.State) (points : Finset PackedPoint) : Prop :=
  ∀ i, decodePoint (basis.rows.get i) ∈ packedSpan points

def RelativeIndependent (chosen : List PackedPoint) (extension : Finset PackedPoint) : Prop :=
  ∀ x ∈ extension, decodePoint x ∉ packedSpan (chosen.toFinset ∪ extension.erase x)

def TripleCompatible (allowed : PackedAllowed) (points : Finset PackedPoint) : Prop :=
  ∀ x ∈ points, ∀ y ∈ points, ∀ z ∈ points,
    x ≠ y → x ≠ z → y ≠ z → allowed (xorPoint x y) (xorPoint x z) = true

private theorem chosen_step (chosen : List PackedPoint) (x : PackedPoint) :
    (chosen ++ [x]).toFinset = insert x chosen.toFinset := by
  ext y
  simp [or_comm]

theorem relativeIndependent_not_mem {chosen : List PackedPoint} {extension : Finset PackedPoint}
    (h : RelativeIndependent chosen extension) {x : PackedPoint} (hx : x ∈ extension) :
    x ∉ chosen.toFinset := by
  intro hchosen
  exact h x hx (mem_packedSpan (Finset.mem_union_left _ hchosen))

theorem relativeIndependent_step {chosen : List PackedPoint} {extension : Finset PackedPoint}
    (h : RelativeIndependent chosen extension) {x : PackedPoint} (hx : x ∈ extension) :
    RelativeIndependent (chosen ++ [x]) (extension.erase x) := by
  intro y hy hmem
  apply h y (Finset.mem_erase.mp hy).2
  apply packedSpan_mono (other := chosen.toFinset ∪ extension.erase y) ?_ hmem
  rw [chosen_step]
  intro z hz
  rcases Finset.mem_union.mp hz with hz | hz
  · rcases Finset.mem_insert.mp hz with rfl | hz
    · exact Finset.mem_union_right _
        (Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hy).1.symm, hx⟩)
    · exact Finset.mem_union_left _ hz
  · exact Finset.mem_union_right _
      (Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hz).1,
        (Finset.mem_erase.mp (Finset.mem_erase.mp hz).2).2⟩)

theorem rowsIn_step {chosen : List PackedPoint} {basis : BinarySpan9.State}
    (h : RowsIn basis chosen.toFinset) (x : PackedPoint) :
    RowsIn (BinarySpan9.insert basis x) (chosen ++ [x]).toFinset := by
  rw [chosen_step]
  apply BinarySpan9.insert_rows_mem
  · intro i
    exact packedSpan_mono (Finset.subset_insert _ _) (h i)
  · exact mem_packedSpan (Finset.mem_insert_self _ _)

private theorem points_step {chosen : List PackedPoint} {extension : Finset PackedPoint}
    {x : PackedPoint} (hx : x ∈ extension) :
    (chosen ++ [x]).toFinset ∪ extension.erase x = chosen.toFinset ∪ extension := by
  rw [chosen_step]
  ext y
  by_cases hy : y = x <;> simp [hy, hx]

private theorem first_member_split (extension : Finset PackedPoint) (candidates : List PackedPoint)
    (hex : ∃ x ∈ candidates, x ∈ extension) :
    ∃ before x after, candidates = before ++ x :: after ∧ x ∈ extension ∧
      ∀ y ∈ before, y ∉ extension := by
  induction candidates with
  | nil =>
    obtain ⟨x, hx, _⟩ := hex
    cases hx
  | cons x candidates ih =>
    by_cases hx : x ∈ extension
    · exact ⟨[], x, candidates, rfl, hx, by simp⟩
    · have htail : ∃ y ∈ candidates, y ∈ extension := by
        obtain ⟨y, hy, hyext⟩ := hex
        rcases List.mem_cons.mp hy with rfl | hy
        · exact (hx hyext).elim
        · exact ⟨y, hy, hyext⟩
      obtain ⟨before, y, after, heq, hy, hbefore⟩ := ih htail
      refine ⟨x :: before, y, after, by simp [heq], hy, ?_⟩
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact hx
      · exact hbefore z hz

private theorem choice_mem (before : List PackedPoint) (x : PackedPoint) (after : List PackedPoint) :
    (x, after) ∈ choices (before ++ x :: after) := by
  induction before with
  | nil => simp [choices]
  | cons y before ih => exact List.mem_cons_of_mem _ ih

private theorem erase_subset_after (extension : Finset PackedPoint) (before : List PackedPoint)
    (x : PackedPoint) (after : List PackedPoint)
    (hsubset : extension ⊆ (before ++ x :: after).toFinset)
    (hbefore : ∀ y ∈ before, y ∉ extension) : extension.erase x ⊆ after.toFinset := by
  intro y hy
  obtain ⟨hne, hyext⟩ := Finset.mem_erase.mp hy
  have hc := List.mem_toFinset.mp (hsubset hyext)
  rcases List.mem_append.mp hc with hc | hc
  · exact (hbefore y hc hyext).elim
  · rcases List.mem_cons.mp hc with heq | hc
    · exact (hne heq).elim
    · exact List.mem_toFinset.mpr hc

theorem existsExtension_complete (allowed : PackedAllowed) (remaining : Nat)
    (chosen candidates : List PackedPoint) (basis : BinarySpan9.State)
    (extension : Finset PackedPoint) (hcard : extension.card = remaining)
    (hsubset : extension ⊆ candidates.toFinset) (hrows : RowsIn basis chosen.toFinset)
    (hind : RelativeIndependent chosen extension)
    (htriples : TripleCompatible allowed (chosen.toFinset ∪ extension)) :
    existsExtension allowed remaining chosen candidates basis = true := by
  induction remaining generalizing chosen candidates basis extension with
  | zero => rfl
  | succ remaining ih =>
    have hlength : remaining + 1 ≤ candidates.length := by
      have hc := (Finset.card_le_card hsubset).trans candidates.toFinset_card_le
      omega
    have hnonempty : extension.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨x, hx⟩ := hnonempty
    obtain ⟨before, x, after, rfl, hx, hbefore⟩ := first_member_split extension candidates
      ⟨x, List.mem_toFinset.mp (hsubset hx), hx⟩
    rw [existsExtension, if_neg (by omega)]
    apply List.any_eq_true.mpr
    refine ⟨(x, after), choice_mem before x after, ?_⟩
    have hxreduce : BinarySpan9.reduce basis x ≠ 0 := by
      intro hz
      apply hind x hx
      apply packedSpan_mono Finset.subset_union_left
      exact BinarySpan9.mem_of_reduce_eq_zero basis _ hrows x hz
    simp only [if_neg hxreduce]
    have hrows' := rowsIn_step hrows x
    have hind' := relativeIndependent_step hind hx
    have hafter := erase_subset_after extension before x after hsubset hbefore
    apply ih (chosen ++ [x]) _ (BinarySpan9.insert basis x) (extension.erase x)
    · rw [Finset.card_erase_of_mem hx, hcard]
      omega
    · intro y hy
      apply List.mem_toFinset.mpr
      apply List.mem_filter.mpr
      refine ⟨List.mem_toFinset.mp (hafter hy), ?_⟩
      apply Bool.and_eq_true_iff.mpr
      constructor
      · apply bne_iff_ne.mpr
        intro hz
        apply hind' y hy
        apply packedSpan_mono Finset.subset_union_left
        exact BinarySpan9.mem_of_reduce_eq_zero _ _ hrows' y hz
      · apply List.all_eq_true.mpr
        intro z hz
        have hxz : x ≠ z := by
          intro heq
          exact relativeIndependent_not_mem hind hx (heq.symm ▸ List.mem_toFinset.mpr hz)
        have hyz : y ≠ z := by
          intro heq
          exact relativeIndependent_not_mem hind (Finset.mem_erase.mp hy).2
            (heq.symm ▸ List.mem_toFinset.mpr hz)
        exact htriples z (Finset.mem_union_left _ (List.mem_toFinset.mpr hz))
          x (Finset.mem_union_right _ hx) y
          (Finset.mem_union_right _ (Finset.mem_erase.mp hy).2)
          hxz.symm hyz.symm (Finset.mem_erase.mp hy).1.symm
    · exact hrows'
    · exact hind'
    · rw [points_step hx]
      exact htriples

end Lemmata.RM59.SimplexSearch
