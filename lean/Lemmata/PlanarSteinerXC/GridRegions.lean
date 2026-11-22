module

public import Lemmata.PlanarSteinerXC.GridNext

/-!
# The regions of the planar cover graph of the grid

The faces of the cover graph `J` of the grid are: one face inside every variable cycle, one
triangle inside every clause clique `A`, two faces inside every edge gadget (`g₁`, between `x_u`,
`A`, `z`, `B`, and `g₂`, between `A`, `x_v`, `C`, `z`), one face for every unit square of the grid,
and the outer face. Around a variable, every literal occurrence has a region *after* it and a region
*before* it (counterclockwise); the planar cyclic order satisfies
`after o = before (next o)`.
-/

@[expose] public section

set_option autoImplicit false

namespace Lemmata.PlanarSteinerXC

namespace Grid

variable {h : ℕ}

/-- Unit squares of the grid, indexed by their lower left corner. -/
abbrev Cell (h : ℕ) := Fin (h - 1) × Fin (h - 1)

/-- The regions of the variable–clause incidence graph: the two gadget faces of every edge, the
unit squares and the outer face. -/
abbrev Region (h : ℕ) := OE h ⊕ OE h ⊕ Cell h ⊕ Unit

/-- The faces of `J`: variable cycles, clause triangles and regions. -/
abbrev Face (h : ℕ) := (Pt h ⊕ OE h) ⊕ OE h ⊕ Region h

instance instDecEqOE : DecidableEq (OE h) := fun a b => Subtype.instDecidableEq a b
instance instDecEqRegion : DecidableEq (Region h) := fun a b => instDecidableEqSum a b
instance instDecEqFace : DecidableEq (Face h) := fun a b => instDecidableEqSum a b

def varF (x : Pt h ⊕ OE h) : Face h := .inl x
def triF (e : OE h) : Face h := .inr (.inl e)
def g1F (e : OE h) : Face h := .inr (.inr (.inl e))
def g2F (e : OE h) : Face h := .inr (.inr (.inr (.inl e)))
def cellF (c : Cell h) : Face h := .inr (.inr (.inr (.inr (.inl c))))
def outerF : Face h := .inr (.inr (.inr (.inr (.inr ()))))

/-- The unit square at `(a, b)`, or the outer face if out of range. -/
def cellAt (a b : ℕ) : Face h :=
  if hab : a + 2 ≤ h ∧ b + 2 ≤ h then cellF (⟨a, by lia⟩, ⟨b, by lia⟩) else outerF

/-- The quadrant of a point between direction `d` and the next direction counterclockwise. -/
def quad (p : Pt h) : Dir → Face h
  | .E => if p.1.val + 1 < h ∧ p.2.val + 1 < h then cellAt p.1.val p.2.val else outerF
  | .N => if 0 < p.1.val ∧ p.2.val + 1 < h then cellAt (p.1.val - 1) p.2.val else outerF
  | .W => if 0 < p.1.val ∧ 0 < p.2.val then cellAt (p.1.val - 1) (p.2.val - 1) else outerF
  | .S => if p.1.val + 1 < h ∧ 0 < p.2.val then cellAt p.1.val (p.2.val - 1) else outerF

theorem quad_outer_of_absent {p : Pt h} {d : Dir} (hd : ¬ present p d) : quad p d = outerF := by
  cases d <;> simp only [present] at hd <;> simp [quad, hd]

theorem quad_outer_of_absent_succ {p : Pt h} {d : Dir} (hd : ¬ present p d.succ) :
    quad p d = outerF := by
  cases d <;> simp only [Dir.succ, present] at hd <;> simp [quad, hd] <;> intros <;> lia

/-- The face to the left of an oriented edge (above a rightward edge, left of an upward one). -/
def leftF (e : OE h) : Face h := if e.1.2 then quad e.1.1 .N else quad e.1.1 .E

/-- The face to the right of an oriented edge. -/
def rightF (e : OE h) : Face h := if e.1.2 then quad e.1.1 .E else quad e.1.1 .S

/-- The region after an occurrence, counterclockwise around its variable. -/
def after (o : OE h × Fin 7) : Face h :=
  match o.2 with
  | 0 => leftF o.1 | 1 => g2F o.1 | 2 => g1F o.1 | 3 => g1F o.1
  | 4 => rightF o.1 | 5 => rightF o.1 | 6 => g2F o.1

/-- The region before an occurrence. -/
def before (o : OE h × Fin 7) : Face h :=
  match o.2 with
  | 0 => g1F o.1 | 1 => leftF o.1 | 2 => g2F o.1 | 3 => rightF o.1
  | 4 => g1F o.1 | 5 => g2F o.1 | 6 => rightF o.1

theorem after_occAt_true (p : Pt h) (d : Dir) (hp : present p d) :
    after (occAt p d true hp) = quad p d := by
  cases d
  · simp [after, occAt, kOf, edgeIn, leftF]
  · simp [after, occAt, kOf, edgeIn, leftF]
  · have h1 : 0 < p.1.val := hp
    simp only [after, occAt, kOf, edgeIn, rightF, quad, Bool.false_eq_true, ite_false]
    congr 1 <;> simp <;> lia
  · have h1 : 0 < p.2.val := hp
    simp only [after, occAt, kOf, edgeIn, rightF, quad, ite_true]
    congr 1 <;> simp <;> lia

theorem before_occAt_false (p : Pt h) (d : Dir) (hp : present p d) :
    before (occAt p d false hp) = quad p d.pred := by
  cases d
  · simp [before, occAt, kOf, edgeIn, rightF, Dir.pred]
  · simp [before, occAt, kOf, edgeIn, rightF, Dir.pred]
  · have h1 : 0 < p.1.val := hp
    simp only [before, occAt, kOf, edgeIn, leftF, quad, Dir.pred, Bool.false_eq_true, ite_false]
    congr 1 <;> simp <;> lia
  · have h1 : 0 < p.2.val := hp
    simp only [before, occAt, kOf, edgeIn, leftF, quad, Dir.pred, ite_true]
    congr 1 <;> simp <;> lia

theorem after_occAt_false (p : Pt h) (d : Dir) (hp : present p d) :
    after (occAt p d false hp) = before (occAt p d true hp) := by
  cases d <;> simp [after, before, occAt, kOf]

variable (hh : 2 ≤ h)

/-- **Planarity of the cyclic order.** The region after an occurrence is the region before the
next occurrence of the same variable. -/
theorem after_eq_before_next (o : OE h × Fin 7) : after o = before (nextPerm hh o) := by
  rw [nextPerm_apply]
  by_cases ho : IsX o
  · obtain ⟨p, d, b, hp, rfl⟩ := exists_occAt ho
    cases b
    · rw [nextOcc_occAt_false, after_occAt_false]
    · rw [nextOcc_occAt_true, after_occAt_true, before_occAt_false]
      rcases Dir.nextIn_skip (pat p) d (pat_good hh p) (pat_eq_true.mpr hp) with hs | ⟨h1, h2⟩
      · rw [hs, Dir.pred_succ]
      · rw [quad_outer_of_absent_succ (by simpa [pat] using h1),
          quad_outer_of_absent (by simpa [pat] using h2)]
  · have hz := (not_isX_iff o).mp ho
    have hnext : nextOcc hh o = (o.1, zNext o.2) := by rw [nextOcc, dif_neg ho]
    rw [hnext]
    obtain ⟨e, k⟩ := o
    simp only at hz
    rcases hz with rfl | rfl | rfl <;> simp [after, before, zNext]

theorem after_ne_before (o : OE h × Fin 7) : after o ≠ before o := by
  obtain ⟨e, k⟩ := o
  have hq : ∀ (p : Pt h) (d : Dir), quad p d ≠ g1F e ∧ quad p d ≠ g2F e := by
    intro p d
    cases d <;> simp only [quad, cellAt] <;> split_ifs <;> simp [g1F, g2F, cellF, outerF]
  have hl : leftF e ≠ g1F e ∧ leftF e ≠ g2F e := by
    unfold leftF; split_ifs <;> exact hq _ _
  have hr : rightF e ≠ g1F e ∧ rightF e ≠ g2F e := by
    unfold rightF; split_ifs <;> exact hq _ _
  fin_cases k <;> simp only [after, before] <;>
    first
    | exact hl.1 | exact hl.2 | exact hr.1 | exact hr.2
    | exact (fun h' => hl.1 h'.symm) | exact (fun h' => hl.2 h'.symm)
    | exact (fun h' => hr.1 h'.symm) | exact (fun h' => hr.2 h'.symm)
    | simp [g1F, g2F]

end Grid

end Lemmata.PlanarSteinerXC
