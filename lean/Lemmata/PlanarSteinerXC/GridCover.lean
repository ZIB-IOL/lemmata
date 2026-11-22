module

public import Lemmata.PlanarSteinerXC.GridRegions

/-!
# The cover graph of the grid formula

`gridCNF` is the product formula `z_e = x_u x_v` of the `h × h` grid with the planar cyclic order
of the literal occurrences, and `Jg` is its cover graph (Lemma 3). We describe the neighbourhoods:
a true port `(o, 0)` is adjacent to `(o, 1)`, to the false port of the previous occurrence and,
for a negative literal, to the literal vertex `(o, 2)`; symmetrically for false ports; a literal
vertex is adjacent to its port and to the other literal vertices of its clause.
-/

@[expose] public section

set_option autoImplicit false

namespace Lemmata.PlanarSteinerXC

namespace Grid

open SimpleGraph

variable {h : ℕ} (hh : 2 ≤ h)

/-- The product formula of the grid with the planar cyclic order of the occurrences. -/
def gridCNF : CNF (OE h × Fin 7) (Pt h ⊕ OE h) (OE h × Fin 3) :=
  productCNF src tgt (nextPerm hh) (var_nextPerm hh) (nextPerm_cyclic hh)

/-- The planar cover graph `J` of the grid formula. -/
abbrev Jg : SimpleGraph ((OE h × Fin 7) × Fin 3) := (gridCNF hh).coverGraph

abbrev JV (h : ℕ) := (OE h × Fin 7) × Fin 3

theorem gridCNF_next : (gridCNF hh).next = nextPerm hh := rfl
theorem gridCNF_var : (gridCNF hh).var = prodVar src tgt := rfl
theorem gridCNF_clause : (gridCNF hh).clause = prodClause := rfl
theorem gridCNF_pos : (gridCNF hh).pos = prodPos := rfl

theorem nextPerm_ne (o : OE h × Fin 7) : nextPerm hh o ≠ o := by
  rw [nextPerm_apply]
  by_cases ho : IsX o
  · obtain ⟨p, d, b, hp, rfl⟩ := exists_occAt ho
    cases b
    · rw [nextOcc_occAt_false]
      intro heq; have := (occAt_inj _ _ heq).2.2; simp at this
    · rw [nextOcc_occAt_true]
      intro heq; have := (occAt_inj _ _ heq).2.2; simp at this
  · have hz := (not_isX_iff o).mp ho
    rw [nextOcc, dif_neg ho]
    obtain ⟨e, k⟩ := o
    simp only at hz
    rcases hz with rfl | rfl | rfl <;> simp [zNext]

theorem prev_ne (o : OE h × Fin 7) : (nextPerm hh).symm o ≠ o := by
  intro heq
  have := nextPerm_ne hh ((nextPerm hh).symm o)
  rw [Equiv.apply_symm_apply, heq] at this
  exact this rfl

/-- Adjacency in `Jg`. -/
theorem Jg_adj (a b : JV h) : (Jg hh).Adj a b ↔ a ≠ b ∧
    ((gridCNF hh).rel a b ∨ (gridCNF hh).rel b a) := by
  unfold Jg CNF.coverGraph; rw [fromRel_adj]

/-- Clique partners: different occurrences of the same clause. -/
def SameClause (o o' : OE h × Fin 7) : Prop := o ≠ o' ∧ prodClause o = prodClause o'

instance (o o' : OE h × Fin 7) : Decidable (SameClause o o') := by unfold SameClause; infer_instance

theorem falsePort_eq (o : OE h × Fin 7) :
    (gridCNF hh).falsePort o = if prodPos o then 1 else 0 := rfl

theorem adj_port0 (o : OE h × Fin 7) (b : JV h) :
    (Jg hh).Adj (o, 0) b ↔ b = (o, 1) ∨ b = ((nextPerm hh).symm o, 1) ∨
      (b = (o, 2) ∧ prodPos o = false) := by
  obtain ⟨o', r⟩ := b
  rw [Jg_adj]
  constructor
  · rintro ⟨hne, h1 | h1⟩ <;> unfold CNF.rel at h1 <;> simp only at h1
    · rcases h1 with ⟨rfl, -, rfl⟩ | ⟨-, h2, -⟩ | ⟨-, -, h2, -⟩ | ⟨-, h2, -⟩
      · left; rfl
      · simp at h2
      · simp at h2
      · simp at h2
    · rcases h1 with ⟨-, -, h2⟩ | ⟨h2, rfl, -⟩ | ⟨-, -, -, h2⟩ | ⟨rfl, rfl, h2⟩
      · simp at h2
      · right; left; rw [gridCNF_next] at h2; rw [h2]; simp
      · simp at h2
      · right; right; refine ⟨rfl, ?_⟩
        rw [falsePort_eq] at h2
        cases hp : prodPos o' <;> simp_all
  · rintro (h | h | ⟨h, hp⟩) <;> cases h
    · exact ⟨by simp, Or.inl (Or.inl ⟨rfl, rfl, rfl⟩)⟩
    · refine ⟨by simp, Or.inr (Or.inr (Or.inl ⟨?_, rfl, rfl⟩))⟩
      simp [gridCNF_next]
    · refine ⟨by simp, Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, ?_⟩)))⟩
      rw [falsePort_eq, hp]; rfl

theorem adj_port1 (o : OE h × Fin 7) (b : JV h) :
    (Jg hh).Adj (o, 1) b ↔ b = (o, 0) ∨ b = (nextPerm hh o, 0) ∨
      (b = (o, 2) ∧ prodPos o = true) := by
  obtain ⟨o', r⟩ := b
  rw [Jg_adj]
  constructor
  · rintro ⟨hne, h1 | h1⟩ <;> unfold CNF.rel at h1 <;> simp only at h1
    · rcases h1 with ⟨-, h2, -⟩ | ⟨rfl, -, rfl⟩ | ⟨-, -, h2, -⟩ | ⟨-, h2, -⟩
      · simp at h2
      · right; left; rfl
      · simp at h2
      · simp at h2
    · rcases h1 with ⟨rfl, rfl, -⟩ | ⟨-, -, h2⟩ | ⟨-, -, -, h2⟩ | ⟨rfl, rfl, h2⟩
      · left; rfl
      · simp at h2
      · simp at h2
      · right; right; refine ⟨rfl, ?_⟩
        rw [falsePort_eq] at h2
        cases hp : prodPos o' <;> simp_all
  · rintro (h | h | ⟨h, hp⟩) <;> cases h
    · exact ⟨by simp, Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)⟩
    · exact ⟨by simp, Or.inl (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))⟩
    · refine ⟨by simp, Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, ?_⟩)))⟩
      rw [falsePort_eq, hp]; rfl

theorem adj_lit (o : OE h × Fin 7) (b : JV h) :
    (Jg hh).Adj (o, 2) b ↔ b = (o, if prodPos o then 1 else 0) ∨
      (∃ o', b = (o', 2) ∧ SameClause o o') := by
  obtain ⟨o', r⟩ := b
  rw [Jg_adj]
  constructor
  · rintro ⟨hne, h1 | h1⟩ <;> unfold CNF.rel at h1 <;> simp only at h1
    · rcases h1 with ⟨-, h2, -⟩ | ⟨-, h2, -⟩ | ⟨h2, h3, -, rfl⟩ | ⟨rfl, -, rfl⟩
      · simp at h2
      · simp at h2
      · right; exact ⟨o', rfl, h2, h3⟩
      · left; rw [falsePort_eq]
    · rcases h1 with ⟨-, -, h2⟩ | ⟨-, -, h2⟩ | ⟨h2, h3, rfl, -⟩ | ⟨rfl, rfl, h2⟩
      · simp at h2
      · simp at h2
      · right; exact ⟨o', rfl, fun h => h2 h.symm, h3.symm⟩
      · exfalso; rw [falsePort_eq] at h2; revert h2; split_ifs <;> simp
  · rintro (h | ⟨o'', h, h1, h2⟩)
    · cases h
      refine ⟨?_, Or.inl (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, by rw [falsePort_eq]⟩)))⟩
      split_ifs <;> simp
    · cases h
      exact ⟨by simpa using h1, Or.inl (Or.inr (Or.inr (Or.inl ⟨h1, h2, rfl, rfl⟩)))⟩

end Grid

end Lemmata.PlanarSteinerXC
