module

public import Lemmata.PlanarSteinerXC.CoverGraph

/-!
# The square grid

Grid points are pairs `(i, j)` of elements of `Fin h`; `i` is the horizontal coordinate. An
*oriented edge* is a point together with a direction: rightward (`false`) or upward (`true`).
Oriented edges are in bijection with the edges of `grid h = pathGraph h □ pathGraph h`, and there
are `2 h (h - 1)` of them.
-/

@[expose] public section

set_option autoImplicit false

namespace Lemmata.PlanarSteinerXC

open SimpleGraph

namespace Grid

variable (h : ℕ)

/-- Grid points. -/
abbrev Pt := Fin h × Fin h

/-- Oriented grid edges: from a point to the right (`false`) or upward (`true`). -/
abbrev OE := {x : Pt h × Bool // if x.2 then x.1.2.val + 1 < h else x.1.1.val + 1 < h}

variable {h}

/-- The source of an oriented edge. -/
def src (e : OE h) : Pt h := e.1.1

theorem oe_vert {e : OE h} (hv : e.1.2 = true) : e.1.1.2.val + 1 < h := by
  have := e.2; simp only [hv, ite_true] at this; exact this

theorem oe_horiz {e : OE h} (hv : e.1.2 = false) : e.1.1.1.val + 1 < h := by
  have := e.2; simp only [hv, Bool.false_eq_true, ite_false] at this; exact this

/-- The target of an oriented edge. -/
def tgt (e : OE h) : Pt h :=
  if hv : e.1.2 = true then (e.1.1.1, ⟨e.1.1.2.val + 1, oe_vert hv⟩)
  else (⟨e.1.1.1.val + 1, oe_horiz (by simpa using hv)⟩, e.1.1.2)

theorem tgt_vert {e : OE h} (hv : e.1.2 = true) :
    tgt e = (e.1.1.1, ⟨e.1.1.2.val + 1, oe_vert hv⟩) := by
  simp [tgt, hv]

theorem tgt_horiz {e : OE h} (hv : e.1.2 = false) :
    tgt e = (⟨e.1.1.1.val + 1, oe_horiz hv⟩, e.1.1.2) := by
  simp [tgt, hv]

theorem grid_adj_src_tgt (e : OE h) : (grid h).Adj (src e) (tgt e) := by
  cases hv : e.1.2
  · simp [tgt_horiz hv, grid, boxProd_adj, pathGraph_adj, src]
  · simp [tgt_vert hv, grid, boxProd_adj, pathGraph_adj, src]

/-- Coordinate sum: the target is one step beyond the source. -/
theorem tgt_sum (e : OE h) :
    (tgt e).1.val + (tgt e).2.val = (src e).1.val + (src e).2.val + 1 := by
  cases hv : e.1.2
  · rw [tgt_horiz hv]; simp [src]; lia
  · rw [tgt_vert hv]; simp [src]; lia

theorem src_tgt_injective {e e' : OE h} (h1 : src e = src e') (h2 : tgt e = tgt e') : e = e' := by
  obtain ⟨⟨p, d⟩, hp⟩ := e
  obtain ⟨⟨p', d'⟩, hp'⟩ := e'
  simp only [src] at h1
  subst h1
  congr 1
  simp only [Prod.mk.injEq, true_and]
  cases d <;> cases d'
  · rfl
  · exfalso
    rw [tgt_horiz (e := ⟨(p, false), hp⟩) rfl, tgt_vert (e := ⟨(p, true), hp'⟩) rfl] at h2
    simp only [Prod.mk.injEq, Fin.ext_iff] at h2
    lia
  · exfalso
    rw [tgt_vert (e := ⟨(p, true), hp⟩) rfl, tgt_horiz (e := ⟨(p, false), hp'⟩) rfl] at h2
    simp only [Prod.mk.injEq, Fin.ext_iff] at h2
    lia
  · rfl

/-- Oriented edges are the edges of the grid. -/
noncomputable def oeEquiv : OE h ≃ (grid h).edgeSet :=
  Equiv.ofBijective (fun e => ⟨s(src e, tgt e), grid_adj_src_tgt e⟩) <| by
    constructor
    · intro e e' heq
      have := congrArg Subtype.val heq
      simp only [Sym2.eq_iff] at this
      rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact src_tgt_injective h1 h2
      · exfalso
        have s1 := tgt_sum e
        have s2 := tgt_sum e'
        rw [h1, h2] at s1
        lia
    · rintro ⟨ε, hε⟩
      induction ε using Sym2.ind with
      | h a b =>
        have hab : (grid h).Adj a b := hε
        unfold grid at hab
        rw [boxProd_adj, pathGraph_adj, pathGraph_adj] at hab
        rcases hab with ⟨h1 | h1, h2⟩ | ⟨h1 | h1, h2⟩
        · refine ⟨⟨(a, false), by simp; lia⟩, Subtype.ext ?_⟩
          simp only [src]
          rw [tgt_horiz rfl]
          congr 1; ext <;> simp [Fin.ext_iff] <;> lia
        · refine ⟨⟨(b, false), by simp; lia⟩, Subtype.ext ?_⟩
          simp only [src]
          rw [tgt_horiz rfl, Sym2.eq_swap]
          congr 1; ext <;> simp [Fin.ext_iff] <;> lia
        · refine ⟨⟨(a, true), by simp; lia⟩, Subtype.ext ?_⟩
          simp only [src]
          rw [tgt_vert rfl]
          congr 1; ext <;> simp [Fin.ext_iff] <;> lia
        · refine ⟨⟨(b, true), by simp; lia⟩, Subtype.ext ?_⟩
          simp only [src]
          rw [tgt_vert rfl, Sym2.eq_swap]
          congr 1; ext <;> simp [Fin.ext_iff] <;> lia

theorem oeEquiv_apply (e : OE h) : ((oeEquiv e : (grid h).edgeSet) : Sym2 (Pt h)) = s(src e, tgt e) :=
  rfl

theorem card_fin_lt (h : ℕ) :
    (Finset.univ.filter (fun i : Fin h => i.val + 1 < h)).card = h - 1 := by
  rcases h with _ | h
  · simp
  · have : Finset.univ.filter (fun i : Fin (h + 1) => i.val + 1 < h + 1) =
        (Finset.univ.filter (fun i : Fin (h + 1) => i ≠ Fin.last h)) := by
      ext i; simp [Fin.ext_iff, Fin.val_last]; lia
    rw [this, Finset.filter_ne' , Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_fin]

/-- There are `2 h (h - 1)` oriented edges. -/
theorem card_oe : Fintype.card (OE h) = 2 * h * (h - 1) := by
  classical
  rw [Fintype.card_subtype]
  have : (Finset.univ.filter fun x : Pt h × Bool =>
      if x.2 then x.1.2.val + 1 < h else x.1.1.val + 1 < h) =
      ((Finset.univ.filter fun p : Pt h => p.1.val + 1 < h) ×ˢ {false}) ∪
      ((Finset.univ.filter fun p : Pt h => p.2.val + 1 < h) ×ˢ {true}) := by
    ext ⟨p, d⟩
    cases d <;> simp
  rw [this, Finset.card_union_of_disjoint]
  · rw [Finset.card_product, Finset.card_product, Finset.card_singleton, Finset.card_singleton]
    have h1 : (Finset.univ.filter fun p : Pt h => p.1.val + 1 < h) =
        (Finset.univ.filter fun i : Fin h => i.val + 1 < h) ×ˢ Finset.univ := by
      ext p; simp
    have h2 : (Finset.univ.filter fun p : Pt h => p.2.val + 1 < h) =
        Finset.univ ×ˢ (Finset.univ.filter fun i : Fin h => i.val + 1 < h) := by
      ext p; simp
    rw [h1, h2, Finset.card_product, Finset.card_product, card_fin_lt, Finset.card_univ,
      Fintype.card_fin]
    ring
  · rw [Finset.disjoint_left]
    rintro ⟨p, d⟩ h1 h2
    simp only [Finset.mem_product, Finset.mem_singleton] at h1 h2
    rw [h1.2] at h2; exact absurd h2.2 (by decide)

end Grid

end Lemmata.PlanarSteinerXC
