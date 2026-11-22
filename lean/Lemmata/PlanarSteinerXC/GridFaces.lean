module

public import Lemmata.PlanarSteinerXC.GridCover
public import Lemmata.PlanarSteinerXC.FaceSystem

/-!
# The faces of the cover graph of the grid

Every edge of `Jg` is assigned the two faces on its sides:

* the pair edge `(o,0)(o,1)` separates the variable face from the region on the side of the
  literal vertex (the region after `o` for a negative literal and before `o` for a positive one);
* the cycle edge `(o,1)(next o,0)` separates the variable face from the region after `o`;
* the port edge of `(o,2)` separates the regions after and before `o`;
* clique edges separate the clause triangle and the gadget regions.
-/

@[expose] public section

set_option autoImplicit false

namespace Lemmata.PlanarSteinerXC

namespace Grid

open SimpleGraph

variable {h : ℕ} (hh : 2 ≤ h)

/-- The region on the side of the literal vertex of the pair of `o`. -/
def rpair (o : OE h × Fin 7) : Face h := if prodPos o then before o else after o

/-- Faces of the clique edge between the occurrences `(e, k)` and `(e, k')`. -/
def cliqueF (e : OE h) (k k' : Fin 7) : Finset (Face h) :=
  if k = 0 ∧ k' = 1 then {triF e, leftF e}
  else if k = 0 ∧ k' = 2 then {triF e, g1F e}
  else if k = 1 ∧ k' = 2 then {triF e, g2F e}
  else if k = 3 ∧ k' = 4 then {g1F e, rightF e}
  else if k = 5 ∧ k' = 6 then {g2F e, rightF e}
  else ∅

/-- Faces of a directed pair of vertices. -/
def dFaces (a b : JV h) : Finset (Face h) :=
  (if a.1 = b.1 ∧ a.2 = 0 ∧ b.2 = 1 then {varF (prodVar src tgt a.1), rpair a.1} else ∅) ∪
  (if b.1 = nextPerm hh a.1 ∧ a.2 = 1 ∧ b.2 = 0 then {varF (prodVar src tgt a.1), after a.1}
    else ∅) ∪
  (if a.1 = b.1 ∧ a.2 = 2 ∧ b.2 = (if prodPos a.1 then 1 else 0) then {after a.1, before a.1}
    else ∅) ∪
  (if a.2 = 2 ∧ b.2 = 2 ∧ a.1.1 = b.1.1 then cliqueF a.1.1 a.1.2 b.1.2 else ∅)

/-- The faces on the two sides of an edge. -/
def edgeFaces : Sym2 (JV h) → Finset (Face h) :=
  Sym2.lift ⟨fun a b => dFaces hh a b ∪ dFaces hh b a, fun _ _ => Finset.union_comm _ _⟩

theorem edgeFaces_mk (a b : JV h) : edgeFaces hh s(a, b) = dFaces hh a b ∪ dFaces hh b a := rfl

theorem faces_pair (o : OE h × Fin 7) :
    edgeFaces hh s((o, 0), (o, 1)) = {varF (prodVar src tgt o), rpair o} := by
  have h1 := (nextPerm_ne hh o).symm
  simp [edgeFaces_mk, dFaces, h1]

theorem faces_cycle (o : OE h × Fin 7) :
    edgeFaces hh s((o, 1), (nextPerm hh o, 0)) = {varF (prodVar src tgt o), after o} := by
  have h1 := nextPerm_ne hh o
  simp [edgeFaces_mk, dFaces, h1]

theorem faces_port (o : OE h × Fin 7) :
    edgeFaces hh s((o, 2), (o, if prodPos o then 1 else 0)) = {after o, before o} := by
  cases hp : prodPos o <;> simp [edgeFaces_mk, dFaces, hp]

theorem faces_clique (o o' : OE h × Fin 7) (he : o.1 = o'.1) (hne : o ≠ o') :
    edgeFaces hh s((o, 2), (o', 2)) = cliqueF o.1 o.2 o'.2 ∪ cliqueF o.1 o'.2 o.2 := by
  simp [edgeFaces_mk, dFaces, hne, he, Ne.symm hne]

/-! ### Distinctness of faces -/

/-- Region faces (the gadget faces, the unit squares and the outer face). -/
def IsReg : Face h → Prop
  | .inr (.inr _) => True
  | _ => False

theorem isReg_cellAt (a b : ℕ) : IsReg (cellAt (h := h) a b) := by
  unfold cellAt; split_ifs <;> trivial

theorem isReg_quad (p : Pt h) (d : Dir) : IsReg (quad p d) := by
  cases d <;> simp only [quad] <;> split_ifs <;> first | exact isReg_cellAt _ _ | trivial

theorem isReg_leftF (e : OE h) : IsReg (leftF e) := by
  unfold leftF; split_ifs <;> exact isReg_quad _ _

theorem isReg_rightF (e : OE h) : IsReg (rightF e) := by
  unfold rightF; split_ifs <;> exact isReg_quad _ _

theorem isReg_after (o : OE h × Fin 7) : IsReg (after o) := by
  obtain ⟨e, k⟩ := o
  fin_cases k <;> first | exact isReg_leftF e | exact isReg_rightF e | trivial

theorem isReg_before (o : OE h × Fin 7) : IsReg (before o) := by
  obtain ⟨e, k⟩ := o
  fin_cases k <;> first | exact isReg_leftF e | exact isReg_rightF e | trivial

theorem isReg_rpair (o : OE h × Fin 7) : IsReg (rpair o) := by
  unfold rpair; split_ifs
  · exact isReg_before o
  · exact isReg_after o

theorem ne_varF {f : Face h} (hf : IsReg f) (x : Pt h ⊕ OE h) : f ≠ varF x := by
  rintro rfl; exact hf

theorem ne_triF {f : Face h} (hf : IsReg f) (e : OE h) : f ≠ triF e := by
  rintro rfl; exact hf

theorem quad_ne_g (p : Pt h) (d : Dir) (e : OE h) : quad p d ≠ g1F e ∧ quad p d ≠ g2F e := by
  cases d <;> simp only [quad, cellAt] <;> split_ifs <;> simp [g1F, g2F, cellF, outerF]

theorem leftF_ne_g (e e' : OE h) : leftF e ≠ g1F e' ∧ leftF e ≠ g2F e' := by
  unfold leftF; split_ifs <;> exact quad_ne_g _ _ _

theorem rightF_ne_g (e e' : OE h) : rightF e ≠ g1F e' ∧ rightF e ≠ g2F e' := by
  unfold rightF; split_ifs <;> exact quad_ne_g _ _ _

theorem g1F_ne_g2F (e e' : OE h) : g1F e ≠ g2F e' := by simp [g1F, g2F]

/-! ### Counting -/

noncomputable instance : DecidableRel (Jg hh).Adj := Classical.decRel _

/-- The edges of `Jg` on the boundary of a face. -/
noncomputable def faceEdges (f : Face h) : Finset (Sym2 (JV h)) :=
  (Jg hh).edgeFinset.filter (fun ε => f ∈ edgeFaces hh ε)

/-- The other end of an edge. -/
def oEnd (w : JV h) (ε : Sym2 (JV h)) : JV h := if hw : w ∈ ε then Sym2.Mem.other' hw else w

theorem oEnd_spec {w : JV h} {ε : Sym2 (JV h)} (hw : w ∈ ε) : s(w, oEnd w ε) = ε := by
  unfold oEnd; rw [dif_pos hw]; exact Sym2.other_spec' hw

theorem oEnd_mk (w w' : JV h) : oEnd w s(w, w') = w' :=
  Sym2.congr_right.mp (oEnd_spec (Sym2.mem_mk_left w w'))

theorem edgeDeg_faceEdges (f : Face h) (w : JV h) :
    edgeDeg (faceEdges hh f) w =
      (((Jg hh).neighborFinset w).filter (fun w' => f ∈ edgeFaces hh s(w, w'))).card := by
  unfold edgeDeg faceEdges
  symm
  apply Finset.card_nbij' (fun w' => s(w, w')) (fun ε => oEnd w ε)
  · intro w' hw'
    simp only [Finset.mem_coe, Finset.mem_filter, mem_neighborFinset] at hw'
    simp only [Finset.mem_coe, Finset.mem_filter, mem_edgeFinset, mem_edgeSet]
    exact ⟨⟨hw'.1, hw'.2⟩, Sym2.mem_mk_left _ _⟩
  · intro ε hε
    simp only [Finset.mem_coe, Finset.mem_filter, mem_edgeFinset] at hε
    obtain ⟨⟨hε1, hε2⟩, hε3⟩ := hε
    have hs := oEnd_spec hε3
    simp only [Finset.mem_coe, Finset.mem_filter, mem_neighborFinset]
    rw [hs]
    refine ⟨?_, hε2⟩
    rw [← mem_edgeSet, hs]; exact hε1
  · intro w' _; exact oEnd_mk w w'
  · intro ε hε
    simp only [Finset.mem_coe, Finset.mem_filter] at hε
    exact oEnd_spec hε.2

theorem count_tri {α β : Type*} [DecidableEq α] [DecidableEq β] (F : α → Finset β)
    {a₁ a₂ a₃ : α} {x y z : β} (f : β) (h12 : a₁ ≠ a₂) (h13 : a₁ ≠ a₃) (h23 : a₂ ≠ a₃)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (h1 : F a₁ = {x, y}) (h2 : F a₂ = {x, z})
    (h3 : F a₃ = {y, z}) :
    (({a₁, a₂, a₃} : Finset α).filter (fun a => f ∈ F a)).card = 0 ∨
      (({a₁, a₂, a₃} : Finset α).filter (fun a => f ∈ F a)).card = 2 := by
  rw [Finset.filter_insert, Finset.filter_insert, Finset.filter_singleton, h1, h2, h3]
  by_cases hx : f = x
  · subst hx; right
    simp [hxy, hxz, h12]
  by_cases hy : f = y
  · subst hy; right
    simp [hxy.symm, hyz, h13]
  by_cases hz : f = z
  · subst hz; right
    simp [hxz.symm, hyz.symm, h23]
  · left; simp [hx, hy, hz]

theorem count_two {α β : Type*} [DecidableEq α] [DecidableEq β] (F : α → Finset β)
    {a₁ a₂ : α} {x y : β} (f : β) (h12 : a₁ ≠ a₂) (h1 : F a₁ = {x, y}) (h2 : F a₂ = {x, y}) :
    (({a₁, a₂} : Finset α).filter (fun a => f ∈ F a)).card = 0 ∨
      (({a₁, a₂} : Finset α).filter (fun a => f ∈ F a)).card = 2 := by
  rw [Finset.filter_insert, Finset.filter_singleton, h1, h2]
  by_cases hf : f ∈ ({x, y} : Finset β)
  · right; simp only [hf, if_true]; rw [Finset.card_pair h12]
  · left; simp [hf]

theorem deg_tri (w : JV h) {a₁ a₂ a₃ : JV h} {x y z : Face h} (f : Face h)
    (hN : ∀ b, (Jg hh).Adj w b ↔ b = a₁ ∨ b = a₂ ∨ b = a₃)
    (h12 : a₁ ≠ a₂) (h13 : a₁ ≠ a₃) (h23 : a₂ ≠ a₃) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (h1 : edgeFaces hh s(w, a₁) = {x, y}) (h2 : edgeFaces hh s(w, a₂) = {x, z})
    (h3 : edgeFaces hh s(w, a₃) = {y, z}) :
    edgeDeg (faceEdges hh f) w = 0 ∨ edgeDeg (faceEdges hh f) w = 2 := by
  have hN' : (Jg hh).neighborFinset w = {a₁, a₂, a₃} := by
    ext b; rw [mem_neighborFinset, hN]; simp
  rw [edgeDeg_faceEdges, hN']
  exact count_tri (fun a => edgeFaces hh s(w, a)) f h12 h13 h23 hxy hxz hyz h1 h2 h3

theorem deg_two (w : JV h) {a₁ a₂ : JV h} {x y : Face h} (f : Face h)
    (hN : ∀ b, (Jg hh).Adj w b ↔ b = a₁ ∨ b = a₂) (h12 : a₁ ≠ a₂)
    (h1 : edgeFaces hh s(w, a₁) = {x, y}) (h2 : edgeFaces hh s(w, a₂) = {x, y}) :
    edgeDeg (faceEdges hh f) w = 0 ∨ edgeDeg (faceEdges hh f) w = 2 := by
  have hN' : (Jg hh).neighborFinset w = {a₁, a₂} := by
    ext b; rw [mem_neighborFinset, hN]; simp
  rw [edgeDeg_faceEdges, hN']
  exact count_two (fun a => edgeFaces hh s(w, a)) f h12 h1 h2

/-! ### The faces at each vertex -/

theorem var_prev (o : OE h × Fin 7) : prodVar src tgt ((nextPerm hh).symm o) = prodVar src tgt o := by
  have := var_nextPerm hh ((nextPerm hh).symm o)
  rw [Equiv.apply_symm_apply] at this
  exact this.symm

theorem after_prev (o : OE h × Fin 7) : after ((nextPerm hh).symm o) = before o := by
  rw [after_eq_before_next hh, Equiv.apply_symm_apply]

theorem faces_cycle_prev (o : OE h × Fin 7) :
    edgeFaces hh s((o, 0), ((nextPerm hh).symm o, 1)) = {varF (prodVar src tgt o), before o} := by
  rw [Sym2.eq_swap]
  have := faces_cycle hh ((nextPerm hh).symm o)
  rw [Equiv.apply_symm_apply, var_prev, after_prev] at this
  exact this

/-- Clique partners of an occurrence. -/
def partners (e : OE h) : Fin 7 → Finset (OE h × Fin 7)
  | 0 => {(e, 1), (e, 2)} | 1 => {(e, 0), (e, 2)} | 2 => {(e, 0), (e, 1)}
  | 3 => {(e, 4)} | 4 => {(e, 3)} | 5 => {(e, 6)} | 6 => {(e, 5)}

theorem sameClause_iff (e : OE h) (k : Fin 7) (o' : OE h × Fin 7) :
    SameClause (e, k) o' ↔ o' ∈ partners e k := by
  obtain ⟨e', k'⟩ := o'
  unfold SameClause prodClause
  by_cases he : e = e'
  · subst he
    fin_cases k <;> fin_cases k' <;> simp [partners]
  · have : ∀ k₀ : Fin 7, (e', k₀) ∉ partners e k := by
      intro k₀; fin_cases k <;> simp [partners, Ne.symm he]
    simp only [this, iff_false, not_and, ne_eq, Prod.mk.injEq, he, false_and, not_false_eq_true,
      implies_true]

theorem adj_lit' (e : OE h) (k : Fin 7) (b : JV h) :
    (Jg hh).Adj ((e, k), 2) b ↔ b = ((e, k), if prodPos (e, k) then 1 else 0) ∨
      ∃ o' ∈ partners e k, b = (o', 2) := by
  rw [adj_lit]
  simp only [sameClause_iff]
  constructor
  · rintro (h | ⟨o', h1, h2⟩)
    · exact Or.inl h
    · exact Or.inr ⟨o', h2, h1⟩
  · rintro (h | ⟨o', h1, h2⟩)
    · exact Or.inl h
    · exact Or.inr ⟨o', h2, h1⟩

theorem faces_port' (o : OE h × Fin 7) :
    edgeFaces hh s((o, if prodPos o then 1 else 0), (o, 2)) = {after o, before o} := by
  rw [Sym2.eq_swap]; exact faces_port hh o

theorem faces_cl (e : OE h) (k k' : Fin 7) (hne : k ≠ k') :
    edgeFaces hh s(((e, k), 2), ((e, k'), 2)) = cliqueF e k k' ∪ cliqueF e k' k :=
  faces_clique hh (e, k) (e, k') rfl (by simpa using hne)

theorem triF_ne_g1F (e : OE h) : triF e ≠ g1F e := by simp [triF, g1F]
theorem triF_ne_g2F (e : OE h) : triF e ≠ g2F e := by simp [triF, g2F]

/-- **Faces are cycles.** Every face meets every vertex of `Jg` in `0` or `2` boundary edges. -/
theorem edgeDeg_faces (f : Face h) (w : JV h) :
    edgeDeg (faceEdges hh f) w = 0 ∨ edgeDeg (faceEdges hh f) w = 2 := by
  obtain ⟨o, r⟩ := w
  have hprev := prev_ne hh o
  have hnext := nextPerm_ne hh o
  have hab := after_ne_before o
  have hva := ne_varF (isReg_after o) (prodVar src tgt o)
  have hvb := ne_varF (isReg_before o) (prodVar src tgt o)
  fin_cases r
  · -- true port
    cases hp : prodPos o
    · refine deg_tri hh (o, 0) f (a₁ := (o, 1)) (a₂ := ((nextPerm hh).symm o, 1)) (a₃ := (o, 2))
        (x := varF (prodVar src tgt o)) (y := after o) (z := before o) ?_ ?_ (by simp) (by simp)
        hva.symm hvb.symm hab ?_ (faces_cycle_prev hh o) ?_
      · intro b; rw [adj_port0]; simp [hp]
      · simp [Ne.symm hprev]
      · rw [faces_pair, rpair, hp]; rfl
      · have := faces_port' hh o; simp only [hp] at this; exact this
    · refine deg_two hh (o, 0) f (a₁ := (o, 1)) (a₂ := ((nextPerm hh).symm o, 1))
        (x := varF (prodVar src tgt o)) (y := before o) ?_ ?_ ?_ (faces_cycle_prev hh o)
      · intro b; rw [adj_port0]; simp [hp]
      · simp [Ne.symm hprev]
      · rw [faces_pair, rpair, hp]; rfl
  · -- false port
    cases hp : prodPos o
    · refine deg_two hh (o, 1) f (a₁ := (o, 0)) (a₂ := (nextPerm hh o, 0))
        (x := varF (prodVar src tgt o)) (y := after o) ?_ ?_ ?_ (faces_cycle hh o)
      · intro b; rw [adj_port1]; simp [hp]
      · simp [Ne.symm hnext]
      · rw [Sym2.eq_swap, faces_pair, rpair, hp]; rfl
    · refine deg_tri hh (o, 1) f (a₁ := (o, 0)) (a₂ := (nextPerm hh o, 0)) (a₃ := (o, 2))
        (x := varF (prodVar src tgt o)) (y := before o) (z := after o) ?_ ?_ (by simp) (by simp)
        hvb.symm hva.symm hab.symm ?_ (faces_cycle hh o) ?_
      · intro b; rw [adj_port1]; simp [hp]
      · simp [Ne.symm hnext]
      · rw [Sym2.eq_swap, faces_pair, rpair, hp]; rfl
      · rw [Finset.pair_comm]; simpa [hp] using faces_port' hh o
  · -- literal vertex
    obtain ⟨e, k⟩ := o
    have hl := leftF_ne_g e e
    have hr := rightF_ne_g e e
    have hlt := ne_triF (isReg_leftF e) e
    have hrt := ne_triF (isReg_rightF e) e
    have hgt1 := triF_ne_g1F e
    have hgt2 := triF_ne_g2F e
    have hg12 := g1F_ne_g2F e e
    fin_cases k
    · refine deg_tri hh ((e, 0), 2) f (a₁ := ((e, 0), 0)) (a₂ := ((e, 1), 2)) (a₃ := ((e, 2), 2))
        (x := leftF e) (y := g1F e) (z := triF e) ?_ (by simp) (by simp) (by simp)
        hl.1 hlt hgt1.symm ?_ ?_ ?_
      · intro b; rw [adj_lit']; simp [partners, prodPos]
      · have := faces_port hh ((e, 0) : OE h × Fin 7); simpa [prodPos, after, before] using this
      · rw [faces_cl hh e 0 1 (by decide)]; simp [cliqueF, Finset.pair_comm]
      · rw [faces_cl hh e 0 2 (by decide)]; simp [cliqueF, Finset.pair_comm]
    · refine deg_tri hh ((e, 1), 2) f (a₁ := ((e, 1), 0)) (a₂ := ((e, 2), 2)) (a₃ := ((e, 0), 2))
        (x := g2F e) (y := leftF e) (z := triF e) ?_ (by simp) (by simp) (by simp)
        (fun h' => hl.2 h'.symm) hgt2.symm hlt ?_ ?_ ?_
      · intro b; rw [adj_lit']; simp [partners, prodPos]; tauto
      · have := faces_port hh ((e, 1) : OE h × Fin 7); simpa [prodPos, after, before] using this
      · rw [faces_cl hh e 1 2 (by decide)]; simp [cliqueF, Finset.pair_comm]
      · rw [faces_cl hh e 1 0 (by decide)]; simp [cliqueF, Finset.pair_comm]
    · refine deg_tri hh ((e, 2), 2) f (a₁ := ((e, 2), 1)) (a₂ := ((e, 0), 2)) (a₃ := ((e, 1), 2))
        (x := g1F e) (y := g2F e) (z := triF e) ?_ (by simp) (by simp) (by simp)
        hg12 hgt1.symm hgt2.symm ?_ ?_ ?_
      · intro b; rw [adj_lit']; simp [partners, prodPos]
      · have := faces_port hh ((e, 2) : OE h × Fin 7); simpa [prodPos, after, before] using this
      · rw [faces_cl hh e 2 0 (by decide)]; simp [cliqueF, Finset.pair_comm]
      · rw [faces_cl hh e 2 1 (by decide)]; simp [cliqueF, Finset.pair_comm]
    · refine deg_two hh ((e, 3), 2) f (a₁ := ((e, 3), 1)) (a₂ := ((e, 4), 2))
        (x := g1F e) (y := rightF e) ?_ (by simp) ?_ ?_
      · intro b; rw [adj_lit']; simp [partners, prodPos]
      · have := faces_port hh ((e, 3) : OE h × Fin 7); simpa [prodPos, after, before] using this
      · rw [faces_cl hh e 3 4 (by decide)]; simp [cliqueF]
    · refine deg_two hh ((e, 4), 2) f (a₁ := ((e, 4), 0)) (a₂ := ((e, 3), 2))
        (x := g1F e) (y := rightF e) ?_ (by simp) ?_ ?_
      · intro b; rw [adj_lit']; simp [partners, prodPos]
      · rw [Finset.pair_comm]
        simpa [prodPos, after, before] using faces_port hh ((e, 4) : OE h × Fin 7)
      · rw [faces_cl hh e 4 3 (by decide)]; simp [cliqueF]
    · refine deg_two hh ((e, 5), 2) f (a₁ := ((e, 5), 1)) (a₂ := ((e, 6), 2))
        (x := g2F e) (y := rightF e) ?_ (by simp) ?_ ?_
      · intro b; rw [adj_lit']; simp [partners, prodPos]
      · rw [Finset.pair_comm]
        simpa [prodPos, after, before] using faces_port hh ((e, 5) : OE h × Fin 7)
      · rw [faces_cl hh e 5 6 (by decide)]; simp [cliqueF]
    · refine deg_two hh ((e, 6), 2) f (a₁ := ((e, 6), 0)) (a₂ := ((e, 5), 2))
        (x := g2F e) (y := rightF e) ?_ (by simp) ?_ ?_
      · intro b; rw [adj_lit']; simp [partners, prodPos]
      · have := faces_port hh ((e, 6) : OE h × Fin 7); simpa [prodPos, after, before] using this
      · rw [faces_cl hh e 6 5 (by decide)]; simp [cliqueF]

end Grid

end Lemmata.PlanarSteinerXC
