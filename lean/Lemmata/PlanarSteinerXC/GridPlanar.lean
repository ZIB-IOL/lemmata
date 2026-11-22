module

public import Lemmata.PlanarSteinerXC.GridFaces

/-!
# The cover graph of the grid is planar

We complete the verification of the face system of `Jg`: every edge lies on two faces, faces are
nonempty, `Jg` and its dual are connected, and Euler's formula holds. We also record that `Jg` has
maximum degree three and no isolated vertices.
-/

@[expose] public section

set_option autoImplicit false

namespace Lemmata.PlanarSteinerXC

namespace Grid

open SimpleGraph

variable {h : ℕ} (hh : 2 ≤ h)

/-! ### Two faces per edge -/

theorem fin3_cases (r : Fin 3) : r = 0 ∨ r = 1 ∨ r = 2 := by fin_cases r <;> simp

theorem card_pair_of_ne {α : Type*} [DecidableEq α] {x y : α} (hxy : x ≠ y) :
    ({x, y} : Finset α).card = 2 := Finset.card_pair hxy

theorem card_cl (e : OE h) (k : Fin 7) (o' : OE h × Fin 7) (ho' : o' ∈ partners e k) :
    (edgeFaces hh s(((e, k), 2), (o', 2))).card = 2 := by
  have hl := leftF_ne_g e e
  have hr := rightF_ne_g e e
  have hlt := ne_triF (isReg_leftF e) e
  have hgt1 := triF_ne_g1F e
  have hgt2 := triF_ne_g2F e
  fin_cases k <;> simp only [partners, Finset.mem_insert, Finset.mem_singleton] at ho' <;>
    rcases ho' with rfl | rfl <;>
    first
    | (rw [faces_cl hh e _ _ (by decide)]; simp only [cliqueF]; simp;
       first
       | exact card_pair_of_ne hlt.symm
       | exact card_pair_of_ne hgt1
       | exact card_pair_of_ne hgt2
       | exact card_pair_of_ne (fun h' => hr.1 h'.symm)
       | exact card_pair_of_ne (fun h' => hr.2 h'.symm))

theorem card_edgeFaces (a b : JV h) (hab : (Jg hh).Adj a b) : (edgeFaces hh s(a, b)).card = 2 := by
  obtain ⟨o, r⟩ := a
  have hab' := after_ne_before o
  have hva := ne_varF (isReg_after o) (prodVar src tgt o)
  have hvb := ne_varF (isReg_before o) (prodVar src tgt o)
  have hvr := ne_varF (isReg_rpair o) (prodVar src tgt o)
  rcases fin3_cases r with rfl | rfl | rfl
  · rw [adj_port0] at hab
    rcases hab with rfl | rfl | ⟨rfl, hp⟩
    · rw [faces_pair]; exact card_pair_of_ne hvr.symm
    · rw [faces_cycle_prev]; exact card_pair_of_ne hvb.symm
    · have := faces_port' hh o; simp only [hp, Bool.false_eq_true, ↓reduceIte] at this
      rw [this]; exact card_pair_of_ne hab'
  · rw [adj_port1] at hab
    rcases hab with rfl | rfl | ⟨rfl, hp⟩
    · rw [Sym2.eq_swap, faces_pair]; exact card_pair_of_ne hvr.symm
    · rw [faces_cycle]; exact card_pair_of_ne hva.symm
    · have := faces_port' hh o; simp only [hp, ↓reduceIte] at this
      rw [this]; exact card_pair_of_ne hab'
  · obtain ⟨e, k⟩ := o
    rw [adj_lit'] at hab
    rcases hab with rfl | ⟨o', ho', rfl⟩
    · rw [faces_port]; exact card_pair_of_ne hab'
    · exact card_cl hh e k o' ho'

/-! ### Degrees -/

theorem degree_port0 (o : OE h × Fin 7) :
    (Jg hh).degree (o, 0) = if prodPos o then 2 else 3 := by
  rw [← card_neighborFinset_eq_degree]
  cases hp : prodPos o
  · have : (Jg hh).neighborFinset (o, 0) = {(o, 1), ((nextPerm hh).symm o, 1), (o, 2)} := by
      ext b; rw [mem_neighborFinset, adj_port0]; simp [hp]
    rw [this, Finset.card_insert_of_notMem (by simp [Ne.symm (prev_ne hh o)]),
      Finset.card_pair (by simp)]
    rfl
  · have : (Jg hh).neighborFinset (o, 0) = {(o, 1), ((nextPerm hh).symm o, 1)} := by
      ext b; rw [mem_neighborFinset, adj_port0]; simp [hp]
    rw [this, Finset.card_pair (by simp [Ne.symm (prev_ne hh o)])]
    rfl

theorem degree_port1 (o : OE h × Fin 7) :
    (Jg hh).degree (o, 1) = if prodPos o then 3 else 2 := by
  rw [← card_neighborFinset_eq_degree]
  cases hp : prodPos o
  · have : (Jg hh).neighborFinset (o, 1) = {(o, 0), (nextPerm hh o, 0)} := by
      ext b; rw [mem_neighborFinset, adj_port1]; simp [hp]
    rw [this, Finset.card_pair (by simp [Ne.symm (nextPerm_ne hh o)])]
    rfl
  · have : (Jg hh).neighborFinset (o, 1) = {(o, 0), (nextPerm hh o, 0), (o, 2)} := by
      ext b; rw [mem_neighborFinset, adj_port1]; simp [hp]
    rw [this, Finset.card_insert_of_notMem (by simp [Ne.symm (nextPerm_ne hh o)]),
      Finset.card_pair (by simp)]
    rfl

theorem degree_lit (e : OE h) (k : Fin 7) :
    (Jg hh).degree ((e, k), 2) = if k.val ≤ 2 then 3 else 2 := by
  rw [← card_neighborFinset_eq_degree]
  have : (Jg hh).neighborFinset ((e, k), 2) =
      insert ((e, k), if prodPos (e, k) then 1 else 0) ((partners e k).image (fun o' => (o', 2))) := by
    ext b
    rw [mem_neighborFinset, adj_lit', Finset.mem_insert, Finset.mem_image]
    constructor
    · rintro (h' | ⟨o', h1, h2⟩)
      · exact Or.inl h'
      · exact Or.inr ⟨o', h1, h2.symm⟩
    · rintro (h' | ⟨o', h1, h2⟩)
      · exact Or.inl h'
      · exact Or.inr ⟨o', h1, h2.symm⟩
  have hnot : ((e, k), if prodPos (e, k) then 1 else 0) ∉
      (partners e k).image (fun o' => ((o', 2) : JV h)) := by
    intro hmem
    rw [Finset.mem_image] at hmem
    obtain ⟨a, -, ha⟩ := hmem
    have := congrArg Prod.snd ha
    revert this; simp only; split_ifs <;> decide
  rw [this, Finset.card_insert_of_notMem hnot, Finset.card_image_of_injective _
    (fun a b hab => by simpa using hab)]
  fin_cases k <;> simp [partners]

theorem degree_le_three (w : JV h) : (Jg hh).degree w ≤ 3 := by
  obtain ⟨⟨e, k⟩, r⟩ := w
  rcases fin3_cases r with rfl | rfl | rfl
  · rw [degree_port0]; split_ifs <;> lia
  · rw [degree_port1]; split_ifs <;> lia
  · rw [degree_lit]; split_ifs <;> lia

theorem no_isolated (w : JV h) : ∃ w', (Jg hh).Adj w w' := by
  obtain ⟨o, r⟩ := w
  rcases fin3_cases r with rfl | rfl | rfl
  · exact ⟨(o, 1), (adj_port0 hh o _).mpr (Or.inl rfl)⟩
  · exact ⟨(o, 0), (adj_port1 hh o _).mpr (Or.inl rfl)⟩
  · exact ⟨_, (adj_lit hh o _).mpr (Or.inl rfl)⟩

/-! ### Euler's formula -/

theorem sum_degree : ∑ w : JV h, (Jg hh).degree w = 52 * Fintype.card (OE h) := by
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  have : ∀ e : OE h, ∑ k : Fin 7, ∑ r : Fin 3, (Jg hh).degree ((e, k), r) = 52 := by
    intro e
    simp only [Fin.sum_univ_three, Fin.sum_univ_seven, degree_port0, degree_port1, degree_lit]
    simp [prodPos]
  rw [Finset.sum_congr rfl (fun e _ => this e), Finset.sum_const, Finset.card_univ, smul_eq_mul,
    mul_comm]

theorem card_edges : Nat.card (Jg hh).edgeSet = 26 * Fintype.card (OE h) := by
  have h1 := (Jg hh).sum_degrees_eq_twice_card_edges
  rw [sum_degree] at h1
  rw [Nat.card_eq_fintype_card, ← edgeFinset_card]
  lia

theorem card_JV : Fintype.card (JV h) = 21 * Fintype.card (OE h) := by
  simp only [Fintype.card_prod, Fintype.card_fin]; ring

theorem card_face : Fintype.card (Face h) = h * h + 4 * Fintype.card (OE h) + (h - 1) * (h - 1) + 1 := by
  simp only [Face, Region, Cell, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_unit, Pt]
  ring

theorem euler : Fintype.card (JV h) + Fintype.card (Face h) = Nat.card (Jg hh).edgeSet + 2 := by
  rw [card_JV, card_face, card_edges, card_oe]
  obtain ⟨m, rfl⟩ : ∃ m, h = m + 1 := ⟨h - 1, by lia⟩
  simp only [Nat.add_sub_cancel]
  ring

/-! ### Connectivity -/

theorem reach_role (o : OE h × Fin 7) (r : Fin 3) : (Jg hh).Reachable (o, r) (o, 0) := by
  rcases fin3_cases r with rfl | rfl | rfl
  · rfl
  · exact ((adj_port1 hh o _).mpr (Or.inl rfl)).reachable
  · have h1 : (Jg hh).Adj (o, 2) (o, if prodPos o then 1 else 0) :=
      (adj_lit hh o _).mpr (Or.inl rfl)
    refine h1.reachable.trans ?_
    split_ifs
    · exact ((adj_port1 hh o _).mpr (Or.inl rfl)).reachable
    · rfl

theorem reach_next (o : OE h × Fin 7) : (Jg hh).Reachable (o, 0) (nextPerm hh o, 0) :=
  ((adj_port0 hh o _).mpr (Or.inl rfl)).reachable.trans
    ((adj_port1 hh o _).mpr (Or.inr (Or.inl rfl))).reachable

theorem reach_pow (o : OE h × Fin 7) (k : ℕ) :
    (Jg hh).Reachable (o, 0) ((nextPerm hh ^ k) o, 0) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ', Equiv.Perm.mul_apply]; exact ih.trans (reach_next hh _)

theorem reach_var (o o' : OE h × Fin 7) (hv : prodVar src tgt o = prodVar src tgt o') :
    (Jg hh).Reachable (o, 0) (o', 0) := by
  obtain ⟨k, hk⟩ := nextPerm_cyclic hh o o' hv
  rw [← hk]; exact reach_pow hh o k

theorem reach_gadget (e : OE h) :
    (Jg hh).Reachable ((e, 0), 0) ((e, 1), 0) ∧ (Jg hh).Reachable ((e, 0), 0) ((e, 2), 0) := by
  have a1 : (Jg hh).Adj ((e, 0), 0) ((e, 0), 2) := (adj_port0 hh _ _).mpr (Or.inr (Or.inr ⟨rfl, rfl⟩))
  have a2 : (Jg hh).Adj ((e, 0), 2) ((e, 1), 2) :=
    (adj_lit' hh e 0 _).mpr (Or.inr ⟨(e, 1), by simp [partners], rfl⟩)
  have a3 : (Jg hh).Adj ((e, 1), 2) ((e, 1), 0) := (adj_lit' hh e 1 _).mpr (Or.inl rfl)
  have a4 : (Jg hh).Adj ((e, 0), 2) ((e, 2), 2) :=
    (adj_lit' hh e 0 _).mpr (Or.inr ⟨(e, 2), by simp [partners], rfl⟩)
  have a5 : (Jg hh).Adj ((e, 2), 2) ((e, 2), 1) := (adj_lit' hh e 2 _).mpr (Or.inl rfl)
  have a6 : (Jg hh).Adj ((e, 2), 1) ((e, 2), 0) := (adj_port1 hh _ _).mpr (Or.inl rfl)
  exact ⟨a1.reachable.trans (a2.reachable.trans a3.reachable),
    a1.reachable.trans (a4.reachable.trans (a5.reachable.trans a6.reachable))⟩

include hh in
theorem present_E_or_W (p : Pt h) (hE : ¬ present p .E) : present p .W := by
  simp only [present] at hE ⊢; lia

/-- An occurrence of the variable of a grid point. -/
def occP (p : Pt h) : OE h × Fin 7 :=
  if hE : present p .E then occAt p .E false hE else occAt p .W false (present_E_or_W hh p hE)

theorem var_occP (p : Pt h) : prodVar src tgt (occP hh p) = .inl p := by
  unfold occP
  split_ifs <;> exact (prodVar_eq_inl_iff _ _).mpr ⟨isX_occAt _ _ _ _, ptOf_occAt _ _ _ _⟩

theorem var_e0 (e : OE h) : prodVar src tgt ((e, 0) : OE h × Fin 7) = .inl (src e) := rfl
theorem var_e1 (e : OE h) : prodVar src tgt ((e, 1) : OE h × Fin 7) = .inl (tgt e) := rfl

theorem reach_edge (e : OE h) : (Jg hh).Reachable (occP hh (src e), 0) (occP hh (tgt e), 0) :=
  (reach_var hh _ _ (by rw [var_occP, var_e0])).trans
    ((reach_gadget hh e).1.trans (reach_var hh _ _ (by rw [var_occP, var_e1])))

theorem exists_oe_of_adj {p q : Pt h} (hpq : (grid h).Adj p q) :
    ∃ e : OE h, (src e = p ∧ tgt e = q) ∨ (src e = q ∧ tgt e = p) := by
  obtain ⟨e, he⟩ := (oeEquiv (h := h)).surjective ⟨s(p, q), hpq⟩
  have := congrArg Subtype.val he
  rw [oeEquiv_apply, Sym2.eq_iff] at this
  exact ⟨e, this⟩

theorem reach_grid {p q : Pt h} (w : (grid h).Walk p q) :
    (Jg hh).Reachable (occP hh p, 0) (occP hh q, 0) := by
  induction w with
  | nil => rfl
  | cons hadj _ ih =>
    refine Reachable.trans ?_ ih
    obtain ⟨e, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := exists_oe_of_adj hadj
    · exact reach_edge hh e
    · exact (reach_edge hh e).symm

include hh in
theorem grid_connected : (grid h).Connected := by
  obtain ⟨m, rfl⟩ : ∃ m, h = m + 1 := ⟨h - 1, by lia⟩
  exact (connected_pathGraph_add_one m).boxProd (connected_pathGraph_add_one m)

/-- A base point of the grid. -/
def p0 : Pt h := (⟨0, by lia⟩, ⟨0, by lia⟩)

theorem reach_base (w : JV h) : (Jg hh).Reachable w (occP hh (p0 hh), 0) := by
  obtain ⟨o, r⟩ := w
  refine (reach_role hh o r).trans ?_
  have hgrid : ∀ p : Pt h, (Jg hh).Reachable (occP hh p, 0) (occP hh (p0 hh), 0) := by
    intro p
    obtain ⟨w⟩ := (grid_connected hh).preconnected p (p0 hh)
    exact reach_grid hh w
  by_cases ho : IsX o
  · refine (reach_var hh o (occP hh (ptOf o)) ?_).trans (hgrid _)
    rw [var_occP]; exact (prodVar_eq_inl_iff _ _).mpr ⟨ho, rfl⟩
  · have h1 : prodVar src tgt o = prodVar src tgt ((o.1, 2) : OE h × Fin 7) := by
      rw [(prodVar_eq_inr_iff _ _).mpr ⟨ho, rfl⟩]; rfl
    refine (reach_var hh _ _ h1).trans ?_
    refine (reach_gadget hh o.1).2.symm.trans ?_
    refine (reach_var hh _ (occP hh (src o.1)) (by rw [var_occP, var_e0])).trans (hgrid _)

theorem Jg_connected : (Jg hh).Connected := by
  have : Nonempty (JV h) := ⟨(occP hh (p0 hh), 0)⟩
  rw [connected_iff_exists_forall_reachable]
  exact ⟨(occP hh (p0 hh), 0), fun w => (reach_base hh w).symm⟩

/-! ### Faces are nonempty and the dual is connected -/

theorem mem_faceEdges {a b : JV h} (hab : (Jg hh).Adj a b) {f : Face h}
    (hf : f ∈ edgeFaces hh s(a, b)) : s(a, b) ∈ faceEdges hh f := by
  simp only [faceEdges, Finset.mem_filter, mem_edgeFinset, mem_edgeSet]
  exact ⟨hab, hf⟩

theorem adj_cycle (o : OE h × Fin 7) : (Jg hh).Adj (o, 1) (nextPerm hh o, 0) :=
  (adj_port1 hh o _).mpr (Or.inr (Or.inl rfl))

theorem adj_port (o : OE h × Fin 7) : (Jg hh).Adj (o, 2) (o, if prodPos o then 1 else 0) :=
  (adj_lit hh o _).mpr (Or.inl rfl)

theorem adj_cl02 (e : OE h) : (Jg hh).Adj ((e, 0), 2) ((e, 2), 2) :=
  (adj_lit' hh e 0 _).mpr (Or.inr ⟨(e, 2), by simp [partners], rfl⟩)

/-- The corner of a unit square. -/
def corner (c : Cell h) : Pt h :=
  (⟨c.1.val, Nat.lt_of_lt_of_le c.1.isLt (Nat.sub_le h 1)⟩,
    ⟨c.2.val, Nat.lt_of_lt_of_le c.2.isLt (Nat.sub_le h 1)⟩)

theorem present_corner (c : Cell h) : present (corner c) .E := by
  show c.1.val + 1 < h; lia

theorem quad_corner (c : Cell h) : quad (corner c) .E = cellF c := by
  have h1 : (corner c).1.val + 1 < h := by simp only [corner]; lia
  have h2 : (corner c).2.val + 1 < h := by simp only [corner]; lia
  simp only [quad, h1, h2, and_self, ite_true, cellAt]
  rw [dif_pos (by simp only [corner]; lia)]
  rfl

theorem before_outer : before (occAt (p0 hh) .E false (by show 0 + 1 < h; lia)) = outerF := by
  rw [before_occAt_false]
  simp [quad, Dir.pred, p0]

theorem faces_nonempty (f : Face h) : (faceEdges hh f).Nonempty := by
  rcases f with x | e | e | e | c | u
  · -- variable faces
    have ho : ∃ o, prodVar src tgt o = x := by
      rcases x with p | e
      · exact ⟨occP hh p, var_occP hh p⟩
      · exact ⟨(e, 2), rfl⟩
    obtain ⟨o, rfl⟩ := ho
    exact ⟨_, mem_faceEdges hh (adj_cycle hh o) (by rw [faces_cycle]; simp [varF])⟩
  · exact ⟨_, mem_faceEdges hh (adj_cl02 hh e) (by rw [faces_cl hh e 0 2 (by decide)]; simp [cliqueF, triF])⟩
  · exact ⟨_, mem_faceEdges hh (adj_port hh (e, 2)) (by rw [faces_port]; simp [after, g1F])⟩
  · exact ⟨_, mem_faceEdges hh (adj_port hh (e, 2)) (by rw [faces_port]; simp [before, g2F])⟩
  · refine ⟨_, mem_faceEdges hh (adj_port hh (occAt (corner c) .E true (present_corner c))) ?_⟩
    rw [faces_port, after_occAt_true, quad_corner]; simp [cellF]
  · refine ⟨_, mem_faceEdges hh (adj_port hh (occAt (p0 hh) .E false (by show 0 + 1 < h; lia))) ?_⟩
    rw [faces_port, before_outer]; simp [outerF]

/-- The dual graph of the face system. -/
abbrev dualG : SimpleGraph (Face h) :=
  SimpleGraph.fromRel fun f g : Face h => ∃ ε, ε ∈ faceEdges hh f ∧ ε ∈ faceEdges hh g

theorem dual_reach {a b : JV h} (hab : (Jg hh).Adj a b) {f g : Face h}
    (hf : f ∈ edgeFaces hh s(a, b)) (hg : g ∈ edgeFaces hh s(a, b)) : (dualG hh).Reachable f g := by
  by_cases hfg : f = g
  · rw [hfg]
  · apply Adj.reachable
    rw [fromRel_adj]
    exact ⟨hfg, Or.inl ⟨s(a, b), mem_faceEdges hh hab hf, mem_faceEdges hh hab hg⟩⟩

theorem dual_var_after (o : OE h × Fin 7) :
    (dualG hh).Reachable (varF (prodVar src tgt o)) (after o) :=
  dual_reach hh (adj_cycle hh o) (by rw [faces_cycle]; simp) (by rw [faces_cycle]; simp)

theorem dual_g1_g2 (e : OE h) : (dualG hh).Reachable (g1F e) (g2F e) :=
  dual_reach hh (adj_port hh (e, 2)) (by rw [faces_port]; simp [after])
    (by rw [faces_port]; simp [before])

theorem dual_src (e : OE h) : (dualG hh).Reachable (varF (.inl (src e))) (g1F e) :=
  dual_var_after hh (e, 3)

theorem dual_tgt (e : OE h) : (dualG hh).Reachable (varF (.inl (tgt e))) (g2F e) :=
  dual_var_after hh (e, 1)

theorem dual_grid {p q : Pt h} (w : (grid h).Walk p q) :
    (dualG hh).Reachable (varF (.inl p)) (varF (.inl q)) := by
  induction w with
  | nil => rfl
  | cons hadj _ ih =>
    refine Reachable.trans ?_ ih
    obtain ⟨e, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := exists_oe_of_adj hadj
    · exact (dual_src hh e).trans ((dual_g1_g2 hh e).trans (dual_tgt hh e).symm)
    · exact (dual_tgt hh e).trans ((dual_g1_g2 hh e).symm.trans (dual_src hh e).symm)

theorem dual_base (f : Face h) : (dualG hh).Reachable f (varF (.inl (p0 hh))) := by
  have hgrid : ∀ p : Pt h, (dualG hh).Reachable (varF (.inl p)) (varF (.inl (p0 hh))) := by
    intro p
    obtain ⟨w⟩ := (grid_connected hh).preconnected p (p0 hh)
    exact dual_grid hh w
  have hg1 : ∀ e : OE h, (dualG hh).Reachable (g1F e) (varF (.inl (p0 hh))) :=
    fun e => (dual_src hh e).symm.trans (hgrid _)
  rcases f with x | e | e | e | c | u
  · rcases x with p | e
    · exact hgrid p
    · exact (dual_var_after hh (e, 2)).trans (hg1 e)
  · exact (dual_reach hh (adj_cl02 hh e) (f := triF e) (g := g1F e)
      (by rw [faces_cl hh e 0 2 (by decide)]; simp [cliqueF])
      (by rw [faces_cl hh e 0 2 (by decide)]; simp [cliqueF])).trans (hg1 e)
  · exact hg1 e
  · exact (dual_g1_g2 hh e).symm.trans (hg1 e)
  · have := dual_var_after hh (occAt (corner c) .E true (present_corner c))
    rw [after_occAt_true, quad_corner,
      (prodVar_eq_inl_iff _ _).mpr ⟨isX_occAt _ _ _ _, ptOf_occAt _ _ _ _⟩] at this
    exact this.symm.trans (hgrid _)
  · have hp : present (p0 hh) .E := by show 0 + 1 < h; lia
    have h1 := dual_reach hh (adj_port hh (occAt (p0 hh) .E false hp))
      (f := outerF) (g := after (occAt (p0 hh) .E false hp))
      (by rw [faces_port, before_outer]; simp) (by rw [faces_port]; simp)
    have h2 := dual_var_after hh (occAt (p0 hh) .E false hp)
    rw [(prodVar_eq_inl_iff _ _).mpr ⟨isX_occAt _ _ _ _, ptOf_occAt _ _ _ _⟩] at h2
    exact h1.trans (h2.symm.trans (hgrid _))

theorem dual_connected : (dualG hh).Connected := by
  have : Nonempty (Face h) := ⟨outerF⟩
  rw [connected_iff_exists_forall_reachable]
  exact ⟨varF (.inl (p0 hh)), fun f => (dual_base hh f).symm⟩

/-! ### The face system -/

/-- **The planar cover graph of the grid.** The faces of `Jg` form a planar face system. -/
noncomputable def gridFaces : PlanarFaces (Jg hh) where
  Face := Face h
  edges := faceEdges hh
  edges_subset := fun f ε hε => by
    simp only [faceEdges, Finset.mem_filter, mem_edgeFinset] at hε; exact hε.1
  edges_nonempty := faces_nonempty hh
  edgeDeg_eq := edgeDeg_faces hh
  two_faces := fun ε hε => by
    induction ε using Sym2.ind with
    | h a b =>
      have hfil : (Finset.univ.filter fun f => s(a, b) ∈ faceEdges hh f) = edgeFaces hh s(a, b) := by
        ext f
        simp only [faceEdges, Finset.mem_filter, Finset.mem_univ, true_and, mem_edgeFinset]
        exact ⟨fun h' => h'.2, fun h' => ⟨hε, h'⟩⟩
      rw [hfil]
      exact card_edgeFaces hh a b hε
  connected := Jg_connected hh
  dual_connected := dual_connected hh
  euler := euler hh

end Grid

end Lemmata.PlanarSteinerXC
