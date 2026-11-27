module

public import Lemmata.PlanarSteinerXC.Radial
public import Lemmata.PlanarSteinerXC.Duality

/-!
# The flag system of the radial graph

The faces of the radial graph `H` are the *sides* `(φ, e)` of the edges of `J`: the quadrilaterals
`u q_e v f_φ`. A *flag* of `H` is a side together with an endpoint `u` of `e` and two bits: `term`
(the vertex of the flag is the terminal end `q_e` or `f_φ` rather than `u`) and `spoke` (the edge
of the flag is the spoke `u f_φ` rather than the half-edge `u q_e`). The flag graph is the dual
`Q*` of the barycentric subdivision `Q` of `H`.
-/

@[expose] public section

set_option autoImplicit false

namespace Lemmata.PlanarSteinerXC

open SimpleGraph

namespace PlanarFaces

variable {V : Type*} [Fintype V] [DecidableEq V] {J : SimpleGraph V} (S : PlanarFaces J)

/-! ### The other face at an edge, the other edge at a vertex, the other endpoint -/

theorem exists_unique_other_face {f : S.Face} {e : Sym2 V} (he : e ∈ S.edges f) :
    ∃! g, g ≠ f ∧ e ∈ S.edges g := by
  have h := S.two_faces e (S.mem_edgeSet_of_mem he)
  obtain ⟨a, b, hab, hs⟩ := Finset.card_eq_two.mp h
  have hmem : ∀ g, e ∈ S.edges g ↔ g = a ∨ g = b := by
    intro g
    have := congrArg (g ∈ ·) hs
    simpa using this
  rcases (hmem f).mp he with rfl | rfl
  · exact ⟨b, ⟨hab.symm, (hmem b).mpr (Or.inr rfl)⟩, fun g ⟨hg, hge⟩ =>
      ((hmem g).mp hge).resolve_left hg⟩
  · exact ⟨a, ⟨hab, (hmem a).mpr (Or.inl rfl)⟩, fun g ⟨hg, hge⟩ =>
      ((hmem g).mp hge).resolve_right hg⟩

/-- The other face containing an edge. -/
noncomputable def otherFace (f : S.Face) (e : Sym2 V) : S.Face := by
  classical
  exact if h : e ∈ S.edges f then Classical.choose (S.exists_unique_other_face h).exists else f

theorem otherFace_spec {f : S.Face} {e : Sym2 V} (he : e ∈ S.edges f) :
    S.otherFace f e ≠ f ∧ e ∈ S.edges (S.otherFace f e) := by
  classical
  unfold otherFace
  rw [dif_pos he]
  exact Classical.choose_spec (S.exists_unique_other_face he).exists

theorem otherFace_unique {f g : S.Face} {e : Sym2 V} (he : e ∈ S.edges f) (hg : g ≠ f)
    (hge : e ∈ S.edges g) : g = S.otherFace f e :=
  (S.exists_unique_other_face he).unique ⟨hg, hge⟩ (S.otherFace_spec he)

theorem otherFace_otherFace {f : S.Face} {e : Sym2 V} (he : e ∈ S.edges f) :
    S.otherFace (S.otherFace f e) e = f := by
  have h1 := S.otherFace_spec he
  exact (S.otherFace_unique h1.2 h1.1.symm he).symm

theorem exists_unique_other_edge {f : S.Face} {e : Sym2 V} {u : V} (he : e ∈ S.edges f)
    (hu : u ∈ e) : ∃! e', e' ≠ e ∧ e' ∈ S.edges f ∧ u ∈ e' := by
  have h : edgeDeg (S.edges f) u = 2 := S.edgeDeg_eq_two_of_mem ⟨e, he, hu⟩
  obtain ⟨a, b, hab, hs⟩ := Finset.card_eq_two.mp h
  have hmem : ∀ c, (c ∈ S.edges f ∧ u ∈ c) ↔ c = a ∨ c = b := by
    intro c
    have := congrArg (c ∈ ·) hs
    simpa [edgeDeg] using this
  rcases (hmem e).mp ⟨he, hu⟩ with rfl | rfl
  · exact ⟨b, ⟨hab.symm, (hmem b).mpr (Or.inr rfl)⟩, fun c ⟨hc, hc'⟩ =>
      ((hmem c).mp hc').resolve_left hc⟩
  · exact ⟨a, ⟨hab, (hmem a).mpr (Or.inl rfl)⟩, fun c ⟨hc, hc'⟩ =>
      ((hmem c).mp hc').resolve_right hc⟩

/-- The other edge of a face at a vertex. -/
noncomputable def otherEdge (f : S.Face) (u : V) (e : Sym2 V) : Sym2 V := by
  classical
  exact if h : e ∈ S.edges f ∧ u ∈ e then
    Classical.choose (S.exists_unique_other_edge h.1 h.2).exists else e

theorem otherEdge_spec {f : S.Face} {e : Sym2 V} {u : V} (he : e ∈ S.edges f) (hu : u ∈ e) :
    S.otherEdge f u e ≠ e ∧ S.otherEdge f u e ∈ S.edges f ∧ u ∈ S.otherEdge f u e := by
  classical
  unfold otherEdge
  rw [dif_pos ⟨he, hu⟩]
  exact Classical.choose_spec (S.exists_unique_other_edge he hu).exists

theorem otherEdge_unique {f : S.Face} {e c : Sym2 V} {u : V} (he : e ∈ S.edges f) (hu : u ∈ e)
    (hc : c ≠ e) (hcf : c ∈ S.edges f) (huc : u ∈ c) : c = S.otherEdge f u e :=
  (S.exists_unique_other_edge he hu).unique ⟨hc, hcf, huc⟩ (S.otherEdge_spec he hu)

theorem otherEdge_otherEdge {f : S.Face} {e : Sym2 V} {u : V} (he : e ∈ S.edges f)
    (hu : u ∈ e) : S.otherEdge f u (S.otherEdge f u e) = e := by
  have h1 := S.otherEdge_spec he hu
  exact (S.otherEdge_unique h1.2.1 h1.2.2 h1.1.symm he hu).symm

/-- The other endpoint of an edge. -/
def otherEnd (u : V) (e : Sym2 V) : V := if h : u ∈ e then Sym2.Mem.other' h else u

theorem otherEnd_spec {u : V} {e : Sym2 V} (hu : u ∈ e) : s(u, otherEnd u e) = e := by
  unfold otherEnd; rw [dif_pos hu]; exact Sym2.other_spec' hu

theorem otherEnd_mem {u : V} {e : Sym2 V} (hu : u ∈ e) : otherEnd u e ∈ e := by
  unfold otherEnd; rw [dif_pos hu]; exact Sym2.other_mem' hu

theorem otherEnd_ne {u : V} {e : Sym2 V} (hu : u ∈ e) (he : e ∈ J.edgeSet) :
    otherEnd u e ≠ u := by
  intro h
  have := otherEnd_spec hu
  rw [h] at this
  rw [← this] at he
  exact J.loopless.irrefl u (J.mem_edgeSet.mp he)

theorem otherEnd_otherEnd {u : V} {e : Sym2 V} (hu : u ∈ e) :
    otherEnd (otherEnd u e) e = u := by
  have h1 := otherEnd_mem hu
  unfold otherEnd at h1 ⊢
  rw [dif_pos hu] at h1 ⊢
  rw [dif_pos h1]
  exact Sym2.other_invol' hu h1

theorem adj_otherEnd {u : V} {e : Sym2 V} (hu : u ∈ e) (he : e ∈ J.edgeSet) :
    J.Adj u (otherEnd u e) := by
  rw [← J.mem_edgeSet, otherEnd_spec hu]; exact he

/-! ### Sides, corners and flags -/

/-- A side: a face of `J` with one of its edges; these are the faces of `H`. -/
@[ext] structure Side where
  face : S.Face
  edge : Sym2 V
  edge_mem : edge ∈ S.edges face

/-- A corner: a face of `J` with a vertex on it; these are the spokes of `H`. -/
@[ext] structure Corner where
  face : S.Face
  vert : V
  vert_mem : vert ∈ S.verts face

/-- A flag of `H`. -/
@[ext] structure Flag where
  face : S.Face
  edge : Sym2 V
  vert : V
  term : Bool
  spoke : Bool
  edge_mem : edge ∈ S.edges face
  vert_mem : vert ∈ edge

def Side.equiv : S.Side ≃ {p : S.Face × Sym2 V // p.2 ∈ S.edges p.1} where
  toFun s := ⟨(s.face, s.edge), s.edge_mem⟩
  invFun p := ⟨p.1.1, p.1.2, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def Corner.equiv : S.Corner ≃ {p : S.Face × V // p.2 ∈ S.verts p.1} where
  toFun s := ⟨(s.face, s.vert), s.vert_mem⟩
  invFun p := ⟨p.1.1, p.1.2, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def Flag.equiv : S.Flag ≃
    {x : S.Face × Sym2 V × V × Bool × Bool // x.2.1 ∈ S.edges x.1 ∧ x.2.2.1 ∈ x.2.1} where
  toFun φ := ⟨(φ.face, φ.edge, φ.vert, φ.term, φ.spoke), φ.edge_mem, φ.vert_mem⟩
  invFun x := ⟨x.1.1, x.1.2.1, x.1.2.2.1, x.1.2.2.2.1, x.1.2.2.2.2, x.2.1, x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance : Fintype S.Side := by classical exact Fintype.ofEquiv _ (Side.equiv S).symm
noncomputable instance : Fintype S.Corner := by
  classical exact Fintype.ofEquiv _ (Corner.equiv S).symm
noncomputable instance : Fintype S.Flag := by classical exact Fintype.ofEquiv _ (Flag.equiv S).symm
instance : DecidableEq S.Side := (Side.equiv S).decidableEq
noncomputable instance : DecidableEq S.Corner := by classical exact (Corner.equiv S).decidableEq
instance : DecidableEq S.Flag := (Flag.equiv S).decidableEq

variable {S}

theorem Flag.edge_mem_edgeSet (φ : S.Flag) : φ.edge ∈ J.edgeSet := S.mem_edgeSet_of_mem φ.edge_mem

theorem Flag.vert_mem_verts (φ : S.Flag) : φ.vert ∈ S.verts φ.face := ⟨φ.edge, φ.edge_mem, φ.vert_mem⟩

variable (S)

/-- The vertex of `H` of a flag. -/
def vtx (φ : S.Flag) : S.RadV :=
  if φ.term then
    (if φ.spoke then .inr (.inr φ.face) else .inr (.inl ⟨φ.edge, φ.edge_mem_edgeSet⟩))
  else .inl φ.vert

/-- The edge of `H` of a flag: a half-edge `u q_e` (a dart of `J`) or a spoke `u f_φ`. -/
def edg (φ : S.Flag) : J.Dart ⊕ S.Corner :=
  if φ.spoke then .inr ⟨φ.face, φ.vert, φ.vert_mem_verts⟩
  else .inl ⟨(φ.vert, otherEnd φ.vert φ.edge), adj_otherEnd φ.vert_mem φ.edge_mem_edgeSet⟩

/-- The face of `H` of a flag. -/
def fac (φ : S.Flag) : S.Side := ⟨φ.face, φ.edge, φ.edge_mem⟩

/-- Change the vertex of the flag. -/
def t0 (φ : S.Flag) : S.Flag := { φ with term := !φ.term }

/-- Change the edge of the flag (inside the same side). -/
def t1 (φ : S.Flag) : S.Flag :=
  if φ.term then
    { φ with vert := otherEnd φ.vert φ.edge, vert_mem := otherEnd_mem φ.vert_mem }
  else { φ with spoke := !φ.spoke }

/-- Change the side of the flag. -/
noncomputable def t2 (φ : S.Flag) : S.Flag :=
  if φ.spoke then
    { φ with edge := S.otherEdge φ.face φ.vert φ.edge,
             edge_mem := (S.otherEdge_spec φ.edge_mem φ.vert_mem).2.1,
             vert_mem := (S.otherEdge_spec φ.edge_mem φ.vert_mem).2.2 }
  else
    { φ with face := S.otherFace φ.face φ.edge,
             edge_mem := (S.otherFace_spec φ.edge_mem).2 }

/-! ### The flag system axioms -/

section Axioms

variable {S}

theorem exists_mem_sym2 (e : Sym2 V) : ∃ u, u ∈ e := by
  induction e using Sym2.ind with
  | h a b => exact ⟨a, Sym2.mem_mk_left a b⟩

theorem otherEnd_mk (u w : V) : otherEnd u s(u, w) = w := by
  have h := otherEnd_spec (Sym2.mem_mk_left u w)
  exact Sym2.congr_right.mp h

@[simp] theorem t0_term (φ : S.Flag) : (S.t0 φ).term = !φ.term := rfl
@[simp] theorem t0_spoke (φ : S.Flag) : (S.t0 φ).spoke = φ.spoke := rfl
@[simp] theorem t0_face (φ : S.Flag) : (S.t0 φ).face = φ.face := rfl
@[simp] theorem t0_edge (φ : S.Flag) : (S.t0 φ).edge = φ.edge := rfl
@[simp] theorem t0_vert (φ : S.Flag) : (S.t0 φ).vert = φ.vert := rfl

@[simp] theorem t1_term (φ : S.Flag) : (S.t1 φ).term = φ.term := by
  unfold t1; split <;> rfl
@[simp] theorem t1_spoke (φ : S.Flag) :
    (S.t1 φ).spoke = if φ.term then φ.spoke else !φ.spoke := by
  unfold t1; split <;> simp_all
@[simp] theorem t1_vert (φ : S.Flag) :
    (S.t1 φ).vert = if φ.term then otherEnd φ.vert φ.edge else φ.vert := by
  unfold t1; split <;> simp_all
@[simp] theorem t1_face (φ : S.Flag) : (S.t1 φ).face = φ.face := by
  unfold t1; split <;> rfl
@[simp] theorem t1_edge (φ : S.Flag) : (S.t1 φ).edge = φ.edge := by
  unfold t1; split <;> rfl

@[simp] theorem t2_term (φ : S.Flag) : (S.t2 φ).term = φ.term := by
  unfold t2; split <;> rfl
@[simp] theorem t2_spoke (φ : S.Flag) : (S.t2 φ).spoke = φ.spoke := by
  unfold t2; split <;> rfl
@[simp] theorem t2_vert (φ : S.Flag) : (S.t2 φ).vert = φ.vert := by
  unfold t2; split <;> rfl
@[simp] theorem t2_face (φ : S.Flag) :
    (S.t2 φ).face = if φ.spoke then φ.face else S.otherFace φ.face φ.edge := by
  unfold t2; split <;> simp_all
@[simp] theorem t2_edge (φ : S.Flag) :
    (S.t2 φ).edge = if φ.spoke then S.otherEdge φ.face φ.vert φ.edge else φ.edge := by
  unfold t2; split <;> simp_all

theorem t0_t0 (φ : S.Flag) : S.t0 (S.t0 φ) = φ := by
  ext <;> simp

theorem t1_t1 (φ : S.Flag) : S.t1 (S.t1 φ) = φ := by
  ext
  · simp
  · simp
  · cases h : φ.term <;> simp [h, otherEnd_otherEnd φ.vert_mem]
  · simp
  · cases h : φ.term <;> simp [h]

theorem t2_t2 (φ : S.Flag) : S.t2 (S.t2 φ) = φ := by
  ext
  · cases h : φ.spoke <;> simp [h, S.otherFace_otherFace φ.edge_mem]
  · cases h : φ.spoke <;> simp [h, S.otherEdge_otherEdge φ.edge_mem φ.vert_mem]
  · simp
  · simp
  · simp

theorem vtx_t0 (φ : S.Flag) : S.vtx (S.t0 φ) ≠ S.vtx φ := by
  unfold vtx
  cases h : φ.term <;> cases hs : φ.spoke <;> simp [h, hs]

theorem edg_t0 (φ : S.Flag) : S.edg (S.t0 φ) = S.edg φ := rfl

theorem fac_t0 (φ : S.Flag) : S.fac (S.t0 φ) = S.fac φ := rfl

theorem vtx_t1 (φ : S.Flag) : S.vtx (S.t1 φ) = S.vtx φ := by
  unfold vtx
  cases h : φ.term <;> cases hs : φ.spoke <;> simp [h, hs]

theorem edg_t1 (φ : S.Flag) : S.edg (S.t1 φ) ≠ S.edg φ := by
  have hne := otherEnd_ne φ.vert_mem φ.edge_mem_edgeSet
  unfold edg
  cases h : φ.term <;> cases hs : φ.spoke
  · simp [h, hs]
  · simp [h, hs]
  · simp only [t1_spoke, h, hs, ite_true, Bool.false_eq_true, ite_false, ne_eq, Sum.inl.injEq]
    intro hd
    have := congrArg (fun d : J.Dart => d.toProd.1) hd
    simp only [t1_vert, h, ite_true] at this
    exact hne this
  · simp only [t1_spoke, h, hs, ite_true, ne_eq, Sum.inr.injEq]
    intro hc
    have := congrArg Corner.vert hc
    simp only [t1_vert, h, ite_true] at this
    exact hne this

theorem fac_t1 (φ : S.Flag) : S.fac (S.t1 φ) = S.fac φ := by
  unfold fac; congr 1 <;> simp

theorem vtx_t2 (φ : S.Flag) : S.vtx (S.t2 φ) = S.vtx φ := by
  unfold vtx
  cases h : φ.term <;> cases hs : φ.spoke <;> simp [h, hs]

theorem edg_t2 (φ : S.Flag) : S.edg (S.t2 φ) = S.edg φ := by
  unfold edg
  cases hs : φ.spoke <;> simp [hs]

theorem fac_t2 (φ : S.Flag) : S.fac (S.t2 φ) ≠ S.fac φ := by
  cases h : φ.spoke
  · intro hf
    have := congrArg Side.face hf
    simp only [fac, t2_face, h, Bool.false_eq_true, ite_false] at this
    exact (S.otherFace_spec φ.edge_mem).1 this
  · intro hf
    have := congrArg Side.edge hf
    simp only [fac, t2_edge, h, ite_true] at this
    exact (S.otherEdge_spec φ.edge_mem φ.vert_mem).1 this

variable (S)

theorem vtx_surj (hJ : ∀ v : V, ∃ w, J.Adj v w) : Function.Surjective S.vtx := by
  rintro (u | ⟨e, he⟩ | f)
  · obtain ⟨w, hw⟩ := hJ u
    obtain ⟨f, hf⟩ := S.exists_face_of_edge (J.mem_edgeSet.mpr hw)
    exact ⟨⟨f, s(u, w), u, false, false, hf, Sym2.mem_mk_left _ _⟩, rfl⟩
  · obtain ⟨f, hf⟩ := S.exists_face_of_edge he
    obtain ⟨u, hu⟩ := exists_mem_sym2 e
    exact ⟨⟨f, e, u, true, false, hf, hu⟩, rfl⟩
  · obtain ⟨e, he⟩ := S.edges_nonempty f
    obtain ⟨u, hu⟩ := exists_mem_sym2 e
    exact ⟨⟨f, e, u, true, true, he, hu⟩, rfl⟩

theorem edg_surj : Function.Surjective S.edg := by
  rintro (d | ⟨f, u, hu⟩)
  · obtain ⟨f, hf⟩ := S.exists_face_of_edge (J.mem_edgeSet.mpr d.adj)
    refine ⟨⟨f, s(d.fst, d.snd), d.fst, false, false, hf, Sym2.mem_mk_left _ _⟩, ?_⟩
    simp only [edg, Bool.false_eq_true, ite_false, Sum.inl.injEq]
    ext <;> simp [otherEnd_mk, -SimpleGraph.Dart.sym2Mk_fst_snd]
  · obtain ⟨e, he, hue⟩ := hu
    exact ⟨⟨f, e, u, false, true, he, hue⟩, rfl⟩

theorem fac_surj : Function.Surjective S.fac := by
  rintro ⟨f, e, he⟩
  obtain ⟨u, hu⟩ := exists_mem_sym2 e
  exact ⟨⟨f, e, u, false, false, he, hu⟩, rfl⟩

/-- The flag system of the radial graph. -/
noncomputable def flagSystem (hJ : ∀ v : V, ∃ w, J.Adj v w) :
    FlagSystem S.Flag S.RadV (J.Dart ⊕ S.Corner) S.Side where
  vtx := S.vtx
  edg := S.edg
  fac := S.fac
  τ0 := S.t0
  τ1 := S.t1
  τ2 := S.t2
  τ0_inv := t0_t0
  τ1_inv := t1_t1
  τ2_inv := t2_t2
  vtx_τ0 := vtx_t0
  edg_τ0 := edg_t0
  fac_τ0 := fac_t0
  vtx_τ1 := vtx_t1
  edg_τ1 := edg_t1
  fac_τ1 := fac_t1
  vtx_τ2 := vtx_t2
  edg_τ2 := edg_t2
  fac_τ2 := fac_t2
  vtx_surj := S.vtx_surj hJ
  edg_surj := S.edg_surj
  fac_surj := S.fac_surj

end Axioms

/-! ### Counting: Euler's formula for the flag system -/

section Counting

/-- A nondiagonal pair has exactly two members. -/
theorem card_mem_sym2 {e : Sym2 V} (he : ¬ e.IsDiag) :
    (Finset.univ.filter (fun u => u ∈ e)).card = 2 := by
  induction e using Sym2.ind with
  | h a b =>
    have hab : a ≠ b := fun h => he (by simp [h])
    have : Finset.univ.filter (fun u => u ∈ s(a, b)) = {a, b} := by
      ext u; simp [Sym2.mem_iff]
    rw [this, Finset.card_pair hab]

theorem card_side : Fintype.card S.Side = 2 * Nat.card J.edgeSet := by
  classical
  let eqv : S.Side ≃ Σ e : J.edgeSet, {f : S.Face // (e : Sym2 V) ∈ S.edges f} :=
    { toFun := fun s => ⟨⟨s.edge, S.mem_edgeSet_of_mem s.edge_mem⟩, ⟨s.face, s.edge_mem⟩⟩
      invFun := fun p => ⟨p.2.1, p.1.1, p.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr eqv, Fintype.card_sigma]
  have h2 : ∀ e : J.edgeSet, Fintype.card {f : S.Face // (e : Sym2 V) ∈ S.edges f} = 2 := by
    intro e
    rw [Fintype.card_subtype]
    exact S.two_faces e e.2
  simp only [h2, Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card]
  ring

theorem card_flag : Fintype.card S.Flag = 8 * Fintype.card S.Side := by
  classical
  let eqv : S.Flag ≃ Σ s : S.Side, {u : V // u ∈ s.edge} × Bool × Bool :=
    { toFun := fun φ => ⟨⟨φ.face, φ.edge, φ.edge_mem⟩, ⟨φ.vert, φ.vert_mem⟩, φ.term, φ.spoke⟩
      invFun := fun p => ⟨p.1.face, p.1.edge, p.2.1.1, p.2.2.1, p.2.2.2, p.1.edge_mem, p.2.1.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr eqv, Fintype.card_sigma]
  have h2 : ∀ s : S.Side, Fintype.card ({u : V // u ∈ s.edge} × Bool × Bool) = 8 := by
    intro s
    rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_bool, Fintype.card_subtype,
      card_mem_sym2 (J.not_isDiag_of_mem_edgeSet (S.mem_edgeSet_of_mem s.edge_mem))]
  simp only [h2, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  ring

/-- Double counting for an edge set without loops: the degrees sum to twice the size. -/
theorem sum_edgeDeg (F : Finset (Sym2 V)) (hF : ∀ e ∈ F, ¬ e.IsDiag) :
    ∑ u : V, edgeDeg F u = 2 * F.card := by
  classical
  simp only [edgeDeg, Finset.card_filter]
  rw [Finset.sum_comm]
  rw [Finset.card_eq_sum_ones, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  rw [← Finset.card_filter, card_mem_sym2 (hF e he)]
  ring

theorem edgeDeg_eq_zero_of_not_mem {f : S.Face} {u : V} (hu : u ∉ S.verts f) :
    edgeDeg (S.edges f) u = 0 :=
  Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr fun e he hue => hu ⟨e, he, hue⟩)

/-- On a face, the number of vertices equals the number of edges. -/
theorem card_verts_eq (f : S.Face) :
    Nat.card {u : V // u ∈ S.verts f} = (S.edges f).card := by
  classical
  have h1 := sum_edgeDeg (S.edges f) (fun e he => J.not_isDiag_of_mem_edgeSet
    (S.mem_edgeSet_of_mem he))
  have h2 : ∑ u : V, edgeDeg (S.edges f) u =
      ∑ u : V, if u ∈ S.verts f then 2 else 0 := by
    apply Finset.sum_congr rfl
    intro u _
    by_cases hu : u ∈ S.verts f
    · simp only [hu, ite_true]; exact S.edgeDeg_eq_two_of_mem hu
    · simp only [hu, ite_false]; exact S.edgeDeg_eq_zero_of_not_mem hu
  rw [h2, ← Finset.sum_filter, Finset.sum_const, smul_eq_mul] at h1
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  lia

theorem card_corner : Fintype.card S.Corner = Fintype.card S.Side := by
  classical
  let e1 : S.Corner ≃ Σ f : S.Face, {u : V // u ∈ S.verts f} :=
    { toFun := fun c => ⟨c.face, c.vert, c.vert_mem⟩
      invFun := fun p => ⟨p.1, p.2.1, p.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let e2 : S.Side ≃ Σ f : S.Face, {e : Sym2 V // e ∈ S.edges f} :=
    { toFun := fun c => ⟨c.face, c.edge, c.edge_mem⟩
      invFun := fun p => ⟨p.1, p.2.1, p.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e1, Fintype.card_congr e2, Fintype.card_sigma, Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro f _
  rw [← Nat.card_eq_fintype_card, card_verts_eq, Fintype.card_subtype]
  simp

/-- **Euler's formula for the flag system of `H`.** -/
theorem flag_euler [DecidableRel J.Adj] :
    2 * (Fintype.card S.RadV + Fintype.card (J.Dart ⊕ S.Corner) + Fintype.card S.Side) =
      Fintype.card S.Flag + 4 := by
  classical
  have he := S.euler
  have hd : Fintype.card J.Dart = 2 * Nat.card J.edgeSet := by
    rw [dart_card_eq_twice_card_edges, edgeFinset_card, Nat.card_eq_fintype_card]
  have hR : Fintype.card S.RadV = Fintype.card V + Nat.card J.edgeSet + Fintype.card S.Face := by
    rw [← Nat.card_eq_fintype_card, Nat.card_sum, Nat.card_sum, Nat.card_eq_fintype_card (α := V),
      Nat.card_eq_fintype_card (α := S.Face)]
    ring
  rw [hR, Fintype.card_sum, hd, card_corner, card_flag, card_side]
  lia

end Counting

/-! ### Connectivity of the flag graph -/

section Connectivity

variable (hJ : ∀ v : V, ∃ w, J.Adj v w)

/-- The flag graph of `H`. -/
noncomputable abbrev fg : SimpleGraph S.Flag := (S.flagSystem hJ).graph

/-- The base flag of a side at an endpoint. -/
def baseFlag (f : S.Face) (e : Sym2 V) (u : V) (he : e ∈ S.edges f) (hu : u ∈ e) : S.Flag :=
  ⟨f, e, u, false, false, he, hu⟩

theorem fg_adj_t0 (φ : S.Flag) : (S.fg hJ).Adj φ (S.t0 φ) := (S.flagSystem hJ).adj_τ0 φ
theorem fg_adj_t1 (φ : S.Flag) : (S.fg hJ).Adj φ (S.t1 φ) := (S.flagSystem hJ).adj_τ1 φ
theorem fg_adj_t2 (φ : S.Flag) : (S.fg hJ).Adj φ (S.t2 φ) := (S.flagSystem hJ).adj_τ2 φ

theorem reach_base (φ : S.Flag) :
    (S.fg hJ).Reachable φ (S.baseFlag φ.face φ.edge φ.vert φ.edge_mem φ.vert_mem) := by
  obtain ⟨f, e, u, a, b, he, hu⟩ := φ
  cases a <;> cases b
  · exact Reachable.refl _
  · -- spoke: one `t1` step
    have h1 : S.t1 ⟨f, e, u, false, true, he, hu⟩ = S.baseFlag f e u he hu := by
      ext <;> simp [baseFlag]
    exact h1 ▸ (S.fg_adj_t1 hJ _).reachable
  · have h1 : S.t0 ⟨f, e, u, true, false, he, hu⟩ = S.baseFlag f e u he hu := by
      ext <;> simp [baseFlag]
    exact h1 ▸ (S.fg_adj_t0 hJ _).reachable
  · have h1 : S.t0 ⟨f, e, u, true, true, he, hu⟩ = ⟨f, e, u, false, true, he, hu⟩ := by
      ext <;> simp
    have h2 : S.t1 ⟨f, e, u, false, true, he, hu⟩ = S.baseFlag f e u he hu := by
      ext <;> simp [baseFlag]
    exact (h1 ▸ (S.fg_adj_t0 hJ _).reachable).trans (h2 ▸ (S.fg_adj_t1 hJ _).reachable)

theorem reach_base_otherEnd (f : S.Face) (e : Sym2 V) (u : V) (he : e ∈ S.edges f)
    (hu : u ∈ e) :
    (S.fg hJ).Reachable (S.baseFlag f e u he hu)
      (S.baseFlag f e (otherEnd u e) he (otherEnd_mem hu)) := by
  have h1 : S.t0 (S.baseFlag f e u he hu) = ⟨f, e, u, true, false, he, hu⟩ := by
    ext <;> simp [baseFlag]
  have h2 : S.t1 ⟨f, e, u, true, false, he, hu⟩ =
      ⟨f, e, otherEnd u e, true, false, he, otherEnd_mem hu⟩ := by
    ext <;> simp
  have h3 : S.t0 ⟨f, e, otherEnd u e, true, false, he, otherEnd_mem hu⟩ =
      S.baseFlag f e (otherEnd u e) he (otherEnd_mem hu) := by
    ext <;> simp [baseFlag]
  exact ((h1 ▸ (S.fg_adj_t0 hJ _).reachable).trans (h2 ▸ (S.fg_adj_t1 hJ _).reachable)).trans
    (h3 ▸ (S.fg_adj_t0 hJ _).reachable)

theorem reach_base_otherFace (f : S.Face) (e : Sym2 V) (u : V) (he : e ∈ S.edges f)
    (hu : u ∈ e) :
    (S.fg hJ).Reachable (S.baseFlag f e u he hu)
      (S.baseFlag (S.otherFace f e) e u (S.otherFace_spec he).2 hu) := by
  have h1 : S.t2 (S.baseFlag f e u he hu) =
      S.baseFlag (S.otherFace f e) e u (S.otherFace_spec he).2 hu := by
    ext <;> simp [baseFlag]
  exact h1 ▸ (S.fg_adj_t2 hJ _).reachable

theorem reach_base_otherEdge (f : S.Face) (e : Sym2 V) (u : V) (he : e ∈ S.edges f)
    (hu : u ∈ e) :
    (S.fg hJ).Reachable (S.baseFlag f e u he hu)
      (S.baseFlag f (S.otherEdge f u e) u (S.otherEdge_spec he hu).2.1
        (S.otherEdge_spec he hu).2.2) := by
  have h1 : S.t1 (S.baseFlag f e u he hu) = ⟨f, e, u, false, true, he, hu⟩ := by
    ext <;> simp [baseFlag]
  have h2 : S.t2 ⟨f, e, u, false, true, he, hu⟩ =
      ⟨f, S.otherEdge f u e, u, false, true, (S.otherEdge_spec he hu).2.1,
        (S.otherEdge_spec he hu).2.2⟩ := by
    ext <;> simp
  have h3 : S.t1 ⟨f, S.otherEdge f u e, u, false, true, (S.otherEdge_spec he hu).2.1,
        (S.otherEdge_spec he hu).2.2⟩ =
      S.baseFlag f (S.otherEdge f u e) u (S.otherEdge_spec he hu).2.1
        (S.otherEdge_spec he hu).2.2 := by
    ext <;> simp [baseFlag]
  exact ((h1 ▸ (S.fg_adj_t1 hJ _).reachable).trans (h2 ▸ (S.fg_adj_t2 hJ _).reachable)).trans
    (h3 ▸ (S.fg_adj_t1 hJ _).reachable)

theorem reach_base_same (f : S.Face) (e₁ e₂ : Sym2 V) (u : V) (h₁ : e₁ ∈ S.edges f)
    (hu₁ : u ∈ e₁) (h₂ : e₂ ∈ S.edges f) (hu₂ : u ∈ e₂) :
    (S.fg hJ).Reachable (S.baseFlag f e₁ u h₁ hu₁) (S.baseFlag f e₂ u h₂ hu₂) := by
  by_cases h : e₂ = e₁
  · subst h; exact Reachable.refl _
  · have := S.otherEdge_unique h₁ hu₁ h h₂ hu₂
    subst this
    exact S.reach_base_otherEdge hJ f e₁ u h₁ hu₁

theorem reach_base_link (hlink : S.LinksConnected) (u : V) (f g : S.Face) (e₁ e₂ : Sym2 V)
    (h₁ : e₁ ∈ S.edges f) (hu₁ : u ∈ e₁) (h₂ : e₂ ∈ S.edges g) (hu₂ : u ∈ e₂) :
    (S.fg hJ).Reachable (S.baseFlag f e₁ u h₁ hu₁) (S.baseFlag g e₂ u h₂ hu₂) := by
  obtain ⟨p⟩ := hlink u f g ⟨e₁, h₁, hu₁⟩ ⟨e₂, h₂, hu₂⟩
  induction p generalizing e₁ with
  | nil => exact S.reach_base_same hJ _ e₁ e₂ u h₁ hu₁ h₂ hu₂
  | @cons a b c hab p ih =>
    rw [fromRel_adj] at hab
    obtain ⟨hne, hab⟩ := hab
    obtain ⟨d, hda, hdb, hud⟩ : ∃ d, d ∈ S.edges a ∧ d ∈ S.edges b ∧ u ∈ d := by
      rcases hab with ⟨d, h1, h2, h3⟩ | ⟨d, h1, h2, h3⟩
      · exact ⟨d, h1, h2, h3⟩
      · exact ⟨d, h2, h1, h3⟩
    have hb : b = S.otherFace a d := S.otherFace_unique hda (Ne.symm hne) hdb
    refine (S.reach_base_same hJ a e₁ d u h₁ hu₁ hda hud).trans ?_
    refine (S.reach_base_otherFace hJ a d u hda hud).trans ?_
    have := ih d hdb hud
    subst hb
    exact this h₂

theorem reach_base_walk (hlink : S.LinksConnected) {u w : V} (p : J.Walk u w) :
    ∀ (f₁ : S.Face) (e₁ : Sym2 V) (h₁ : e₁ ∈ S.edges f₁) (hu₁ : u ∈ e₁)
      (f₂ : S.Face) (e₂ : Sym2 V) (h₂ : e₂ ∈ S.edges f₂) (hw₂ : w ∈ e₂),
      (S.fg hJ).Reachable (S.baseFlag f₁ e₁ u h₁ hu₁) (S.baseFlag f₂ e₂ w h₂ hw₂) := by
  induction p with
  | nil =>
    intro f₁ e₁ h₁ hu₁ f₂ e₂ h₂ hw₂
    exact S.reach_base_link hJ hlink _ _ _ _ _ h₁ hu₁ h₂ hw₂
  | @cons a b c hab p ih =>
    intro f₁ e₁ h₁ hu₁ f₂ e₂ h₂ hw₂
    have hab' : s(a, b) ∈ J.edgeSet := J.mem_edgeSet.mpr hab
    obtain ⟨g, hg⟩ := S.exists_face_of_edge hab'
    have hbmem : b ∈ s(a, b) := Sym2.mem_mk_right _ _
    refine (S.reach_base_link hJ hlink a f₁ g e₁ s(a, b) h₁ hu₁ hg (Sym2.mem_mk_left _ _)).trans ?_
    have hstep := S.reach_base_otherEnd hJ g s(a, b) a hg (Sym2.mem_mk_left _ _)
    have heq : S.baseFlag g s(a, b) (otherEnd a s(a, b)) hg (otherEnd_mem (Sym2.mem_mk_left _ _)) =
        S.baseFlag g s(a, b) b hg hbmem := by
      ext <;> simp [baseFlag, otherEnd_mk]
    rw [heq] at hstep
    exact hstep.trans (ih g s(a, b) hg hbmem f₂ e₂ h₂ hw₂)

/-- **The flag graph of `H` is connected.** -/
theorem fg_connected [Nonempty V] (hlink : S.LinksConnected) :
    (S.fg hJ).Connected := by
  obtain ⟨w₀, h₀⟩ := hJ (Classical.arbitrary V)
  obtain ⟨f₀, hf₀⟩ := S.exists_face_of_edge (J.mem_edgeSet.mpr h₀)
  have hne : Nonempty S.Flag :=
    ⟨S.baseFlag f₀ s(Classical.arbitrary V, w₀) _ hf₀ (Sym2.mem_mk_left _ _)⟩
  refine ⟨fun φ ψ => ?_⟩
  obtain ⟨p⟩ := S.connected.preconnected φ.vert ψ.vert
  exact ((S.reach_base hJ φ).trans (S.reach_base_walk hJ hlink p _ _ φ.edge_mem φ.vert_mem _ _
    ψ.edge_mem ψ.vert_mem)).trans (S.reach_base hJ ψ).symm

end Connectivity

end PlanarFaces

end Lemmata.PlanarSteinerXC
