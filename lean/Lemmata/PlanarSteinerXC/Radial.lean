module

public import Lemmata.PlanarSteinerXC.FaceSystem
public import Lemmata.PlanarSteinerXC.CoverGraph

/-!
# The radial Steiner instance (Lemma 4 and Proposition 5)

Given a plane graph `J` (with a planar face system), the graph `H` has the vertices of `J` as
optional vertices, one *edge terminal* `q_e` subdividing every edge `e`, and one *face terminal*
`f_φ` for every face, joined to the vertices on its boundary. `R` is the set of all terminals.

For `S ⊆ V(J)`, `H[R ∪ S]` is connected iff `S` is a vertex cover of `J` (Lemma 4). Minimizing the
number of edges and then maximizing the number of marked edges exposes a face of each of the four
Steiner polyhedra whose marker coordinates are exactly the minimum-cover face of `J`
(Proposition 5).
-/

@[expose] public section

set_option autoImplicit false

namespace Lemmata.PlanarSteinerXC

open SimpleGraph

/-! ### General counting facts -/

section Counting

variable {W : Type*} [Finite W]

/-- Edges of an induced subgraph, together with the edges that leave the vertex set, are at most
the edges of the graph. -/
theorem card_induce_add_card_outside_le (K : SimpleGraph W) (C : Set W) :
    Nat.card (K.induce C).edgeSet + Nat.card {e | e ∈ K.edgeSet ∧ ¬ ∀ v ∈ e, v ∈ C} ≤
      Nat.card K.edgeSet := by
  classical
  have hfin : Set.Finite K.edgeSet := Set.toFinite _
  let f := (Embedding.induce (G := K) C).mapEdgeSet
  have hrange : Set.range (fun e => (f e : Sym2 W)) ⊆ {e | e ∈ K.edgeSet ∧ ∀ v ∈ e, v ∈ C} := by
    rintro _ ⟨⟨e, he⟩, rfl⟩
    induction e using Sym2.ind with
    | h a b =>
      refine ⟨(f ⟨s(a, b), he⟩).2, ?_⟩
      simp only [f, Embedding.mapEdgeSet]
      intro v hv
      rcases Sym2.mem_iff.mp hv with rfl | rfl
      · exact a.2
      · exact b.2
  have hinj : Function.Injective (fun e => (f e : Sym2 W)) :=
    Subtype.val_injective.comp f.injective
  have h1 : Nat.card (K.induce C).edgeSet = (Set.range (fun e => (f e : Sym2 W))).ncard := by
    rw [Set.ncard_range_of_injective hinj]
  rw [h1, Nat.card_coe_set_eq, Nat.card_coe_set_eq, ← Set.ncard_union_eq]
  · apply Set.ncard_le_ncard _ hfin
    rintro e (he | he)
    · exact (hrange he).1
    · exact he.1
  · rw [Set.disjoint_left]
    rintro e he ⟨-, he'⟩
    exact he' (hrange he).2

/-- A vertex set inducing a connected subgraph has at most one more vertex than the number of
edges inside it; the edges leaving it count extra. -/
theorem card_le_of_induce_connected (K : SimpleGraph W) (C : Set W)
    (hC : (K.induce C).Connected) :
    Nat.card C + Nat.card {e | e ∈ K.edgeSet ∧ ¬ ∀ v ∈ e, v ∈ C} ≤ Nat.card K.edgeSet + 1 := by
  have h1 := hC.card_vert_le_card_edgeSet_add_one
  have h2 := card_induce_add_card_outside_le K C
  lia

end Counting

/-! ### The radial graph -/

variable {V : Type*} [Fintype V] [DecidableEq V] {J : SimpleGraph V}

namespace PlanarFaces

variable (S : PlanarFaces J)

/-- The vertices of the radial graph: optional vertices, edge terminals, face terminals. -/
abbrev RadV := V ⊕ (J.edgeSet ⊕ S.Face)

/-- Adjacency of the radial graph. -/
def radAdj : S.RadV → S.RadV → Prop
  | .inl v, .inr (.inl e) => v ∈ (e : Sym2 V)
  | .inr (.inl e), .inl v => v ∈ (e : Sym2 V)
  | .inl v, .inr (.inr f) => v ∈ S.verts f
  | .inr (.inr f), .inl v => v ∈ S.verts f
  | _, _ => False

/-- The radial Steiner graph `H`. -/
def radial : SimpleGraph S.RadV where
  Adj := S.radAdj
  symm := ⟨by rintro (v | e | f) (w | e' | f') h <;> simp_all [radAdj]⟩
  loopless := ⟨by rintro (v | e | f) h <;> simp_all [radAdj]⟩

noncomputable instance instFintypeRadV : Fintype S.RadV := by
  classical exact inferInstance

noncomputable instance instDecRelRadial : DecidableRel S.radial.Adj := Classical.decRel _

/-- The terminals: all edge terminals and face terminals. -/
def terms : Set S.RadV := Set.range Sum.inr

@[simp] theorem radial_adj_inl_edge (v : V) (e : J.edgeSet) :
    S.radial.Adj (.inl v) (.inr (.inl e)) ↔ v ∈ (e : Sym2 V) := Iff.rfl

@[simp] theorem radial_adj_inl_face (v : V) (f : S.Face) :
    S.radial.Adj (.inl v) (.inr (.inr f)) ↔ v ∈ S.verts f := Iff.rfl

@[simp] theorem radial_adj_edge_inl (v : V) (e : J.edgeSet) :
    S.radial.Adj (.inr (.inl e)) (.inl v) ↔ v ∈ (e : Sym2 V) := Iff.rfl

@[simp] theorem radial_adj_face_inl (v : V) (f : S.Face) :
    S.radial.Adj (.inr (.inr f)) (.inl v) ↔ v ∈ S.verts f := Iff.rfl

theorem not_radial_adj_inl_inl (v w : V) : ¬ S.radial.Adj (.inl v) (.inl w) := id

theorem not_radial_adj_inr_inr (a b : J.edgeSet ⊕ S.Face) :
    ¬ S.radial.Adj (.inr a) (.inr b) := by
  rcases a with a | a <;> rcases b with b | b <;> exact id

/-- Every edge of `H` joins an optional vertex and a terminal. -/
theorem radial_adj_cases {x y : S.RadV} (h : S.radial.Adj x y) :
    (∃ v t, x = .inl v ∧ y = .inr t) ∨ (∃ v t, x = .inr t ∧ y = .inl v) := by
  rcases x with v | t <;> rcases y with w | t'
  · exact absurd h (S.not_radial_adj_inl_inl v w)
  · exact Or.inl ⟨v, t', rfl, rfl⟩
  · exact Or.inr ⟨w, t, rfl, rfl⟩
  · exact absurd h (S.not_radial_adj_inr_inr t t')

/-- A face containing each vertex (for the marked edges). -/
noncomputable def markFace (hJ : ∀ v : V, ∃ w, J.Adj v w) (v : V) : S.Face :=
  Classical.choose (S.exists_face_of_adj (Classical.choose_spec (hJ v)))

theorem mem_verts_markFace (hJ : ∀ v : V, ∃ w, J.Adj v w) (v : V) :
    v ∈ S.verts (S.markFace hJ v) :=
  Classical.choose_spec (S.exists_face_of_adj (Classical.choose_spec (hJ v)))

/-! ### Lemma 4: covers give connected induced subgraphs -/

/-- The terminals together with the optional vertices of `T`. -/
def withOpt (T : Set V) : Set S.RadV := S.terms ∪ Sum.inl '' T

theorem inr_mem_withOpt (T : Set V) (t : J.edgeSet ⊕ S.Face) : (.inr t : S.RadV) ∈ S.withOpt T :=
  Or.inl ⟨t, rfl⟩

theorem inl_mem_withOpt {T : Set V} {v : V} : (.inl v : S.RadV) ∈ S.withOpt T ↔ v ∈ T := by
  simp [withOpt, terms]

/-- **Lemma 4.** If `T` is a vertex cover of `J`, then `H[R ∪ T]` is connected. -/
theorem induce_connected_of_cover [Nonempty V] (hJ : ∀ v : V, ∃ w, J.Adj v w) {T : Set V}
    (hT : J.IsVertexCover T) : (S.radial.induce (S.withOpt T)).Connected := by
  classical
  set W := S.withOpt T
  let I := S.radial.induce W
  have hadjI : ∀ x y (hx : x ∈ W) (hy : y ∈ W), S.radial.Adj x y → I.Adj ⟨x, hx⟩ ⟨y, hy⟩ :=
    fun _ _ _ _ h => h
  -- every face terminal reaches a fixed face terminal
  obtain ⟨w₀, h₀⟩ := hJ (Classical.arbitrary V)
  obtain ⟨f₀, hf₀⟩ := S.exists_face_of_adj h₀
  let F (f : S.Face) : W := ⟨.inr (.inr f), S.inr_mem_withOpt T _⟩
  have hstep : ∀ (f : S.Face) (x : V) (hx : x ∈ T), x ∈ S.verts f →
      I.Adj (F f) ⟨.inl x, S.inl_mem_withOpt.mpr hx⟩ :=
    fun f x hx hxf => hadjI _ _ _ _ hxf
  have key : ∀ {a b : S.Face}, S.dual.Walk a b → I.Reachable (F a) (F b) := by
    intro a b p
    induction p with
    | nil => exact Reachable.refl _
    | @cons a b c hab p ih =>
      refine Reachable.trans ?_ ih
      rw [dual, fromRel_adj] at hab
      obtain ⟨-, hab⟩ := hab
      obtain ⟨e, hea, heb⟩ : ∃ e, e ∈ S.edges a ∧ e ∈ S.edges b := by
        rcases hab with ⟨e, h1, h2⟩ | ⟨e, h1, h2⟩
        · exact ⟨e, h1, h2⟩
        · exact ⟨e, h2, h1⟩
      have heJ := S.mem_edgeSet_of_mem hea
      induction e using Sym2.ind with
      | h x y =>
        have hcov := hT (J.mem_edgeSet.mp heJ)
        rcases hcov with hx | hx
        · exact (hstep a x hx ⟨_, hea, Sym2.mem_mk_left _ _⟩).reachable.trans
            (hstep b x hx ⟨_, heb, Sym2.mem_mk_left _ _⟩).reachable.symm
        · exact (hstep a y hx ⟨_, hea, Sym2.mem_mk_right _ _⟩).reachable.trans
            (hstep b y hx ⟨_, heb, Sym2.mem_mk_right _ _⟩).reachable.symm
  have hface : ∀ f, I.Reachable (F f₀) (F f) := fun f =>
    let ⟨p⟩ := S.dual_conn.preconnected f₀ f
    key p
  have hall : ∀ w : W, I.Reachable (F f₀) w := by
    rintro ⟨x, hx⟩
    rcases x with v | (e | f)
    · have hv : v ∈ T := S.inl_mem_withOpt.mp hx
      exact (hface (S.markFace hJ v)).trans (hstep _ v hv (S.mem_verts_markFace hJ v)).reachable
    · obtain ⟨e, he⟩ := e
      induction e using Sym2.ind with
      | h x y =>
        obtain ⟨f, hf⟩ := S.exists_face_of_edge he
        have hcov := hT (J.mem_edgeSet.mp he)
        rcases hcov with hxT | hxT
        · have hxW : (.inl x : S.RadV) ∈ W := S.inl_mem_withOpt.mpr hxT
          have h2 : I.Adj ⟨.inl x, hxW⟩ ⟨_, hx⟩ := hadjI (.inl x) _ hxW hx (Sym2.mem_mk_left _ _)
          exact (hface f).trans ((hstep f x hxT ⟨_, hf, Sym2.mem_mk_left _ _⟩).reachable.trans
            h2.reachable)
        · have hxW : (.inl y : S.RadV) ∈ W := S.inl_mem_withOpt.mpr hxT
          have h2 : I.Adj ⟨.inl y, hxW⟩ ⟨_, hx⟩ := hadjI (.inl y) _ hxW hx (Sym2.mem_mk_right _ _)
          exact (hface f).trans ((hstep f y hxT ⟨_, hf, Sym2.mem_mk_right _ _⟩).reachable.trans
            h2.reachable)
    · exact hface f
  exact (connected_iff_exists_forall_reachable _).mpr ⟨F f₀, hall⟩

/-! ### Counting edges of terminal connectors -/

section Prop5

variable [Nonempty V] (hJ : ∀ v : V, ∃ w, J.Adj v w)

/-- A fixed face terminal. -/
noncomputable def root : S.RadV :=
  .inr (.inr (S.markFace hJ (Classical.arbitrary V)))

theorem root_mem_terms : S.root hJ ∈ S.terms := ⟨_, rfl⟩

include hJ in
/-- Every terminal has another terminal. -/
theorem exists_other_term (t : J.edgeSet ⊕ S.Face) :
    ∃ t' : J.edgeSet ⊕ S.Face, t' ≠ t := by
  rcases t with e | f
  · exact ⟨.inr (S.markFace hJ (Classical.arbitrary V)), by simp⟩
  · obtain ⟨w, hw⟩ := hJ (Classical.arbitrary V)
    exact ⟨.inl ⟨_, J.mem_edgeSet.mpr hw⟩, by simp⟩

include hJ in
/-- In a terminal connector, every terminal has an incident edge. -/
theorem term_mem_support {K : SimpleGraph S.RadV} (hc : Connects K S.terms)
    (t : J.edgeSet ⊕ S.Face) : ∃ y, K.Adj (.inr t) y := by
  obtain ⟨t', ht'⟩ := S.exists_other_term hJ t
  obtain ⟨p⟩ := hc (.inr t) ⟨t, rfl⟩ (.inr t') ⟨t', rfl⟩
  cases p with
  | nil => exact absurd rfl ht'
  | cons h _ => exact ⟨_, h⟩

/-- The vertices reachable from the root. -/
def comp (K : SimpleGraph S.RadV) : Set S.RadV := {w | K.Reachable (S.root hJ) w}

/-- The optional vertices reachable from the root. -/
def optOf (K : SimpleGraph S.RadV) : Set V := {v | K.Reachable (S.root hJ) (.inl v)}

theorem terms_subset_comp {K : SimpleGraph S.RadV} (hc : Connects K S.terms) :
    S.terms ⊆ S.comp hJ K :=
  fun t ht => hc _ (S.root_mem_terms hJ) t ht

theorem comp_eq {K : SimpleGraph S.RadV} (hc : Connects K S.terms) :
    S.comp hJ K = S.withOpt (S.optOf hJ K) := by
  ext x
  rcases x with v | t
  · simp [comp, optOf, S.inl_mem_withOpt]
  · simp only [S.inr_mem_withOpt, iff_true]
    exact S.terms_subset_comp hJ hc ⟨t, rfl⟩

/-- The optional vertices of a terminal connector form a vertex cover. -/
theorem optOf_isVertexCover {K : SimpleGraph S.RadV} (hK : K ≤ S.radial)
    (hc : Connects K S.terms) : J.IsVertexCover (S.optOf hJ K) := by
  intro u v huv
  set e : J.edgeSet := ⟨s(u, v), J.mem_edgeSet.mpr huv⟩
  obtain ⟨y, hy⟩ := S.term_mem_support hJ hc (.inl e)
  have hyH := hK hy
  rcases y with w | t
  · have hw : w ∈ (e : Sym2 V) := hyH
    have hreach : K.Reachable (S.root hJ) (.inl w) :=
      (S.terms_subset_comp hJ hc ⟨.inl e, rfl⟩).trans hy.reachable
    rcases Sym2.mem_iff.mp hw with rfl | rfl
    · exact Or.inl hreach
    · exact Or.inr hreach
  · exact absurd hyH (S.not_radial_adj_inr_inr _ _)

theorem comp_induce_connected (K : SimpleGraph S.RadV) :
    (K.induce (S.comp hJ K)).Connected := by
  have h : S.comp hJ K = (K.connectedComponentMk (S.root hJ)).supp := by
    ext w
    simp only [comp, Set.mem_ofPred_eq, ConnectedComponent.mem_supp_iff,
      ConnectedComponent.eq]
    exact ⟨Reachable.symm, Reachable.symm⟩
  rw [h]
  exact (K.connectedComponentMk (S.root hJ)).connected_toSimpleGraph

theorem ncard_withOpt (T : Set V) :
    (S.withOpt T).ncard = Nat.card S.terms + T.ncard := by
  rw [withOpt, Set.ncard_union_eq, Nat.card_coe_set_eq, Set.ncard_image_of_injective _ Sum.inl_injective]
  · rw [Set.disjoint_left]
    rintro _ ⟨t, rfl⟩ ⟨v, -, hv⟩
    exact Sum.inl_ne_inr hv

/-- **Counting lemma.** A terminal connector `K` satisfies
`|R| + |S_K| + #(edges outside the root component) ≤ |E(K)| + 1`, where `S_K` is the set of
optional vertices in the root component (a vertex cover). -/
theorem connector_count {K : SimpleGraph S.RadV} (hc : Connects K S.terms) :
    Nat.card S.terms + (S.optOf hJ K).ncard +
      Nat.card {e | e ∈ K.edgeSet ∧ ¬ ∀ v ∈ e, v ∈ S.comp hJ K} ≤ Nat.card K.edgeSet + 1 := by
  have h := card_le_of_induce_connected K (S.comp hJ K) (S.comp_induce_connected hJ K)
  rw [Nat.card_coe_set_eq, S.comp_eq hJ hc, S.ncard_withOpt] at h
  rw [S.comp_eq hJ hc]
  exact h

/-- The minimum cover size. -/
noncomputable def tau : ℕ := (Classical.choose (exists_isMinCover J)).ncard

theorem tau_spec : IsMinCover J (Classical.choose (exists_isMinCover J)) :=
  Classical.choose_spec (exists_isMinCover J)

theorem tau_le {T : Set V} (hT : J.IsVertexCover T) : tau (J := J) ≤ T.ncard :=
  (tau_spec (J := J)).2 T hT

theorem tau_eq_of_isMinCover {T : Set V} (hT : IsMinCover J T) : T.ncard = tau (J := J) :=
  le_antisymm (hT.2 _ (tau_spec (J := J)).1) (tau_le hT.1)

/-- The optimal number of edges plus one. -/
noncomputable def optPlusOne : ℕ := Nat.card S.terms + tau (J := J)

include hJ in
theorem connector_lower {K : SimpleGraph S.RadV} (hK : K ≤ S.radial)
    (hc : Connects K S.terms) : S.optPlusOne ≤ Nat.card K.edgeSet + 1 := by
  have h1 := S.connector_count hJ hc
  have h2 := tau_le (S.optOf_isVertexCover hJ hK hc)
  unfold optPlusOne
  lia

/-- The terminal connectors with the optimal number of edges. -/
def Fam0 : Set (SimpleGraph S.RadV) :=
  {K | K ≤ S.radial ∧ Connects K S.terms ∧ Nat.card K.edgeSet + 1 = S.optPlusOne}

theorem Fam0_optOf_isMinCover {K : SimpleGraph S.RadV} (hK : K ∈ S.Fam0) :
    IsMinCover J (S.optOf hJ K) := by
  obtain ⟨hle, hc, hcard⟩ := hK
  have h1 := S.connector_count hJ hc
  have hcov := S.optOf_isVertexCover hJ hle hc
  refine ⟨hcov, fun T hT => ?_⟩
  have := tau_le hT
  unfold optPlusOne at hcard
  lia

theorem Fam0_edges_inside {K : SimpleGraph S.RadV} (hK : K ∈ S.Fam0) {e : Sym2 S.RadV}
    (he : e ∈ K.edgeSet) : ∀ v ∈ e, v ∈ S.comp hJ K := by
  obtain ⟨hle, hc, hcard⟩ := hK
  have h1 := S.connector_count hJ hc
  have h2 := tau_le (S.optOf_isVertexCover hJ hle hc)
  by_contra hout
  have hpos : 0 < Nat.card {e | e ∈ K.edgeSet ∧ ¬ ∀ v ∈ e, v ∈ S.comp hJ K} := by
    rw [Nat.card_coe_set_eq]
    exact (Set.ncard_pos (Set.toFinite _)).mpr ⟨e, he, hout⟩
  unfold optPlusOne at hcard
  lia

theorem Fam0_mem_comp_of_adj {K : SimpleGraph S.RadV} (hK : K ∈ S.Fam0) {x y : S.RadV}
    (h : K.Adj x y) : x ∈ S.comp hJ K :=
  S.Fam0_edges_inside hJ hK (K.mem_edgeSet.mpr h) x (Sym2.mem_mk_left _ _)

include hJ in
/-- The edge sets with the optimal number of edges are minimal Steiner trees. -/
theorem Fam0_isMinConnector {K : SimpleGraph S.RadV} (hK : K ∈ S.Fam0) :
    IsMinConnector S.radial S.terms K := by
  refine ⟨hK.1, hK.2.1, fun K' hK' hc' => ?_⟩
  have hlow := S.connector_lower hJ (hK'.trans hK.1) hc'
  have hcard := hK.2.2
  rw [← edgeSet_inj]
  apply Set.eq_of_subset_of_ncard_le (edgeSet_subset_edgeSet.mpr hK') _ (Set.toFinite _)
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
  lia

include hJ in
/-- The edge sets with the optimal number of edges have connected support containing `R`. -/
theorem Fam0_isConnectedSupport {K : SimpleGraph S.RadV} (hK : K ∈ S.Fam0) :
    IsConnectedSupport S.radial S.terms K := by
  refine ⟨hK.1, ?_, ?_⟩
  · rintro _ ⟨t, rfl⟩
    obtain ⟨y, hy⟩ := S.term_mem_support hJ hK.2.1 t
    exact ⟨y, hy⟩
  · rintro u ⟨u', hu⟩ v ⟨v', hv⟩
    have hu' := S.Fam0_mem_comp_of_adj hJ hK hu
    have hv' := S.Fam0_mem_comp_of_adj hJ hK hv
    exact (Reachable.symm hu').trans hv'

end Prop5

/-! ### Marked edges and the double face -/

section Markers

variable [Nonempty V] (hJ : ∀ v : V, ∃ w, J.Adj v w)

/-- The marked edge at an optional vertex. -/
noncomputable def marker (v : V) : Sym2 S.RadV := s(.inl v, .inr (.inr (S.markFace hJ v)))

theorem marker_mem (v : V) : S.marker hJ v ∈ S.radial.edgeSet :=
  S.mem_verts_markFace hJ v

/-- The marked edge as a coordinate. -/
noncomputable def markerEdge (v : V) : S.radial.edgeSet := ⟨S.marker hJ v, S.marker_mem hJ v⟩

theorem markerEdge_injective : Function.Injective (S.markerEdge hJ) := by
  intro v w h
  have h' := congrArg Subtype.val h
  simp only [markerEdge, marker, Sym2.eq_iff, Sum.inl.injEq, reduceCtorEq, and_false,
    or_false] at h'
  exact h'.1

/-- The marked vertices of an edge set. -/
def marked (K : SimpleGraph S.RadV) : Set V := {v | S.marker hJ v ∈ K.edgeSet}

/-- Counting marked edges. -/
noncomputable def markSum : (S.radial.edgeSet → ℝ) →ₗ[ℝ] ℝ :=
  by classical exact sumOver (Finset.univ.image (S.markerEdge hJ))

theorem markSum_edgeVec (K : SimpleGraph S.RadV) :
    S.markSum hJ (edgeVec S.radial K) = ((S.marked hJ K).ncard : ℝ) := by
  classical
  unfold markSum
  rw [sumOver_apply, Finset.sum_image (fun v _ w _ h => S.markerEdge_injective hJ h)]
  simp_rw [edgeVec_apply]
  rw [Finset.sum_boole]
  congr 1
  unfold marked
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_ofPred]
  rfl

/-- Reading the marked coordinates. -/
noncomputable def markRead : (S.radial.edgeSet → ℝ) →ₗ[ℝ] (V → ℝ) :=
  LinearMap.funLeft ℝ ℝ (S.markerEdge hJ)

theorem markRead_edgeVec (K : SimpleGraph S.RadV) :
    S.markRead hJ (edgeVec S.radial K) = vertexVec (S.marked hJ K) := by
  classical
  funext v
  simp only [markRead, LinearMap.funLeft_apply, edgeVec_apply, vertexVec_apply]
  rfl

theorem marked_subset_optOf {K : SimpleGraph S.RadV} (hK : K ∈ S.Fam0) :
    S.marked hJ K ⊆ S.optOf hJ K := by
  intro v hv
  exact S.Fam0_mem_comp_of_adj hJ hK (K.mem_edgeSet.mp hv)

theorem ncard_marked_le {K : SimpleGraph S.RadV} (hK : K ∈ S.Fam0) :
    (S.marked hJ K).ncard ≤ tau (J := J) := by
  rw [← tau_eq_of_isMinCover (S.Fam0_optOf_isMinCover hJ hK)]
  exact Set.ncard_le_ncard (S.marked_subset_optOf hJ hK)

/-- The optimal edge sets that contain all their possible markers. -/
def Fam2 : Set (SimpleGraph S.RadV) :=
  {K | K ∈ S.Fam0 ∧ (S.marked hJ K).ncard = tau (J := J)}

theorem Fam2_marked_eq {K : SimpleGraph S.RadV} (hK : K ∈ S.Fam2 hJ) :
    S.marked hJ K = S.optOf hJ K := by
  apply Set.eq_of_subset_of_ncard_le (S.marked_subset_optOf hJ hK.1) _ (Set.toFinite _)
  rw [hK.2, tau_eq_of_isMinCover (S.Fam0_optOf_isMinCover hJ hK.1)]

/-- Every minimum cover is the marked set of an optimal tree. -/
theorem exists_lift {T : Set V} (hT : IsMinCover J T) :
    ∃ K ∈ S.Fam0, S.marked hJ K = T := by
  classical
  set W := S.withOpt T with hW
  have hconn := S.induce_connected_of_cover hJ hT.1
  let r : W → W → Prop := fun a b =>
    ∃ v ∈ T, a.1 = .inl v ∧ b.1 = .inr (.inr (S.markFace hJ v))
  let M : SimpleGraph W := SimpleGraph.fromRel r
  have hM : M ≤ S.radial.induce W := by
    intro a b hab
    rw [fromRel_adj] at hab
    obtain ⟨-, ⟨v, -, ha, hb⟩ | ⟨v, -, hb, ha⟩⟩ := hab
    · change S.radial.Adj a.1 b.1
      rw [ha, hb]; exact S.mem_verts_markFace hJ v
    · change S.radial.Adj a.1 b.1
      rw [ha, hb]; exact S.mem_verts_markFace hJ v
  have hnbr : ∀ (x : W) (v : V), x.1 = .inl v → ∀ y, M.Adj x y →
      y.1 = .inr (.inr (S.markFace hJ v)) := by
    intro x v hx y hxy
    rw [fromRel_adj] at hxy
    obtain ⟨-, ⟨v', -, ha, hb⟩ | ⟨v', -, hb, ha⟩⟩ := hxy
    · rw [hx, Sum.inl.injEq] at ha
      rw [hb, ha]
    · rw [hx] at ha
      exact absurd ha (by simp)
  have hMacyc : M.IsAcyclic := by
    intro a c hc
    have hnil : ¬ c.Nil := hc.not_nil
    have hadj := c.adj_snd hnil
    -- one endpoint of the first edge is an optional vertex
    obtain ⟨x, v, hxv, hx⟩ : ∃ x : W, ∃ v : V, x.1 = .inl v ∧ x ∈ c.support := by
      have h' := hadj
      rw [fromRel_adj] at h'
      obtain ⟨-, ⟨v, -, ha, -⟩ | ⟨v, -, hb, -⟩⟩ := h'
      · exact ⟨a, v, ha, c.start_mem_support⟩
      · exact ⟨c.snd, v, hb, c.getVert_mem_support 1⟩
    have h2 := hc.ncard_neighborSet_toSubgraph_eq_two hx
    have hsub : c.toSubgraph.neighborSet x ⊆
        {⟨.inr (.inr (S.markFace hJ v)), S.inr_mem_withOpt T _⟩} := by
      intro y hy
      have hy' : M.Adj x y := c.toSubgraph.adj_sub hy
      have := hnbr x v hxv y hy'
      exact Subtype.ext this
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_singleton, h2] at this
    lia
  obtain ⟨T', hMT', hT'H, htree⟩ := hconn.exists_isTree_le_of_le_of_isAcyclic hM hMacyc
  let f : W ↪ S.RadV := Function.Embedding.subtype _
  let K := T'.map f
  have hKle : K ≤ S.radial := by
    intro x y hxy
    rw [map_adj] at hxy
    obtain ⟨a, b, hab, rfl, rfl⟩ := hxy
    exact hT'H hab
  have hKconn : Connects K S.terms := by
    intro t ht t' ht'
    have hreach : T'.Reachable ⟨t, Or.inl ht⟩ ⟨t', Or.inl ht'⟩ := htree.connected.preconnected _ _
    exact hreach.map (Embedding.map f T').toHom
  have hcardT' : Nat.card T'.edgeSet + 1 = Nat.card W :=
    (isTree_iff_connected_and_card.mp htree).2
  have hcardK : Nat.card K.edgeSet = Nat.card T'.edgeSet := by
    rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq, edgeSet_map,
      Set.ncard_image_of_injective _ f.sym2Map.injective]
  have hW : Nat.card W = S.optPlusOne := by
    rw [Nat.card_coe_set_eq, S.ncard_withOpt, optPlusOne, tau_eq_of_isMinCover hT]
  refine ⟨K, ⟨hKle, hKconn, by lia⟩, ?_⟩
  ext v
  simp only [marked, Set.mem_ofPred_eq, marker, mem_edgeSet]
  change (T'.map f).Adj _ _ ↔ _
  rw [map_adj]
  constructor
  · rintro ⟨a, b, -, ha, -⟩
    have : (.inl v : S.RadV) ∈ W := ha ▸ a.2
    exact S.inl_mem_withOpt.mp this
  · intro hv
    have hvW : (.inl v : S.RadV) ∈ W := S.inl_mem_withOpt.mpr hv
    refine ⟨⟨_, hvW⟩, ⟨_, S.inr_mem_withOpt T _⟩, hMT' ?_, rfl, rfl⟩
    rw [fromRel_adj]
    refine ⟨fun h => by simp at h, Or.inl ⟨v, hv, rfl, rfl⟩⟩

/-- The double face: the convex hull of the optimal trees with all markers. -/
noncomputable def doubleFace : Set (S.radial.edgeSet → ℝ) :=
  convexHull ℝ (edgeVec S.radial '' S.Fam2 hJ)

/-- The marker coordinates of the double face are the minimum-cover face. -/
theorem markRead_doubleFace : S.markRead hJ '' S.doubleFace hJ = minCoverFace J := by
  unfold doubleFace minCoverFace
  rw [← LinearMap.coe_toAffineMap, image_convexHull_eq, Set.image_image]
  congr 1
  ext x
  simp only [Set.mem_image, LinearMap.coe_toAffineMap, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨K, hK, rfl⟩
    refine ⟨S.marked hJ K, ?_, (S.markRead_edgeVec hJ K).symm⟩
    rw [S.Fam2_marked_eq hJ hK]
    exact S.Fam0_optOf_isMinCover hJ hK.1
  · rintro ⟨T, hT, rfl⟩
    obtain ⟨K, hK, hmk⟩ := S.exists_lift hJ hT
    refine ⟨K, ⟨hK, ?_⟩, ?_⟩
    · rw [hmk, tau_eq_of_isMinCover hT]
    · rw [S.markRead_edgeVec, hmk]

/-- Restricting a family of terminal connectors that contains all optimal ones to the optimal
number of edges, and then to the maximum number of markers, gives the double face. -/
theorem family_double_face (P : SimpleGraph S.RadV → Prop)
    (hP1 : ∀ K, P K → K ≤ S.radial ∧ Connects K S.terms) (hP2 : ∀ K ∈ S.Fam0, P K) :
    (convexHull ℝ (edgeVec S.radial '' {K | P K}) ∩
        {x | sumOver Finset.univ x = (S.optPlusOne : ℝ) - 1}) ∩
      {x | S.markSum hJ x = (tau (J := J) : ℝ)} = S.doubleFace hJ := by
  classical
  have hpos : 1 ≤ S.optPlusOne := by
    obtain ⟨y, hy⟩ := S.exists_other_term hJ (.inr (S.markFace hJ (Classical.arbitrary V)))
    have : 0 < Nat.card S.terms := by
      rw [Nat.card_coe_set_eq]
      exact (Set.ncard_pos (Set.toFinite _)).mpr ⟨_, ⟨y, rfl⟩⟩
    unfold optPlusOne; lia
  rw [convexHull_inter_hyperplane_of_ge]
  · have hset : edgeVec S.radial '' {K | P K} ∩
        {x | sumOver Finset.univ x = (S.optPlusOne : ℝ) - 1} = edgeVec S.radial '' S.Fam0 := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_image, Set.mem_ofPred_eq, sumOver_apply]
      constructor
      · rintro ⟨⟨K, hK, rfl⟩, hsum⟩
        obtain ⟨hle, hc⟩ := hP1 K hK
        rw [sum_edgeVec _ _ hle] at hsum
        refine ⟨K, ⟨hle, hc, ?_⟩, rfl⟩
        have : (Nat.card K.edgeSet : ℝ) + 1 = S.optPlusOne := by linarith
        exact_mod_cast this
      · rintro ⟨K, hK, rfl⟩
        refine ⟨⟨K, hP2 K hK, rfl⟩, ?_⟩
        rw [sum_edgeVec _ _ hK.1]
        have : ((Nat.card K.edgeSet + 1 : ℕ) : ℝ) = S.optPlusOne := by exact_mod_cast hK.2.2
        push_cast at this; linarith
    rw [hset, convexHull_inter_hyperplane_of_le]
    · unfold doubleFace
      congr 1
      ext x
      simp only [Set.mem_inter_iff, Set.mem_image, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨⟨K, hK, rfl⟩, hmark⟩
        rw [S.markSum_edgeVec] at hmark
        exact ⟨K, ⟨hK, by exact_mod_cast hmark⟩, rfl⟩
      · rintro ⟨K, hK, rfl⟩
        exact ⟨⟨K, hK.1, rfl⟩, by rw [S.markSum_edgeVec]; exact_mod_cast hK.2⟩
    · rintro x ⟨K, hK, rfl⟩
      rw [S.markSum_edgeVec]
      exact_mod_cast S.ncard_marked_le hJ hK
  · rintro x ⟨K, hK, rfl⟩
    obtain ⟨hle, hc⟩ := hP1 K hK
    rw [sumOver_apply, sum_edgeVec _ _ hle]
    have := S.connector_lower hJ hle hc
    have h' : ((S.optPlusOne : ℕ) : ℝ) ≤ (Nat.card K.edgeSet : ℝ) + 1 := by exact_mod_cast this
    linarith

include hJ in
/-- The dominant has the same minimum face as `Pmin` for the all-ones objective. -/
theorem dom_inter_eq :
    Dom S.radial S.terms ∩ {x | sumOver Finset.univ x = (S.optPlusOne : ℝ) - 1} =
      Pmin S.radial S.terms ∩ {x | sumOver Finset.univ x = (S.optPlusOne : ℝ) - 1} := by
  classical
  have hlow : ∀ p ∈ Pmin S.radial S.terms, (S.optPlusOne : ℝ) - 1 ≤ sumOver Finset.univ p := by
    intro p hp
    unfold Pmin at hp
    refine (convexHull_min ?_ ?_ : convexHull ℝ _ ⊆ {x | (S.optPlusOne : ℝ) - 1 ≤
      sumOver Finset.univ x}) hp
    · rintro x ⟨K, hK, rfl⟩
      simp only [Set.mem_ofPred_eq, sumOver_apply]
      rw [sum_edgeVec _ _ hK.1]
      have := S.connector_lower hJ hK.1 hK.2.1
      have h' : ((S.optPlusOne : ℕ) : ℝ) ≤ (Nat.card K.edgeSet : ℝ) + 1 := by exact_mod_cast this
      linarith
    · intro a ha b hb s t hs ht hst
      simp only [Set.mem_ofPred_eq, map_add, map_smul, smul_eq_mul] at ha hb ⊢
      nlinarith
  ext x
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨p, hp, r, hr, rfl⟩, hsum⟩
    have h1 := hlow p hp
    have hr0 : 0 ≤ sumOver Finset.univ r := by
      rw [sumOver_apply]; exact Finset.sum_nonneg fun e _ => hr e
    rw [map_add] at hsum
    have hrz : sumOver Finset.univ r = 0 := by linarith
    have hr' : r = 0 := by
      rw [sumOver_apply, Finset.sum_eq_zero_iff_of_nonneg (fun e _ => hr e)] at hrz
      funext e; exact hrz e (Finset.mem_univ _)
    subst hr'
    simp only [map_zero, add_zero] at hsum ⊢
    exact ⟨hp, hsum⟩
  · rintro ⟨hp, hsum⟩
    exact ⟨⟨x, hp, 0, le_refl _, by rw [add_zero]⟩, hsum⟩

include hJ in
/-- **Proposition 5.** Each of the four Steiner polyhedra of the radial instance has a face whose
marker coordinates form the minimum-cover face of `J`. -/
theorem xc_minCoverFace_le_steiner :
    xc (minCoverFace J) ≤ xc (Pmin S.radial S.terms) ∧
      xc (minCoverFace J) ≤ xc (Pconn S.radial S.terms) ∧
      xc (minCoverFace J) ≤ xc (Pup S.radial S.terms) ∧
      xc (minCoverFace J) ≤ xc (Dom S.radial S.terms) := by
  have hbase : xc (minCoverFace J) ≤ xc (S.doubleFace hJ) := by
    rw [← S.markRead_doubleFace hJ, ← LinearMap.coe_toAffineMap]
    exact xc_image_le _ _
  have hchain : ∀ X : Set (S.radial.edgeSet → ℝ),
      (X ∩ {x | sumOver Finset.univ x = (S.optPlusOne : ℝ) - 1}) ∩
        {x | S.markSum hJ x = (tau (J := J) : ℝ)} = S.doubleFace hJ →
      xc (minCoverFace J) ≤ xc X := by
    intro X hX
    refine hbase.trans ?_
    rw [← hX]
    exact (xc_inter_hyperplane_le _ _ _).trans (xc_inter_hyperplane_le _ _ _)
  have hmin := S.family_double_face hJ (IsMinConnector S.radial S.terms)
    (fun K hK => ⟨hK.1, hK.2.1⟩) (fun K hK => S.Fam0_isMinConnector hJ hK)
  refine ⟨hchain _ hmin, hchain _ ?_, hchain _ ?_, hchain _ ?_⟩
  · exact S.family_double_face hJ (IsConnectedSupport S.radial S.terms)
      (fun K hK => ⟨hK.1, fun a ha b hb => hK.2.2 a (hK.2.1 ha) b (hK.2.1 hb)⟩)
      (fun K hK => S.Fam0_isConnectedSupport hJ hK)
  · exact S.family_double_face hJ (fun K => K ≤ S.radial ∧ Connects K S.terms)
      (fun K hK => hK) (fun K hK => ⟨hK.1, hK.2.1⟩)
  · rw [S.dom_inter_eq hJ]
    exact hmin

end Markers

end PlanarFaces

end Lemmata.PlanarSteinerXC
