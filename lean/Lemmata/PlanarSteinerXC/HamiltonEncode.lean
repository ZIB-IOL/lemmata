module

public import Lemmata.PlanarSteinerXC.HamiltonDecode

/-!
# Theorem 6, encoding

Given a vertex cover `T` of `J`, take a spanning forest `K` of `H[R ∪ T]`. Colour red the
terminals, the vertices of `T`, and the edges of `H` that lie in `K` or have their optional end
outside `T`; colour everything else blue (in particular all faces of `H`). Every flag is
bichromatic, the red class is connected through `K`, and the blue class is connected because the
faces of `H` stay connected through the edges outside the forest `K`. Hence the cut of this
colouring is a Hamiltonian cycle of `Γ` through all forced edges, and its decoding coordinates
read `T`.
-/

@[expose] public section

set_option autoImplicit false

namespace Lemmata.PlanarSteinerXC

open SimpleGraph

namespace PlanarFaces

variable {V : Type*} [Fintype V] [DecidableEq V] {J : SimpleGraph V} [DecidableRel J.Adj]
  (S : PlanarFaces J) [Nonempty V] (hJ : ∀ v : V, ∃ w, J.Adj v w)

/-- The optional end of an edge of `H`. -/
def optEnd : J.Dart ⊕ S.Corner → V
  | .inl d => d.fst
  | .inr c => c.vert

/-- The terminal end of an edge of `H`. -/
def termEnd : J.Dart ⊕ S.Corner → J.edgeSet ⊕ S.Face
  | .inl d => .inl ⟨d.edge, d.edge_mem⟩
  | .inr c => .inr c.face

theorem hEdge_eq (a : J.Dart ⊕ S.Corner) : S.hEdge a = s(.inl (S.optEnd a), .inr (S.termEnd a)) := by
  rcases a with d | c <;> rfl

/-- A flag with given edge and given end vertex. -/
theorem exists_flag_vtx_edg (a : J.Dart ⊕ S.Corner) (term : Bool) :
    ∃ φ : S.Flag, S.edg φ = a ∧ φ.term = term ∧ φ.vert = S.optEnd a := by
  rcases a with d | c
  · obtain ⟨f, hf⟩ := S.exists_face_of_edge (J.mem_edgeSet.mpr d.adj)
    refine ⟨⟨f, d.edge, d.fst, term, false, hf, Sym2.mem_mk_left _ _⟩, ?_, rfl, rfl⟩
    exact (S.edg_eq_dart_iff _ d).mpr ⟨rfl, rfl, rfl⟩
  · obtain ⟨e, he, hue⟩ := c.vert_mem
    exact ⟨⟨c.face, e, c.vert, term, true, he, hue⟩, rfl, rfl, rfl⟩

theorem vtx_of_term_false {φ : S.Flag} (h : φ.term = false) : S.vtx φ = .inl φ.vert := by
  simp [vtx, h]

theorem vtx_of_edg_term {φ : S.Flag} {a : J.Dart ⊕ S.Corner} (ha : S.edg φ = a)
    (h : φ.term = true) : S.vtx φ = .inr (S.termEnd a) := by
  subst ha
  unfold vtx edg
  cases hs : φ.spoke <;> simp [h, hs, termEnd, Dart.edge, otherEnd_spec φ.vert_mem]

/-- A flag with a given edge on a given side, with its optional end as vertex. -/
theorem exists_flag_edg_fac {a : J.Dart ⊕ S.Corner} {σ : S.Side}
    (h : S.hEdge a ∈ S.sideEdges σ) :
    ∃ φ : S.Flag, S.edg φ = a ∧ S.fac φ = σ ∧ φ.term = false ∧ φ.vert = S.optEnd a := by
  rcases a with d | c
  · have hσ := (S.dart_mem_sideEdges_iff σ d).mp h
    have hu : d.fst ∈ σ.edge := by rw [hσ]; exact Sym2.mem_mk_left _ _
    refine ⟨⟨σ.face, σ.edge, d.fst, false, false, σ.edge_mem, hu⟩, ?_, rfl, rfl, rfl⟩
    exact (S.edg_eq_dart_iff _ d).mpr ⟨rfl, rfl, hσ⟩
  · obtain ⟨h1, h2⟩ := (S.corner_mem_sideEdges_iff σ c).mp h
    refine ⟨⟨σ.face, σ.edge, c.vert, false, true, σ.edge_mem, h2⟩, ?_, rfl, rfl, rfl⟩
    simp only [edg, ite_true, Sum.inr.injEq]
    cases c; simp_all

theorem optEnd_edg (φ : S.Flag) : S.optEnd (S.edg φ) = φ.vert := by
  unfold edg
  cases φ.spoke <;> rfl

theorem fac_mem_of_edg (φ : S.Flag) : S.hEdge (S.edg φ) ∈ S.sideEdges (S.fac φ) :=
  S.hEdge_edg_mem φ

/-- The colouring of the encoding. -/
noncomputable def encCol (T : Set V) (K : SimpleGraph S.RadV) : S.QE → ZMod 2 := fun q => by
  classical
  exact match q with
    | .inl (.inl v) => if v ∈ T then 1 else 0
    | .inl (.inr _) => 1
    | .inr (.inl a) => if S.hEdge a ∈ K.edgeSet ∨ S.optEnd a ∉ T then 1 else 0
    | .inr (.inr _) => 0

variable {S} in
theorem encCol_inl_inl (T : Set V) (K : SimpleGraph S.RadV) (v : V) :
    S.encCol T K (.inl (.inl v)) = 1 ↔ v ∈ T := by
  classical
  simp only [encCol]; split_ifs with h <;> simp [h]

variable {S} in
theorem encCol_inl_inl_zero (T : Set V) (K : SimpleGraph S.RadV) (v : V) :
    S.encCol T K (.inl (.inl v)) = 0 ↔ v ∉ T := by
  classical
  simp only [encCol]; split_ifs with h <;> simp [h]

variable {S} in
theorem encCol_term (T : Set V) (K : SimpleGraph S.RadV) (t : J.edgeSet ⊕ S.Face) :
    S.encCol T K (.inl (.inr t)) = 1 := by
  simp [encCol]

variable {S} in
theorem encCol_side (T : Set V) (K : SimpleGraph S.RadV) (σ : S.Side) :
    S.encCol T K (.inr (.inr σ)) = 0 := by
  simp [encCol]

variable {S} in
theorem encCol_edge (T : Set V) (K : SimpleGraph S.RadV) (a : J.Dart ⊕ S.Corner) :
    S.encCol T K (.inr (.inl a)) = 1 ↔ S.hEdge a ∈ K.edgeSet ∨ S.optEnd a ∉ T := by
  classical
  simp only [encCol]; split_ifs with h <;> simp [h]

variable {S} in
theorem encCol_edge_zero (T : Set V) (K : SimpleGraph S.RadV) (a : J.Dart ⊕ S.Corner) :
    S.encCol T K (.inr (.inl a)) = 0 ↔ ¬ (S.hEdge a ∈ K.edgeSet ∨ S.optEnd a ∉ T) := by
  classical
  simp only [encCol]; split_ifs with h <;> simp [h]

theorem encCol_vtx_term (T : Set V) (K : SimpleGraph S.RadV) {φ : S.Flag} (h : φ.term = true) :
    S.encCol T K (.inl (S.vtx φ)) = 1 := by
  unfold vtx
  cases hs : φ.spoke <;> simp [encCol, h, hs]

theorem encCol_vtx_not_term (T : Set V) (K : SimpleGraph S.RadV) {φ : S.Flag}
    (h : φ.term = false) : S.encCol T K (.inl (S.vtx φ)) = S.encCol T K (.inl (.inl φ.vert)) := by
  rw [S.vtx_of_term_false h]

variable (hlink : S.LinksConnected)

include hlink in
/-- **Encoding.** Every vertex cover of `J` is read by a Hamiltonian `s`-`t` path of `G'` through
all forced edges. -/
theorem encode {T : Set V} (hT : J.IsVertexCover T) :
    ∃ p : (S.G' hJ).Walk (S.sF hJ) (S.tF hJ), p.IsHamiltonian ∧
      (∀ ε ∈ S.forcedSet hJ, (ε : Sym2 S.Flag) ∈ (walkGraph p).edgeSet) ∧
      S.readDec hJ (edgeVec (S.G' hJ) (walkGraph p)) = vertexVec T := by
  classical
  set F := S.flagSystem hJ with hF
  have hfg : F.graph.Connected := S.fg_connected hJ hlink
  have heul := S.flag_euler
  -- a spanning forest of `H[R ∪ T]`
  set W := S.withOpt T with hW
  have hconnW := S.induce_connected_of_cover hJ hT
  let G₀ : SimpleGraph S.RadV :=
    { Adj := fun x y => S.radial.Adj x y ∧ x ∈ W ∧ y ∈ W
      symm := ⟨fun x y h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
      loopless := ⟨fun x h => S.radial.loopless.irrefl x h.1⟩ }
  obtain ⟨K, hKG₀, hKacyc, hKreach⟩ := G₀.exists_isAcyclic_reachable_eq_le
  have hKH : K ≤ S.radial := fun x y h => (hKG₀ h).1
  have hKconn : ∀ x ∈ W, ∀ y ∈ W, K.Reachable x y := by
    intro x hx y hy
    rw [hKreach]
    obtain ⟨q⟩ := hconnW.preconnected ⟨x, hx⟩ ⟨y, hy⟩
    let hom : S.radial.induce W →g G₀ := ⟨fun z => z.1, fun {a b} h => ⟨h, a.2, b.2⟩⟩
    exact ⟨q.map hom⟩
  set col := S.encCol T K with hcol
  have hside' : ∀ σ, col (.inr (.inr σ)) = 0 := fun σ => encCol_side T K σ
  have hterm' : ∀ t, col (.inl (.inr t)) = 1 := fun t => encCol_term T K t
  -- every flag is bichromatic
  have hbich : ∀ φ : S.Flag, col (.inl (S.vtx φ)) = 1 ∨ col (.inr (.inl (S.edg φ))) = 1 := by
    intro φ
    rw [hcol]
    cases h : φ.term
    · rw [S.encCol_vtx_not_term T K h]
      by_cases hv : φ.vert ∈ T
      · left; exact (encCol_inl_inl T K _).mpr hv
      · right
        rw [encCol_edge, S.optEnd_edg]
        exact Or.inr hv
    · left; exact S.encCol_vtx_term T K h
  -- the cut of the colouring as a spanning subgraph
  let D : SimpleGraph S.Flag :=
    { Adj := fun a b => F.graph.Adj a b ∧ F.cutVal col s(a, b) = 1
      symm := ⟨fun a b h => ⟨h.1.symm, by rw [Sym2.eq_swap]; exact h.2⟩⟩
      loopless := ⟨fun a h => F.graph.loopless.irrefl a h.1⟩ }
  have hDle : D ≤ F.graph := fun a b h => h.1
  have hDadj : ∀ φ i, D.Adj φ (F.tau i φ) ↔ F.cut col (F.edgeAt φ i) = 1 := by
    intro φ i
    exact ⟨fun h => h.2, fun h => ⟨F.adj_tau φ i, h⟩⟩
  have hzD : F.zvec D = F.cut col := by
    funext ε
    obtain ⟨φ, i, rfl⟩ := F.exists_edgeAt ε
    rcases FlagSystem.zmod2_cases (F.cut col (F.edgeAt φ i)) with h | h
    · rw [h, FlagSystem.zvec_eq_zero_iff]
      intro hm
      have := (hDadj φ i).mp hm
      rw [h] at this; exact zero_ne_one this
    · rw [h, FlagSystem.zvec_eq_one_iff]
      exact (hDadj φ i).mpr h
  have hreg : F.TwoRegular D := by
    refine ⟨hDle, fun φ => ?_⟩
    obtain ⟨h0, h1, h2⟩ := F.cut_edgeAt col φ
    have hs : col (.inr (.inr (F.fac φ))) = 0 := encCol_side T K _
    rw [hs, add_zero] at h0 h1
    simp only [hDadj]
    rw [Set.ncard_eq_toFinset_card', Set.toFinset_ofPred, Finset.card_filter, Fin.sum_univ_three]
    rw [h0, h1, h2]
    have hb : col (.inl (F.vtx φ)) = 1 ∨ col (.inr (.inl (F.edg φ))) = 1 := hbich φ
    rcases hb with hv | he
    · rcases FlagSystem.zmod2_cases (col (.inr (.inl (F.edg φ)))) with he | he
      · rw [hv, he]; decide
      · rw [hv, he]; decide
    · rcases FlagSystem.zmod2_cases (col (.inl (F.vtx φ))) with hv | hv
      · rw [hv, he]; decide
      · rw [hv, he]; decide
  -- monochromatic connectivity
  let R : S.QE → S.QE → Prop := fun p q => F.QAdj p q ∧ col p = col q
  have hRsymm : Symmetric R := fun a b h => ⟨by obtain ⟨φ, ha, hb⟩ := h.1; exact ⟨φ, hb, ha⟩,
    h.2.symm⟩
  have hsymm : ∀ a b, Relation.ReflTransGen R a b → Relation.ReflTransGen R b a := by
    intro a b h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hbc ih => exact (Relation.ReflTransGen.single (hRsymm hbc)).trans ih
  have hstep : ∀ (φ : S.Flag) (a b : S.QE), a ∈ F.elts φ → b ∈ F.elts φ → col a = col b →
      Relation.ReflTransGen R a b :=
    fun φ a b ha hb hab => Relation.ReflTransGen.single ⟨⟨φ, ha, hb⟩, hab⟩
  have hvm : ∀ φ : S.Flag, (.inl (S.vtx φ) : S.QE) ∈ F.elts φ :=
    fun φ => (S.mem_elts hJ φ _).mpr (Or.inl rfl)
  have hem : ∀ φ : S.Flag, (.inr (.inl (S.edg φ)) : S.QE) ∈ F.elts φ :=
    fun φ => (S.mem_elts hJ φ _).mpr (Or.inr (Or.inl rfl))
  have hfm : ∀ φ : S.Flag, (.inr (.inr (S.fac φ)) : S.QE) ∈ F.elts φ :=
    fun φ => (S.mem_elts hJ φ _).mpr (Or.inr (Or.inr rfl))
  have hcolW : ∀ x ∈ W, col (.inl x) = 1 := by
    rintro (v | t) hx
    · exact (encCol_inl_inl T K v).mpr (S.inl_mem_withOpt.mp hx)
    · exact encCol_term T K t
  -- an edge of `H` joins its ends through red elements when it is red
  have hedgeTerm : ∀ a, col (.inr (.inl a)) = 1 →
      Relation.ReflTransGen R (.inr (.inl a)) (.inl (.inr (S.termEnd a))) := by
    intro a ha
    obtain ⟨φ, hφa, hφt, -⟩ := S.exists_flag_vtx_edg a true
    have hv : S.vtx φ = .inr (S.termEnd a) := S.vtx_of_edg_term hφa hφt
    have h1 := hem φ; rw [hφa] at h1
    have h2 := hvm φ; rw [hv] at h2
    exact hstep φ _ _ h1 h2 (ha.trans (encCol_term T K _).symm)
  have hedgeOpt : ∀ a, col (.inr (.inl a)) = col (.inl (.inl (S.optEnd a))) →
      Relation.ReflTransGen R (.inr (.inl a)) (.inl (.inl (S.optEnd a))) := by
    intro a ha
    obtain ⟨φ, hφa, hφt, hφv⟩ := S.exists_flag_vtx_edg a false
    have hv : S.vtx φ = .inl (S.optEnd a) := by rw [S.vtx_of_term_false hφt, hφv]
    have h1 := hem φ; rw [hφa] at h1
    have h2 := hvm φ; rw [hv] at h2
    exact hstep φ _ _ h1 h2 ha
  -- red hub
  set f₀ := S.markFace hJ (Classical.arbitrary V)
  let r₀ : S.QE := .inl (.inr (.inr f₀))
  have hKwalk : ∀ (y z : S.RadV) (q : K.Walk y z), y ∈ W →
      Relation.ReflTransGen R (.inl y) (.inl z) := by
    intro y z q
    induction q with
    | nil => intro _; exact Relation.ReflTransGen.refl
    | @cons y y' z hyy' q ih =>
      intro hy
      have hy' : y' ∈ W := (hKG₀ hyy').2.2
      refine Relation.ReflTransGen.trans ?_ (ih hy')
      obtain ⟨a, ha⟩ := S.hEdge_surj (S.radial.mem_edgeSet.mpr (hKH hyy'))
      have hared : col (.inr (.inl a)) = 1 := by
        rw [encCol_edge]; left; rw [ha]; exact hyy'
      have hends := S.hEdge_eq a
      rw [ha] at hends
      have hoW : (.inl (S.optEnd a) : S.RadV) ∈ W ∨ True := Or.inr trivial
      have hc1 := hedgeTerm a hared
      rcases Sym2.eq_iff.mp hends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have hc2 := hedgeOpt a (hared.trans (hcolW _ hy).symm)
        exact (hsymm _ _ hc2).trans hc1
      · have hc2 := hedgeOpt a (hared.trans (hcolW _ hy').symm)
        exact (hsymm _ _ hc1).trans hc2
  have hR1 : ∀ x ∈ W, Relation.ReflTransGen R (.inl x) r₀ := by
    intro x hx
    obtain ⟨q⟩ := hKconn x hx _ (S.inr_mem_withOpt T (.inr f₀))
    exact hKwalk _ _ q hx
  have hR2 : ∀ a, col (.inr (.inl a)) = 1 → Relation.ReflTransGen R (.inr (.inl a)) r₀ :=
    fun a ha => (hedgeTerm a ha).trans (hR1 _ (S.inr_mem_withOpt T _))
  -- blue hub
  let σ₀ := S.fac (S.rootFlag hJ)
  let b₀ : S.QE := .inr (.inr σ₀)
  have hB3 : ∀ σ, Relation.ReflTransGen R (.inr (.inr σ)) b₀ := by
    intro σ
    have hfc := (S.radialFaces hJ hlink).faces_connected_avoiding (K := K) hKH hKacyc σ σ₀
    have key : ∀ σ', Relation.ReflTransGen ((S.radialFaces hJ hlink).AdjAvoid K) σ σ' →
        Relation.ReflTransGen R (.inr (.inr σ)) (.inr (.inr σ')) := by
      intro σ' h
      induction h with
      | refl => exact Relation.ReflTransGen.refl
      | @tail σ₁ σ₂ _ hadj ih =>
        refine ih.trans ?_
        obtain ⟨ε, h1, h2, hεK⟩ := hadj
        change ε ∈ S.sideEdges σ₁ at h1
        change ε ∈ S.sideEdges σ₂ at h2
        obtain ⟨a, rfl⟩ := S.hEdge_surj (S.sideEdges_subset σ₁ _ h1)
        obtain ⟨φ₁, hφ₁a, hφ₁σ, hφ₁t, hφ₁v⟩ := S.exists_flag_edg_fac h1
        obtain ⟨φ₂, hφ₂a, hφ₂σ, hφ₂t, hφ₂v⟩ := S.exists_flag_edg_fac h2
        have hf1 := hfm φ₁; rw [hφ₁σ] at hf1
        have hf2 := hfm φ₂; rw [hφ₂σ] at hf2
        rcases FlagSystem.zmod2_cases (col (.inr (.inl a))) with ha | ha
        · have he1 := hem φ₁; rw [hφ₁a] at he1
          have he2 := hem φ₂; rw [hφ₂a] at he2
          exact (hstep φ₁ _ _ hf1 he1 ((encCol_side T K _).trans ha.symm)).trans
            (hstep φ₂ _ _ he2 hf2 (ha.trans (encCol_side T K _).symm))
        · have hopt : S.optEnd a ∉ T := by
            have := (encCol_edge T K a).mp ha
            rcases this with h | h
            · exact absurd h hεK
            · exact h
          have hcol0 : col (.inl (.inl (S.optEnd a))) = 0 := (encCol_inl_inl_zero T K _).mpr hopt
          have hv1 := hvm φ₁; rw [S.vtx_of_term_false hφ₁t, hφ₁v] at hv1
          have hv2 := hvm φ₂; rw [S.vtx_of_term_false hφ₂t, hφ₂v] at hv2
          exact (hstep φ₁ _ _ hf1 hv1 ((encCol_side T K _).trans hcol0.symm)).trans
            (hstep φ₂ _ _ hv2 hf2 (hcol0.trans (encCol_side T K _).symm))
    exact key σ₀ hfc
  have hB1 : ∀ v, v ∉ T → Relation.ReflTransGen R (.inl (.inl v)) b₀ := by
    intro v hv
    set ψ := S.decFlag hJ v
    have hvt : S.vtx ψ = .inl v := rfl
    have h1 := hvm ψ; rw [hvt] at h1
    exact (hstep ψ _ _ h1 (hfm ψ) (((encCol_inl_inl_zero T K v).mpr hv).trans
      (encCol_side T K _).symm)).trans (hB3 _)
  have hB2 : ∀ a, col (.inr (.inl a)) = 0 → Relation.ReflTransGen R (.inr (.inl a)) b₀ := by
    intro a ha
    obtain ⟨φ, hφa, -, -⟩ := S.exists_flag_vtx_edg a false
    have h1 := hem φ; rw [hφa] at h1
    exact (hstep φ _ _ h1 (hfm φ) (ha.trans (encCol_side T K _).symm)).trans (hB3 _)
  have hred : ∀ q, col q = 1 → Relation.ReflTransGen R q r₀ := by
    rintro ((v | t) | (a | σ)) hq
    · exact hR1 _ (S.inl_mem_withOpt.mpr ((encCol_inl_inl T K v).mp hq))
    · exact hR1 _ (S.inr_mem_withOpt T t)
    · exact hR2 a hq
    · rw [hside'] at hq; exact absurd hq zero_ne_one
  have hblue : ∀ q, col q = 0 → Relation.ReflTransGen R q b₀ := by
    rintro ((v | t) | (a | σ)) hq
    · exact hB1 v ((encCol_inl_inl_zero T K v).mp hq)
    · rw [hterm'] at hq; exact absurd hq one_ne_zero
    · exact hB2 a hq
    · exact hB3 σ
  have hmono : F.MonoConnected col := by
    intro a b hab
    rcases FlagSystem.zmod2_cases (col a) with h | h
    · exact (hblue a h).trans (hsymm _ _ (hblue b (hab ▸ h)))
    · exact (hred a h).trans (hsymm _ _ (hred b (hab ▸ h)))
  -- the cut is connected
  have hmin : ∀ z, F.IsEven z → (∀ ε, z ε ≠ 0 → (ε : Sym2 S.Flag) ∈ D.edgeSet) →
      z = 0 ∨ z = F.zvec D := by
    intro z hz hsub
    rw [hzD]
    apply F.even_sub_cut hfg heul col hmono z hz
    intro ε hε
    by_contra hne
    have h1 : F.zvec D ε = 1 := (F.zvec_eq_one_iff D ε).mpr (hsub ε hne)
    rw [hzD, hε] at h1
    exact zero_ne_one h1
  haveI : Nonempty S.Flag := ⟨S.rootFlag hJ⟩
  have hDconn := F.connected_of_minimal hreg hmin
  have hforcedcut : ∀ φ : S.Flag, φ.term = true → D.Adj φ (S.t1 φ) := by
    intro φ hφ
    refine ⟨S.fg_adj_t1 hJ φ, ?_⟩
    have := F.cutVal_τ1 col φ
    change F.cutVal col s(φ, S.t1 φ) = _ at this
    rw [this, hside', add_zero]
    exact S.encCol_vtx_term T K hφ
  have hstD : D.Adj (S.sF hJ) (S.tF hJ) := hforcedcut _ (S.rootFlag_term hJ)
  obtain ⟨p, hp, hpD⟩ := F.exists_hamiltonian_path hreg hDconn hstD
  have hpedge : ∀ ε, ε ∈ (walkGraph p).edgeSet ↔ ε ∈ D.edgeSet ∧ ε ≠ s(S.sF hJ, S.tF hJ) := by
    intro ε
    rw [hpD, edgeSet_deleteEdges]; simp
  refine ⟨p, hp, ?_, ?_⟩
  · rintro ⟨ε, hεmem⟩ hε
    simp only [forcedSet, Finset.mem_filter, Finset.mem_univ, true_and] at hε
    obtain ⟨φ, hφ, hεφ⟩ := hε
    change ε ∈ (walkGraph p).edgeSet
    rw [hpedge, hεφ]
    refine ⟨hforcedcut φ hφ, ?_⟩
    rw [edgeSet_deleteEdges, hεφ] at hεmem
    exact hεmem.2
  · funext v
    rw [readDec, LinearMap.funLeft_apply, edgeVec_apply, vertexVec_apply]
    set ψ := S.decFlag hJ v with hψ
    have hdecval : (S.decEdge hJ v : Sym2 S.Flag) = s(ψ, S.t1 ψ) := rfl
    have hne0 : s(ψ, S.t1 ψ) ≠ s(S.sF hJ, S.tF hJ) := by
      have := (S.decEdge hJ v).2
      rw [hdecval, edgeSet_deleteEdges] at this
      exact this.2
    have hval : s(ψ, S.t1 ψ) ∈ (walkGraph p).edgeSet ↔ v ∈ T := by
      rw [hpedge]
      simp only [hne0, ne_eq, not_false_eq_true, and_true, mem_edgeSet]
      constructor
      · intro h
        have := h.2
        have hc := F.cutVal_τ1 col ψ
        change F.cutVal col s(ψ, S.t1 ψ) = _ at hc
        rw [hc, hside', add_zero] at this
        have hvt : F.vtx ψ = .inl v := rfl
        rw [hvt] at this
        exact (encCol_inl_inl T K v).mp this
      · intro hv
        refine ⟨S.fg_adj_t1 hJ ψ, ?_⟩
        have hc := F.cutVal_τ1 col ψ
        change F.cutVal col s(ψ, S.t1 ψ) = _ at hc
        rw [hc, hside', add_zero]
        exact (encCol_inl_inl T K v).mpr hv
    rw [hdecval]
    by_cases hv : v ∈ T
    · simp only [hval.mpr hv, hv, ite_true]
    · simp only [hv, ite_false, (not_congr hval).mpr hv]

/-- The forced-edge count of an edge set is at most the number of forced edges, with equality
exactly when all forced edges are present. -/
theorem forced_sum_le (K : SimpleGraph S.Flag) :
    sumOver (S.forcedSet hJ) (edgeVec (S.G' hJ) K) ≤ ((S.forcedSet hJ).card : ℝ) := by
  rw [sumOver_apply, Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
  exact Finset.sum_le_sum fun ε _ => edgeVec_le_one _ _ ε

theorem forced_sum_eq_iff (K : SimpleGraph S.Flag) :
    sumOver (S.forcedSet hJ) (edgeVec (S.G' hJ) K) = ((S.forcedSet hJ).card : ℝ) ↔
      ∀ ε ∈ S.forcedSet hJ, (ε : Sym2 S.Flag) ∈ K.edgeSet := by
  rw [sumOver_apply, Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
  constructor
  · intro h ε hε
    have h0 : ∑ ε ∈ S.forcedSet hJ, (1 - edgeVec (S.G' hJ) K ε) = 0 := by
      rw [Finset.sum_sub_distrib, h, sub_self]
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun ε _ => sub_nonneg.mpr
      (edgeVec_le_one _ _ ε))).mp h0 ε hε
    rw [← edgeVec_eq_one_iff]
    linarith
  · intro h
    apply Finset.sum_congr rfl
    intro ε hε
    exact (edgeVec_eq_one_iff _ _ _).mpr (h ε hε)

include hlink in
/-- **Theorem 6.** The decoding coordinates map the forced-edge face of the Hamiltonian path
polytope of `G'` onto the vertex cover polytope of `J`. -/
theorem readDec_hpFace : S.readDec hJ '' S.hpFace hJ = VC J := by
  classical
  unfold hpFace HP VC
  rw [convexHull_inter_hyperplane_of_le (sumOver (S.forcedSet hJ)) _
    (by rintro x ⟨K, -, rfl⟩; exact S.forced_sum_le hJ K)]
  rw [← LinearMap.coe_toAffineMap, image_convexHull_eq]
  congr 1
  ext y
  simp only [Set.mem_image, Set.mem_inter_iff, Set.mem_ofPred_eq, LinearMap.coe_toAffineMap]
  constructor
  · rintro ⟨_, ⟨⟨K, ⟨p, hp, rfl⟩, rfl⟩, hsum⟩, rfl⟩
    obtain ⟨T, hT, hTeq⟩ := S.decode hJ hlink p hp ((S.forced_sum_eq_iff hJ _).mp hsum)
    exact ⟨T, hT, hTeq.symm⟩
  · rintro ⟨T, hT, rfl⟩
    obtain ⟨p, hp, hforced, hread⟩ := S.encode hJ hlink hT
    exact ⟨_, ⟨⟨_, ⟨p, hp, rfl⟩, rfl⟩, (S.forced_sum_eq_iff hJ _).mpr hforced⟩, hread⟩

include hlink in
/-- Consequently `xc (VC J) ≤ xc (HP G' s t)`. -/
theorem xc_VC_le_HP : xc (VC J) ≤ xc (HP (S.G' hJ) (S.sF hJ) (S.tF hJ)) := by
  rw [← S.readDec_hpFace hJ hlink, ← LinearMap.coe_toAffineMap]
  exact (xc_image_le _ _).trans (xc_inter_hyperplane_le _ _ _)

include hlink in
/-- And `xc (VC J) ≤ xc (Pmin G' {s, t})`. -/
theorem xc_VC_le_Pmin : xc (VC J) ≤ xc (Pmin (S.G' hJ) {S.sF hJ, S.tF hJ}) := by
  classical
  exact (S.xc_VC_le_HP hJ hlink).trans (xc_hp_le_pmin _ _ _)

end PlanarFaces

end Lemmata.PlanarSteinerXC
