module

public import Lemmata.PlanarSteinerXC.RadialFaces

/-!
# The Hamiltonian path face: setup and decoding

`Γ` is the flag graph of the radial graph `H` (the dual `Q*` of its barycentric subdivision).
The *forced* edges of `Γ` are those dual to the edges `t b_ψ` of `Q` joining a terminal `t` of `H`
to the centre of a face `ψ` of `H` containing it. We delete one forced edge `st` and obtain `G'`.
For an optional vertex `v`, the *decoding coordinate* is the edge of `Γ` dual to `v b_ψ` for a
fixed face `ψ ∋ v`.

**Decoding.** Every Hamiltonian `s`-`t` path of `G'` through all forced edges, closed by `st`,
is a Hamiltonian cycle of `Γ`; by duality it is the cut of a colouring of `Q` whose colour classes
are connected. All terminals get one colour and all face centres the other; the optional vertices
coloured like the terminals form a vertex cover of `J`, and the decoding coordinates read exactly
this cover.
-/

@[expose] public section

set_option autoImplicit false

namespace Lemmata.PlanarSteinerXC

open SimpleGraph

namespace PlanarFaces

variable {V : Type*} [Fintype V] [DecidableEq V] {J : SimpleGraph V} [DecidableRel J.Adj]
  (S : PlanarFaces J) [Nonempty V] (hJ : ∀ v : V, ∃ w, J.Adj v w)

/-- The colouring space: vertices, edges and faces of `H`. -/
abbrev QE := S.RadV ⊕ (J.Dart ⊕ S.Corner) ⊕ S.Side

/-- The root flag: a flag whose vertex is a terminal. -/
noncomputable def rootFlag : S.Flag :=
  ⟨S.markFace hJ (Classical.arbitrary V), (Classical.choose (S.mem_verts_markFace hJ
    (Classical.arbitrary V))), Classical.arbitrary V, true, false,
    (Classical.choose_spec (S.mem_verts_markFace hJ (Classical.arbitrary V))).1,
    (Classical.choose_spec (S.mem_verts_markFace hJ (Classical.arbitrary V))).2⟩

theorem rootFlag_term : (S.rootFlag hJ).term = true := rfl

/-- The two ends of the deleted forced edge. -/
noncomputable def sF : S.Flag := S.rootFlag hJ
noncomputable def tF : S.Flag := S.t1 (S.rootFlag hJ)

theorem sF_tF_adj : (S.fg hJ).Adj (S.sF hJ) (S.tF hJ) := S.fg_adj_t1 hJ _

/-- The graph `G' = Γ - st`. -/
noncomputable abbrev G' : SimpleGraph S.Flag := (S.flagSystem hJ).minus (S.sF hJ) (S.tF hJ)

/-- The forced edges of `Γ`. -/
def IsForced (ε : Sym2 S.Flag) : Prop := ∃ φ : S.Flag, φ.term = true ∧ ε = s(φ, S.t1 φ)

/-- The forced edges of `G'`. -/
noncomputable def forcedSet : Finset (S.G' hJ).edgeSet := by
  classical exact Finset.univ.filter fun ε => S.IsForced (ε : Sym2 S.Flag)

/-- The flag used to read an optional vertex. -/
noncomputable def decFlag (v : V) : S.Flag :=
  ⟨S.markFace hJ v, Classical.choose (S.mem_verts_markFace hJ v), v, false, false,
    (Classical.choose_spec (S.mem_verts_markFace hJ v)).1,
    (Classical.choose_spec (S.mem_verts_markFace hJ v)).2⟩

theorem decFlag_term (v : V) : (S.decFlag hJ v).term = false := rfl

theorem ne_of_term {φ ψ : S.Flag} (h : φ.term ≠ ψ.term) : φ ≠ ψ := fun h' => h (by rw [h'])

theorem decEdge_mem (v : V) :
    s(S.decFlag hJ v, S.t1 (S.decFlag hJ v)) ∈ (S.G' hJ).edgeSet := by
  rw [edgeSet_deleteEdges]
  refine ⟨S.fg_adj_t1 hJ _, ?_⟩
  simp only [Set.mem_singleton_iff, Sym2.eq_iff]
  rintro (⟨h1, -⟩ | ⟨h1, -⟩)
  · have := congrArg Flag.term h1
    simp [decFlag, sF, rootFlag] at this
  · have := congrArg Flag.term h1
    simp [decFlag, tF, rootFlag] at this

/-- The decoding coordinate of an optional vertex. -/
noncomputable def decEdge (v : V) : (S.G' hJ).edgeSet :=
  ⟨s(S.decFlag hJ v, S.t1 (S.decFlag hJ v)), S.decEdge_mem hJ v⟩

/-- Reading the decoding coordinates. -/
noncomputable def readDec : ((S.G' hJ).edgeSet → ℝ) →ₗ[ℝ] (V → ℝ) :=
  LinearMap.funLeft ℝ ℝ (S.decEdge hJ)

/-- The face of the Hamiltonian path polytope cut out by the forced edges. -/
noncomputable def hpFace : Set ((S.G' hJ).edgeSet → ℝ) :=
  HP (S.G' hJ) (S.sF hJ) (S.tF hJ) ∩
    {x | sumOver (S.forcedSet hJ) x = ((S.forcedSet hJ).card : ℝ)}

/-! ### Colourings -/

theorem elts_def (φ : S.Flag) :
    (S.flagSystem hJ).elts φ = {.inl (S.vtx φ), .inr (.inl (S.edg φ)), .inr (.inr (S.fac φ))} :=
  rfl

theorem cut_edgeAt_one (x : S.QE → ZMod 2) (φ : S.Flag) :
    (S.flagSystem hJ).cut x ((S.flagSystem hJ).edgeAt φ 1) =
      x (.inl (S.vtx φ)) + x (.inr (.inr (S.fac φ))) :=
  ((S.flagSystem hJ).cut_edgeAt x φ).2.1

/-- The edges `s(φ, t₁ φ)` of `Γ`. -/
theorem edgeAt_one_val (φ : S.Flag) :
    (((S.flagSystem hJ).edgeAt φ 1 : (S.fg hJ).edgeSet) : Sym2 S.Flag) = s(φ, S.t1 φ) := rfl

/-! ### Identifying flags from their corners -/

theorem vtx_eq_edge_iff (φ : S.Flag) (e : J.edgeSet) :
    S.vtx φ = .inr (.inl e) ↔ φ.term = true ∧ φ.spoke = false ∧ φ.edge = e.1 := by
  unfold vtx
  cases h1 : φ.term <;> cases h2 : φ.spoke <;> simp only [ite_true, ite_false, Bool.false_eq_true,
    reduceCtorEq, false_and, and_false, Sum.inr.injEq, Sum.inl.injEq, true_and, and_true]
  · constructor
    · intro h; rw [← h]
    · intro h; exact Subtype.ext h

theorem vtx_eq_inl_iff (φ : S.Flag) (v : V) : S.vtx φ = .inl v ↔ φ.term = false ∧ φ.vert = v := by
  unfold vtx
  cases h1 : φ.term <;> cases h2 : φ.spoke <;> simp

theorem edg_eq_dart_iff (φ : S.Flag) (d : J.Dart) :
    S.edg φ = .inl d ↔ φ.spoke = false ∧ φ.vert = d.fst ∧ φ.edge = d.edge := by
  obtain ⟨⟨a, b⟩, hab⟩ := d
  unfold edg
  cases h2 : φ.spoke
  · simp only [Bool.false_eq_true, ite_false, Sum.inl.injEq, true_and]
    constructor
    · intro h
      have h1 := congrArg (fun d : J.Dart => d.toProd) h
      simp only [Prod.mk.injEq] at h1
      obtain ⟨rfl, rfl⟩ := h1
      exact ⟨rfl, (otherEnd_spec φ.vert_mem).symm⟩
    · rintro ⟨h1, h2'⟩
      ext
      · exact h1
      · show otherEnd φ.vert φ.edge = b
        rw [h1, h2']; exact otherEnd_mk a b
  · simp

theorem mem_elts (φ : S.Flag) (q : S.QE) :
    q ∈ (S.flagSystem hJ).elts φ ↔
      q = .inl (S.vtx φ) ∨ q = .inr (.inl (S.edg φ)) ∨ q = .inr (.inr (S.fac φ)) := by
  rw [elts_def]; simp

theorem zmod2_eq_add_one {a b : ZMod 2} (h : a + b = 1) : b = a + 1 := by
  rcases FlagSystem.zmod2_cases a with rfl | rfl <;> rcases FlagSystem.zmod2_cases b with rfl | rfl <;> simp_all <;>
    decide

theorem zmod2_ne_add_one (a : ZMod 2) : a ≠ a + 1 := by
  rcases FlagSystem.zmod2_cases a with rfl | rfl <;> decide

/-! ### Decoding -/

variable (hlink : S.LinksConnected)

include hlink in
/-- **Decoding.** A Hamiltonian `s`-`t` path of `G'` through all forced edges reads a vertex
cover of `J` in its decoding coordinates. -/
theorem decode (p : (S.G' hJ).Walk (S.sF hJ) (S.tF hJ)) (hp : p.IsHamiltonian)
    (hforced : ∀ ε ∈ S.forcedSet hJ, (ε : Sym2 S.Flag) ∈ (walkGraph p).edgeSet) :
    ∃ T : Set V, J.IsVertexCover T ∧
      S.readDec hJ (edgeVec (S.G' hJ) (walkGraph p)) = vertexVec T := by
  classical
  set F := S.flagSystem hJ with hF
  have hfg : F.graph.Connected := S.fg_connected hJ hlink
  have heul := S.flag_euler
  obtain ⟨hreg, hDconn⟩ := F.twoRegular_of_hamiltonian_path (S.sF_tF_adj hJ) p hp
  set D := walkGraph p ⊔ edge (S.sF hJ) (S.tF hJ) with hD
  have hst_ne : S.sF hJ ≠ S.tF hJ := (S.sF_tF_adj hJ).ne
  have hstD : s(S.sF hJ, S.tF hJ) ∈ D.edgeSet := by
    rw [hD, edgeSet_sup, edgeSet_edge_of_ne hst_ne]; exact Or.inr rfl
  have heven := F.zvec_isEven hreg
  obtain ⟨x, hx⟩ := F.even_eq_cut hfg heul (F.zvec D) heven
  have hmin : ∀ z, F.IsEven z → (∀ ε, F.cut x ε = 0 → z ε = 0) → z = 0 ∨ z = F.cut x := by
    intro z hz hsub
    rw [← hx]
    apply F.even_sub_of_connected hreg hDconn z hz
    intro ε hε
    by_contra hnot
    have h0 : F.zvec D ε = 0 := (F.zvec_eq_zero_iff D ε).mpr hnot
    rw [hx] at h0
    exact hε (hsub ε h0)
  have hne : F.cut x ≠ 0 := by
    rw [← hx]; intro h
    have := congrFun h (F.edgeAt (S.sF hJ) 1)
    rw [Pi.zero_apply, FlagSystem.zvec_eq_zero_iff] at this
    exact this hstD
  have hmono := F.monoConnected_of_minimal hfg x hne hmin
  -- forced edges lie on the cycle
  have hforcedD : ∀ φ : S.Flag, φ.term = true → s(φ, S.t1 φ) ∈ D.edgeSet := by
    intro φ hφ
    by_cases h0 : s(φ, S.t1 φ) = s(S.sF hJ, S.tF hJ)
    · rw [h0]; exact hstD
    · have hmem : s(φ, S.t1 φ) ∈ (S.G' hJ).edgeSet := by
        rw [edgeSet_deleteEdges]; exact ⟨S.fg_adj_t1 hJ φ, h0⟩
      have hin : (⟨_, hmem⟩ : (S.G' hJ).edgeSet) ∈ S.forcedSet hJ := by
        simp only [forcedSet, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨φ, hφ, rfl⟩
      have := hforced _ hin
      rw [hD, edgeSet_sup]; exact Or.inl this
  have hterm : ∀ φ : S.Flag, φ.term = true →
      x (.inl (S.vtx φ)) + x (.inr (.inr (S.fac φ))) = 1 := by
    intro φ hφ
    have h1 : F.zvec D (F.edgeAt φ 1) = 1 := (F.zvec_eq_one_iff _ _).mpr (hforcedD φ hφ)
    rw [hx, S.cut_edgeAt_one] at h1
    exact h1
  -- colours of the face terminals, the sides and the edge terminals
  let g : S.Face → ZMod 2 := fun f => x (.inl (.inr (.inr f)))
  have hside : ∀ σ : S.Side, x (.inr (.inr σ)) = g σ.face + 1 := by
    intro σ
    obtain ⟨u, hu⟩ := exists_mem_sym2 σ.edge
    have := hterm ⟨σ.face, σ.edge, u, true, true, σ.edge_mem, hu⟩ rfl
    exact zmod2_eq_add_one this
  have hqe : ∀ σ : S.Side,
      x (.inl (.inr (.inl ⟨σ.edge, S.mem_edgeSet_of_mem σ.edge_mem⟩))) = g σ.face := by
    intro σ
    obtain ⟨u, hu⟩ := exists_mem_sym2 σ.edge
    have h1 := hterm ⟨σ.face, σ.edge, u, true, false, σ.edge_mem, hu⟩ rfl
    have h2 := hside σ
    simp only [vtx, fac, ite_true, Bool.false_eq_true, ite_false] at h1
    rw [h2] at h1
    have := zmod2_eq_add_one h1
    rw [eq_comm, ← sub_eq_zero] at this
    have h3 : x (.inl (.inr (.inl ⟨σ.edge, S.mem_edgeSet_of_mem σ.edge_mem⟩))) + 1 =
        g σ.face + 1 := by
      have := zmod2_eq_add_one (by rw [add_comm] at h1 ⊢; exact h1)
      exact this.symm
    exact add_right_cancel h3
  have hg : ∀ f f', g f = g f' := by
    intro f f'
    obtain ⟨q⟩ := S.dual_conn.preconnected f f'
    induction q with
    | nil => rfl
    | @cons a b c hab q ih =>
      refine Eq.trans ?_ ih
      rw [dual, fromRel_adj] at hab
      obtain ⟨-, hab⟩ := hab
      obtain ⟨e, hea, heb⟩ : ∃ e, e ∈ S.edges a ∧ e ∈ S.edges b := by
        rcases hab with ⟨e, h1, h2⟩ | ⟨e, h1, h2⟩
        · exact ⟨e, h1, h2⟩
        · exact ⟨e, h2, h1⟩
      have h1 := hqe ⟨a, e, hea⟩
      have h2 := hqe ⟨b, e, heb⟩
      exact h1.symm.trans h2
  -- the colour `c` of all terminals
  set c := g (S.markFace hJ (Classical.arbitrary V)) with hc
  have hgc : ∀ f, g f = c := fun f => hg f _
  have hsidec : ∀ σ : S.Side, x (.inr (.inr σ)) = c + 1 := fun σ => by rw [hside, hgc]
  have hqec : ∀ (e : J.edgeSet), x (.inl (.inr (.inl e))) = c := by
    intro e
    obtain ⟨f, hf⟩ := S.exists_face_of_edge e.2
    have := hqe ⟨f, e.1, hf⟩
    rw [hgc] at this
    exact this
  refine ⟨{v | x (.inl (.inl v)) = c}, ?_, ?_⟩
  · -- the optional vertices of colour `c` form a vertex cover
    intro u w huw
    by_contra hcon
    simp only [Set.mem_ofPred_eq, not_or] at hcon
    obtain ⟨hu, hw⟩ := hcon
    set e : J.edgeSet := ⟨s(u, w), J.mem_edgeSet.mpr huw⟩ with he
    let d1 : J.Dart := ⟨(u, w), huw⟩
    let d2 : J.Dart := ⟨(w, u), huw.symm⟩
    let Comp : Set S.QE := {.inl (.inr (.inl e)), .inr (.inl (.inl d1)), .inr (.inl (.inl d2))}
    let r₀ : S.QE := .inl (.inr (.inr (S.markFace hJ (Classical.arbitrary V))))
    have hr₀ : x r₀ = c := rfl
    have hchain := hmono (.inl (.inr (.inl e))) r₀ ((hqec e).trans hr₀.symm)
    have hinv : ∀ r ∈ Comp, x r = c → ∀ r', F.QAdj r r' → x r = x r' → r' ∈ Comp := by
      intro r hr hrc r' hadj hxr
      obtain ⟨φ, hrφ, hr'φ⟩ := hadj
      rw [S.mem_elts] at hrφ hr'φ
      -- the side of `φ` has the other colour
      have hnotside : r' ≠ .inr (.inr (S.fac φ)) := by
        intro h; rw [h, hsidec] at hxr; rw [hrc] at hxr; exact zmod2_ne_add_one c hxr
      simp only [Comp, Set.mem_insert_iff, Set.mem_singleton_iff] at hr ⊢
      rcases hr with rfl | rfl | rfl
      · -- `r` is the edge terminal `q_e`
        have hv : S.vtx φ = .inr (.inl e) := by
          rcases hrφ with h | h | h
          · exact (Sum.inl.inj h).symm
          · exact absurd h (by simp)
          · exact absurd h (by simp)
        obtain ⟨-, hsp, hedge⟩ := (S.vtx_eq_edge_iff φ e).mp hv
        rcases hr'φ with rfl | rfl | rfl
        · left; rw [hv]
        · right
          have hvm := φ.vert_mem
          rw [hedge, he, Sym2.mem_iff] at hvm
          rcases hvm with hvu | hvw
          · left
            rw [(S.edg_eq_dart_iff φ d1).mpr ⟨hsp, hvu, by rw [hedge]; rfl⟩]
          · right
            rw [(S.edg_eq_dart_iff φ d2).mpr ⟨hsp, hvw, by rw [hedge, he]; exact Sym2.eq_swap⟩]
        · exact absurd rfl hnotside
      · -- `r` is the dart `u → w`
        have hd : S.edg φ = .inl d1 := by
          rcases hrφ with h | h | h
          · exact absurd h (by simp)
          · exact (Sum.inl.inj (Sum.inr.inj h)).symm
          · exact absurd h (by simp)
        obtain ⟨hsp, hvert, hedge⟩ := (S.edg_eq_dart_iff φ d1).mp hd
        rcases hr'φ with rfl | rfl | rfl
        · left
          cases hterm' : φ.term
          · exfalso
            have : S.vtx φ = .inl u := (S.vtx_eq_inl_iff φ u).mpr ⟨hterm', hvert⟩
            rw [this] at hxr
            exact hu (hxr.symm.trans hrc)
          · congr 2
            exact (S.vtx_eq_edge_iff φ e).mpr ⟨hterm', hsp, hedge⟩
        · right; left; rw [hd]
        · exact absurd rfl hnotside
      · -- `r` is the dart `w → u`
        have hd : S.edg φ = .inl d2 := by
          rcases hrφ with h | h | h
          · exact absurd h (by simp)
          · exact (Sum.inl.inj (Sum.inr.inj h)).symm
          · exact absurd h (by simp)
        obtain ⟨hsp, hvert, hedge⟩ := (S.edg_eq_dart_iff φ d2).mp hd
        rcases hr'φ with rfl | rfl | rfl
        · left
          cases hterm' : φ.term
          · exfalso
            have : S.vtx φ = .inl w := (S.vtx_eq_inl_iff φ w).mpr ⟨hterm', hvert⟩
            rw [this] at hxr
            exact hw (hxr.symm.trans hrc)
          · congr 2
            refine (S.vtx_eq_edge_iff φ e).mpr ⟨hterm', hsp, ?_⟩
            rw [hedge]; exact Sym2.eq_swap
        · right; right; rw [hd]
        · exact absurd rfl hnotside
    have hfinal : ∀ b, Relation.ReflTransGen (fun p q => F.QAdj p q ∧ x p = x q)
        (.inl (.inr (.inl e))) b → b ∈ Comp ∧ x b = c := by
      intro b hb
      induction hb with
      | refl => exact ⟨by simp [Comp], hqec e⟩
      | tail _ hst ih =>
        obtain ⟨ih1, ih2⟩ := ih
        exact ⟨hinv _ ih1 ih2 _ hst.1 hst.2, hst.2.symm.trans ih2⟩
    have := (hfinal r₀ hchain).1
    simp [Comp, r₀] at this
  · -- the decoding coordinates read the cover
    funext v
    rw [readDec, LinearMap.funLeft_apply, edgeVec_apply, vertexVec_apply]
    set ψ := S.decFlag hJ v with hψ
    have hdecval : (S.decEdge hJ v : Sym2 S.Flag) = s(ψ, S.t1 ψ) := rfl
    have hne0 : s(ψ, S.t1 ψ) ≠ s(S.sF hJ, S.tF hJ) := by
      have := (S.decEdge hJ v).2
      rw [hdecval, edgeSet_deleteEdges] at this
      exact this.2
    have hdecD : s(ψ, S.t1 ψ) ∈ (walkGraph p).edgeSet ↔ s(ψ, S.t1 ψ) ∈ D.edgeSet := by
      rw [hD, edgeSet_sup, edgeSet_edge_of_ne hst_ne, Set.mem_union, Set.mem_singleton_iff]
      constructor
      · exact Or.inl
      · rintro (h | h)
        · exact h
        · exact absurd h hne0
    have hval : s(ψ, S.t1 ψ) ∈ D.edgeSet ↔ x (.inl (.inl v)) = c := by
      have h1 : s(ψ, S.t1 ψ) ∈ D.edgeSet ↔ F.zvec D (F.edgeAt ψ 1) = 1 :=
        (F.zvec_eq_one_iff D (F.edgeAt ψ 1)).symm
      rw [h1, hx, S.cut_edgeAt_one, hsidec]
      have hvtx : S.vtx ψ = .inl v := rfl
      rw [hvtx]
      rcases FlagSystem.zmod2_cases (x (.inl (.inl v))) with h | h <;>
        rcases FlagSystem.zmod2_cases c with h' | h' <;> simp [h, h'] <;> decide
    rw [hdecval]
    by_cases hv : x (.inl (.inl v)) = c
    · simp only [hdecD.trans hval, hv, Set.mem_ofPred_eq, ite_true]
    · simp only [hdecD.trans hval, hv, Set.mem_ofPred_eq, ite_false]

end PlanarFaces

end Lemmata.PlanarSteinerXC
