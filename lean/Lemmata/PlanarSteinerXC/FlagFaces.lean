module

public import Lemmata.PlanarSteinerXC.CycleSpace
public import Lemmata.PlanarSteinerXC.FaceSystem

/-!
# The flag graph is planar

For a connected flag system satisfying Euler's formula, the stars of the vertices, edges and faces
(the elements of `Q`) are the faces of a planar face system of the flag graph.
-/

@[expose] public section

set_option autoImplicit false

namespace Lemmata.PlanarSteinerXC

open SimpleGraph

namespace FlagSystem

universe u

variable {Φ Q0 Q1 Q2 : Type u} (F : FlagSystem Φ Q0 Q1 Q2)
variable [DecidableEq Q0] [DecidableEq Q1] [DecidableEq Q2] [Fintype Φ] [DecidableEq Φ]
  [Fintype Q0] [Fintype Q1] [Fintype Q2]

/-- The star of an element of `Q`: the edges of the flag graph dual to edges of `Q` at it. -/
noncomputable def star (q : Q0 ⊕ Q1 ⊕ Q2) : Finset (Sym2 Φ) :=
  F.graph.edgeFinset.filter fun ε => q ∈ F.shared ε

theorem mem_star {q : Q0 ⊕ Q1 ⊕ Q2} {ε : Sym2 Φ} :
    ε ∈ F.star q ↔ ε ∈ F.graph.edgeSet ∧ q ∈ F.shared ε := by
  simp [star]

theorem card_shared (ε : Sym2 Φ) (hε : ε ∈ F.graph.edgeSet) : (F.shared ε).card = 2 := by
  obtain ⟨φ, p, q, hsh, hpq, -, -⟩ := F.edge_shared ⟨ε, hε⟩
  rw [hsh, Finset.card_pair hpq]

theorem star_edgeDeg (q : Q0 ⊕ Q1 ⊕ Q2) (φ : Φ) :
    edgeDeg (F.star q) φ = 0 ∨ edgeDeg (F.star q) φ = 2 := by
  classical
  unfold edgeDeg
  -- the edges at `φ` are the three `edgeAt φ i`
  have hset : (F.star q).filter (fun ε => φ ∈ ε) =
      (Finset.univ.filter fun i : Fin 3 => q ∈ F.shared (F.edgeAt φ i)).image
        (fun i => ((F.edgeAt φ i : F.graph.edgeSet) : Sym2 Φ)) := by
    ext ε
    simp only [Finset.mem_filter, mem_star, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨hε, hq⟩, hφ⟩
      have : (⟨ε, hε⟩ : F.graph.edgeSet) ∈ F.inc φ := by simp [inc, hφ]
      rw [F.inc_eq] at this
      obtain ⟨i, -, hi⟩ := Finset.mem_image.mp this
      refine ⟨i, ?_, congrArg Subtype.val hi⟩
      rw [hi]; exact hq
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨(F.edgeAt φ i).2, hi⟩, Sym2.mem_mk_left _ _⟩
  rw [hset, Finset.card_image_of_injective _
    (fun i j h => F.edgeAt_injective φ (Subtype.ext h))]
  have h0 : F.shared ((F.edgeAt φ 0 : F.graph.edgeSet) : Sym2 Φ) =
      {.inr (.inl (F.edg φ)), .inr (.inr (F.fac φ))} := F.shared_τ0 φ
  have h1 : F.shared ((F.edgeAt φ 1 : F.graph.edgeSet) : Sym2 Φ) =
      {.inl (F.vtx φ), .inr (.inr (F.fac φ))} := F.shared_τ1 φ
  have h2 : F.shared ((F.edgeAt φ 2 : F.graph.edgeSet) : Sym2 Φ) =
      {.inl (F.vtx φ), .inr (.inl (F.edg φ))} := F.shared_τ2 φ
  rw [Finset.card_filter, Fin.sum_univ_three]
  rw [h0, h1, h2]
  by_cases hv : q = .inl (F.vtx φ)
  · subst hv
    rw [if_neg (by simp), if_pos (by simp), if_pos (by simp)]
    right; rfl
  by_cases he : q = .inr (.inl (F.edg φ))
  · subst he
    rw [if_pos (by simp), if_neg (by simp), if_pos (by simp)]
    right; rfl
  by_cases hf : q = .inr (.inr (F.fac φ))
  · subst hf
    rw [if_pos (by simp), if_pos (by simp), if_neg (by simp)]
    right; rfl
  left
  rw [if_neg (by simp [he, hf]), if_neg (by simp [hv, hf]), if_neg (by simp [hv, he])]

theorem two_stars (ε : Sym2 Φ) (hε : ε ∈ F.graph.edgeSet) :
    (Finset.univ.filter (fun q => ε ∈ F.star q)).card = 2 := by
  rw [← F.card_shared ε hε]
  congr 1
  ext q
  simp [mem_star, hε]

theorem star_nonempty (q : Q0 ⊕ Q1 ⊕ Q2) : (F.star q).Nonempty := by
  -- every element lies on a flag, and two of the three edges at that flag share it
  obtain ⟨φ, hφ⟩ : ∃ φ, q ∈ F.elts φ := by
    rcases q with a | b | c
    · obtain ⟨φ, rfl⟩ := F.vtx_surj a; refine ⟨φ, ?_⟩; simp [elts]
    · obtain ⟨φ, rfl⟩ := F.edg_surj b; refine ⟨φ, ?_⟩; simp [elts]
    · obtain ⟨φ, rfl⟩ := F.fac_surj c; refine ⟨φ, ?_⟩; simp [elts]
  simp only [elts, Finset.mem_insert, Finset.mem_singleton] at hφ
  rcases hφ with rfl | rfl | rfl
  · exact ⟨s(φ, F.τ1 φ), (F.mem_star).mpr ⟨F.adj_τ1 φ, by rw [F.shared_τ1]; simp⟩⟩
  · exact ⟨s(φ, F.τ0 φ), (F.mem_star).mpr ⟨F.adj_τ0 φ, by rw [F.shared_τ0]; simp⟩⟩
  · exact ⟨s(φ, F.τ0 φ), (F.mem_star).mpr ⟨F.adj_τ0 φ, by rw [F.shared_τ0]; simp⟩⟩

theorem star_dual_connected (hconn : F.graph.Connected) :
    (SimpleGraph.fromRel fun q q' : Q0 ⊕ Q1 ⊕ Q2 =>
      ∃ ε, ε ∈ F.star q ∧ ε ∈ F.star q').Connected := by
  classical
  set G := (SimpleGraph.fromRel fun q q' : Q0 ⊕ Q1 ⊕ Q2 => ∃ ε, ε ∈ F.star q ∧ ε ∈ F.star q')
  -- two elements of a flag are adjacent or equal
  have hpair : ∀ φ p q, p ∈ F.elts φ → q ∈ F.elts φ → G.Reachable p q := by
    intro φ p q hp hq
    by_cases hpq : p = q
    · rw [hpq]
    obtain ⟨ε, hε⟩ := F.exists_edge_between hp hq hpq
    apply Adj.reachable
    rw [fromRel_adj]
    refine ⟨hpq, Or.inl ⟨ε, (F.mem_star).mpr ⟨ε.2, by rw [hε]; simp⟩,
      (F.mem_star).mpr ⟨ε.2, by rw [hε]; simp⟩⟩⟩
  -- the vertex of a flag reaches the vertex of every other flag
  obtain ⟨φ₀⟩ := hconn.nonempty
  have hflag : ∀ φ, G.Reachable (.inl (F.vtx φ₀)) (.inl (F.vtx φ)) := by
    intro φ
    obtain ⟨p⟩ := hconn.preconnected φ₀ φ
    induction p with
    | nil => rfl
    | @cons a b c hab p ih =>
      refine Reachable.trans ?_ ih
      -- `a` and `b` share two elements; go through the shared ones
      rcases F.edge_cases hab with rfl | rfl | rfl
      · refine (hpair a _ (.inr (.inl (F.edg a))) (by simp [elts]) (by simp [elts])).trans ?_
        exact hpair (F.τ0 a) _ _ (by simp [elts, F.edg_τ0]) (by simp [elts])
      · rw [F.vtx_τ1]
      · rw [F.vtx_τ2]
  refine (connected_iff_exists_forall_reachable _).mpr ⟨.inl (F.vtx φ₀), fun q => ?_⟩
  rcases q with a | b | c
  · obtain ⟨φ, rfl⟩ := F.vtx_surj a; exact hflag φ
  · obtain ⟨φ, rfl⟩ := F.edg_surj b
    exact (hflag φ).trans (hpair φ _ _ (by simp [elts]) (by simp [elts]))
  · obtain ⟨φ, rfl⟩ := F.fac_surj c
    exact (hflag φ).trans (hpair φ _ _ (by simp [elts]) (by simp [elts]))

/-- **The flag graph is planar.** The stars form a planar face system. -/
noncomputable def planarFaces (hconn : F.graph.Connected)
    (heuler : 2 * (Fintype.card Q0 + Fintype.card Q1 + Fintype.card Q2) = Fintype.card Φ + 4) :
    PlanarFaces F.graph where
  Face := Q0 ⊕ Q1 ⊕ Q2
  edges := F.star
  edges_subset := fun q ε hε => ((F.mem_star).mp hε).1
  edges_nonempty := F.star_nonempty
  edgeDeg_eq := F.star_edgeDeg
  two_faces := F.two_stars
  connected := hconn
  dual_connected := F.star_dual_connected hconn
  euler := by
    have hE := F.two_mul_card_edges
    rw [Nat.card_eq_fintype_card, Fintype.card_sum, Fintype.card_sum]
    lia

/-- The flag graph is cubic. -/
theorem degree_eq_three (φ : Φ) : F.graph.degree φ = 3 := by
  classical
  rw [← card_incidenceFinset_eq_degree, ← F.card_inc φ]
  rw [← Finset.card_map (Function.Embedding.subtype _)]
  congr 1
  ext ε
  simp only [mem_incidenceFinset, inc, Finset.mem_map, Finset.mem_filter, Finset.mem_univ,
    true_and, Function.Embedding.subtype_apply]
  constructor
  · intro hε
    exact ⟨⟨ε, hε.1⟩, hε.2, rfl⟩
  · rintro ⟨⟨e, he⟩, hφ, rfl⟩
    exact ⟨he, hφ⟩

end FlagSystem

end Lemmata.PlanarSteinerXC
