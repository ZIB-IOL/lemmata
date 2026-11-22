module

public import Lemmata.PlanarSteinerXC.FaceSystem
public import Lemmata.PlanarSteinerXC.CycleSpace
public import Mathlib.Algebra.BigOperators.Ring.Nat

/-!
# The complement of a forest is dual-connected

In a planar face system, the faces stay connected through shared edges outside any acyclic
subgraph `K`. (This holds for any face system; Euler's formula is not needed.) The sum over a set
`A` of faces of their boundaries is an even edge set; if `A` is a proper nonempty component, this
sum is nonzero and lies inside `K`, contradicting the existence of a leaf in a nonempty forest.
-/

@[expose] public section

set_option autoImplicit false

namespace Lemmata.PlanarSteinerXC

open SimpleGraph

namespace PlanarFaces

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} (S : PlanarFaces G)

/-- Faces sharing an edge outside `K`. -/
def AdjAvoid (K : SimpleGraph V) (a b : S.Face) : Prop :=
  ∃ e, e ∈ S.edges a ∧ e ∈ S.edges b ∧ e ∉ K.edgeSet

/-- **The faces are connected through edges outside any acyclic subgraph.** -/
theorem faces_connected_avoiding {K : SimpleGraph V} (hK : K ≤ G) (hacyc : K.IsAcyclic)
    (a b : S.Face) : Relation.ReflTransGen (S.AdjAvoid K) a b := by
  classical
  by_contra hab
  set A : Finset S.Face := Finset.univ.filter (fun c => Relation.ReflTransGen (S.AdjAvoid K) a c)
    with hA
  have haA : a ∈ A := by simp [hA, Relation.ReflTransGen.refl]
  have hbA : b ∉ A := by simpa [hA] using hab
  -- the number of faces of `A` at an edge
  let cnt : Sym2 V → ℕ := fun e => (A.filter (fun c => e ∈ S.edges c)).card
  -- an edge on exactly one face of `A` lies in `K`
  have hz1 : ∀ e ∈ G.edgeSet, cnt e % 2 = 1 → e ∈ K.edgeSet := by
    intro e he hodd
    by_contra heK
    obtain ⟨f, g, hfg, hf, hg⟩ := S.exists_two_faces he
    have hall : ∀ c, e ∈ S.edges c → c = f ∨ c = g := by
      intro c hc
      have h2 := S.two_faces e he
      have hsub : ({f, g, c} : Finset S.Face) ⊆ Finset.univ.filter (fun c => e ∈ S.edges c) := by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl <;> simpa
      by_contra hc'
      push Not at hc'
      have : ({f, g, c} : Finset S.Face).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp [hfg, Ne.symm hc'.1]),
          Finset.card_pair (Ne.symm hc'.2)]
      have := Finset.card_le_card hsub
      lia
    have hcnt : cnt e = (if f ∈ A then 1 else 0) + (if g ∈ A then 1 else 0) := by
      have : A.filter (fun c => e ∈ S.edges c) = A.filter (fun c => c = f ∨ c = g) := by
        ext c; simp only [Finset.mem_filter]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨h1, hall c h2⟩
        · rintro ⟨h1, rfl | rfl⟩ <;> exact ⟨h1, by assumption⟩
      simp only [cnt, this, Finset.filter_or]
      rw [Finset.card_union_of_disjoint]
      · congr 1 <;> split_ifs with h <;> simp_all [Finset.filter_eq']
      · rw [Finset.disjoint_filter]; rintro x - rfl; exact hfg
    -- the two faces at `e` are adjacent avoiding `K`, so both or none lie in `A`
    have hadj : S.AdjAvoid K f g := ⟨e, hf, hg, heK⟩
    have hadj' : S.AdjAvoid K g f := ⟨e, hg, hf, heK⟩
    have hfA : f ∈ A ↔ g ∈ A := by
      simp only [hA, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => h.tail hadj, fun h => h.tail hadj'⟩
    rw [hcnt] at hodd
    by_cases h : f ∈ A
    · rw [if_pos h, if_pos (hfA.mp h)] at hodd; norm_num at hodd
    · rw [if_neg h, if_neg (fun h' => h (hfA.mpr h'))] at hodd; norm_num at hodd
  -- some edge is on exactly one face of `A`
  have hz2 : ∃ e ∈ G.edgeSet, cnt e % 2 = 1 := by
    obtain ⟨p⟩ := S.dual_conn.preconnected a b
    have key : ∀ {c d : S.Face}, S.dual.Walk c d → c ∈ A → d ∉ A →
        ∃ e ∈ G.edgeSet, cnt e % 2 = 1 := by
      intro c d q
      induction q with
      | nil => intro h1 h2; exact absurd h1 h2
      | @cons x y z hxy q ih =>
        intro hx hz
        by_cases hy : y ∈ A
        · exact ih hy hz
        · rw [dual, fromRel_adj] at hxy
          obtain ⟨hne, hxy⟩ := hxy
          obtain ⟨e, hex, hey⟩ : ∃ e, e ∈ S.edges x ∧ e ∈ S.edges y := by
            rcases hxy with ⟨e, h1, h2⟩ | ⟨e, h1, h2⟩
            · exact ⟨e, h1, h2⟩
            · exact ⟨e, h2, h1⟩
          have he := S.mem_edgeSet_of_mem hex
          refine ⟨e, he, ?_⟩
          have hall : ∀ c, e ∈ S.edges c → c = x ∨ c = y := by
            intro c hc
            have h2 := S.two_faces e he
            by_contra hc'
            push Not at hc'
            have hsub : ({x, y, c} : Finset S.Face) ⊆
                Finset.univ.filter (fun c => e ∈ S.edges c) := by
              intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
              rcases hw with rfl | rfl | rfl <;> simpa
            have : ({x, y, c} : Finset S.Face).card = 3 := by
              rw [Finset.card_insert_of_notMem (by simp [hne, Ne.symm hc'.1]),
                Finset.card_pair (Ne.symm hc'.2)]
            have := Finset.card_le_card hsub
            lia
          have : A.filter (fun c => e ∈ S.edges c) = {x} := by
            ext c; simp only [Finset.mem_filter, Finset.mem_singleton]
            constructor
            · rintro ⟨h1, h2⟩
              rcases hall c h2 with rfl | rfl
              · rfl
              · exact absurd h1 hy
            · rintro rfl; exact ⟨hx, hex⟩
          simp [cnt, this]
    exact key p haA hbA
  -- the edges with odd count form a nonempty acyclic graph with all degrees even
  let Z : SimpleGraph V := SimpleGraph.fromEdgeSet {e | e ∈ G.edgeSet ∧ cnt e % 2 = 1}
  have hZK : Z ≤ K := by
    intro u v huv
    rw [fromEdgeSet_adj] at huv
    exact hz1 _ huv.1.1 huv.1.2
  have hZacyc : Z.IsAcyclic := hacyc.anti hZK
  obtain ⟨e₀, he₀, hodd₀⟩ := hz2
  induction e₀ using Sym2.ind with
  | h x y =>
  have hxy : Z.Adj x y := by
    rw [fromEdgeSet_adj]
    exact ⟨⟨he₀, hodd₀⟩, G.ne_of_adj (G.mem_edgeSet.mp he₀)⟩
  obtain ⟨v, hv⟩ := Lemmata.PlanarSteinerXC.IsAcyclic.exists_odd_degree hZacyc hxy
  -- but every degree is even
  have heven : Even (Z.degree v) := by
    -- degree of `v` in `Z` is the number of edges at `v` with odd count
    have hdeg : Z.degree v = ((G.incidenceFinset v).filter (fun e => cnt e % 2 = 1)).card := by
      rw [← card_incidenceFinset_eq_degree]
      congr 1
      ext e
      simp only [mem_incidenceFinset, Finset.mem_filter]
      constructor
      · rintro ⟨he, hve⟩
        rw [edgeSet_fromEdgeSet] at he
        exact ⟨⟨he.1.1, hve⟩, he.1.2⟩
      · rintro ⟨⟨he, hve⟩, hodd⟩
        refine ⟨?_, hve⟩
        rw [edgeSet_fromEdgeSet]
        exact ⟨⟨he, hodd⟩, G.not_isDiag_of_mem_edgeSet he⟩
    -- parity: the sum of the counts at `v` is twice something
    have hsum : ∑ e ∈ G.incidenceFinset v, cnt e = ∑ c ∈ A, edgeDeg (S.edges c) v := by
      have h1 : ∀ e, cnt e = ∑ c ∈ A, if e ∈ S.edges c then 1 else 0 := fun e => by
        simp only [cnt]; rw [Finset.card_filter]
      simp_rw [h1]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro c _
      rw [← Finset.card_filter]
      have hset : (G.incidenceFinset v).filter (fun e => e ∈ S.edges c) =
          (S.edges c).filter (fun e => v ∈ e) := by
        ext e
        simp only [Finset.mem_filter, mem_incidenceFinset]
        constructor
        · rintro ⟨⟨_, hve⟩, he⟩; exact ⟨he, hve⟩
        · rintro ⟨he, hve⟩; exact ⟨⟨S.edges_subset c e he, hve⟩, he⟩
      rw [hset]
      rfl
    have hsum_even : Even (∑ e ∈ G.incidenceFinset v, cnt e) := by
      rw [hsum]
      apply Finset.even_sum
      intro c _
      rcases S.edgeDeg_eq c v with h | h <;> rw [h] <;> decide
    rw [hdeg]
    -- the number of odd terms in a sum with even total is even
    have := Finset.even_sum_iff_even_card_odd (s := G.incidenceFinset v) (f := cnt) |>.mp hsum_even
    convert this using 2
    ext e; simp [Nat.odd_iff]
  rw [hv] at heven
  exact Nat.not_even_one heven

end PlanarFaces

end Lemmata.PlanarSteinerXC
