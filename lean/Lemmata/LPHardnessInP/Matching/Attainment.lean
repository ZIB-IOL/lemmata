module

public import Mathlib.Combinatorics.SimpleGraph.Matching
public import Mathlib.Tactic

@[expose] public section

namespace Lemmata.LPHardnessInP.Matching

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every odd cut of an even complete graph admits a perfect matching with
exactly one crossing edge. The conclusion identifies that edge explicitly;
the later counting lemma converts this to a cut-count equality. -/
theorem exists_unique_crossing_graph (hV : Even (Fintype.card V))
    (U : Finset V) (hU : Odd U.card) :
    ∃ G : SimpleGraph V, (∀ x, ∃! y, G.Adj x y) ∧
      ∃ u ∈ U, ∃ v ∉ U, ∀ x y, x ∈ U → y ∉ U →
        (G.Adj x y ↔ x = u ∧ y = v) := by
  classical
  have hUc : Odd Uᶜ.card := by
    rw [Finset.card_compl]
    have hle : U.card ≤ Fintype.card V := Finset.card_le_univ U
    rw [Nat.odd_iff] at hU ⊢
    rw [Nat.even_iff] at hV
    omega
  obtain ⟨u, hu⟩ := Finset.card_pos.mp hU.pos
  obtain ⟨v, hv⟩ := Finset.card_pos.mp hUc.pos
  have hvU : v ∉ U := Finset.mem_compl.mp hv
  have huv : u ≠ v := by intro h; exact hvU (h ▸ hu)
  let S := U.erase u
  let T := Uᶜ.erase v
  have hS : Even S.card := by
    dsimp [S]
    rw [Finset.card_erase_of_mem hu, Nat.even_iff]
    rw [Nat.odd_iff] at hU
    omega
  have hT : Even T.card := by
    dsimp [T]
    rw [Finset.card_erase_of_mem hv, Nat.even_iff]
    rw [Nat.odd_iff] at hUc
    omega
  obtain ⟨M₁, hM₁verts, hM₁⟩ :=
    (SimpleGraph.IsClique.even_iff_exists_isMatching
      (SimpleGraph.IsClique.top (S : Set V)) (Set.toFinite _)).mp
        (by simpa only [Set.ncard_coe_finset] using hS)
  obtain ⟨M₂, hM₂verts, hM₂⟩ :=
    (SimpleGraph.IsClique.even_iff_exists_isMatching
      (SimpleGraph.IsClique.top (T : Set V)) (Set.toFinite _)).mp
        (by simpa only [Set.ncard_coe_finset] using hT)
  let C : (⊤ : SimpleGraph V).Subgraph := (⊤ : SimpleGraph V).subgraphOfAdj huv
  have hC : C.IsMatching := SimpleGraph.Subgraph.IsMatching.subgraphOfAdj huv
  have h12 : (M₁ ⊔ M₂).IsMatching := by
    apply hM₁.sup hM₂
    rw [hM₁.support_eq_verts, hM₂.support_eq_verts, hM₁verts, hM₂verts]
    apply Set.disjoint_left.mpr
    intro x hxS hxT
    have hxU := (Finset.mem_erase.mp hxS).2
    have hxUc := Finset.mem_compl.mp (Finset.mem_erase.mp hxT).2
    exact hxUc hxU
  have hAll : ((M₁ ⊔ M₂) ⊔ C).IsMatching := by
    apply h12.sup hC
    rw [h12.support_eq_verts, hC.support_eq_verts]
    apply Set.disjoint_left.mpr
    intro x hx hxC
    change x ∈ M₁.verts ∪ M₂.verts at hx
    change x ∈ ({u, v} : Set V) at hxC
    rw [hM₁verts, hM₂verts] at hx
    rcases hx with hx | hx <;> rcases hxC with rfl | rfl
    · exact (Finset.mem_erase.mp hx).1 rfl
    · exact hvU (Finset.mem_erase.mp hx).2
    · exact (Finset.mem_compl.mp (Finset.mem_erase.mp hx).2) hu
    · exact (Finset.mem_erase.mp hx).1 rfl
  have hspan : ((M₁ ⊔ M₂) ⊔ C).IsSpanning := by
    intro x
    change (x ∈ M₁.verts ∪ M₂.verts) ∨ x ∈ ({u, v} : Set V)
    rw [hM₁verts, hM₂verts]
    by_cases hxU : x ∈ U
    · by_cases hxu : x = u
      · exact Or.inr (Or.inl hxu)
      · exact Or.inl (Or.inl (Finset.mem_erase.mpr ⟨hxu, hxU⟩))
    · by_cases hxv : x = v
      · exact Or.inr (Or.inr hxv)
      · exact Or.inl (Or.inr (Finset.mem_erase.mpr ⟨hxv, Finset.mem_compl.mpr hxU⟩))
  refine ⟨((M₁ ⊔ M₂) ⊔ C).spanningCoe, ?_, u, hu, v, hvU, ?_⟩
  · exact SimpleGraph.Subgraph.isPerfectMatching_iff.mp ⟨hAll, hspan⟩
  · intro x y hxU hyU
    change ((M₁.Adj x y ∨ M₂.Adj x y) ∨ C.Adj x y) ↔ x = u ∧ y = v
    have hn₁ : ¬ M₁.Adj x y := by
      intro h
      have hy := h.snd_mem
      rw [hM₁verts] at hy
      exact hyU (Finset.mem_erase.mp hy).2
    have hn₂ : ¬ M₂.Adj x y := by
      intro h
      have hx := h.fst_mem
      rw [hM₂verts] at hx
      exact (Finset.mem_compl.mp (Finset.mem_erase.mp hx).2) hxU
    simp only [hn₁, hn₂, false_or]
    change s(u, v) = s(x, y) ↔ x = u ∧ y = v
    simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk]
    constructor
    · rintro (⟨hux, hvy⟩ | ⟨huy, hvx⟩)
      · exact ⟨hux.symm, hvy.symm⟩
      · exact (hvU (hvx ▸ hxU)).elim
    · rintro ⟨rfl, rfl⟩
      exact Or.inl ⟨rfl, rfl⟩

end Lemmata.LPHardnessInP.Matching
