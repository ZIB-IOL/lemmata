module

public import Lemmata.Centroid.Proof.Combinatorics.Triangles

@[expose] public section

namespace Lemmata.Centroid.Graph

open Finset

variable {V : Type*}

def extend (G : SimpleGraph V) (S : Finset V) : SimpleGraph (Option V) where
  Adj
    | none, none => False
    | none, some v => v ∈ S
    | some v, none => v ∈ S
    | some v, some w => G.Adj v w
  symm := ⟨by
    intro v w h
    cases v <;> cases w
    · exact h
    · exact h
    · exact h
    · exact G.adj_symm h⟩
  loopless := ⟨by intro v; cases v <;> simp⟩

instance [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    DecidableRel (extend G S).Adj := by
  intro v w
  change Decidable (match v, w with
    | none, none => False
    | none, some v => v ∈ S
    | some v, none => v ∈ S
    | some v, some w => G.Adj v w)
  cases v <;> cases w <;> infer_instance

@[simp] theorem extend_adj_none_none (G : SimpleGraph V) (S : Finset V) :
    ¬ (extend G S).Adj none none := id

@[simp] theorem extend_adj_none_some (G : SimpleGraph V) (S : Finset V) (v : V) :
    (extend G S).Adj none (some v) ↔ v ∈ S := Iff.rfl

@[simp] theorem extend_adj_some_none (G : SimpleGraph V) (S : Finset V) (v : V) :
    (extend G S).Adj (some v) none ↔ v ∈ S := Iff.rfl

@[simp] theorem extend_adj_some_some (G : SimpleGraph V) (S : Finset V) (v w : V) :
    (extend G S).Adj (some v) (some w) ↔ G.Adj v w := Iff.rfl

theorem edgeFinset_extend [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    (extend G S).edgeFinset = G.edgeFinset.image (Sym2.map some) ∪
      S.image (fun v => s(none, some v)) := by
  classical
  let old : Finset (Sym2 (Option V)) := G.edgeFinset.image (Sym2.map some)
  let new : Finset (Sym2 (Option V)) := S.image (fun v => s(none, some v))
  have hsub : (extend G S).edgeFinset ⊆ old ∪ new := by
    intro e
    refine Sym2.inductionOn e ?_
    intro v w he
    have ha := SimpleGraph.mem_edgeFinset.1 he
    cases v with
    | none =>
      cases w with
      | none => exact False.elim ha
      | some w => exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨w, ha, rfl⟩)
    | some v =>
      cases w with
      | none =>
        apply Finset.mem_union_right
        exact Finset.mem_image.2 ⟨v, ha, Sym2.eq_swap⟩
      | some w =>
        apply Finset.mem_union_left
        exact Finset.mem_image.2 ⟨s(v, w), SimpleGraph.mem_edgeFinset.2 ha, rfl⟩
  apply Finset.Subset.antisymm hsub
  intro e he
  obtain he | he := Finset.mem_union.1 he
  · change e ∈ G.edgeFinset.image (Sym2.map some) at he
    obtain ⟨e₀, he₀, heq⟩ := (Finset.mem_image (s := G.edgeFinset) (f := Sym2.map some)).1 he
    subst e
    have heG : e₀ ∈ G.edgeFinset := he₀
    revert heG
    refine Sym2.inductionOn e₀ ?_
    intro v w hvw
    have ha : G.Adj v w := SimpleGraph.mem_edgeFinset.1 hvw
    exact SimpleGraph.mem_edgeFinset.2 ha
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 he
    exact SimpleGraph.mem_edgeFinset.2 hv

theorem edge_card_extend_le [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    (extend G S).edgeFinset.card ≤ G.edgeFinset.card + S.card := by
  classical
  let old : Finset (Sym2 (Option V)) := G.edgeFinset.image (Sym2.map some)
  let new : Finset (Sym2 (Option V)) := S.image (fun v => s(none, some v))
  have h₁ : (extend G S).edgeFinset.card = (old ∪ new).card :=
    congrArg Finset.card (edgeFinset_extend G S)
  have h₂ := Finset.card_union_le old new
  have h₃ : old.card ≤ G.edgeFinset.card := Finset.card_image_le
  have h₄ : new.card ≤ S.card := Finset.card_image_le
  omega

theorem disjoint_old_new_edges [DecidableEq V] (E : Finset (Sym2 V)) (S : Finset V) :
    Disjoint (E.image (Sym2.map some)) (S.image (fun v => s(none, some v))) := by
  classical
  apply Finset.disjoint_left.2
  intro e he hn
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 he
  obtain ⟨v, hv, hEq⟩ := Finset.mem_image.1 hn
  have hnone : none ∈ Sym2.map some e := hEq ▸ Sym2.mem_mk_left none (some v)
  simp [Sym2.mem_map] at hnone

theorem map_edge_subset [DecidableEq V] (e : Sym2 V) (T : Finset V) :
    (Sym2.map some e).toFinset ⊆ T.map Function.Embedding.some ↔ e.toFinset ⊆ T := by
  refine Sym2.inductionOn e ?_
  intro v w
  simp [Sym2.toFinset_mk_eq, Finset.insert_subset_iff]

theorem map_edge_subset_insert [DecidableEq V] (e : Sym2 V) (T : Finset V) :
    (Sym2.map some e).toFinset ⊆ insert none (T.map Function.Embedding.some) ↔
      e.toFinset ⊆ T := by
  refine Sym2.inductionOn e ?_
  intro v w
  simp [Sym2.toFinset_mk_eq, Finset.insert_subset_iff]

theorem internal_edges_extend [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S T : Finset V) :
    ((extend G S).edgeFinset.filter
      (fun e => e.toFinset ⊆ T.map Function.Embedding.some)).card =
      (G.edgeFinset.filter (fun e => e.toFinset ⊆ T)).card := by
  classical
  rw [edgeFinset_extend, Finset.filter_union, Finset.filter_image, Finset.filter_image]
  simp only [map_edge_subset]
  have hnew : (S.filter (fun v => (s(none, some v)).toFinset ⊆
      T.map Function.Embedding.some)) = ∅ := by
    simp [Sym2.toFinset_mk_eq, Finset.insert_subset_iff]
  rw [hnew]
  simp only [Finset.image_empty, Finset.union_empty]
  exact Finset.card_image_of_injective _ (Sym2.map.injective (Option.some_injective V))

theorem internal_edges_extend_insert [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S T : Finset V) :
    ((extend G S).edgeFinset.filter
      (fun e => e.toFinset ⊆ insert none (T.map Function.Embedding.some))).card =
      (G.edgeFinset.filter (fun e => e.toFinset ⊆ T)).card + (S ∩ T).card := by
  classical
  rw [edgeFinset_extend, Finset.filter_union, Finset.filter_image, Finset.filter_image]
  simp only [map_edge_subset_insert]
  have hnew : (S.filter (fun v => (s(none, some v)).toFinset ⊆
      insert none (T.map Function.Embedding.some))) = S ∩ T := by
    ext v
    simp [Sym2.toFinset_mk_eq, Finset.insert_subset_iff]
  rw [hnew, Finset.card_union_of_disjoint (disjoint_old_new_edges _ _)]
  rw [Finset.card_image_of_injective _ (Sym2.map.injective (Option.some_injective V))]
  congr 1
  exact Finset.card_image_of_injective _
    ((Sym2.mkEmbedding none).injective.comp (Option.some_injective V))

theorem extend_isNClique_map [DecidableEq V] (G : SimpleGraph V) (S : Finset V)
    {n : ℕ} {s : Finset V} (hs : G.IsNClique n s) :
    (extend G S).IsNClique n (s.map Function.Embedding.some) := by
  constructor
  · intro x hx y hy hxy
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.1 hx
    obtain ⟨w, hw, rfl⟩ := Finset.mem_map.1 hy
    exact hs.isClique hv hw (fun h => hxy (congrArg some h))
  · simpa using hs.card_eq

theorem edge_isNClique [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {e : Sym2 V} (he : e ∈ G.edgeFinset) :
    G.IsNClique 2 e.toFinset := by
  refine Sym2.inductionOn e (fun v w he => ?_) he
  have ha : G.Adj v w := SimpleGraph.mem_edgeFinset.1 he
  rw [Sym2.toFinset_mk_eq]
  refine ⟨?_, ?_⟩
  · simpa only [Finset.coe_insert, Finset.coe_singleton] using
      (SimpleGraph.isClique_pair.2 fun _ => ha)
  · simp [ha.ne]

theorem edge_toFinset_injective [DecidableEq V] :
    Function.Injective (Sym2.toFinset : Sym2 V → Finset V) := by
  intro e e' h
  apply Sym2.ext
  intro v
  exact Iff.of_eq (by simpa only [Sym2.mem_toFinset] using congrArg (fun s => v ∈ s) h)

theorem triangle_card_extend_le [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    (G.cliqueFinset 3).card +
      (G.edgeFinset.filter (fun e => e.toFinset ⊆ S)).card ≤
      ((extend G S).cliqueFinset 3).card := by
  classical
  let old : Finset (Finset (Option V)) :=
    (G.cliqueFinset 3).image (fun s => s.map Function.Embedding.some)
  let new : Finset (Finset (Option V)) :=
    (G.edgeFinset.filter (fun e => e.toFinset ⊆ S)).image
      (fun e => insert none (e.toFinset.map Function.Embedding.some))
  have hold : old ⊆ (extend G S).cliqueFinset 3 := by
    intro s hs
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hs
    exact SimpleGraph.mem_cliqueFinset_iff.2
      (extend_isNClique_map G S (SimpleGraph.mem_cliqueFinset_iff.1 ht))
  have hnew : new ⊆ (extend G S).cliqueFinset 3 := by
    intro s hs
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hs
    obtain ⟨he, hS⟩ := Finset.mem_filter.1 he
    apply SimpleGraph.mem_cliqueFinset_iff.2
    apply (extend_isNClique_map G S (edge_isNClique G he)).insert
    intro w hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.1 hw
    exact hS hv
  have hdisj : Disjoint old new := by
    apply Finset.disjoint_left.2
    intro s hs hn
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hs
    obtain ⟨e, he, heq⟩ := Finset.mem_image.1 hn
    have hnone : none ∈ t.map Function.Embedding.some := heq ▸ Finset.mem_insert_self _ _
    simp at hnone
  have holdcard : old.card = (G.cliqueFinset 3).card :=
    Finset.card_image_of_injective _ (Finset.map_injective _)
  have hinj : Function.Injective (fun e : Sym2 V =>
      insert none (e.toFinset.map Function.Embedding.some)) := by
    intro e e' h
    apply edge_toFinset_injective
    apply (Finset.map_injective Function.Embedding.some)
    have h' := congrArg (fun s => s.erase none) h
    simpa using h'
  have hnewcard : new.card = (G.edgeFinset.filter (fun e => e.toFinset ⊆ S)).card :=
    Finset.card_image_of_injective _ hinj
  have hsub := Finset.card_le_card (Finset.union_subset hold hnew)
  rw [Finset.card_union_of_disjoint hdisj, holdcard, hnewcard] at hsub
  exact hsub

def mixedEdges [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) : Finset (V × V) :=
  (A ×ˢ B).filter (fun p => G.Adj p.1 p.2)

theorem mixed_edge_bound [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) :
    (mixedEdges G A B).card ≤
      (G.edgeFinset.filter (fun e => e.toFinset ⊆ A ∪ B)).card +
      (G.edgeFinset.filter (fun e => e.toFinset ⊆ A ∩ B)).card := by
  classical
  let P := mixedEdges G A B
  let P₁ := P.filter (fun p => p.1 < p.2)
  let P₂ := P.filter (fun p => p.2 < p.1)
  let E₁ := P₁.image (fun p => s(p.1, p.2))
  let E₂ := P₂.image (fun p => s(p.1, p.2))
  have hP : P₁ ∪ P₂ = P := by
    ext p
    have hne (hp : p ∈ P) : p.1 ≠ p.2 :=
      (Finset.mem_filter.1 hp).2.ne
    simp only [P₁, P₂, Finset.mem_union, Finset.mem_filter]
    grind [lt_or_gt_of_ne]
  have hdisj : Disjoint P₁ P₂ := by
    apply Finset.disjoint_left.2
    intro p hp hq
    exact lt_asymm (Finset.mem_filter.1 hp).2 (Finset.mem_filter.1 hq).2
  have hinj₁ : Set.InjOn (fun p : V × V => s(p.1, p.2)) P₁ := by
    intro p hp q hq he
    obtain ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ := Sym2.eq_iff.1 he
    · exact Prod.ext h₁ h₂
    · have hp' := (Finset.mem_filter.1 hp).2
      have hq' := (Finset.mem_filter.1 hq).2
      rw [h₁, h₂] at hp'
      exact False.elim (lt_asymm hp' hq')
  have hinj₂ : Set.InjOn (fun p : V × V => s(p.1, p.2)) P₂ := by
    intro p hp q hq he
    obtain ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ := Sym2.eq_iff.1 he
    · exact Prod.ext h₁ h₂
    · have hp' := (Finset.mem_filter.1 hp).2
      have hq' := (Finset.mem_filter.1 hq).2
      rw [h₁, h₂] at hp'
      exact False.elim (lt_asymm hp' hq')
  have hcard : E₁.card + E₂.card = P.card := by
    rw [Finset.card_image_of_injOn hinj₁, Finset.card_image_of_injOn hinj₂]
    rw [← Finset.card_union_of_disjoint hdisj, hP]
  have hsub : E₁ ∪ E₂ ⊆ G.edgeFinset.filter (fun e => e.toFinset ⊆ A ∪ B) := by
    intro e he
    obtain he | he := Finset.mem_union.1 he
    all_goals
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 he
      have hp' := (Finset.mem_filter.1 hp).1
      obtain ⟨hpAB, ha⟩ := Finset.mem_filter.1 hp'
      obtain ⟨hA, hB⟩ := Finset.mem_product.1 hpAB
      apply Finset.mem_filter.2
      exact ⟨SimpleGraph.mem_edgeFinset.2 ha, by
        simpa [Sym2.toFinset_mk_eq, Finset.insert_subset_iff] using
          And.intro (Finset.mem_union_left B hA) (Finset.mem_union_right A hB)⟩
  have hinter : E₁ ∩ E₂ ⊆ G.edgeFinset.filter (fun e => e.toFinset ⊆ A ∩ B) := by
    intro e he
    obtain ⟨he₁, he₂⟩ := Finset.mem_inter.1 he
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 he₁
    obtain ⟨q, hq, heq⟩ := Finset.mem_image.1 he₂
    obtain ⟨hpP, hpLt⟩ := Finset.mem_filter.1 hp
    obtain ⟨hqP, hqLt⟩ := Finset.mem_filter.1 hq
    obtain ⟨hpAB, ha⟩ := Finset.mem_filter.1 hpP
    obtain ⟨hqAB, _⟩ := Finset.mem_filter.1 hqP
    obtain ⟨hA, hB⟩ := Finset.mem_product.1 hpAB
    obtain ⟨hA', hB'⟩ := Finset.mem_product.1 hqAB
    have heq' : s(q.1, q.2) = s(p.1, p.2) := heq
    obtain ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ := Sym2.eq_iff.1 heq'
    · rw [h₁, h₂] at hqLt
      exact False.elim (lt_asymm hpLt hqLt)
    · apply Finset.mem_filter.2
      refine ⟨SimpleGraph.mem_edgeFinset.2 ha, ?_⟩
      simp only [Sym2.toFinset_mk_eq, Finset.insert_subset_iff,
        Finset.singleton_subset_iff, Finset.mem_inter]
      exact ⟨⟨hA, h₂ ▸ hB'⟩, ⟨h₁ ▸ hA', hB⟩⟩
  have h₁ := Finset.card_le_card hsub
  have h₂ := Finset.card_le_card hinter
  have h₃ := Finset.card_union_add_card_inter E₁ E₂
  change E₁.card + E₂.card = (mixedEdges G A B).card at hcard
  omega

theorem three_vertex_bound [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) (δ : Bool) :
    (G.cliqueFinset 3).card + (mixedEdges G A B).card +
      (if δ then (A ∩ B).card else 0) + G.edgeFinset.card + A.card + B.card +
      (if δ then 1 else 0) ≤
      triangleBound (Fintype.card V + G.edgeFinset.card + A.card + B.card +
        (if δ then 1 else 0) + 2) := by
  classical
  let U := A ∪ B
  let J := A ∩ B
  let H := extend G univ
  let U₁ : Finset (Option V) := insert none (U.map Function.Embedding.some)
  let J₁ : Finset (Option V) := insert none (J.map Function.Embedding.some)
  let K := extend H U₁
  let S : Finset (Option (Option V)) :=
    if δ then insert none (J₁.map Function.Embedding.some)
    else J₁.map Function.Embedding.some
  let L := extend K S
  have hUJ : U.card + J.card = A.card + B.card :=
    Finset.card_union_add_card_inter A B
  have hU₁ : U₁.card = U.card + 1 := by simp [U₁]
  have hJ₁ : J₁.card = J.card + 1 := by simp [J₁]
  have hJsub : J₁ ⊆ U₁ := by
    apply Finset.insert_subset_insert
    apply Finset.map_subset_map.2
    exact Finset.inter_subset_left.trans Finset.subset_union_left
  have hS : S.card = J.card + 1 + (if δ then 1 else 0) := by
    cases δ <;> simp [S, hJ₁]
  have heH := edge_card_extend_le G univ
  have heK := edge_card_extend_le H U₁
  have heL := edge_card_extend_le K S
  have he : L.edgeFinset.card ≤ Fintype.card V + G.edgeFinset.card +
      A.card + B.card + (if δ then 1 else 0) + 2 := by
    simp only [Finset.card_univ] at heH
    change H.edgeFinset.card ≤ G.edgeFinset.card + Fintype.card V at heH
    change K.edgeFinset.card ≤ H.edgeFinset.card + U₁.card at heK
    change L.edgeFinset.card ≤ K.edgeFinset.card + S.card at heL
    omega
  have htH := triangle_card_extend_le G univ
  have htK := triangle_card_extend_le H U₁
  have htL := triangle_card_extend_le K S
  have hHU : (H.edgeFinset.filter (fun e => e.toFinset ⊆ U₁)).card =
      (G.edgeFinset.filter (fun e => e.toFinset ⊆ U)).card + U.card := by
    simpa only [Finset.univ_inter] using internal_edges_extend_insert G univ U
  have hHJ : (H.edgeFinset.filter (fun e => e.toFinset ⊆ J₁)).card =
      (G.edgeFinset.filter (fun e => e.toFinset ⊆ J)).card + J.card := by
    simpa only [Finset.univ_inter] using internal_edges_extend_insert G univ J
  have hKS : (K.edgeFinset.filter (fun e => e.toFinset ⊆ S)).card =
      (G.edgeFinset.filter (fun e => e.toFinset ⊆ J)).card + J.card +
        (if δ then J.card + 1 else 0) := by
    cases δ
    · exact (internal_edges_extend H U₁ J₁).trans (by simpa using hHJ)
    · have h := internal_edges_extend_insert H U₁ J₁
      rw [Finset.inter_eq_right.2 hJsub, hJ₁, hHJ] at h
      exact h
  have hmix := mixed_edge_bound G A B
  have ht : (G.cliqueFinset 3).card + (mixedEdges G A B).card +
      (if δ then J.card else 0) + G.edgeFinset.card + A.card + B.card +
        (if δ then 1 else 0) ≤ (L.cliqueFinset 3).card := by
    simp only [Finset.subset_univ, Finset.filter_true] at htH
    change (G.cliqueFinset 3).card + G.edgeFinset.card ≤ (H.cliqueFinset 3).card at htH
    change (H.cliqueFinset 3).card + _ ≤ (K.cliqueFinset 3).card at htK
    change (K.cliqueFinset 3).card + _ ≤ (L.cliqueFinset 3).card at htL
    rw [hHU] at htK
    rw [hKS] at htL
    change (mixedEdges G A B).card ≤
      (G.edgeFinset.filter (fun e => e.toFinset ⊆ U)).card +
      (G.edgeFinset.filter (fun e => e.toFinset ⊆ J)).card at hmix
    cases δ <;> simp only [Bool.false_eq_true, ite_false, ite_true] at * <;> omega
  exact ht.trans ((triangle_bound_edges L).trans (triangleBound_mono he))

end Lemmata.Centroid.Graph
