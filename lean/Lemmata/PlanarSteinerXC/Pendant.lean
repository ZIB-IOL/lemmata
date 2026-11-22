module

public import Lemmata.PlanarSteinerXC.Objects
public import Mathlib.Algebra.Module.Equiv.Basic

/-!
# Two terminals for connected supports: the pendant transfer

Attach a pendant edge at every vertex of `R` and keep only two terminals `t₁ ≠ t₂ ∈ R`. On the face
of `Pconn` where all pendant coordinates equal one, the connected support is forced to contain all
of `R`, and deleting the pendant coordinates gives exactly `Pconn G R`.
-/

@[expose] public section

set_option autoImplicit false

namespace Lemmata.PlanarSteinerXC

open SimpleGraph

variable {W : Type*} [Fintype W] [DecidableEq W] (G : SimpleGraph W) (R : Set W)

/-- The graph `G` with a pendant vertex attached to every vertex of `R`. -/
def pendant : SimpleGraph (W ⊕ R) where
  Adj := fun x y => match x, y with
    | .inl a, .inl b => G.Adj a b
    | .inl a, .inr t => a = t.1
    | .inr t, .inl a => a = t.1
    | .inr _, .inr _ => False
  symm := ⟨by rintro (a | t) (b | t') h <;> simp_all [G.adj_comm]⟩
  loopless := ⟨by rintro (a | t) h <;> simp_all⟩

variable {G R}

@[simp] theorem pendant_adj_inl_inl (a b : W) : (pendant G R).Adj (.inl a) (.inl b) ↔ G.Adj a b :=
  Iff.rfl

@[simp] theorem pendant_adj_inl_inr (a : W) (t : R) :
    (pendant G R).Adj (.inl a) (.inr t) ↔ a = t.1 := Iff.rfl

@[simp] theorem pendant_adj_inr_inl (a : W) (t : R) :
    (pendant G R).Adj (.inr t) (.inl a) ↔ a = t.1 := Iff.rfl

@[simp] theorem pendant_not_adj_inr_inr (t t' : R) : ¬ (pendant G R).Adj (.inr t) (.inr t') := id

theorem pendant_edge_mem (t : R) : s(.inl t.1, .inr t) ∈ (pendant G R).edgeSet := by
  rw [mem_edgeSet]; simp

theorem inl_edge_mem {e : Sym2 W} (he : e ∈ G.edgeSet) :
    Sym2.map Sum.inl e ∈ (pendant G R).edgeSet := by
  induction e using Sym2.ind with
  | h a b => exact he

/-- The pendant edges as coordinates. -/
def pendEdge (t : R) : (pendant G R).edgeSet := ⟨_, pendant_edge_mem t⟩

/-- The pendant coordinates. -/
noncomputable def pendSet [Fintype R] : Finset (pendant G R).edgeSet := by
  classical exact Finset.univ.image pendEdge

/-- Restriction to the edges of `G`. -/
def restrictInl : ((pendant G R).edgeSet → ℝ) →ₗ[ℝ] (G.edgeSet → ℝ) :=
  LinearMap.funLeft ℝ ℝ (fun e : G.edgeSet => ⟨Sym2.map Sum.inl e.1, inl_edge_mem e.2⟩)

/-- Pendant vertices are never internal vertices of paths. -/
theorem path_support_inl {K : SimpleGraph (W ⊕ R)} (hK : K ≤ pendant G R) {a b : W}
    (p : K.Walk (.inl a) (.inl b)) (hp : p.IsPath) : ∀ z ∈ p.support, ∃ c, z = .inl c := by
  intro z hz
  rcases z with c | t
  · exact ⟨c, rfl⟩
  · exfalso
    obtain ⟨i, hi, hle⟩ := Walk.mem_support_iff_exists_getVert.mp hz
    have hi0 : i ≠ 0 := by
      rintro rfl; rw [Walk.getVert_zero] at hi; exact absurd hi (by simp)
    have hil : i ≠ p.length := by
      rintro rfl; rw [Walk.getVert_length] at hi; exact absurd hi (by simp)
    have h2 := hp.ncard_neighborSet_toSubgraph_internal_eq_two hi0 (by lia)
    rw [hi] at h2
    have hsub : p.toSubgraph.neighborSet (.inr t) ⊆ {.inl t.1} := by
      intro y hy
      have hy' : K.Adj (.inr t) y := p.toSubgraph.adj_sub hy
      have := hK hy'
      rcases y with c | t'
      · simp only [pendant_adj_inr_inl] at this; rw [this]; rfl
      · exact absurd this (pendant_not_adj_inr_inr t t')
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_singleton, h2] at this
    lia

/-- Walks through `inl` vertices only descend to the graph pulled back along `inl`. -/
theorem reachable_of_walk_inl {K : SimpleGraph (W ⊕ R)} {x y : W ⊕ R} (p : K.Walk x y) :
    ∀ a b, x = .inl a → y = .inl b → (∀ z ∈ p.support, ∃ c, z = .inl c) →
      (K.comap Sum.inl).Reachable a b := by
  induction p with
  | nil => rintro a b rfl h _; cases h; rfl
  | @cons x x' y hxx' p ih =>
    rintro a b rfl hy hsupp
    obtain ⟨c, rfl⟩ := hsupp x' (by simp)
    have h1 : (K.comap Sum.inl).Adj a c := hxx'
    exact h1.reachable.trans (ih c b rfl hy fun z hz => hsupp z (by simp [hz]))

/-- Sums of incidence coordinates over a set of edges. -/
theorem sum_edgeVec_le_card {V' : Type*} (H : SimpleGraph V') (K : SimpleGraph V')
    (B : Finset H.edgeSet) : sumOver B (edgeVec H K) ≤ (B.card : ℝ) := by
  rw [sumOver_apply, Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
  exact Finset.sum_le_sum fun ε _ => edgeVec_le_one _ _ ε

theorem sum_edgeVec_eq_card_iff {V' : Type*} (H : SimpleGraph V') (K : SimpleGraph V')
    (B : Finset H.edgeSet) :
    sumOver B (edgeVec H K) = (B.card : ℝ) ↔ ∀ ε ∈ B, (ε : Sym2 V') ∈ K.edgeSet := by
  rw [sumOver_apply, Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
  constructor
  · intro h ε hε
    have h0 : ∑ ε ∈ B, (1 - edgeVec H K ε) = 0 := by rw [Finset.sum_sub_distrib, h, sub_self]
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun ε _ => sub_nonneg.mpr
      (edgeVec_le_one _ _ ε))).mp h0 ε hε
    rw [← edgeVec_eq_one_iff]; linarith
  · intro h
    exact Finset.sum_congr rfl fun ε hε => (edgeVec_eq_one_iff _ _ _).mpr (h ε hε)

variable {t₁ t₂ : W}

/-- Lifting an edge set of `G` by adding all pendant edges. -/
def liftPend (K : SimpleGraph W) : SimpleGraph (W ⊕ R) :=
  SimpleGraph.fromRel fun x y => match x, y with
    | .inl a, .inl b => K.Adj a b
    | .inl a, .inr t => a = t.1
    | _, _ => False

theorem liftPend_adj_inl_inl (K : SimpleGraph W) (a b : W) :
    (liftPend (R := R) K).Adj (.inl a) (.inl b) ↔ K.Adj a b := by
  simp only [liftPend, fromRel_adj, ne_eq, Sum.inl.injEq]
  constructor
  · rintro ⟨-, h | h⟩
    · exact h
    · exact h.symm
  · intro h; exact ⟨h.ne, Or.inl h⟩

theorem liftPend_adj_pend (K : SimpleGraph W) (t : R) :
    (liftPend (R := R) K).Adj (.inl t.1) (.inr t) := by
  simp [liftPend, fromRel_adj]

theorem liftPend_spec {K : SimpleGraph W} (hK : IsConnectedSupport G R K) (h₁ : t₁ ∈ R)
    (h₂ : t₂ ∈ R) :
    IsConnectedSupport (pendant G R) {.inl t₁, .inl t₂} (liftPend K) ∧
      (∀ t : R, (pendEdge (G := G) t : Sym2 (W ⊕ R)) ∈ (liftPend K).edgeSet) ∧
      restrictInl (edgeVec (pendant G R) (liftPend K)) = edgeVec G K := by
  classical
  obtain ⟨hKG, hRsupp, hconn⟩ := hK
  have hle : liftPend (R := R) K ≤ pendant G R := by
    rintro (a | t) (b | t') hxy
    · rw [liftPend_adj_inl_inl] at hxy; exact hKG hxy
    · simp only [liftPend, fromRel_adj] at hxy
      obtain ⟨-, h | h⟩ := hxy
      · exact h
      · exact h.elim
    · simp only [liftPend, fromRel_adj] at hxy
      obtain ⟨-, h | h⟩ := hxy
      · exact h.elim
      · exact h
    · simp only [liftPend, fromRel_adj] at hxy
      obtain ⟨-, h | h⟩ := hxy
      · exact h.elim
      · exact h.elim
  -- the hom `inl : K → liftPend K`
  let hom : K →g liftPend (R := R) K := ⟨Sum.inl, fun h => (liftPend_adj_inl_inl K _ _).mpr h⟩
  have hreach : ∀ x ∈ (liftPend (R := R) K).support,
      (liftPend (R := R) K).Reachable (.inl t₁) x := by
    have hroot : ∀ a ∈ K.support, (liftPend (R := R) K).Reachable (.inl t₁) (.inl a) :=
      fun a ha => (hconn t₁ (hRsupp h₁) a ha).map hom
    rintro (a | t) ⟨y, hy⟩
    · rcases y with b | t'
      · exact hroot a ⟨b, (liftPend_adj_inl_inl K a b).mp hy⟩
      · have : a = t'.1 := by
          simp only [liftPend, fromRel_adj] at hy
          obtain ⟨-, h | h⟩ := hy <;> simp_all
        rw [this]; exact hroot _ (hRsupp t'.2)
    · exact (hroot _ (hRsupp t.2)).trans (liftPend_adj_pend K t).reachable
  refine ⟨⟨hle, ?_, ?_⟩, ?_, ?_⟩
  · intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ⟨_, liftPend_adj_pend K ⟨t₁, h₁⟩⟩
    · exact ⟨_, liftPend_adj_pend K ⟨t₂, h₂⟩⟩
  · intro u hu v hv
    exact (hreach u hu).symm.trans (hreach v hv)
  · intro t
    exact liftPend_adj_pend K t
  · funext e
    obtain ⟨e, he⟩ := e
    simp only [restrictInl, LinearMap.funLeft_apply, edgeVec_apply]
    induction e using Sym2.ind with
    | h a b =>
      simp only [Sym2.map_mk, mem_edgeSet, liftPend_adj_inl_inl]

theorem comap_spec {K : SimpleGraph (W ⊕ R)}
    (hK : IsConnectedSupport (pendant G R) {.inl t₁, .inl t₂} K)
    (hpend : ∀ t : R, (pendEdge (G := G) t : Sym2 (W ⊕ R)) ∈ K.edgeSet)
    (h₁ : t₁ ∈ R) (h₂ : t₂ ∈ R) (h12 : t₁ ≠ t₂) :
    IsConnectedSupport G R (K.comap Sum.inl) ∧
      restrictInl (edgeVec (pendant G R) K) = edgeVec G (K.comap Sum.inl) := by
  classical
  obtain ⟨hKle, -, hconn⟩ := hK
  have hinl : ∀ t ∈ R, (.inl t : W ⊕ R) ∈ K.support := fun t ht =>
    ⟨.inr ⟨t, ht⟩, (mem_edgeSet _).mp (hpend ⟨t, ht⟩)⟩
  have hle : K.comap Sum.inl ≤ G := fun a b h => hKle h
  refine ⟨⟨hle, ?_, ?_⟩, ?_⟩
  · intro t ht
    obtain ⟨t', ht', hne⟩ : ∃ t' ∈ R, t' ≠ t := by
      by_cases h : t = t₁
      · exact ⟨t₂, h₂, by rw [h]; exact Ne.symm h12⟩
      · exact ⟨t₁, h₁, Ne.symm h⟩
    obtain ⟨q⟩ := hconn _ (hinl t ht) _ (hinl t' ht')
    have hp := q.bypass_isPath
    have hsupp := path_support_inl hKle q.bypass hp
    have hnil : ¬ q.bypass.Nil := by
      intro h
      have := h.eq
      exact hne (Sum.inl.inj this).symm
    obtain ⟨c, hc⟩ := hsupp _ (q.bypass.getVert_mem_support 1)
    have hadj := q.bypass.adj_snd hnil
    rw [Walk.snd, hc] at hadj
    exact ⟨c, hadj⟩
  · rintro u ⟨c, hc⟩ v ⟨d, hd⟩
    obtain ⟨q⟩ := hconn _ ⟨_, hc⟩ _ ⟨_, hd⟩
    exact reachable_of_walk_inl q.bypass u v rfl rfl (path_support_inl hKle q.bypass q.bypass_isPath)
  · funext e
    obtain ⟨e, he⟩ := e
    simp only [restrictInl, LinearMap.funLeft_apply, edgeVec_apply]
    induction e using Sym2.ind with
    | h a b => simp only [Sym2.map_mk, mem_edgeSet, comap_adj]

theorem pendEdge_mem_pendSet [Fintype R] (t : R) : pendEdge (G := G) t ∈ pendSet (G := G) (R := R) := by
  classical
  simp [pendSet]

/-- **The pendant transfer.** Deleting the pendant coordinates maps the face of
`Pconn (pendant G R) {t₁, t₂}` where all pendant edges are present onto `Pconn G R`. -/
theorem restrictInl_image [Fintype R] (h₁ : t₁ ∈ R) (h₂ : t₂ ∈ R) (h12 : t₁ ≠ t₂) :
    restrictInl '' (Pconn (pendant G R) {.inl t₁, .inl t₂} ∩
      {x | sumOver (pendSet (G := G) (R := R)) x = ((pendSet (G := G) (R := R)).card : ℝ)}) =
      Pconn G R := by
  classical
  unfold Pconn
  rw [convexHull_inter_hyperplane_of_le _ _ (by rintro x ⟨K, -, rfl⟩; exact sum_edgeVec_le_card _ _ _)]
  rw [← LinearMap.coe_toAffineMap, image_convexHull_eq]
  congr 1
  ext y
  simp only [Set.mem_image, Set.mem_inter_iff, Set.mem_ofPred_eq, LinearMap.coe_toAffineMap]
  constructor
  · rintro ⟨_, ⟨⟨K, hK, rfl⟩, hsum⟩, rfl⟩
    have hpend : ∀ t : R, (pendEdge (G := G) t : Sym2 (W ⊕ R)) ∈ K.edgeSet := fun t =>
      (sum_edgeVec_eq_card_iff _ _ _).mp hsum _ (pendEdge_mem_pendSet t)
    obtain ⟨hc, hr⟩ := comap_spec hK hpend h₁ h₂ h12
    exact ⟨_, hc, hr.symm⟩
  · rintro ⟨K, hK, rfl⟩
    obtain ⟨hc, hpend, hr⟩ := liftPend_spec (t₂ := t₂) hK h₁ h₂
    refine ⟨_, ⟨⟨_, hc, rfl⟩, ?_⟩, hr⟩
    rw [sum_edgeVec_eq_card_iff]
    intro ε hε
    simp only [pendSet, Finset.mem_image, Finset.mem_univ, true_and] at hε
    obtain ⟨t, rfl⟩ := hε
    exact hpend t

theorem xc_pconn_le_pendant [Fintype R] (h₁ : t₁ ∈ R) (h₂ : t₂ ∈ R) (h12 : t₁ ≠ t₂) :
    xc (Pconn G R) ≤ xc (Pconn (pendant G R) {.inl t₁, .inl t₂}) := by
  rw [← restrictInl_image h₁ h₂ h12, ← LinearMap.coe_toAffineMap]
  exact (xc_image_le _ _).trans (xc_inter_hyperplane_le _ _ _)

end Lemmata.PlanarSteinerXC
