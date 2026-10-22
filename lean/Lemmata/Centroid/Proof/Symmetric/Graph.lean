module

public import Lemmata.Centroid.Proof.Symmetric.Shadow
public import Lemmata.Centroid.Proof.Combinatorics.Extension

@[expose] public section

namespace Lemmata.Centroid.Symmetric

open Finset

noncomputable section

variable {V : Type*}

def quadricMonomial (i j : V) : Sym V 2 := Sym.cons i (Sym.oneEquiv j)

def cubicMonomial (i j k : V) : Sym V 3 := Sym.cons i (quadricMonomial j k)

theorem quadricMonomial_comm (i j : V) : quadricMonomial i j = quadricMonomial j i := by
  apply Sym.ext
  change i ::ₘ j ::ₘ (0 : Multiset V) = j ::ₘ i ::ₘ 0
  exact Multiset.cons_swap i j 0

theorem cubicMonomial_swap_left (i j k : V) :
    cubicMonomial i j k = cubicMonomial j i k := Sym.cons_swap i j _

theorem cubicMonomial_swap_right (i j k : V) :
    cubicMonomial i j k = cubicMonomial i k j :=
  congrArg (Sym.cons i) (quadricMonomial_comm j k)

@[simp] theorem map_quadricMonomial {W : Type*} (f : V → W) (i j : V) :
    (quadricMonomial i j).map f = quadricMonomial (f i) (f j) := rfl

@[simp] theorem map_cubicMonomial {W : Type*} (f : V → W) (i j k : V) :
    (cubicMonomial i j k).map f = cubicMonomial (f i) (f j) (f k) := rfl

theorem exists_cubicMonomial (s : Sym V 3) : ∃ i j k, s = cubicMonomial i j k := by
  obtain ⟨i, t, rfl⟩ := Sym.exists_eq_cons_of_succ s
  obtain ⟨j, u, rfl⟩ := Sym.exists_eq_cons_of_succ t
  obtain ⟨k, rfl⟩ := Sym.oneEquiv.surjective u
  exact ⟨i, j, k, rfl⟩

theorem equivSym_mk (i j : V) : Sym2.equivSym V s(i, j) = quadricMonomial i j := rfl

def shadowGraph [DecidableEq V] (Q : Finset (Sym2 V)) : SimpleGraph V where
  Adj i j := i ≠ j ∧ s(i, j) ∈ Q
  symm := ⟨by
    intro i j h
    exact ⟨h.1.symm, by simpa only [Sym2.eq_swap] using h.2⟩⟩
  loopless := ⟨by simp⟩

instance [DecidableEq V] (Q : Finset (Sym2 V)) : DecidableRel (shadowGraph Q).Adj := by
  intro i j
  change Decidable (i ≠ j ∧ s(i, j) ∈ Q)
  infer_instance

def shadowLoops [Fintype V] [DecidableEq V] (Q : Finset (Sym2 V)) : Finset V :=
  univ.filter (fun i => s(i, i) ∈ Q)

theorem shadow_edges_loops [Fintype V] [DecidableEq V] (Q : Finset (Sym2 V)) :
    (shadowGraph Q).edgeFinset.card + (shadowLoops Q).card = Q.card := by
  classical
  have hQ : Q = (shadowGraph Q).edgeFinset ∪ (shadowLoops Q).image Sym2.diag := by
    ext e
    refine Sym2.inductionOn e ?_
    intro i j
    constructor
    · intro he
      by_cases h : i = j
      · subst j
        exact Finset.mem_union_right _ (Finset.mem_image.2
          ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, he⟩, rfl⟩)
      · exact Finset.mem_union_left _ (SimpleGraph.mem_edgeFinset.2 ⟨h, he⟩)
    · intro he
      obtain he | he := Finset.mem_union.1 he
      · exact (SimpleGraph.mem_edgeFinset.1 he).2
      · obtain ⟨k, hk, heq⟩ := Finset.mem_image.1 he
        exact heq ▸ (Finset.mem_filter.1 hk).2
  have hdisj : Disjoint (shadowGraph Q).edgeFinset ((shadowLoops Q).image Sym2.diag) := by
    apply Finset.disjoint_left.2
    intro e he hl
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hl
    exact (SimpleGraph.mem_edgeFinset.1 he).1 rfl
  calc
    _ = ((shadowGraph Q).edgeFinset ∪ (shadowLoops Q).image Sym2.diag).card := by
      rw [Finset.card_union_of_disjoint hdisj,
        Finset.card_image_of_injective _ Sym2.diag_injective]
    _ = Q.card := congrArg Finset.card hQ.symm

theorem cubic_pair_mem [DecidableEq V] (C : Finset (Sym V 3)) (Q : Finset (Sym2 V))
    (hQ : ∀ i j k, cubicMonomial i j k ∈ C → s(i, j) ∈ Q)
    {s : Sym V 3} (hs : s ∈ C) {i j : V} (hi : i ∈ s) (hj : j ∈ s) (hij : i ≠ j) :
    s(i, j) ∈ Q := by
  obtain ⟨t, rfl⟩ := Sym.exists_cons_of_mem hi
  have hjt : j ∈ t := (Sym.mem_cons.1 hj).resolve_left (Ne.symm hij)
  obtain ⟨u, rfl⟩ := Sym.exists_cons_of_mem hjt
  obtain ⟨k, rfl⟩ := Sym.oneEquiv.surjective u
  exact hQ i j k hs

theorem cubic_family_bound [Fintype V] [DecidableEq V]
    (C : Finset (Sym V 3)) (Q : Finset (Sym2 V)) (D : Finset V) (δ : Bool)
    (hQ : ∀ i j k, cubicMonomial i j k ∈ C → s(i, j) ∈ Q)
    (hD : ∀ i j, cubicMonomial i i j ∈ C → j ∈ D)
    (hδ : ∀ i, cubicMonomial i i i ∈ C → δ = true) :
    C.card ≤ ((shadowGraph Q).cliqueFinset 3).card +
      (Graph.mixedEdges (shadowGraph Q) (shadowLoops Q) D).card +
      (if δ then (shadowLoops Q ∩ D).card else 0) := by
  classical
  let G := shadowGraph Q
  let A := shadowLoops Q
  let C₀ := C.filter (fun s => s.val.Nodup)
  let C₁ := (Graph.mixedEdges G A D).image (fun p => cubicMonomial p.1 p.1 p.2)
  let C₂ := if δ then (A ∩ D).image (fun i => cubicMonomial i i i) else ∅
  have hsf : C₀.card ≤ (G.cliqueFinset 3).card := by
    have hinj : Set.InjOn (fun s : Sym V 3 => s.val.toFinset) C₀ := by
      intro s hs t ht he
      exact Sym.ext ((Finset.mem_filter.1 hs).2.toFinset_inj
        (Finset.mem_filter.1 ht).2 he)
    have hsub : C₀.image (fun s => s.val.toFinset) ⊆ G.cliqueFinset 3 := by
      intro t ht
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 ht
      obtain ⟨hsC, hsN⟩ := Finset.mem_filter.1 hs
      apply SimpleGraph.mem_cliqueFinset_iff.2
      refine ⟨?_, (Multiset.toFinset_card_of_nodup hsN).trans s.property⟩
      intro i hi j hj hij
      exact ⟨hij, cubic_pair_mem C Q hQ hsC (by simpa using hi) (by simpa using hj) hij⟩
    have h := Finset.card_le_card hsub
    rwa [Finset.card_image_of_injOn hinj] at h
  have hrepeat (i j : V) (hc : cubicMonomial i i j ∈ C) :
      cubicMonomial i i j ∈ C₁ ∪ C₂ := by
    have hi : i ∈ A := Finset.mem_filter.2 ⟨Finset.mem_univ _, hQ i i j hc⟩
    have hj : j ∈ D := hD i j hc
    by_cases hij : i = j
    · subst j
      apply Finset.mem_union_right
      have hδi := hδ i hc
      simp only [C₂, hδi, ite_true]
      exact Finset.mem_image.2 ⟨i, Finset.mem_inter.2 ⟨hi, hj⟩, rfl⟩
    · apply Finset.mem_union_left
      apply Finset.mem_image.2
      refine ⟨(i, j), Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hi, hj⟩, ?_⟩, rfl⟩
      refine ⟨hij, hQ i j i ?_⟩
      rwa [cubicMonomial_swap_right i j i]
  have hcover : C ⊆ C₀ ∪ (C₁ ∪ C₂) := by
    intro s hs
    obtain ⟨i, j, k, rfl⟩ := exists_cubicMonomial s
    by_cases hij : i = j
    · subst j
      exact Finset.mem_union_right _ (hrepeat i k hs)
    by_cases hik : i = k
    · subst k
      rw [cubicMonomial_swap_right i j i] at hs ⊢
      exact Finset.mem_union_right _ (hrepeat i j hs)
    by_cases hjk : j = k
    · subst k
      rw [cubicMonomial_swap_left i j j, cubicMonomial_swap_right j i j] at hs ⊢
      exact Finset.mem_union_right _ (hrepeat j i hs)
    · apply Finset.mem_union_left
      apply Finset.mem_filter.2
      refine ⟨hs, ?_⟩
      change (i ::ₘ j ::ₘ k ::ₘ (0 : Multiset V)).Nodup
      simp [hij, hik, hjk]
  have hC := Finset.card_le_card hcover
  have hU := Finset.card_union_le C₀ (C₁ ∪ C₂)
  have hU' := Finset.card_union_le C₁ C₂
  have hC₁ : C₁.card ≤ (Graph.mixedEdges G A D).card := Finset.card_image_le
  have hC₂ : C₂.card ≤ if δ then (A ∩ D).card else 0 := by
    cases δ
    · simp [C₂]
    · exact Finset.card_image_le
  change C.card ≤ (G.cliqueFinset 3).card + (Graph.mixedEdges G A D).card +
    (if δ then (A ∩ D).card else 0)
  omega

theorem cubic_shadow_bound [Fintype V] [LinearOrder V]
    (C : Finset (Sym V 3)) (Q : Finset (Sym2 V)) (D : Finset V) (δ : Bool)
    (hQ : ∀ i j k, cubicMonomial i j k ∈ C → s(i, j) ∈ Q)
    (hD : ∀ i j, cubicMonomial i i j ∈ C → j ∈ D)
    (hδ : ∀ i, cubicMonomial i i i ∈ C → δ = true) :
    C.card + Q.card + D.card + (if δ then 1 else 0) ≤
      triangleBound (Fintype.card V + Q.card + D.card + (if δ then 1 else 0) + 2) := by
  have hf := cubic_family_bound C Q D δ hQ hD hδ
  have hg := Graph.three_vertex_bound (shadowGraph Q) (shadowLoops Q) D δ
  have hcount := shadow_edges_loops Q
  rw [Nat.add_assoc (Fintype.card V), hcount] at hg
  omega

theorem cubic_shadow_bound_sym [Fintype V] [LinearOrder V]
    (C : Finset (Sym V 3)) (Q : Finset (Sym V 2)) (D : Finset V) (δ : Bool)
    (hQ : ∀ i j k, cubicMonomial i j k ∈ C → quadricMonomial i j ∈ Q)
    (hD : ∀ i j, cubicMonomial i i j ∈ C → j ∈ D)
    (hδ : ∀ i, cubicMonomial i i i ∈ C → δ = true) :
    C.card + Q.card + D.card + (if δ then 1 else 0) ≤
      triangleBound (Fintype.card V + Q.card + D.card + (if δ then 1 else 0) + 2) := by
  classical
  let E := Q.image (Sym2.equivSym V).symm
  have hE : E.card = Q.card := Finset.card_image_of_injective _ (Sym2.equivSym V).symm.injective
  have hQE : ∀ i j k, cubicMonomial i j k ∈ C → s(i, j) ∈ E := by
    intro i j k hc
    apply Finset.mem_image.2
    refine ⟨quadricMonomial i j, hQ i j k hc, ?_⟩
    apply (Sym2.equivSym V).injective
    simp only [Equiv.apply_symm_apply, equivSym_mk]
  simpa only [hE] using cubic_shadow_bound C E D δ hQE hD hδ

theorem card_preimage_sym [DecidableEq V] (R : Finset V) {d : ℕ} (C : Finset (Sym V d))
    (hC : ∀ s ∈ C, ∀ i ∈ s, i ∈ R) :
    (C.preimage (Sym.map (Subtype.val : R → V))
      (Sym.map_injective Subtype.val_injective d).injOn).card = C.card := by
  classical
  rw [Finset.card_preimage]
  apply congrArg Finset.card
  apply Finset.filter_eq_self.2
  intro s hs
  let t : Sym R d := s.attach.map (fun i => ⟨i.val, hC s hs i.val i.property⟩)
  refine ⟨t, ?_⟩
  calc
    t.map Subtype.val = s.attach.map Subtype.val := by
      rw [Sym.map_map]
      rfl
    _ = s := Sym.attach_map_coe s

variable {F I : Type*} [Field F] [Fintype I] [DecidableEq I]

def leadingVariables (m : MonomialOrder I) (S : Submodule F (Coefficients F I 3)) : Finset I :=
  let _ := coefficientOrder m 1
  (Linear.leadingPositions (oneSupport S)).image Sym.oneEquiv.symm

def leadingDoubleVariables (m : MonomialOrder I) (S : Submodule F (Coefficients F I 3)) : Finset I :=
  let _ := coefficientOrder m 1
  (Linear.leadingPositions (doubleShadow S)).image Sym.oneEquiv.symm

theorem mem_leadingVariables (m : MonomialOrder I) (S : Submodule F (Coefficients F I 3)) (i : I) :
    i ∈ leadingVariables m S ↔
      let _ := coefficientOrder m 1
      Linear.IsLeading (oneSupport S) (Sym.oneEquiv i) := by
  let _ := coefficientOrder m 1
  change i ∈ (Linear.leadingPositions (oneSupport S)).image Sym.oneEquiv.symm ↔ _
  constructor
  · intro hi
    obtain ⟨s, hs, he⟩ := Finset.mem_image.1 hi
    have hs' := (Linear.mem_leadingPositions _ _).1 hs
    have hsi : s = Sym.oneEquiv i := by simp only [← he, Equiv.apply_symm_apply]
    rwa [hsi] at hs'
  · intro h
    exact Finset.mem_image.2 ⟨Sym.oneEquiv i, (Linear.mem_leadingPositions _ _).2 h,
      Equiv.symm_apply_apply _ _⟩

theorem mem_leadingDoubleVariables (m : MonomialOrder I)
    (S : Submodule F (Coefficients F I 3)) (i : I) :
    i ∈ leadingDoubleVariables m S ↔
      let _ := coefficientOrder m 1
      Linear.IsLeading (doubleShadow S) (Sym.oneEquiv i) := by
  let _ := coefficientOrder m 1
  change i ∈ (Linear.leadingPositions (doubleShadow S)).image Sym.oneEquiv.symm ↔ _
  constructor
  · intro hi
    obtain ⟨s, hs, he⟩ := Finset.mem_image.1 hi
    have hs' := (Linear.mem_leadingPositions _ _).1 hs
    have hsi : s = Sym.oneEquiv i := by simp only [← he, Equiv.apply_symm_apply]
    rwa [hsi] at hs'
  · intro h
    exact Finset.mem_image.2 ⟨Sym.oneEquiv i, (Linear.mem_leadingPositions _ _).2 h,
      Equiv.symm_apply_apply _ _⟩

theorem card_leadingVariables (m : MonomialOrder I) (S : Submodule F (Coefficients F I 3)) :
    (leadingVariables m S).card = Module.finrank F (oneSupport S) := by
  let _ := coefficientOrder m 1
  rw [leadingVariables, Finset.card_image_of_injective _ Sym.oneEquiv.symm.injective]
  exact Linear.card_leadingPositions _

theorem card_leadingDoubleVariables (m : MonomialOrder I) (S : Submodule F (Coefficients F I 3)) :
    (leadingDoubleVariables m S).card = Module.finrank F (doubleShadow S) := by
  let _ := coefficientOrder m 1
  rw [leadingDoubleVariables, Finset.card_image_of_injective _ Sym.oneEquiv.symm.injective]
  exact Linear.card_leadingPositions _

theorem leadingDoubleVariables_subset (m : MonomialOrder I)
    (S : Submodule F (Coefficients F I 3)) : leadingDoubleVariables m S ⊆ leadingVariables m S := by
  let _ := coefficientOrder m 1
  intro i hi
  exact (mem_leadingVariables m S i).2
    (((mem_leadingDoubleVariables m S i).1 hi).mono (doubleShadow_le_oneSupport S))

theorem leading_pair (m : MonomialOrder I) (S : Submodule F (Coefficients F I 3))
    (i j k : I) (h : cubicMonomial i j k ∈ leadingCubics m S) :
    quadricMonomial i j ∈ leadingQuadrics m S := by
  apply leading_divisor m S k
  change cubicMonomial k i j ∈ leadingCubics m S
  rwa [cubicMonomial_swap_left k i j, cubicMonomial_swap_right i k j]

theorem leading_quadric_variable (m : MonomialOrder I)
    (S : Submodule F (Coefficients F I 3)) (i j : I)
    (h : quadricMonomial i j ∈ leadingQuadrics m S) : i ∈ leadingVariables m S := by
  let _ := coefficientOrder m 1
  let _ := coefficientOrder m 2
  apply (mem_leadingVariables m S i).2
  rw [quadricMonomial_comm] at h
  have hl : Linear.IsLeading (quadraticShadow S) (Sym.cons j (Sym.oneEquiv i)) :=
    (Linear.mem_leadingPositions _ _).1 h
  apply (hl.pullback (cons_strictMono m 1 j)).mono
  rintro v ⟨q, hq, rfl⟩
  exact Submodule.mem_iSup_of_mem j ⟨q, hq, rfl⟩

theorem leading_repeated (m : MonomialOrder I) (S : Submodule F (Coefficients F I 3))
    (i j : I) (h : cubicMonomial i i j ∈ leadingCubics m S) :
    j ∈ leadingDoubleVariables m S := by
  let _ := coefficientOrder m 1
  let _ := coefficientOrder m 2
  let _ := coefficientOrder m 3
  have hl : Linear.IsLeading S (Sym.cons i (Sym.cons i (Sym.oneEquiv j))) :=
    (Linear.mem_leadingPositions _ _).1 h
  apply (mem_leadingDoubleVariables m S j).2
  apply ((hl.pullback (cons_strictMono m 2 i)).pullback (cons_strictMono m 1 i)).mono
  rintro v ⟨q, ⟨c, hc, rfl⟩, rfl⟩
  apply Submodule.subset_span
  refine ⟨fun k => if k = i then 1 else 0, c, hc, ?_⟩
  simp only [contraction_delta]
  rfl

theorem leading_pure (m : MonomialOrder I) (S : Submodule F (Coefficients F I 3))
    (i : I) (h : cubicMonomial i i i ∈ leadingCubics m S) :
    Module.finrank F (tripleShadow S) = 1 := by
  let _ := coefficientOrder m 3
  obtain ⟨c, hc, hci, _⟩ := (Linear.mem_leadingPositions _ _).1 h
  let w := contractCoordinate i (contractCoordinate i (contractCoordinate i c))
  have hw : w ∈ tripleShadow S := by
    apply Submodule.subset_span
    refine ⟨fun k => if k = i then 1 else 0, c, hc, ?_⟩
    simp only [contraction_delta]
    rfl
  have hwne : w ≠ 0 := by
    intro hw0
    have hzero := congrFun hw0 (0 : Sym I 0)
    exact hci hzero
  have hdim : Module.finrank F (tripleShadow S) ≠ 0 := by
    intro hd
    have hb := Submodule.finrank_eq_zero.1 hd
    exact hwne ((Submodule.mem_bot F).1 (hb ▸ hw))
  have hle := finrank_tripleShadow_le_one S
  omega

theorem leading_quadric_support (m : MonomialOrder I)
    (S : Submodule F (Coefficients F I 3)) {q : Sym I 2}
    (hq : q ∈ leadingQuadrics m S) {i : I} (hi : i ∈ q) : i ∈ leadingVariables m S := by
  obtain ⟨j, u, rfl⟩ := Sym.exists_eq_cons_of_succ q
  obtain ⟨k, rfl⟩ := Sym.oneEquiv.surjective u
  change quadricMonomial j k ∈ leadingQuadrics m S at hq
  have hi' : i = j ∨ i = k := by
    change i ∈ j ::ₘ k ::ₘ (0 : Multiset I) at hi
    simpa using hi
  obtain hij | hik := hi'
  · subst i
    exact leading_quadric_variable m S j k hq
  · subst i
    rw [quadricMonomial_comm] at hq
    exact leading_quadric_variable m S k j hq

theorem leading_cubic_support (m : MonomialOrder I)
    (S : Submodule F (Coefficients F I 3)) {s : Sym I 3}
    (hs : s ∈ leadingCubics m S) {i : I} (hi : i ∈ s) : i ∈ leadingVariables m S := by
  obtain ⟨j, k, l, rfl⟩ := exists_cubicMonomial s
  have hi' : i = j ∨ i = k ∨ i = l := by
    change i ∈ j ::ₘ k ::ₘ l ::ₘ (0 : Multiset I) at hi
    simpa using hi
  obtain hij | hik | hil := hi'
  · subst i
    exact leading_quadric_variable m S j k (leading_pair m S j k l hs)
  · subst i
    apply leading_quadric_variable m S k j
    rw [quadricMonomial_comm]
    exact leading_pair m S j k l hs
  · subst i
    apply leading_quadric_variable m S l j
    apply leading_pair m S l j k
    rwa [cubicMonomial_swap_left l j k, cubicMonomial_swap_right j l k]

theorem symmetric_graph_bound (m : MonomialOrder I)
    (S : Submodule F (Coefficients F I 3)) :
    Module.finrank F S + Module.finrank F (quadraticShadow S) +
      Module.finrank F (doubleShadow S) + Module.finrank F (tripleShadow S) ≤
      triangleBound (Module.finrank F (oneSupport S) + Module.finrank F (quadraticShadow S) +
        Module.finrank F (doubleShadow S) + Module.finrank F (tripleShadow S) + 2) := by
  classical
  let _ : LinearOrder I := LinearOrder.lift'
    (fun i => monomialIndex m (Sym.oneEquiv i))
    (fun _ _ h => Sym.oneEquiv.injective (monomialIndex_injective m 1 h))
  let R := leadingVariables m S
  let C := leadingCubics m S
  let Q := leadingQuadrics m S
  let D := leadingDoubleVariables m S
  let C' : Finset (Sym R 3) := C.preimage (Sym.map Subtype.val)
    (Sym.map_injective Subtype.val_injective 3).injOn
  let Q' : Finset (Sym R 2) := Q.preimage (Sym.map Subtype.val)
    (Sym.map_injective Subtype.val_injective 2).injOn
  let D' : Finset R := D.preimage Subtype.val Subtype.val_injective.injOn
  let δ := decide (Module.finrank F (tripleShadow S) = 1)
  have hRcard : R.card = Module.finrank F (oneSupport S) := card_leadingVariables m S
  have hCcard : C'.card = Module.finrank F S := by
    exact (card_preimage_sym R C (fun _ hs _ hi => leading_cubic_support m S hs hi)).trans
      (card_leadingCubics m S)
  have hQcard : Q'.card = Module.finrank F (quadraticShadow S) := by
    exact (card_preimage_sym R Q (fun _ hs _ hi => leading_quadric_support m S hs hi)).trans
      (card_leadingQuadrics m S)
  have hDcard : D'.card = Module.finrank F (doubleShadow S) := by
    have h : D'.card = D.card := by
      rw [Finset.card_preimage]
      apply congrArg Finset.card
      apply Finset.filter_eq_self.2
      intro i hi
      exact ⟨⟨i, leadingDoubleVariables_subset m S hi⟩, rfl⟩
    exact h.trans (card_leadingDoubleVariables m S)
  have hδcount : (if δ then 1 else 0) = Module.finrank F (tripleShadow S) := by
    have hle := finrank_tripleShadow_le_one S
    by_cases hd : Module.finrank F (tripleShadow S) = 1
    · simp [δ, hd]
    · have hz : Module.finrank F (tripleShadow S) = 0 := by omega
      simp [δ, hz]
  have hQ' : ∀ i j k, cubicMonomial i j k ∈ C' → quadricMonomial i j ∈ Q' := by
    intro i j k hc
    have hc' := Finset.mem_preimage.1 hc
    rw [map_cubicMonomial] at hc'
    apply Finset.mem_preimage.2
    rw [map_quadricMonomial]
    exact leading_pair m S i.val j.val k.val hc'
  have hD' : ∀ i j, cubicMonomial i i j ∈ C' → j ∈ D' := by
    intro i j hc
    have hc' := Finset.mem_preimage.1 hc
    rw [map_cubicMonomial] at hc'
    exact Finset.mem_preimage.2 (leading_repeated m S i.val j.val hc')
  have hδ' : ∀ i, cubicMonomial i i i ∈ C' → δ = true := by
    intro i hc
    have hc' := Finset.mem_preimage.1 hc
    rw [map_cubicMonomial] at hc'
    simp only [δ, leading_pure m S i.val hc', decide_true]
  have hg := cubic_shadow_bound_sym C' Q' D' δ hQ' hD' hδ'
  simpa only [hCcard, hQcard, hDcard, hδcount, Fintype.card_coe, hRcard] using hg

theorem graph_bound (S : Submodule F (Coefficients F I 3)) :
    Module.finrank F S + Module.finrank F (quadraticShadow S) +
      Module.finrank F (doubleShadow S) + Module.finrank F (tripleShadow S) ≤
      triangleBound (Module.finrank F (oneSupport S) + Module.finrank F (quadraticShadow S) +
        Module.finrank F (doubleShadow S) + Module.finrank F (tripleShadow S) + 2) := by
  let _ : LinearOrder I := LinearOrder.lift' (Fintype.equivFin I) (Fintype.equivFin I).injective
  exact symmetric_graph_bound MonomialOrder.lex S

end

end Lemmata.Centroid.Symmetric
