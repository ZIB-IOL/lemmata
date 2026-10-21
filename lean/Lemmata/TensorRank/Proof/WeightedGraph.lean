module

public import Lemmata.TensorRank.Def.WeightedGraph
public import Lemmata.TensorRank.Proof.GraphRank
public import Lemmata.TensorRank.Proof.Asymptotic
public import Lemmata.TensorRank.Proof.Parties
public import Lemmata.TensorRank.Proof.IndexedProduct

@[expose] public section

set_option autoImplicit false

open scoped BigOperators
open Classical

namespace Lemmata.TensorRank

@[simp] theorem card_edge (k : ℕ) : Fintype.card (Edge k) = k.choose 2 := by
  simp [Edge]

theorem edge_incident_pair {k : ℕ} (i : Fin k) (e : Incident k i) :
    ∃ j : Neighbors i, e.val = edgeBetween i j.val j.prop := by
  obtain ⟨a, b, hab, he⟩ := Finset.card_eq_two.mp e.val.prop
  have hi : i = a ∨ i = b := by simpa [he] using e.prop
  rcases hi with rfl | rfl
  · exact ⟨⟨b, Ne.symm hab⟩, Subtype.ext he⟩
  · refine ⟨⟨a, hab⟩, Subtype.ext ?_⟩
    simpa only [edgeBetween, Finset.pair_comm] using he

noncomputable def neighborIncident {k : ℕ} (i : Fin k) : Neighbors i ≃ Incident k i :=
  Equiv.ofBijective (fun j => ⟨edgeBetween i j.val j.prop, by simp [edgeBetween]⟩) (by
    constructor
    · intro a b hab
      have he : ({i, a.val} : Finset (Fin k)) = {i, b.val} := congrArg (fun e => e.val.val) hab
      have hm : a.val = i ∨ a.val = b.val := by
        have hm : a.val ∈ ({i, b.val} : Finset (Fin k)) := by rw [← he]; simp
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
      exact Subtype.ext (hm.resolve_left a.prop)
    · intro e
      obtain ⟨j, hj⟩ := edge_incident_pair i e
      exact ⟨j, Subtype.ext hj.symm⟩)

@[simp] theorem neighborIncident_val {k : ℕ} (i : Fin k) (j : Neighbors i) :
    (neighborIncident i j).val = edgeBetween i j.val j.prop := rfl

noncomputable def constantCoordinate {k n : ℕ} (i : Fin k) :
    WeightedCoordinate (fun _ : Edge k => n) i ≃ GraphCoordinate k n i :=
  (Equiv.piCongrLeft (fun _ : Incident k i => Fin n) (neighborIncident i)).symm

theorem weighted_constant_reindex (k n : ℕ) :
    Tensor.reindex (fun i => (constantCoordinate (n := n) i).symm)
      (weightedComplete (fun _ : Edge k => n)) = completeGraph k n := by
  funext x
  have hx (i : Fin k) (e : Incident k i) :
      (constantCoordinate (n := n) i).symm (x i) e =
        x i ((neighborIncident i).symm e) := by
          obtain ⟨j, rfl⟩ := (neighborIncident i).surjective e
          simp [constantCoordinate]
  have hc : (∀ (e : Edge k) (i j : Fin k) (hi : i ∈ e.val) (hj : j ∈ e.val),
      x i ((neighborIncident i).symm ⟨e, hi⟩) = x j ((neighborIncident j).symm ⟨e, hj⟩)) ↔
      ∀ (i j : Fin k) (h : i ≠ j), x i ⟨j, h.symm⟩ = x j ⟨i, h⟩ := by
    constructor
    · intro h i j hij
      let e := edgeBetween i j hij.symm
      have hi : i ∈ e.val := by simp [e, edgeBetween]
      have hj : j ∈ e.val := by simp [e, edgeBetween]
      have hai : (neighborIncident i).symm ⟨e, hi⟩ = ⟨j, hij.symm⟩ := by
        apply (neighborIncident i).injective
        simp only [Equiv.apply_symm_apply]
        apply Subtype.ext
        rfl
      have haj : (neighborIncident j).symm ⟨e, hj⟩ = ⟨i, hij⟩ := by
        apply (neighborIncident j).injective
        apply Subtype.ext
        apply Subtype.ext
        simp [e, edgeBetween, Finset.pair_comm]
      simpa only [hai, haj] using h e i j hi hj
    · intro h e i j hi hj
      by_cases hij : i = j
      · subst j
        rfl
      · have he : e = edgeBetween i j (Ne.symm hij) := by
          apply Subtype.ext
          symm
          apply Finset.eq_of_subset_of_card_le
          · intro a ha
            simp only [edgeBetween, Finset.mem_insert, Finset.mem_singleton] at ha
            rcases ha with rfl | rfl <;> assumption
          · simp [edgeBetween, e.prop, hij]
        subst e
        have hai : (neighborIncident i).symm ⟨edgeBetween i j (Ne.symm hij), hi⟩ = ⟨j, Ne.symm hij⟩ := by
          apply (neighborIncident i).injective
          simp only [Equiv.apply_symm_apply]
          apply Subtype.ext
          rfl
        have haj : (neighborIncident j).symm ⟨edgeBetween i j (Ne.symm hij), hj⟩ = ⟨i, hij⟩ := by
          apply (neighborIncident j).injective
          apply Subtype.ext
          apply Subtype.ext
          simp [edgeBetween, Finset.pair_comm]
        simpa only [hai, haj] using h i j hij
  change (if ∀ (e : Edge k) (i j : Fin k) (hi : i ∈ e.val) (hj : j ∈ e.val),
    (constantCoordinate (n := n) i).symm (x i) ⟨e, hi⟩ =
      (constantCoordinate (n := n) j).symm (x j) ⟨e, hj⟩ then (1 : ℂ) else 0) = _
  simp only [hx, hc, completeGraph]

theorem rank_weighted_constant (k n : ℕ) :
    Tensor.rank (weightedComplete (fun _ : Edge k => n)) = Tensor.rank (completeGraph k n) := by
  rw [← weighted_constant_reindex, Tensor.rank_reindex]

theorem asymptoticRank_weighted_constant (k n : ℕ) :
    Tensor.asymptoticRank (weightedComplete (fun _ : Edge k => n)) =
      Tensor.asymptoticRank (completeGraph k n) := by
  rw [← weighted_constant_reindex, Tensor.asymptoticRank_reindex]

theorem weighted_padding {k : ℕ} {d e : Edge k → ℕ} (hde : ∀ a, d a ≤ e a) :
    Tensor.reindex (fun i (x : WeightedCoordinate d i) a => Fin.castLE (hde a.val) (x a))
      (weightedComplete e) = weightedComplete d := by
  funext x
  change (if ∀ (a : Edge k) (i j : Fin k) (hi : i ∈ a.val) (hj : j ∈ a.val),
    Fin.castLE (hde a) (x i ⟨a, hi⟩) = Fin.castLE (hde a) (x j ⟨a, hj⟩)
    then (1 : ℂ) else 0) = _
  simp only [Fin.castLE_inj, weightedComplete]

theorem asymptoticRank_weighted_mono {k : ℕ} {d e : Edge k → ℕ} (hde : ∀ a, d a ≤ e a) :
    Tensor.asymptoticRank (weightedComplete d) ≤ Tensor.asymptoticRank (weightedComplete e) := by
  have h := (Tensor.reindex_restricts
    (fun i (x : WeightedCoordinate d i) a => Fin.castLE (hde a.val) (x a))
    (weightedComplete e)).asymptoticRank_le
  rwa [weighted_padding] at h

noncomputable def weightedProductCoordinate {k : ℕ} (d e : Edge k → ℕ) (i : Fin k) :
    (WeightedCoordinate d i × WeightedCoordinate e i) ≃ WeightedCoordinate (fun a => d a * e a) i where
  toFun x a := finProdFinEquiv (x.1 a, x.2 a)
  invFun x := (fun a => (finProdFinEquiv.symm (x a)).1, fun a => (finProdFinEquiv.symm (x a)).2)
  left_inv x := by apply Prod.ext <;> funext a <;> simp
  right_inv x := by funext a; exact finProdFinEquiv.apply_symm_apply (x a)

theorem weighted_product_reindex {k : ℕ} (d e : Edge k → ℕ) :
    Tensor.reindex (fun i => weightedProductCoordinate d e i) (weightedComplete (fun a => d a * e a)) =
      Tensor.product (weightedComplete d) (weightedComplete e) := by
  funext x
  simp only [Tensor.reindex, weightedComplete, weightedProductCoordinate, Equiv.coe_fn_mk,
    Tensor.product, finProdFinEquiv.injective.eq_iff, Prod.mk.injEq, forall_and]
  rw [ite_and]
  split_ifs <;> simp_all only [mul_one, mul_zero]

theorem asymptoticRank_weighted_product_le {k : ℕ} (d e : Edge k → ℕ) :
    Tensor.asymptoticRank (weightedComplete (fun a => d a * e a)) ≤
      Tensor.asymptoticRank (weightedComplete d) * Tensor.asymptoticRank (weightedComplete e) := by
  have h := Tensor.asymptoticRank_reindex (weightedProductCoordinate d e)
    (weightedComplete (fun a => d a * e a))
  rw [weighted_product_reindex] at h
  rw [← h]
  exact Tensor.asymptoticRank_product_le _ _

noncomputable def weightedWord (n q : ℕ) : (Fin q → Fin n) ≃ Fin (n ^ q) :=
  Fintype.equivFinOfCardEq (by simp)

noncomputable def weightedPowerCoordinate {k : ℕ} (d : Edge k → ℕ) (q : ℕ) (i : Fin k) :
    (Fin q → WeightedCoordinate d i) ≃ WeightedCoordinate (fun a => d a ^ q) i where
  toFun x a := weightedWord (d a.val) q (fun t => x t a)
  invFun x t a := (weightedWord (d a.val) q).symm (x a) t
  left_inv x := by funext t a; simp
  right_inv x := by funext a; simp

theorem weighted_power_reindex {k : ℕ} (d : Edge k → ℕ) (q : ℕ) :
    Tensor.reindex (fun i => weightedPowerCoordinate d q i) (weightedComplete (fun a => d a ^ q)) =
      Tensor.power (weightedComplete d) q := by
  funext x
  have hc : (∀ (a : Edge k) (i j : Fin k) (hi : i ∈ a.val) (hj : j ∈ a.val),
      weightedWord (d a) q (fun t => x i t ⟨a, hi⟩) =
        weightedWord (d a) q (fun t => x j t ⟨a, hj⟩)) ↔
      ∀ t, ∀ (a : Edge k) (i j : Fin k) (hi : i ∈ a.val) (hj : j ∈ a.val),
        x i t ⟨a, hi⟩ = x j t ⟨a, hj⟩ := by
    constructor
    · intro h t a i j hi hj
      exact congrFun ((weightedWord (d a) q).injective (h a i j hi hj)) t
    · intro h a i j hi hj
      congr 1
      funext t
      exact h t a i j hi hj
  change (if ∀ (a : Edge k) (i j : Fin k) (hi : i ∈ a.val) (hj : j ∈ a.val),
    weightedWord (d a) q (fun t => x i t ⟨a, hi⟩) = weightedWord (d a) q (fun t => x j t ⟨a, hj⟩)
    then (1 : ℂ) else 0) = _
  simp only [Tensor.power, weightedComplete, Fintype.prod_boole, hc]
  split_ifs <;> rfl

theorem rank_weighted_power {k : ℕ} (d : Edge k → ℕ) (q : ℕ) :
    Tensor.rank (weightedComplete (fun a => d a ^ q)) =
      Tensor.rank (Tensor.power (weightedComplete d) q) := by
  rw [← weighted_power_reindex, Tensor.rank_reindex]

theorem asymptoticRank_weighted_power {k : ℕ} (d : Edge k → ℕ) (q : ℕ) :
    Tensor.asymptoticRank (weightedComplete (fun a => d a ^ q)) =
      Tensor.asymptoticRank (weightedComplete d) ^ q := by
  have h := Tensor.asymptoticRank_reindex (weightedPowerCoordinate d q)
    (weightedComplete (fun a => d a ^ q))
  rw [weighted_power_reindex, Tensor.asymptoticRank_power] at h
  exact h.symm

noncomputable def incidentMap {k : ℕ} (σ : Equiv.Perm (Fin k)) (i : Fin k) :
    Incident k i ≃ Incident k (σ i) :=
  (edgeMap σ).subtypeEquiv (fun e => by simp [edgeMap])

noncomputable def weightedRelabelCoordinate {k : ℕ} (d : Edge k → ℕ)
    (σ : Equiv.Perm (Fin k)) (i : Fin k) :
    WeightedCoordinate d (σ i) ≃ WeightedCoordinate (fun e => d (edgeMap σ e)) i :=
  (Equiv.piCongrLeft (fun e : Incident k (σ i) => Fin (d e.val)) (incidentMap σ i)).symm

private theorem weighted_matching_relabel {k : ℕ} (d : Edge k → ℕ)
    (σ : Equiv.Perm (Fin k)) (x : ∀ i, WeightedCoordinate d (σ i)) :
    (∀ (e : Edge k) (i j : Fin k) (hi : i ∈ e.val) (hj : j ∈ e.val),
      x i (incidentMap σ i ⟨e, hi⟩) = x j (incidentMap σ j ⟨e, hj⟩)) ↔
    ∀ (e : Edge k) (i j : Fin k) (hi : i ∈ e.val) (hj : j ∈ e.val),
      Equiv.piCongrLeft (WeightedCoordinate d) σ x i ⟨e, hi⟩ =
        Equiv.piCongrLeft (WeightedCoordinate d) σ x j ⟨e, hj⟩ := by
  constructor
  · intro h e i j hi hj
    obtain ⟨a, rfl⟩ := (edgeMap σ).surjective e
    obtain ⟨u, rfl⟩ := σ.surjective i
    obtain ⟨v, rfl⟩ := σ.surjective j
    have hu : u ∈ a.val := by simpa [edgeMap] using hi
    have hv : v ∈ a.val := by simpa [edgeMap] using hj
    simpa only [Equiv.piCongrLeft_apply_apply, incidentMap, Equiv.subtypeEquiv,
      Equiv.coe_fn_mk] using h a u v hu hv
  · intro h e i j hi hj
    have hi' : σ i ∈ (edgeMap σ e).val := by simpa [edgeMap] using hi
    have hj' : σ j ∈ (edgeMap σ e).val := by simpa [edgeMap] using hj
    simpa only [Equiv.piCongrLeft_apply_apply, incidentMap, Equiv.subtypeEquiv,
      Equiv.coe_fn_mk] using
      h (edgeMap σ e) (σ i) (σ j) hi' hj'

private theorem weightedRelabelCoordinate_apply {k : ℕ} (d : Edge k → ℕ)
    (σ : Equiv.Perm (Fin k)) (i : Fin k) (x : WeightedCoordinate d (σ i))
    (a : Incident k i) : weightedRelabelCoordinate d σ i x a = x (incidentMap σ i a) :=
  Equiv.piCongrLeft_symm_apply _ _ _ _

theorem weighted_relabel_reindex {k : ℕ} (d : Edge k → ℕ) (σ : Equiv.Perm (Fin k)) :
    Tensor.reindex (fun i => weightedRelabelCoordinate d σ i)
      (weightedComplete (fun e => d (edgeMap σ e))) = Tensor.relabel σ (weightedComplete d) := by
  funext x
  change (if ∀ (e : Edge k) (i j : Fin k) (hi : i ∈ e.val) (hj : j ∈ e.val),
    (weightedRelabelCoordinate d σ i (x i)) ⟨e, hi⟩ =
      (weightedRelabelCoordinate d σ j (x j)) ⟨e, hj⟩ then (1 : ℂ) else 0) = _
  simp only [weightedRelabelCoordinate_apply, Tensor.relabel, weightedComplete]
  exact if_congr (weighted_matching_relabel d σ x) rfl rfl

theorem asymptoticRank_weighted_relabel {k : ℕ} (d : Edge k → ℕ)
    (σ : Equiv.Perm (Fin k)) :
    Tensor.asymptoticRank (weightedComplete (fun e => d (edgeMap σ e))) =
      Tensor.asymptoticRank (weightedComplete d) := by
  have h := Tensor.asymptoticRank_reindex (weightedRelabelCoordinate d σ)
    (weightedComplete (fun e => d (edgeMap σ e)))
  rw [weighted_relabel_reindex] at h
  exact h.symm.trans (Tensor.asymptoticRank_relabel σ (weightedComplete d))

noncomputable def weightedTuple {J : Type*} [Fintype J] (d : J → ℕ) :
    (∀ j, Fin (d j)) ≃ Fin (∏ j, d j) :=
  Fintype.equivFinOfCardEq (by simp)

noncomputable def weightedIndexedCoordinate {k : ℕ} {J : Type*} [Fintype J]
    (d : J → Edge k → ℕ) (i : Fin k) :
    (∀ j, WeightedCoordinate (d j) i) ≃ WeightedCoordinate (fun e => ∏ j, d j e) i where
  toFun x a := weightedTuple (fun j => d j a.val) (fun j => x j a)
  invFun x j a := (weightedTuple (fun j => d j a.val)).symm (x a) j
  left_inv x := by funext j a; simp
  right_inv x := by funext a; simp

theorem weighted_indexedProduct_reindex {k : ℕ} {J : Type*} [Fintype J]
    (d : J → Edge k → ℕ) :
    Tensor.reindex (fun i => weightedIndexedCoordinate d i)
      (weightedComplete (fun e => ∏ j, d j e)) =
      Tensor.indexedProduct (fun j => weightedComplete (d j)) := by
  funext x
  have hc : (∀ (e : Edge k) (i j : Fin k) (hi : i ∈ e.val) (hj : j ∈ e.val),
      weightedTuple (fun a => d a e) (fun a => x i a ⟨e, hi⟩) =
        weightedTuple (fun a => d a e) (fun a => x j a ⟨e, hj⟩)) ↔
      ∀ a, ∀ (e : Edge k) (i j : Fin k) (hi : i ∈ e.val) (hj : j ∈ e.val),
        x i a ⟨e, hi⟩ = x j a ⟨e, hj⟩ := by
    constructor
    · intro h a e i j hi hj
      exact congrFun ((weightedTuple (fun a => d a e)).injective (h e i j hi hj)) a
    · intro h e i j hi hj
      congr 1
      funext a
      exact h a e i j hi hj
  change (if ∀ (e : Edge k) (i j : Fin k) (hi : i ∈ e.val) (hj : j ∈ e.val),
    weightedTuple (fun a => d a e) (fun a => x i a ⟨e, hi⟩) =
      weightedTuple (fun a => d a e) (fun a => x j a ⟨e, hj⟩) then (1 : ℂ) else 0) = _
  simp only [Tensor.indexedProduct, weightedComplete, Fintype.prod_boole, hc]

theorem asymptoticRank_weighted_indexedProduct_le {k : ℕ} {J : Type*} [Fintype J]
    (d : J → Edge k → ℕ) :
    Tensor.asymptoticRank (weightedComplete (fun e => ∏ j, d j e)) ≤
      ∏ j, Tensor.asymptoticRank (weightedComplete (d j)) := by
  have h := Tensor.asymptoticRank_reindex (weightedIndexedCoordinate d)
    (weightedComplete (fun e => ∏ j, d j e))
  rw [weighted_indexedProduct_reindex] at h
  rw [← h]
  exact Tensor.asymptoticRank_indexedProduct_le _

theorem weightedComplete_ne_zero {k : ℕ} {d : Edge k → ℕ} (hd : ∀ e, 0 < d e) :
    weightedComplete d ≠ 0 := by
  intro h
  have hx := congrFun h (fun i e => ⟨0, hd e.val⟩)
  simp [weightedComplete] at hx

end Lemmata.TensorRank
