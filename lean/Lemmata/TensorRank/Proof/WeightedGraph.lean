module

/-
Copyright (c) 2026 Kirill Khoruzhii. Licensed under Apache-2.0.
Modified for the arbitrary-field tensor-rank formalization; namespace and imports
adapted for Lemmata. See docs/tensor-rank/NOTICE.txt for upstream attribution
and modification notices, and docs/tensor-rank/LICENSE.txt for the license.
-/

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

variable {𝕜 : Type*} [Field 𝕜]

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
      (weightedComplete (𝕜 := 𝕜) (fun _ : Edge k => n)) = completeGraph (𝕜 := 𝕜) k n := by
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
      (constantCoordinate (n := n) j).symm (x j) ⟨e, hj⟩ then (1 : 𝕜) else 0) = _
  simp only [hx, hc, completeGraph]

theorem asymptoticRank_weighted_constant (k n : ℕ) :
    Tensor.asymptoticRank (weightedComplete (𝕜 := 𝕜) (fun _ : Edge k => n)) =
      Tensor.asymptoticRank (completeGraph (𝕜 := 𝕜) k n) := by
  rw [← weighted_constant_reindex, Tensor.asymptoticRank_reindex]

noncomputable def weightedProductCoordinate {k : ℕ} (d e : Edge k → ℕ) (i : Fin k) :
    (WeightedCoordinate d i × WeightedCoordinate e i) ≃ WeightedCoordinate (fun a => d a * e a) i where
  toFun x a := finProdFinEquiv (x.1 a, x.2 a)
  invFun x := (fun a => (finProdFinEquiv.symm (x a)).1, fun a => (finProdFinEquiv.symm (x a)).2)
  left_inv x := by apply Prod.ext <;> funext a <;> simp
  right_inv x := by funext a; exact finProdFinEquiv.apply_symm_apply (x a)

theorem weighted_product_reindex {k : ℕ} (d e : Edge k → ℕ) :
    Tensor.reindex (fun i => weightedProductCoordinate d e i) (weightedComplete (𝕜 := 𝕜) (fun a => d a * e a)) =
      Tensor.product (weightedComplete (𝕜 := 𝕜) d) (weightedComplete (𝕜 := 𝕜) e) := by
  funext x
  simp only [Tensor.reindex, weightedComplete, weightedProductCoordinate, Equiv.coe_fn_mk,
    Tensor.product, finProdFinEquiv.injective.eq_iff, Prod.mk.injEq, forall_and]
  rw [ite_and]
  split_ifs <;> simp_all only [mul_one, mul_zero]

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
      (weightedComplete (𝕜 := 𝕜) (fun e => ∏ j, d j e)) =
      Tensor.indexedProduct (fun j => weightedComplete (𝕜 := 𝕜) (d j)) := by
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
      weightedTuple (fun a => d a e) (fun a => x j a ⟨e, hj⟩) then (1 : 𝕜) else 0) = _
  simp only [Tensor.indexedProduct, weightedComplete, Fintype.prod_boole, hc]

end Lemmata.TensorRank
