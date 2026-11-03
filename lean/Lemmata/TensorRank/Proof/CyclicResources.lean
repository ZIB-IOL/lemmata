module

/-
Copyright (c) 2026 Kirill Khoruzhii. Licensed under Apache-2.0.
Modified for the arbitrary-field tensor-rank formalization; namespace and imports
adapted for Lemmata. See docs/tensor-rank/NOTICE.txt for upstream attribution
and modification notices, and docs/tensor-rank/LICENSE.txt for the license.
-/

public import Lemmata.TensorRank.Proof.CyclicSchedule
public import Lemmata.TensorRank.Proof.WeightedGraph
public import Lemmata.TensorRank.Proof.PairingGraph

@[expose] public section

set_option autoImplicit false

open scoped BigOperators
open Classical

noncomputable section

namespace Lemmata.TensorRank.CyclicSchedule

variable {k : ℕ} [NeZero k]

/-- The physical edge used by a cyclic reader step, in the original party labels. -/
def stepEdge (e : Fin k ≃ ZMod k) (s : ReaderStep k) : Edge k :=
  edgeBetween (e.symm s.1) (e.symm (rightReader s.1 s.2.val)) (by
    intro h
    exact readers_distinct s.1 s.2.isLt (e.symm.injective h).symm)

theorem stepEdge_eq_iff (e : Fin k ≃ ZMod k) (s : ReaderStep k)
    (a z : Fin k) (h : a ≠ z) :
    stepEdge e s = edgeBetween a z h.symm ↔
      (orderedReadersEquiv s).val = (e a, e z) ∨
        (orderedReadersEquiv s).val = (e z, e a) := by
  constructor
  · intro he
    have hp : ({e.symm s.1, e.symm (rightReader s.1 s.2.val)} : Finset (Fin k)) =
        {a, z} := congrArg Subtype.val he
    have hx : e.symm s.1 = a ∨ e.symm s.1 = z := by
      have hm : e.symm s.1 ∈ ({a, z} : Finset (Fin k)) := by rw [← hp]; simp
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
    have hy : e.symm (rightReader s.1 s.2.val) = a ∨
        e.symm (rightReader s.1 s.2.val) = z := by
      have hm : e.symm (rightReader s.1 s.2.val) ∈ ({a, z} : Finset (Fin k)) := by
        rw [← hp]
        simp
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
    have hxy : e.symm s.1 ≠ e.symm (rightReader s.1 s.2.val) := by
      intro hh
      exact readers_distinct s.1 s.2.isLt (e.symm.injective hh)
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact (hxy (hx.trans hy.symm)).elim
    · left
      apply Prod.ext
      · change s.1 = e a
        simpa only [Equiv.apply_symm_apply] using congrArg e hx
      · change rightReader s.1 s.2.val = e z
        simpa only [Equiv.apply_symm_apply] using congrArg e hy
    · right
      apply Prod.ext
      · change s.1 = e z
        simpa only [Equiv.apply_symm_apply] using congrArg e hx
      · change rightReader s.1 s.2.val = e a
        simpa only [Equiv.apply_symm_apply] using congrArg e hy
    · exact (hxy (hx.trans hy.symm)).elim
  · rintro (he | he)
    · have hx : s.1 = e a := congrArg Prod.fst he
      have hy : rightReader s.1 s.2.val = e z := congrArg Prod.snd he
      have hx' : e.symm s.1 = a := by rw [hx, Equiv.symm_apply_apply]
      have hy' : e.symm (rightReader s.1 s.2.val) = z := by
        rw [hy, Equiv.symm_apply_apply]
      apply Subtype.ext
      change ({e.symm s.1, e.symm (rightReader s.1 s.2.val)} : Finset (Fin k)) = {a, z}
      rw [hx', hy']
    · have hx : s.1 = e z := congrArg Prod.fst he
      have hy : rightReader s.1 s.2.val = e a := congrArg Prod.snd he
      have hx' : e.symm s.1 = z := by rw [hx, Equiv.symm_apply_apply]
      have hy' : e.symm (rightReader s.1 s.2.val) = a := by
        rw [hy, Equiv.symm_apply_apply]
      apply Subtype.ext
      change ({e.symm s.1, e.symm (rightReader s.1 s.2.val)} : Finset (Fin k)) = {a, z}
      rw [hx', hy', Finset.pair_comm]

theorem stepEdge_fiber (e : Fin k ≃ ZMod k) (a z : Fin k) (h : a ≠ z) :
    Finset.univ.filter (fun s : ReaderStep k => stepEdge e s = edgeBetween a z h.symm) =
      edgeSteps (e a) (e z) (fun he => h (e.injective he)) := by
  ext s
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_edgeSteps]
  exact stepEdge_eq_iff e s a z h

/-- Each physical edge receives two copies of a reader resource in one complete round. -/
theorem prod_stepEdgeDimensions (e : Fin k ≃ ZMod k) (D : ℕ) (f : Edge k) :
    (∏ s : ReaderStep k, singleEdgeDimensions (stepEdge e s) D f) = D ^ 2 := by
  obtain ⟨a, z, h, hf⟩ := Finset.card_eq_two.mp f.property
  have he : f = edgeBetween a z h.symm := Subtype.ext hf
  rw [he]
  calc
    (∏ s : ReaderStep k, singleEdgeDimensions (stepEdge e s) D (edgeBetween a z h.symm)) =
        ∏ s ∈ Finset.univ.filter
          (fun s : ReaderStep k => stepEdge e s = edgeBetween a z h.symm), D := by
      rw [Finset.prod_filter]
      apply Finset.prod_congr rfl
      intro s _
      by_cases hs : stepEdge e s = edgeBetween a z h.symm
      · simp [singleEdgeDimensions, hs]
      · simp [singleEdgeDimensions, hs, Ne.symm hs]
    _ = D ^ 2 := by
      rw [Finset.prod_const, stepEdge_fiber e a z h,
        edgeSteps_card (e a) (e z) (fun he => h (e.injective he))]

/-- The graph dimensions used in one simultaneous stage. -/
def stageDims (e : Fin k ≃ ZMod k) (l : Fin (k - 1)) (D : ℕ) (f : Edge k) : ℕ :=
  ∏ a : ZMod k, singleEdgeDimensions (stepEdge e (a, l)) D f

theorem prod_stageDims (e : Fin k ≃ ZMod k) (D : ℕ) (f : Edge k) :
    (∏ l : Fin (k - 1), stageDims e l D f) = D ^ 2 := by
  calc
    (∏ l : Fin (k - 1), stageDims e l D f) =
        ∏ s : ReaderStep k, singleEdgeDimensions (stepEdge e s) D f := by
      rw [Fintype.prod_prod_type]
      exact Finset.prod_comm
    _ = D ^ 2 := prod_stepEdgeDimensions e D f

theorem prod_stageDims_eq (e : Fin k ≃ ZMod k) (D : ℕ) :
    (fun f : Edge k => ∏ l : Fin (k - 1), stageDims e l D f) = fun _ => D ^ 2 := by
  funext f
  exact prod_stageDims e D f

@[simp] theorem stageDims_one (e : Fin k ≃ ZMod k) (l : Fin (k - 1)) (f : Edge k) :
    stageDims e l 1 f = 1 := by
  simp [stageDims, singleEdgeDimensions]

end Lemmata.TensorRank.CyclicSchedule
