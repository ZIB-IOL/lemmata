module

/-
Copyright (c) 2026 Kirill Khoruzhii. Licensed under Apache-2.0.
Modified for the arbitrary-field tensor-rank formalization; namespace and imports
adapted for Lemmata. See docs/tensor-rank/NOTICE.txt for upstream attribution
and modification notices, and docs/tensor-rank/LICENSE.txt for the license.
-/

public import Lemmata.TensorRank.Proof.CyclicPolynomial
public import Lemmata.TensorRank.Proof.CyclicResources
public import Lemmata.TensorRank.Proof.ContextIndexed
public import Lemmata.TensorRank.Proof.ContextWeighted
public import Lemmata.TensorRank.Proof.PlacedPairing
public import Lemmata.TensorRank.Proof.IndexedProduct

@[expose] public section

set_option autoImplicit false

open scoped BigOperators
open Classical

noncomputable section

namespace Lemmata.TensorRank.CyclicPolynomial

variable {𝕜 : Type*} [Field 𝕜] {k : ℕ} [NeZero k]

private theorem trans1 {V W U : Fin k → Type}
    [∀ i, Fintype (V i)] [∀ i, Fintype (W i)] [∀ i, Fintype (U i)]
    {S : Tensor 𝕜 (Fin k) V} {T : Tensor 𝕜 (Fin k) W} {H : Tensor 𝕜 (Fin k) U}
    (h : Tensor.ContextLE 1 S T) (g : Tensor.ContextLE 1 T H) :
    Tensor.ContextLE 1 S H := by
  simpa only [one_mul] using h.trans g zero_le_one

private theorem indexedProduct_one {C : Type} [Fintype C]
    {V W : C → Fin k → Type} [∀ c i, Fintype (V c i)] [∀ c i, Fintype (W c i)]
    {S : ∀ c, Tensor 𝕜 (Fin k) (V c)} {T : ∀ c, Tensor 𝕜 (Fin k) (W c)}
    (h : ∀ c, Tensor.ContextLE 1 (S c) (T c)) :
    Tensor.ContextLE 1 (Tensor.indexedProduct S) (Tensor.indexedProduct T) := by
  have hi := Tensor.ContextLE.indexedProduct (C := C) (V := V) (W := W)
    (S := S) (T := T) (r := fun _ => (1 : ℝ)) h (fun _ => zero_le_one)
  simpa only [Finset.prod_const_one] using hi

/-- The two fixed-output factors at every party form the polynomial stage resource. -/
def stageTensor (e : Fin k ≃ ZMod k) (b l : ℕ) :=
  Tensor.indexedProduct (stageFactor (𝕜 := 𝕜) e b l)

/-- Regroup a stage using the reader pairs of stage `l`, retaining polynomial stage `r`. -/
def pairedTensor (e : Fin k ≃ ZMod k) (b r l : ℕ) :=
  Tensor.indexedProduct (fun a : ZMod k =>
    Tensor.product (stageFactor (𝕜 := 𝕜) e b r (a, false))
      (stageFactor (𝕜 := 𝕜) e b r (CyclicSchedule.rightReader a l, true)))

theorem stageTensor_context_paired (e : Fin k ≃ ZMod k) (b r l : ℕ) :
    Tensor.ContextLE 1 (stageTensor (𝕜 := 𝕜) e b r) (pairedTensor (𝕜 := 𝕜) e b r l) := by
  let S := stageFactor (𝕜 := 𝕜) e b r
  have hi := Tensor.ContextLE.of_reindex _
    (Tensor.indexedProduct_reindex_indices (CyclicSchedule.pairingEquiv l) S)
  have hp := Tensor.ContextLE.of_reindex _
    (Tensor.indexedProduct_pairs_reindex (fun t => S (CyclicSchedule.pairingEquiv l t)))
  exact trans1 hi hp

theorem paired_context_stageTensor (e : Fin k ≃ ZMod k) (b r l : ℕ) :
    Tensor.ContextLE 1 (pairedTensor (𝕜 := 𝕜) e b r l) (stageTensor (𝕜 := 𝕜) e b r) := by
  let S := stageFactor (𝕜 := 𝕜) e b r
  have hi := Tensor.ContextLE.of_reindex_reverse _
    (Tensor.indexedProduct_reindex_indices (CyclicSchedule.pairingEquiv l) S)
  have hp := Tensor.ContextLE.of_reindex_reverse _
    (Tensor.indexedProduct_pairs_reindex (fun t => S (CyclicSchedule.pairingEquiv l t)))
  exact trans1 hp hi

private theorem indexed_weighted_contexts {C : Type} [Fintype C]
    {V : C → Fin k → Type} [∀ c i, Fintype (V c i)]
    (S : ∀ c, Tensor 𝕜 (Fin k) (V c)) (d : C → Edge k → ℕ) :
    Tensor.ContextLE 1
      (Tensor.product (Tensor.indexedProduct S)
        (weightedComplete (𝕜 := 𝕜) (fun f => ∏ c, d c f)))
      (Tensor.indexedProduct (fun c => Tensor.product (S c) (weightedComplete (d c)))) ∧
    Tensor.ContextLE 1
      (Tensor.indexedProduct (fun c => Tensor.product (S c) (weightedComplete (d c))))
      (Tensor.product (Tensor.indexedProduct S)
        (weightedComplete (𝕜 := 𝕜) (fun f => ∏ c, d c f))) := by
  have hg := Tensor.ContextLE.of_reindex _ (weighted_indexedProduct_reindex (𝕜 := 𝕜) d)
  have hg' := Tensor.ContextLE.of_reindex_reverse _ (weighted_indexedProduct_reindex (𝕜 := 𝕜) d)
  have hs := Tensor.ContextLE.of_reindex _
    (Tensor.product_indexedProduct_reindex S (fun c => weightedComplete (𝕜 := 𝕜) (d c)))
  have hs' := Tensor.ContextLE.of_reindex_reverse _
    (Tensor.product_indexedProduct_reindex S (fun c => weightedComplete (𝕜 := 𝕜) (d c)))
  exact ⟨trans1 (hg.leftTensor (Tensor.indexedProduct S)) hs,
    trans1 hs' (hg'.leftTensor (Tensor.indexedProduct S))⟩

theorem readerParties_stepEdge (e : Fin k ≃ ZMod k) (a : ZMod k) (l : Fin (k - 1)) :
    PlacedPairing.edge (readerParties e a (CyclicSchedule.rightReader a l.val)
      (CyclicSchedule.readers_distinct a l.isLt)) = CyclicSchedule.stepEdge e (a, l) := rfl

theorem stage_pair_weighted (e : Fin k ≃ ZMod k) (b : ℕ) (hb : 0 < b)
    (l : Fin (k - 1)) (a : ZMod k) :
    Tensor.ContextLE 1
      (Tensor.product (shortenedPair (𝕜 := 𝕜) e b l.val a)
        (weightedComplete (𝕜 := 𝕜)
          (singleEdgeDimensions (CyclicSchedule.stepEdge e (a, l)) ((k * b + 2) ^ 2))))
      (Tensor.product (stagePair (𝕜 := 𝕜) e b l.val a)
        (weightedComplete (𝕜 := 𝕜)
          (singleEdgeDimensions (CyclicSchedule.stepEdge e (a, l)) ((k * b) ^ 2)))) := by
  let R := readerParties e a (CyclicSchedule.rightReader a l.val)
    (CyclicSchedule.readers_distinct a l.isLt)
  have ho := PlacedPairing.weighted_contextLE_pairing (𝕜 := 𝕜) R ((k * b + 2) ^ 2)
  have hi := PlacedPairing.pairing_contextLE_weighted (𝕜 := 𝕜) R ((k * b) ^ 2)
  dsimp only [R] at ho hi
  rw [readerParties_stepEdge] at ho hi
  have hs := stage_pair_shortening (𝕜 := 𝕜) e b hb l.val l.isLt a
  exact trans1 (trans1 (ho.leftTensor (shortenedPair (𝕜 := 𝕜) e b l.val a)) hs)
    (hi.leftTensor (stagePair (𝕜 := 𝕜) e b l.val a))

/-- All disjoint polynomial factor pairs are shortened simultaneously in one cyclic stage. -/
theorem stage_weighted_context (e : Fin k ≃ ZMod k) (b : ℕ) (hb : 0 < b)
    (l : Fin (k - 1)) :
    Tensor.ContextLE 1
      (Tensor.product (stageTensor (𝕜 := 𝕜) e b (l.val + 1))
        (weightedComplete (𝕜 := 𝕜) (CyclicSchedule.stageDims e l ((k * b + 2) ^ 2))))
      (Tensor.product (stageTensor (𝕜 := 𝕜) e b l.val)
        (weightedComplete (𝕜 := 𝕜) (CyclicSchedule.stageDims e l ((k * b) ^ 2)))) := by
  let S := shortenedPair (𝕜 := 𝕜) e b l.val
  let T := stagePair (𝕜 := 𝕜) e b l.val
  let dout := fun a : ZMod k =>
    singleEdgeDimensions (CyclicSchedule.stepEdge e (a, l)) ((k * b + 2) ^ 2)
  let din := fun a : ZMod k =>
    singleEdgeDimensions (CyclicSchedule.stepEdge e (a, l)) ((k * b) ^ 2)
  have hlocal := indexedProduct_one
    (fun a : ZMod k => stage_pair_weighted (𝕜 := 𝕜) e b hb l a)
  have hregroup := (stageTensor_context_paired (𝕜 := 𝕜) e b (l.val + 1) l.val).rightTensor
    (weightedComplete (𝕜 := 𝕜) (CyclicSchedule.stageDims e l ((k * b + 2) ^ 2)))
  have hsplit := (indexed_weighted_contexts S dout).1
  have hmerge := (indexed_weighted_contexts T din).2
  have hunregroup := (paired_context_stageTensor (𝕜 := 𝕜) e b l.val l.val).rightTensor
    (weightedComplete (𝕜 := 𝕜) (CyclicSchedule.stageDims e l ((k * b) ^ 2)))
  exact trans1 (trans1 (trans1 (trans1 hregroup hsplit) hlocal) hmerge) hunregroup

private def roundDims (e : Fin k ≃ ZMod k) (D n : ℕ) (f : Edge k) : ℕ :=
  if h : n < k - 1 then CyclicSchedule.stageDims e ⟨n, h⟩ D f else 1

private theorem prod_roundDims (e : Fin k ≃ ZMod k) (D : ℕ) (f : Edge k) :
    (∏ n ∈ Finset.range (k - 1), roundDims e D n f) = D ^ 2 := by
  calc
    (∏ n ∈ Finset.range (k - 1), roundDims e D n f) =
        ∏ l : Fin (k - 1), roundDims e D l.val f := Finset.prod_range _
    _ = ∏ l : Fin (k - 1), CyclicSchedule.stageDims e l D f := by
      apply Finset.prod_congr rfl
      intro l _
      simp [roundDims, l.isLt]
    _ = D ^ 2 := CyclicSchedule.prod_stageDims e D f

/-- The complete cyclic schedule matches all intermediate polynomial resources exactly. -/
theorem round_weighted_context (e : Fin k ≃ ZMod k) (b : ℕ) (hb : 0 < b) :
    Tensor.ContextLE 1
      (Tensor.product (stageTensor (𝕜 := 𝕜) e b (k - 1))
        (weightedComplete (𝕜 := 𝕜) (fun _ : Edge k => (k * b + 2) ^ 4)))
      (Tensor.product (stageTensor (𝕜 := 𝕜) e b 0)
        (weightedComplete (𝕜 := 𝕜) (fun _ : Edge k => (k * b) ^ 4))) := by
  have hc := Tensor.ContextLE.weighted_chain (stageTensor (𝕜 := 𝕜) e b)
    (roundDims e ((k * b) ^ 2)) (roundDims e ((k * b + 2) ^ 2)) (k - 1)
    (fun n hn => by
      have hd (D : ℕ) : roundDims e D n = CyclicSchedule.stageDims e ⟨n, hn⟩ D := by
        funext f
        simp [roundDims, hn]
      rw [hd ((k * b + 2) ^ 2), hd ((k * b) ^ 2)]
      exact stage_weighted_context (𝕜 := 𝕜) e b hb ⟨n, hn⟩)
  have hout : (fun f : Edge k => ∏ n ∈ Finset.range (k - 1),
      roundDims e ((k * b + 2) ^ 2) n f) = fun _ => (k * b + 2) ^ 4 := by
    funext f
    rw [prod_roundDims, ← pow_mul]
  have hin : (fun f : Edge k => ∏ n ∈ Finset.range (k - 1),
      roundDims e ((k * b) ^ 2) n f) = fun _ => (k * b) ^ 4 := by
    funext f
    rw [prod_roundDims, ← pow_mul]
  rw [hout, hin] at hc
  exact hc

/-- A full round changes the graph edge dimension from `(k*b)^4` to `(k*b+2)^4`. -/
theorem round_context (e : Fin k ≃ ZMod k) (b : ℕ) (hb : 0 < b) :
    Tensor.ContextLE 1
      (Tensor.product (stageTensor (𝕜 := 𝕜) e b (k - 1))
        (completeGraph (𝕜 := 𝕜) k ((k * b + 2) ^ 4)))
      (Tensor.product (stageTensor (𝕜 := 𝕜) e b 0)
        (completeGraph (𝕜 := 𝕜) k ((k * b) ^ 4))) := by
  have ho := Tensor.ContextLE.of_reindex_reverse _
    (weighted_constant_reindex (𝕜 := 𝕜) k ((k * b + 2) ^ 4))
  have hi := Tensor.ContextLE.of_reindex _
    (weighted_constant_reindex (𝕜 := 𝕜) k ((k * b) ^ 4))
  exact trans1 (trans1 (ho.leftTensor (stageTensor (𝕜 := 𝕜) e b (k - 1)))
    (round_weighted_context (𝕜 := 𝕜) e b hb))
      (hi.leftTensor (stageTensor (𝕜 := 𝕜) e b 0))

/-- The zero stage of one length round is the full stage of the next length. -/
theorem round_full_context (e : Fin k ≃ ZMod k) (b : ℕ) (hb : 0 < b) :
    Tensor.ContextLE 1
      (Tensor.product (stageTensor (𝕜 := 𝕜) e b (k - 1))
        (completeGraph (𝕜 := 𝕜) k ((k * b + 2) ^ 4)))
      (Tensor.product (stageTensor (𝕜 := 𝕜) e (b + 1) (k - 1))
        (completeGraph (𝕜 := 𝕜) k ((k * b) ^ 4))) := by
  have hfactor (t : CyclicSchedule.Token k) :
      Tensor.ContextLE 1 (stageFactor (𝕜 := 𝕜) e b 0 t)
        (stageFactor (𝕜 := 𝕜) e (b + 1) (k - 1) t) :=
    trans1 (stageFactor_zero_context_constant (𝕜 := 𝕜) e b t)
      (constant_context_stageFactor_full (𝕜 := 𝕜) e (b + 1) t)
  have hstage := indexedProduct_one hfactor
  exact trans1 (round_context (𝕜 := 𝕜) e b hb)
    (hstage.rightTensor (completeGraph (𝕜 := 𝕜) k ((k * b) ^ 4)))

end Lemmata.TensorRank.CyclicPolynomial
