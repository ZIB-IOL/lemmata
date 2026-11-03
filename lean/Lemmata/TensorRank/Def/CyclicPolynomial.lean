module

/-
Copyright (c) 2026 Kirill Khoruzhii. Licensed under Apache-2.0.
Modified for the arbitrary-field tensor-rank formalization; namespace and imports
adapted for Lemmata. See docs/tensor-rank/NOTICE.txt for upstream attribution
and modification notices, and docs/tensor-rank/LICENSE.txt for the license.
-/

public import Lemmata.TensorRank.Def.CyclicSchedule
public import Lemmata.TensorRank.Proof.PolynomialPlacement
public import Lemmata.TensorRank.Def.PolynomialPacking

@[expose] public section

set_option autoImplicit false

open Classical

noncomputable section

namespace Lemmata.TensorRank.CyclicPolynomial

variable {𝕜 : Type*} [Field 𝕜] {k : ℕ} [NeZero k]

abbrev Input (j : ZMod k) := PolynomialProduct.Other j

def outputParties (e : Fin k ≃ ZMod k) (j : ZMod k) : Fin k ≃ Option (Input j) :=
  e.trans (Equiv.optionSubtypeNe j).symm

def tensor (e : Fin k ≃ ZMod k) (j : ZMod k) (a : ZMod k → ℕ) :=
  PolynomialProduct.placed (𝕜 := 𝕜) (outputParties e j) (fun p : Input j => a p.val)

def stageFactor (e : Fin k ≃ ZMod k) (b l : ℕ) (t : CyclicSchedule.Token k) :=
  tensor (𝕜 := 𝕜) e t.1 (CyclicSchedule.inputLength b l t)

def readerParties (e : Fin k ≃ ZMod k) (a z : ZMod k) (h : a ≠ z) :
    Fin k ≃ (Bool ⊕ CyclicSchedule.Shared a z) :=
  e.trans (CyclicSchedule.readerPartiesEquiv a z h)

def readerEdge (e : Fin k ≃ ZMod k) (a z : ZMod k) (h : a ≠ z) (d : ℕ) :=
  Tensor.relabel (readerParties e a z h)
    (PolynomialProduct.Packing.readerPairing (𝕜 := 𝕜) (J := CyclicSchedule.Shared a z) d)

def stagePair (e : Fin k ≃ ZMod k) (b l : ℕ) (a : ZMod k) :=
  Tensor.product (stageFactor (𝕜 := 𝕜) e b l (a, false))
    (stageFactor (𝕜 := 𝕜) e b l (CyclicSchedule.rightReader a l, true))

def shortenedPair (e : Fin k ≃ ZMod k) (b l : ℕ) (a : ZMod k) :=
  Tensor.product (stageFactor (𝕜 := 𝕜) e b (l + 1) (a, false))
    (stageFactor (𝕜 := 𝕜) e b (l + 1) (CyclicSchedule.rightReader a l, true))

end Lemmata.TensorRank.CyclicPolynomial
