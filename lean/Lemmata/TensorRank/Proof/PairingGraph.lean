module

public import Lemmata.TensorRank.Proof.ReaderTransport
public import Lemmata.TensorRank.Proof.Context
public import Lemmata.TensorRank.Def.WeightedGraph

@[expose] public section

set_option autoImplicit false

open scoped BigOperators
open Classical

noncomputable section

namespace Lemmata.TensorRank

def singleEdgeDimensions {k : ℕ} (edge : Edge k) (M : ℕ) (f : Edge k) : ℕ :=
  if f = edge then M else 1

theorem singleEdgeDimensions_pos {k M : ℕ} (edge : Edge k) (hM : 0 < M) :
    ∀ f, 0 < singleEdgeDimensions edge M f := by
  intro f
  simp only [singleEdgeDimensions]
  split_ifs <;> positivity

theorem prod_singleEdgeDimensions {k : ℕ} (edge : Edge k) (M : ℕ) :
    (∏ f, singleEdgeDimensions edge M f) = M := by simp [singleEdgeDimensions]

def singleEdgeCoordinate {k : ℕ} (edge : Edge k) (M : ℕ) (i : Fin k) (hi : i ∈ edge.val) :
    Fin M ≃ WeightedCoordinate (singleEdgeDimensions edge M) i where
  toFun t f := if h : f.val = edge then Fin.cast (by simp [singleEdgeDimensions, h]) t
    else ⟨0, by simp [singleEdgeDimensions, h]⟩
  invFun x := Fin.cast (by simp [singleEdgeDimensions]) (x ⟨edge, hi⟩)
  left_inv t := by apply Fin.ext; simp [Fin.cast]
  right_inv x := by
    funext f
    by_cases hf : f.val = edge
    · obtain rfl : f = ⟨edge, hi⟩ := Subtype.ext hf
      apply Fin.ext
      simp [Fin.cast]
    · apply Fin.ext
      have hx : (x f).val < 1 := by simpa [singleEdgeDimensions, hf] using (x f).isLt
      simp only [dite_eq_right hf]
      change 0 = (x f).val
      omega

theorem singleEdgeCoordinate_value {k : ℕ} (edge : Edge k) (M : ℕ)
    (i : Fin k) (hi : i ∈ edge.val) (t : Fin M) :
    ((singleEdgeCoordinate edge M i hi t) ⟨edge, hi⟩).val = t.val := by
  simp [singleEdgeCoordinate, Fin.cast]

def singleEdgeInactiveCoordinate {k : ℕ} (edge : Edge k) (M : ℕ) (i : Fin k)
    (hi : i ∉ edge.val) : PUnit ≃ WeightedCoordinate (singleEdgeDimensions edge M) i where
  toFun _ f := ⟨0, by
    have hf : f.val ≠ edge := by intro h; apply hi; simpa only [h] using f.prop
    simp [singleEdgeDimensions, hf]⟩
  invFun _ := PUnit.unit
  left_inv _ := Subsingleton.elim _ _
  right_inv x := by
    funext f
    apply Fin.ext
    have hf : f.val ≠ edge := by intro h; apply hi; simpa only [h] using f.prop
    have hx : (x f).val < 1 := by simpa [singleEdgeDimensions, hf] using (x f).isLt
    change 0 = (x f).val
    omega

theorem weighted_single_support_iff {k : ℕ} (a b : Fin k) (hab : a ≠ b) (M : ℕ)
    (x : ∀ i, WeightedCoordinate (singleEdgeDimensions (edgeBetween a b hab.symm) M) i) :
    (∀ (f : Edge k) (i j : Fin k) (hi : i ∈ f.val) (hj : j ∈ f.val),
      x i ⟨f, hi⟩ = x j ⟨f, hj⟩) ↔
      (x a ⟨edgeBetween a b hab.symm, by simp [edgeBetween]⟩).val =
        (x b ⟨edgeBetween a b hab.symm, by simp [edgeBetween]⟩).val := by
  constructor
  · intro h
    exact congrArg Fin.val (h _ a b _ _)
  · intro h f i j hi hj
    apply Fin.ext
    by_cases hf : f = edgeBetween a b hab.symm
    · subst f
      have hi' : i = a ∨ i = b := by simpa [edgeBetween] using hi
      have hj' : j = a ∨ j = b := by simpa [edgeBetween] using hj
      rcases hi' with rfl | rfl <;> rcases hj' with rfl | rfl
      · rfl
      · exact h
      · exact h.symm
      · rfl
    · have hi0 : (x i ⟨f, hi⟩).val < 1 := by
        simpa [singleEdgeDimensions, hf] using (x i ⟨f, hi⟩).isLt
      have hj0 : (x j ⟨f, hj⟩).val < 1 := by
        simpa [singleEdgeDimensions, hf] using (x j ⟨f, hj⟩).isLt
      omega

namespace Separation

def pairingGraphCoordinate {k : ℕ} (a b : Fin k) (hab : a ≠ b) (M : ℕ)
    (p : Party (k - 2)) : PairCoordinate M p ≃
      WeightedCoordinate (singleEdgeDimensions (edgeBetween a b hab.symm) M) (readerEquiv a b hab p) :=
  match p with
  | .inl false => singleEdgeCoordinate _ M a (by simp [edgeBetween])
  | .inl true => singleEdgeCoordinate _ M b (by simp [edgeBetween])
  | .inr j => singleEdgeInactiveCoordinate _ M (readerEquiv a b hab (.inr j)) (by
      intro h
      simp only [edgeBetween, Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with ha | hb
      · have hh : readerEquiv a b hab (.inr j) = readerEquiv a b hab (.inl false) := ha
        have hf := (readerEquiv a b hab).injective hh
        cases hf
      · have hh : readerEquiv a b hab (.inr j) = readerEquiv a b hab (.inl true) := hb
        have hf := (readerEquiv a b hab).injective hh
        cases hf)

theorem pairingGraph_reindex {k : ℕ} (a b : Fin k) (hab : a ≠ b) (M : ℕ) :
    Tensor.reindex (fun p => pairingGraphCoordinate a b hab M p)
      (Tensor.relabel (readerEquiv a b hab)
        (weightedComplete (singleEdgeDimensions (edgeBetween a b hab.symm) M))) = readerPairing M := by
  funext x
  let edge := edgeBetween a b hab.symm
  let e := readerEquiv a b hab
  let y := Equiv.piCongrLeft (WeightedCoordinate (singleEdgeDimensions edge M)) e
    (fun p => pairingGraphCoordinate a b hab M p (x p))
  have hy (p : Party (k - 2)) : y (e p) = pairingGraphCoordinate a b hab M p (x p) := by simp [y]
  have ha : (y a ⟨edge, by simp [edge, edgeBetween]⟩).val = (x (.inl false)).val := by
    change (y (e (.inl false)) ⟨edge, by change a ∈ edge.val; simp [edge, edgeBetween]⟩).val = _
    rw [hy]
    exact singleEdgeCoordinate_value edge M a _ (x (.inl false))
  have hb : (y b ⟨edge, by simp [edge, edgeBetween]⟩).val = (x (.inl true)).val := by
    change (y (e (.inl true)) ⟨edge, by change b ∈ edge.val; simp [edge, edgeBetween]⟩).val = _
    rw [hy]
    exact singleEdgeCoordinate_value edge M b _ (x (.inl true))
  change weightedComplete (singleEdgeDimensions edge M) y = readerPairing M x
  change (if ∀ (f : Edge k) (i j : Fin k) (hi : i ∈ f.val) (hj : j ∈ f.val),
      y i ⟨f, hi⟩ = y j ⟨f, hj⟩ then 1 else 0) = _
  simp only [weighted_single_support_iff a b hab M]
  dsimp only [edge] at ha hb
  rw [ha, hb]
  simp only [readerPairing, Fin.ext_iff]

theorem pairingGraph_context_rank {k : ℕ} (a b : Fin k) (hab : a ≠ b) (M : ℕ)
    {U : Fin k → Type} [∀ i, Fintype (U i)] (H : Tensor ℂ (Fin k) U) :
    Tensor.asymptoticRank (Tensor.product
      (Tensor.relabel (readerEquiv a b hab).symm (readerPairing M)) H) =
      Tensor.asymptoticRank (Tensor.product
        (weightedComplete (singleEdgeDimensions (edgeBetween a b hab.symm) M)) H) := by
  let e := readerEquiv a b hab
  let G := weightedComplete (singleEdgeDimensions (edgeBetween a b hab.symm) M)
  rw [Tensor.asymptoticRank_relabel_context e (readerPairing M) H,
    ← pairingGraph_reindex a b hab M,
    Tensor.asymptoticRank_product_reindex (Tensor.relabel e G) (Tensor.relabel e H)
      (fun p => pairingGraphCoordinate a b hab M p),
    ← Tensor.relabel_product e G H]
  exact Tensor.asymptoticRank_relabel e (Tensor.product G H)

theorem pairing_contextLE_weighted {k : ℕ} (a b : Fin k) (hab : a ≠ b) (M : ℕ) :
    Tensor.ContextLE 1 (Tensor.relabel (readerEquiv a b hab).symm (readerPairing M))
      (weightedComplete (singleEdgeDimensions (edgeBetween a b hab.symm) M)) := by
  intro U _ H
  rw [one_mul]
  exact (pairingGraph_context_rank a b hab M H).le

theorem weighted_contextLE_pairing {k : ℕ} (a b : Fin k) (hab : a ≠ b) (M : ℕ) :
    Tensor.ContextLE 1 (weightedComplete (singleEdgeDimensions (edgeBetween a b hab.symm) M))
      (Tensor.relabel (readerEquiv a b hab).symm (readerPairing M)) := by
  intro U _ H
  rw [one_mul]
  exact (pairingGraph_context_rank a b hab M H).ge

theorem fixed_type_contextLE_graph {k : ℕ} (hk : 2 ≤ k) (a b : Fin k) (hab : a ≠ b)
    {C : Type} [Fintype C] {N : ℕ} {V : Fin k → Type} [∀ i, Fintype (V i)]
    (Z : C → Tensor ℂ (Fin k) V) {left : V a → C} {right : V b → C}
    (hleft : Tensor.Reads Z a left) (hright : Tensor.Reads Z b right)
    {h : C → Fin (N + 1)} (base : Types.Words h) :
    Tensor.ContextLE ((k - 1 : ℕ) : ℝ)
      (Tensor.product
        (weightedComplete (singleEdgeDimensions (edgeBetween a b hab.symm)
          (Fintype.card (Types.Words h)))) (Tensor.wordTensor Z base.val))
      (Tensor.power (∑ c, Z c) N) := by
  intro U _ H
  rw [Tensor.asymptoticRank_product_assoc,
    ← pairingGraph_context_rank a b hab (Fintype.card (Types.Words h))
      (Tensor.product (Tensor.wordTensor Z base.val) H)]
  exact fixed_type_bound_readers hk a b hab Z H hleft hright base

end Separation

end Lemmata.TensorRank
