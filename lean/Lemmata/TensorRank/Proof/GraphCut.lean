module

public import Lemmata.TensorRank.Def.Graph
public import Lemmata.TensorRank.Proof.Flattening

@[expose] public section

set_option autoImplicit false

open scoped BigOperators

namespace Lemmata.TensorRank

abbrev CutLabels {k : ℕ} (S : Finset (Fin k)) (n : ℕ) :=
  ({i : Fin k // i ∈ S} × {i : Fin k // i ∉ S}) → Fin n

noncomputable def cutCoordinates {k n : ℕ} (S : Finset (Fin k)) (hn : 0 < n)
    (z : CutLabels S n) : ∀ i, GraphCoordinate k n i := by
  classical
  exact fun i j => if hi : i ∈ S then
    if hj : j.val ∉ S then z (⟨i, hi⟩, ⟨j.val, hj⟩) else ⟨0, hn⟩
  else if hj : j.val ∈ S then z (⟨j.val, hj⟩, ⟨i, hi⟩) else ⟨0, hn⟩

private theorem cutCoordinates_match {k n : ℕ} (S : Finset (Fin k)) (hn : 0 < n)
    (z : CutLabels S n) (i j : Fin k) (h : i ≠ j) :
    cutCoordinates S hn z i ⟨j, h.symm⟩ = cutCoordinates S hn z j ⟨i, h⟩ := by
  classical
  by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;> simp [cutCoordinates, hi, hj]

theorem completeGraph_identity_minor {k n : ℕ} (S : Finset (Fin k)) (hn : 0 < n) :
    (Tensor.flatten (completeGraph k n) S).submatrix
      (fun z : CutLabels S n => fun i => cutCoordinates S hn z i.val)
      (fun z : CutLabels S n => fun i => cutCoordinates S hn z i.val) = 1 := by
  classical
  funext a b
  let x := Tensor.joinCut S
    (fun i => cutCoordinates S hn a i.val) (fun i => cutCoordinates S hn b i.val)
  have hm : (∀ (i j : Fin k) (h : i ≠ j), x i ⟨j, h.symm⟩ = x j ⟨i, h⟩) ↔ a = b := by
    constructor
    · intro h
      funext p
      have hij : p.1.val ≠ p.2.val := by
        intro he
        exact p.2.property (he ▸ p.1.property)
      simpa [x, Tensor.joinCut, cutCoordinates, p.1.property, p.2.property] using
        h p.1.val p.2.val hij
    · rintro rfl i j h
      have hx : x = cutCoordinates S hn a := by
        funext i
        simp [x, Tensor.joinCut]
      rw [hx]
      exact cutCoordinates_match S hn a i j h
  change completeGraph k n x = _
  simp only [completeGraph, hm, Matrix.one_apply]

theorem completeGraph_cut_rank_lower {k n : ℕ} (S : Finset (Fin k)) (hn : 0 < n) :
    n ^ (S.card * (k - S.card)) ≤ Tensor.rank (completeGraph k n) := by
  classical
  have h := Tensor.card_le_rank_of_identity (completeGraph k n) S _ _
    (completeGraph_identity_minor S hn)
  simpa [CutLabels, Fintype.card_prod, Fintype.card_subtype_compl,
    Fintype.card_coe] using h

theorem completeGraph_cut_lower {k n : ℕ} (S : Finset (Fin k)) (hn : 0 < n) :
    (n : ℝ) ^ (S.card * (k - S.card)) ≤ Tensor.asymptoticRank (completeGraph k n) := by
  classical
  have h := Tensor.card_le_asymptoticRank_of_identity (completeGraph k n) S _ _
    (completeGraph_identity_minor S hn)
  simpa [CutLabels, Fintype.card_prod, Fintype.card_subtype_compl,
    Fintype.card_coe] using h

private theorem balanced_product (k : ℕ) : (k / 2) * (k - k / 2) = k * k / 4 := by
  let a := k / 2
  have hk : k = 2 * a ∨ k = 2 * a + 1 := by omega
  rcases hk with hk | hk
  · have hs : k - a = a := by omega
    change a * (k - a) = k * k / 4
    rw [hs, hk]
    have he : (2 * a) * (2 * a) = 4 * (a * a) := by ring
    rw [he]
    omega
  · have hs : k - a = a + 1 := by omega
    change a * (k - a) = k * k / 4
    rw [hs, hk]
    have he : (2 * a + 1) * (2 * a + 1) = 4 * (a * (a + 1)) + 1 := by ring
    rw [he]
    omega

theorem completeGraph_balanced_lower {k n : ℕ} (hn : 0 < n) :
    (n : ℝ) ^ ((k * k / 4 : ℕ) : ℝ) ≤ Tensor.asymptoticRank (completeGraph k n) := by
  let S : Finset (Fin k) := Finset.univ.map (Fin.castLEEmb (Nat.div_le_self k 2))
  have hS : S.card = k / 2 := by simp [S]
  have h := completeGraph_cut_lower S hn
  simpa only [hS, balanced_product, Real.rpow_natCast] using h

end Lemmata.TensorRank
