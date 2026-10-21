module

public import Lemmata.TensorRank.Def.Graph
public import Lemmata.TensorRank.Proof.Products
public import Lemmata.TensorRank.Proof.Maps

@[expose] public section

set_option autoImplicit false

open scoped BigOperators
open Classical

namespace Lemmata.TensorRank

noncomputable def wordIndex (n q : ℕ) : (Fin q → Fin n) ≃ Fin (n ^ q) :=
  Fintype.equivFinOfCardEq (by simp)

noncomputable def graphPowerEquiv {k : ℕ} (n q : ℕ) (i : Fin k) :
    (Fin q → GraphCoordinate k n i) ≃ GraphCoordinate k (n ^ q) i where
  toFun x j := wordIndex n q (fun t => x t j)
  invFun x t j := (wordIndex n q).symm (x j) t
  left_inv x := by funext t j; simp
  right_inv x := by funext j; simp

theorem completeGraph_power_reindex (k n q : ℕ) :
    Tensor.reindex (fun i => graphPowerEquiv n q i) (completeGraph k (n ^ q)) =
      Tensor.power (completeGraph k n) q := by
  funext x
  have hm :
      (∀ (i j : Fin k) (h : i ≠ j),
        wordIndex n q (fun t => x i t ⟨j, h.symm⟩) =
          wordIndex n q (fun t => x j t ⟨i, h⟩)) ↔
      ∀ t, ∀ (i j : Fin k) (h : i ≠ j), x i t ⟨j, h.symm⟩ = x j t ⟨i, h⟩ := by
    constructor
    · intro h t i j hij
      exact congrFun ((wordIndex n q).injective (h i j hij)) t
    · intro h i j hij
      congr 1
      funext t
      exact h t i j hij
  change (if ∀ (i j : Fin k) (h : i ≠ j),
    wordIndex n q (fun t => x i t ⟨j, h.symm⟩) =
      wordIndex n q (fun t => x j t ⟨i, h⟩) then (1 : ℂ) else 0) = _
  simp only [Tensor.power, completeGraph, Fintype.prod_boole, hm]
  split_ifs <;> simp_all

theorem rank_completeGraph_power (k n q : ℕ) :
    Tensor.rank (completeGraph k (n ^ q)) = Tensor.rank (Tensor.power (completeGraph k n) q) := by
  rw [← completeGraph_power_reindex, Tensor.rank_reindex]

theorem completeGraph_padding {k n m : ℕ} (hnm : n ≤ m) :
    Tensor.reindex (fun i (x : GraphCoordinate k n i) j => Fin.castLE hnm (x j))
      (completeGraph k m) =
      completeGraph k n := by
  funext x
  have hm : (∀ (i j : Fin k) (h : i ≠ j),
      Fin.castLE hnm (x i ⟨j, h.symm⟩) = Fin.castLE hnm (x j ⟨i, h⟩)) ↔
      ∀ (i j : Fin k) (h : i ≠ j), x i ⟨j, h.symm⟩ = x j ⟨i, h⟩ := by
    simp only [Fin.castLE_inj]
  change (if ∀ (i j : Fin k) (h : i ≠ j),
    Fin.castLE hnm (x i ⟨j, h.symm⟩) = Fin.castLE hnm (x j ⟨i, h⟩)
    then (1 : ℂ) else 0) = _
  simp only [completeGraph, hm]

theorem rank_completeGraph_mono {k n m : ℕ} (hnm : n ≤ m) :
    Tensor.rank (completeGraph k n) ≤ Tensor.rank (completeGraph k m) := by
  rw [← completeGraph_padding hnm]
  exact Tensor.rank_reindex_le _ _

theorem asymptoticRank_completeGraph_mono {k n m : ℕ} (hnm : n ≤ m) :
    Tensor.asymptoticRank (completeGraph k n) ≤ Tensor.asymptoticRank (completeGraph k m) := by
  have h := (Tensor.reindex_restricts
    (fun i (x : GraphCoordinate k n i) j => Fin.castLE hnm (x j))
    (completeGraph k m)).asymptoticRank_le
  rwa [completeGraph_padding] at h

theorem completeGraph_ne_zero {k n : ℕ} (hn : 0 < n) : completeGraph k n ≠ 0 := by
  intro h
  have he := congrFun h (fun _ _ => ⟨0, hn⟩)
  simp [completeGraph] at he

theorem asymptoticRank_completeGraph_one (k : ℕ) :
    Tensor.asymptoticRank (completeGraph k 1) = 1 := by
  have h : completeGraph k 1 = Tensor.pure (fun _ _ => (1 : ℂ)) := by
    funext x
    have hm : ∀ (i j : Fin k) (h : i ≠ j),
        x i ⟨j, h.symm⟩ = x j ⟨i, h⟩ := fun _ _ _ => Subsingleton.elim _ _
    simpa [completeGraph, Tensor.pure] using hm
  rw [h]
  exact Tensor.asymptoticRank_pure _ (by rw [← h]; exact completeGraph_ne_zero (by decide))

end Lemmata.TensorRank
