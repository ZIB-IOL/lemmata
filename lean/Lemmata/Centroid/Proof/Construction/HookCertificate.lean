module

public import Lemmata.Centroid.Proof.Construction.HookSpans
public import Lemmata.Centroid.Proof.Construction.HookRank
public import Lemmata.Centroid.Proof.Construction.HookConcise
public import Lemmata.Centroid.Proof.Construction.LowerBound
public import Lemmata.Centroid.Proof.Construction.Relabel

@[expose] public section

open scoped BigOperators
open Classical

namespace Lemmata.Centroid.Construction.Hook

noncomputable section

variable {F : Type*} [Field F]

def pairBC (n : ℕ) (b c : Option (Fin n)) : BigCentroid.Opposite (Core n) 0 → RatFunc F :=
  fun x => Realization.basisVector b (x ⟨1, by decide⟩) * Realization.basisVector c (x ⟨2, by decide⟩)

theorem pairBC_selected_zero_mem (n t : ℕ) (ht : t ≤ n) (j : Fin t) :
    pairBC (F := F) n (some (j.castLE ht)) none ∈ oppositeSpan n t ht 0 := by
  have he : pairBC (F := F) n (some (j.castLE ht)) none =
      BigCentroid.oppositeSimple (rowPoint (F := F) n t ht j) 0 := by
    ext x
    erw [Realization.oppositeSimple_zero]
    rfl
  rw [he]
  exact rowPoint_mem n t ht 0 j

theorem pairBC_mem (n t : ℕ) (ht : t ≤ n) (j : Option (Fin n)) (k : Fin n) :
    pairBC (F := F) n j (some k) ∈ oppositeSpan n t ht 0 := by
  by_cases hj : SelectedRow ht j
  · obtain ⟨r, rfl⟩ := hj
    have he : pairBC (F := F) n (some (r.castLE ht)) (some k) =
        BigCentroid.oppositeSimple (oldPoint (F := F) n t ht (some (r.castLE ht), k)) 0 +
          BigCentroid.oppositeSimple (rowPoint (F := F) n t ht r) 0 := by
      ext x
      simp only [Pi.add_apply]
      erw [Realization.oppositeSimple_zero, Realization.oppositeSimple_zero]
      simp only [oldPoint, rowPoint, factors_one, factors_two, splitC_selected, fVector, Pi.sub_apply]
      change _ * _ = _ * (_ - _) + _ * _
      ring
    rw [he]
    exact Submodule.add_mem _ (oldPoint_mem n t ht 0 _) (rowPoint_mem n t ht 0 r)
  · have he : pairBC (F := F) n j (some k) =
        BigCentroid.oppositeSimple (oldPoint (F := F) n t ht (j, k)) 0 := by
      ext x
      erw [Realization.oppositeSimple_zero]
      simp only [oldPoint, factors_one, factors_two, splitC, hj, ite_false]
      rfl
    rw [he]
    exact oldPoint_mem n t ht 0 _

private theorem basisPair_zero {K : Type*} [Field K] {n : ℕ} (a : ∀ i, Core n i)
    (x : BigCentroid.Opposite (Core n) 0) :
    Realization.basisVector (F := K) (fun j : {j : Fin 3 // j ≠ 0} => a j.val) x =
      Realization.basisVector (a 1) (x ⟨1, by decide⟩) * Realization.basisVector (a 2) (x ⟨2, by decide⟩) := by
  rw [← Realization.oppositeSimple_basisVector]
  erw [Realization.oppositeSimple_zero]

private theorem basisPair_one {K : Type*} [Field K] {n : ℕ} (a : ∀ i, Core n i)
    (x : BigCentroid.Opposite (Core n) 1) :
    Realization.basisVector (F := K) (fun j : {j : Fin 3 // j ≠ 1} => a j.val) x =
      Realization.basisVector (a 0) (x ⟨0, by decide⟩) * Realization.basisVector (a 2) (x ⟨2, by decide⟩) := by
  rw [← Realization.oppositeSimple_basisVector]
  erw [Realization.oppositeSimple_one]

private theorem basisPair_two {K : Type*} [Field K] {n : ℕ} (a : ∀ i, Core n i)
    (x : BigCentroid.Opposite (Core n) 2) :
    Realization.basisVector (F := K) (fun j : {j : Fin 3 // j ≠ 2} => a j.val) x =
      Realization.basisVector (a 0) (x ⟨0, by decide⟩) * Realization.basisVector (a 1) (x ⟨1, by decide⟩) := by
  rw [← Realization.oppositeSimple_basisVector]
  erw [Realization.oppositeSimple_two]

private theorem liftCore_basisVector (n : ℕ) (a : Fin n) :
    liftCore (Realization.basisVector (F := RatFunc F) a) = Realization.basisVector (some a) := by
  ext x
  cases x <;> simp [liftCore, Realization.basisVector]

theorem map_pairs {K : Type*} [Field K] (φ : F →+* K) (n t : ℕ) (ht : t ≤ n) :
    Realization.mapPairs φ (pairs (F := F) n t ht) = pairs (F := K) n t ht := by
  funext i l x
  fin_cases i
  · change φ (Realization.basisVector (fun j : {j : Fin 3 // j ≠ 0} => pairPoint n t ht 0 l j.val) x) =
      Realization.basisVector (fun j : {j : Fin 3 // j ≠ 0} => pairPoint n t ht 0 l j.val) x
    exact congrFun (Realization.map_basisVector φ _) x

  · rcases l with p | k
    · change φ (Realization.basisVector (fun j : {j : Fin 3 // j ≠ 1} => pairPoint n t ht 1 (Sum.inl p) j.val) x) =
        Realization.basisVector (fun j : {j : Fin 3 // j ≠ 1} => pairPoint n t ht 1 (Sum.inl p) j.val) x
      exact congrFun (Realization.map_basisVector φ _) x
    · change φ (Realization.basisVector (fun j : {j : Fin 3 // j ≠ 1} => pairPoint n t ht 1 (Sum.inr k) j.val) x -
          Realization.basisVector (fun _ : {j : Fin 3 // j ≠ 1} => (none : Option (Fin n))) x) =
        Realization.basisVector (fun j : {j : Fin 3 // j ≠ 1} => pairPoint n t ht 1 (Sum.inr k) j.val) x -
          Realization.basisVector (fun _ : {j : Fin 3 // j ≠ 1} => (none : Option (Fin n))) x
      rw [map_sub]
      rw [congrFun (Realization.map_basisVector φ _) x, congrFun (Realization.map_basisVector φ _) x]
  · change φ (Realization.basisVector (fun j : {j : Fin 3 // j ≠ 2} => pairPoint n t ht 2 l j.val) x) =
      Realization.basisVector (fun j : {j : Fin 3 // j ≠ 2} => pairPoint n t ht 2 l j.val) x
    exact congrFun (Realization.map_basisVector φ _) x

theorem pairs_mem (n t : ℕ) (ht₀ : 0 < t) (ht : t ≤ n) (i : Fin 3) (l : Dual n t i) :
    pairs (F := RatFunc F) n t ht i l ∈ oppositeSpan n t ht i := by
  fin_cases i
  · rcases l with ⟨b, c⟩ | j
    · have he : pairs (F := RatFunc F) n t ht 0 (Sum.inl (b, c)) = pairBC n b (some c) := by
        ext x
        change Realization.basisVector (fun j : {j : Fin 3 // j ≠ 0} => pairPoint n t ht 0 (Sum.inl (b, c)) j.val) x = _
        erw [basisPair_zero]
        rfl
      erw [he]
      exact pairBC_mem n t ht b c
    · have he : pairs (F := RatFunc F) n t ht 0 (Sum.inr j) = pairBC n (some (j.castLE ht)) none := by
        ext x
        change Realization.basisVector (fun k : {k : Fin 3 // k ≠ 0} => pairPoint n t ht 0 (Sum.inr j) k.val) x = _
        erw [basisPair_zero]
        rfl
      erw [he]
      exact pairBC_selected_zero_mem n t ht j
  · rcases l with ⟨a, c⟩ | k
    · cases c with
      | none =>
        have he : pairs (F := RatFunc F) n t ht 1 (Sum.inl (a, none)) =
            liftACzero n (Realization.basisVector a) := by
          ext x
          change Realization.basisVector (fun j : {j : Fin 3 // j ≠ 1} => pairPoint n t ht 1 (Sum.inl (a, none)) j.val) x = _
          erw [basisPair_one]
          change Realization.basisVector (F := RatFunc F) (some a) (x ⟨0, by decide⟩) *
              Realization.basisVector none (x ⟨2, by decide⟩) =
            liftCore (Realization.basisVector a) (x ⟨0, by decide⟩) * Realization.basisVector none (x ⟨2, by decide⟩)
          rw [liftCore_basisVector]
        erw [he]
        exact liftACzero_mem n t ht₀ ht _
      | some c =>
        have he : pairs (F := RatFunc F) n t ht 1 (Sum.inl (a, some c)) =
            liftACcolumn n c (Realization.basisVector a) := by
          ext x
          change Realization.basisVector (fun j : {j : Fin 3 // j ≠ 1} => pairPoint n t ht 1 (Sum.inl (a, some c)) j.val) x = _
          erw [basisPair_one]
          change Realization.basisVector (F := RatFunc F) (some a) (x ⟨0, by decide⟩) *
              Realization.basisVector (some c) (x ⟨2, by decide⟩) =
            liftCore (Realization.basisVector a) (x ⟨0, by decide⟩) * Realization.basisVector (some c) (x ⟨2, by decide⟩)
          rw [liftCore_basisVector]
        erw [he]
        exact liftACcolumn_mem n t ht₀ ht _ _
    · have he : pairs (F := RatFunc F) n t ht 1 (Sum.inr k) = extraAC n (k.castLE ht) := by
        ext x
        change Realization.basisVector (F := RatFunc F) (fun j : {j : Fin 3 // j ≠ 1} => pairPoint n t ht 1 (Sum.inr k) j.val) x -
            Realization.basisVector (fun _ : {j : Fin 3 // j ≠ 1} => (none : Option (Fin n))) x = _
        erw [basisPair_one (pairPoint n t ht 1 (Sum.inr k)),
          basisPair_one (fun _ => (none : Option (Fin n)))]
        change Realization.basisVector (F := RatFunc F) none (x ⟨0, by decide⟩) *
            Realization.basisVector (some (k.castLE ht)) (x ⟨2, by decide⟩) -
            Realization.basisVector none (x ⟨0, by decide⟩) * Realization.basisVector none (x ⟨2, by decide⟩) =
          Realization.basisVector none (x ⟨0, by decide⟩) *
            (Realization.basisVector (some (k.castLE ht)) (x ⟨2, by decide⟩) - Realization.basisVector none (x ⟨2, by decide⟩))
        ring
      erw [he]
      exact extraAC_mem n t ht₀ ht k
  · rcases l with ⟨a, b⟩ | j
    · have he : pairs (F := RatFunc F) n t ht 2 (Sum.inl (a, b)) = liftABrow n b (Realization.basisVector a) := by
        ext x
        change Realization.basisVector (fun k : {k : Fin 3 // k ≠ 2} => pairPoint n t ht 2 (Sum.inl (a, b)) k.val) x = _
        erw [basisPair_two]
        change Realization.basisVector (F := RatFunc F) (some a) (x ⟨0, by decide⟩) *
            Realization.basisVector b (x ⟨1, by decide⟩) =
          liftCore (Realization.basisVector a) (x ⟨0, by decide⟩) * Realization.basisVector b (x ⟨1, by decide⟩)
        rw [liftCore_basisVector]
      erw [he]
      exact liftABrow_mem n t ht₀ ht b _
    · have he : pairs (F := RatFunc F) n t ht 2 (Sum.inr j) = extraAB n (some (j.castLE ht)) := by
        ext x
        change Realization.basisVector (fun k : {k : Fin 3 // k ≠ 2} => pairPoint n t ht 2 (Sum.inr j) k.val) x = _
        erw [basisPair_two]
        rfl
      erw [he]
      exact extraAB_mem n t ht₀ ht j

theorem frameSpans (n t : ℕ) (ht₀ : 0 < t) (ht : t ≤ n) :
    Realization.FrameSpans (Realization.mapPairs (algebraMap F (RatFunc F)) (pairs n t ht))
      (basePoint (F := F) n t ht) := by
  rw [map_pairs]
  intro i l
  exact pairs_mem n t ht₀ ht i l

theorem rationalBorderRankAtMost (n t : ℕ) (ht₀ : 0 < t) (ht : t ≤ n) :
    Tensor.RationalBorderRankAtMost (tensor (F := F) n t ht) (n * (n + 1) + t + (n + 1)) := by
  have h := Realization.rational_spanning_frame (pairs (F := F) n t ht) (basePoint (F := F) n t ht)
    (basePoint_rankAtMost (F := F) n t ht) (frameSpans n t ht₀ ht)
  have hc : Fintype.card (PointIndex n t) + n = n * (n + 1) + t + (n + 1) := by
    simp only [PointIndex, Fintype.card_sum, Fintype.card_prod, Fintype.card_option,
      Fintype.card_fin, Fintype.card_unit]
    ring
  rw [hc] at h
  exact h

theorem minimal_border_rank (n t : ℕ) (hn : 0 < n) (ht₀ : 0 < t) (ht : t ≤ n) :
    Tensor.rationalBorderRank (tensor (F := F) n t ht) = n * (n + 1) + t + (n + 1) := by
  apply le_antisymm
  · exact (Tensor.rationalBorderRank_le_iff _ _).mpr (rationalBorderRankAtMost n t ht₀ ht)
  · have h := (concise (F := F) n t hn ht₀ ht).le_rationalBorderRank 0
    rwa [coordinate_card] at h

def coordinateEquiv (n t : ℕ) (i : Fin 3) :
    Realization.Coordinates (Core n) (Dual n t) i ≃ Fin (n * (n + 1) + t + (n + 1)) :=
  Fintype.equivFinOfCardEq (coordinate_card n t i)

theorem exists_minimal (n t : ℕ) (hn : 0 < n) (ht₀ : 0 < t) (ht : t ≤ n) (hlarge : n < t ^ 2) :
    ∃ T : Tensor F (Fin 3) (fun _ => Fin (n * (n + 1) + t + (n + 1))),
      Tensor.Concise T ∧ Tensor.rationalBorderRank T = n * (n + 1) + t + (n + 1) ∧
        generalBoundAt n (n + 1 + t) ≤ Module.finrank F (Tensor.centroid T) := by
  let T := Tensor.relabel (coordinateEquiv n t) (tensor (F := F) n t ht)
  refine ⟨T, (concise n t hn ht₀ ht).relabel (coordinateEquiv n t), ?_, ?_⟩
  · apply le_antisymm
    · apply (Tensor.rationalBorderRank_le_iff _ _).mpr
      exact (rationalBorderRankAtMost n t ht₀ ht).relabel (coordinateEquiv n t)
    · simpa only [Fintype.card_fin] using
        ((concise (F := F) n t hn ht₀ ht).relabel (coordinateEquiv n t)).le_rationalBorderRank 0
  · have hnum : generalBoundAt n (n + 1 + t) = 1 + (n * (n * (n + 1) + t) + t ^ 2) := by
      rw [generalBoundAt_second hn]
      have hsub := Nat.sub_add_cancel hlarge.le
      nlinarith
    rw [hnum]
    exact (centroid_lower_bound n t ht).trans
      (Tensor.finrank_centroid_le_relabel (coordinateEquiv n t) _)

end

end Lemmata.Centroid.Construction.Hook
