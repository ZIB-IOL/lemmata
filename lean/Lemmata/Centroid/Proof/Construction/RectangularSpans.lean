module

public import Lemmata.Centroid.Proof.Construction.RectangularFrames

@[expose] public section

open scoped BigOperators
open Classical

namespace Lemmata.Centroid.Construction.Rectangular

noncomputable section

variable {F : Type*} [Field F]

def oppositeSpan (n t : ℕ) (ht : t ≤ n) (i : Fin 3) :=
  Submodule.span (RatFunc F) (Set.range (fun p => BigCentroid.oppositeSimple (basePoint (F := F) n t ht p) i))

theorem oldPoint_mem (n t : ℕ) (ht : t ≤ n) (i : Fin 3) (p : Fin n × Option (Fin n)) :
    BigCentroid.oppositeSimple (oldPoint (F := F) n t ht p) i ∈ oppositeSpan n t ht i :=
  Submodule.subset_span ⟨Sum.inl p, rfl⟩

theorem extraPoint_mem (n t : ℕ) (ht : t ≤ n) (i : Fin 3) (k : Option (Fin t)) :
    BigCentroid.oppositeSimple (extraPoint (F := F) n t ht k) i ∈ oppositeSpan n t ht i :=
  Submodule.subset_span ⟨Sum.inr k, rfl⟩

theorem gridTensorPoint_zero_mem (n t : ℕ) (ht : t ≤ n) (p : Fin n × Option (Fin n)) :
    BigCentroid.oppositeSimple (gridTensorPoint (F := F) n t p) 0 ∈ oppositeSpan n t ht 0 := by
  by_cases hr : ∃ k, selected ht k = p.2
  · obtain ⟨k, hk⟩ := hr
    have he : BigCentroid.oppositeSimple (gridTensorPoint (F := F) n t p) 0 =
        BigCentroid.oppositeSimple (oldPoint (F := F) n t ht p) 0 +
          lambda (F := F) n t p.1 p.2 • BigCentroid.oppositeSimple (extraPoint (F := F) n t ht k) 0 := by
      ext x
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      erw [Realization.oppositeSimple_zero, Realization.oppositeSimple_zero, Realization.oppositeSimple_zero]
      simp only [gridTensorPoint, oldPoint, extraPoint, factors_one, factors_two]
      have hs : splitScalar (F := F) n t ht p.1 p.2 = lambda (F := F) n t p.1 p.2 := by
        rw [← hk, splitScalar_selected]
      rw [hs, hk]
      let b := Realization.basisVector (F := RatFunc F) (Sum.inl (some p.1)) (x ⟨1, by decide⟩)
      let c := Realization.basisVector (F := RatFunc F) (Sum.inl p.2) (x ⟨2, by decide⟩)
      let d := Realization.basisVector (F := RatFunc F) (Sum.inl none) (x ⟨1, by decide⟩)
      change b * c = (b - lambda (F := F) n t p.1 p.2 * d) * c + lambda (F := F) n t p.1 p.2 * (d * c)
      ring
    rw [he]
    exact Submodule.add_mem _ (oldPoint_mem n t ht 0 p)
      (Submodule.smul_mem _ _ (extraPoint_mem n t ht 0 k))
  · have hs : splitScalar (F := F) n t ht p.1 p.2 = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      exact ite_eq_right (fun h => hr ⟨k, h⟩)
    have he : BigCentroid.oppositeSimple (gridTensorPoint (F := F) n t p) 0 =
        BigCentroid.oppositeSimple (oldPoint (F := F) n t ht p) 0 := by
      ext x
      erw [Realization.oppositeSimple_zero, Realization.oppositeSimple_zero]
      simp only [gridTensorPoint, oldPoint, factors_one, factors_two, hs, zero_smul, sub_zero]
    rw [he]
    exact oldPoint_mem n t ht 0 p

def liftAC (n t : ℕ) : ((Fin n × Option (Fin n)) → RatFunc F) →ₗ[RatFunc F]
    (BigCentroid.Opposite (Core n t) 1 → RatFunc F) where
  toFun f x := Sum.elim (fun c => f (x ⟨0, by decide⟩, c)) (fun _ => 0) (x ⟨2, by decide⟩)
  map_add' f g := by
    ext x
    let a : Fin n := x ⟨0, by decide⟩
    let c : Option (Fin n) ⊕ Fin t := x ⟨2, by decide⟩
    change Sum.elim (fun c => f (a, c) + g (a, c)) (fun _ => 0) c =
      Sum.elim (fun c => f (a, c)) (fun _ => 0) c + Sum.elim (fun c => g (a, c)) (fun _ => 0) c
    cases c <;> simp
  map_smul' c f := by
    ext x
    let a : Fin n := x ⟨0, by decide⟩
    let b : Option (Fin n) ⊕ Fin t := x ⟨2, by decide⟩
    change Sum.elim (fun b => c * f (a, b)) (fun _ => 0) b =
      c * Sum.elim (fun b => f (a, b)) (fun _ => 0) b
    cases b <;> simp

theorem liftAC_column (n t : ℕ) (ht : t ≤ n) (p : Fin n × Option (Fin n)) :
    liftAC n t (weightedColumn (M (F := F) n) (H (F := F) n t) p) =
      BigCentroid.oppositeSimple (oldPoint (F := F) n t ht p) 1 := by
  ext x
  erw [Realization.oppositeSimple_one]
  let a : Fin n := x ⟨0, by decide⟩
  let c : Option (Fin n) ⊕ Fin t := x ⟨2, by decide⟩
  change Sum.elim (fun c => gridPoint (F := F) n t p.1 p.2 a *
      Realization.basisVector p.2 c) (fun _ => 0) c =
    gridPoint (F := F) n t p.1 p.2 a * Realization.basisVector (Sum.inl p.2) c
  cases c <;> simp [Realization.basisVector]

theorem liftAC_mem (n t : ℕ) (ht : t ≤ n) (x : Fin n × Option (Fin n) → RatFunc F) :
    liftAC n t x ∈ oppositeSpan n t ht 1 := by
  apply Circuit.span_lift_mem _
    (weighted_columns_span (M (F := F) n) (M_isUnit (F := F) n) (H (F := F) n t) (H_ne_zero (F := F) n t))
    _ _ _ x
  intro p
  rw [liftAC_column n t ht]
  exact oldPoint_mem n t ht 1 p

def liftABzero (n t : ℕ) : (Fin n → RatFunc F) →ₗ[RatFunc F]
    (BigCentroid.Opposite (Core n t) 2 → RatFunc F) where
  toFun f x := f (x ⟨0, by decide⟩) * Realization.basisVector (Sum.inl none) (x ⟨1, by decide⟩)
  map_add' f g := by
    ext x
    change (f (x ⟨0, by decide⟩) + g (x ⟨0, by decide⟩)) * _ = _
    exact add_mul _ _ _
  map_smul' c f := by
    ext x
    change (c * f (x ⟨0, by decide⟩)) * _ = _
    exact mul_assoc _ _ _

theorem oldPoint_row (n t : ℕ) (ht : t ≤ n) (j : Fin n) :
    (∑ r, relation (F := F) n t r • BigCentroid.oppositeSimple (oldPoint (F := F) n t ht (j, r)) 2) =
      -liftABzero n t (hPrime (F := F) n t ht j) := by
  ext x
  let a : Fin n := x ⟨0, by decide⟩
  let b : Option (Fin n) ⊕ Fin t := x ⟨1, by decide⟩
  have h0 := congrFun (row_zero (F := F) n t j) a
  have hs := congrFun (row_split (F := F) n t ht j) a
  erw [Finset.sum_apply, Pi.zero_apply] at h0
  erw [Finset.sum_apply] at hs
  change (∑ r, relation (F := F) n t r * gridPoint (F := F) n t j r a) = 0 at h0
  change (∑ r, (relation (F := F) n t r * splitScalar (F := F) n t ht j r) *
    gridPoint (F := F) n t j r a) = hPrime (F := F) n t ht j a at hs
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply]
  simp_rw [Realization.oppositeSimple_two]
  change (∑ r, relation (F := F) n t r * (gridPoint (F := F) n t j r a *
      (Realization.basisVector (Sum.inl (some j)) b -
        splitScalar (F := F) n t ht j r * Realization.basisVector (Sum.inl none) b))) =
    -(hPrime (F := F) n t ht j a * Realization.basisVector (Sum.inl none) b)
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  have he : (∑ r, relation (F := F) n t r *
      (gridPoint (F := F) n t j r a * Realization.basisVector (Sum.inl (some j)) b)) = 0 := by
    simp_rw [← mul_assoc]
    rw [← Finset.sum_mul, h0, zero_mul]
  rw [he, zero_sub]
  congr 1
  rw [← hs, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r hr
  ring

theorem liftABzero_mem (n t : ℕ) (ht : t ≤ n) (v : Fin n → RatFunc F) :
    liftABzero n t v ∈ oppositeSpan n t ht 2 := by
  apply Circuit.span_lift_mem _ (hPrime_span (F := F) n t ht) _ _ _ v
  intro j
  have hm : (∑ r, relation (F := F) n t r •
      BigCentroid.oppositeSimple (oldPoint (F := F) n t ht (j, r)) 2) ∈ oppositeSpan n t ht 2 :=
    Submodule.sum_mem _ (fun r _ => Submodule.smul_mem _ _ (oldPoint_mem n t ht 2 (j, r)))
  rw [oldPoint_row] at hm
  exact (Submodule.neg_mem_iff _).mp hm

theorem gridTensorPoint_two_mem (n t : ℕ) (ht : t ≤ n) (p : Fin n × Option (Fin n)) :
    BigCentroid.oppositeSimple (gridTensorPoint (F := F) n t p) 2 ∈ oppositeSpan n t ht 2 := by
  have he : BigCentroid.oppositeSimple (gridTensorPoint (F := F) n t p) 2 =
      BigCentroid.oppositeSimple (oldPoint (F := F) n t ht p) 2 +
        splitScalar (F := F) n t ht p.1 p.2 • liftABzero n t (gridPoint (F := F) n t p.1 p.2) := by
    ext x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    erw [Realization.oppositeSimple_two, Realization.oppositeSimple_two]
    let a := gridPoint (F := F) n t p.1 p.2 (x ⟨0, by decide⟩)
    let b := Realization.basisVector (F := RatFunc F) (Sum.inl (some p.1)) (x ⟨1, by decide⟩)
    let c := Realization.basisVector (F := RatFunc F) (Sum.inl none) (x ⟨1, by decide⟩)
    let d := splitScalar (F := F) n t ht p.1 p.2
    change a * b = a * (b - d * c) + d * (a * c)
    ring
  rw [he]
  exact Submodule.add_mem _ (oldPoint_mem n t ht 2 p)
    (Submodule.smul_mem _ _ (liftABzero_mem n t ht _))

def liftABprime (n t : ℕ) : ((Fin n × Fin n) → RatFunc F) →ₗ[RatFunc F]
    (BigCentroid.Opposite (Core n t) 2 → RatFunc F) where
  toFun f x := Sum.elim (fun b => Option.elim b 0 (fun b => f (x ⟨0, by decide⟩, b)))
    (fun _ => 0) (x ⟨1, by decide⟩)
  map_add' f g := by
    ext x
    let a : Fin n := x ⟨0, by decide⟩
    let b : Option (Fin n) ⊕ Fin t := x ⟨1, by decide⟩
    change Sum.elim (fun b => Option.elim b 0 (fun b => f (a, b) + g (a, b))) (fun _ => 0) b =
      Sum.elim (fun b => Option.elim b 0 (fun b => f (a, b))) (fun _ => 0) b +
        Sum.elim (fun b => Option.elim b 0 (fun b => g (a, b))) (fun _ => 0) b
    rcases b with (_ | b) | b <;> simp
  map_smul' c f := by
    ext x
    let a : Fin n := x ⟨0, by decide⟩
    let b : Option (Fin n) ⊕ Fin t := x ⟨1, by decide⟩
    change Sum.elim (fun b => Option.elim b 0 (fun b => c * f (a, b))) (fun _ => 0) b =
      c * Sum.elim (fun b => Option.elim b 0 (fun b => f (a, b))) (fun _ => 0) b
    rcases b with (_ | b) | b <;> simp

theorem liftABprime_column (n t : ℕ) (p : Fin n × Fin n) :
    liftABprime n t (weightedColumn (M (F := F) n) (M (F := F) n) p) =
      BigCentroid.oppositeSimple (gridTensorPoint (F := F) n t (p.2, some p.1)) 2 := by
  let : DecidableEq (Fin n) := fun _ _ => Classical.propDecidable _
  ext x
  erw [Realization.oppositeSimple_two]
  let a : Fin n := x ⟨0, by decide⟩
  let b : Option (Fin n) ⊕ Fin t := x ⟨1, by decide⟩
  dsimp only [liftABprime, LinearMap.coe_mk, AddHom.coe_mk, weightedColumn,
    gridTensorPoint, factors_zero, factors_one]
  change Sum.elim (fun b => Option.elim b 0 (fun b => M (F := F) n a p.1 * M (F := F) n a p.2 *
      (if b = p.2 then 1 else 0))) (fun _ => 0) b =
    gridPoint (F := F) n t p.2 (some p.1) a * Realization.basisVector (Sum.inl (some p.2)) b
  rcases b with (_ | b) | b <;> simp [Realization.basisVector, gridPoint, H, ← M_apply, mul_comm]

theorem liftABprime_mem (n t : ℕ) (ht : t ≤ n) (v : Fin n × Fin n → RatFunc F) :
    liftABprime n t v ∈ oppositeSpan n t ht 2 := by
  apply Circuit.span_lift_mem _
    (weighted_columns_span (M (F := F) n) (M_isUnit (F := F) n) (M (F := F) n) (M_ne_zero (F := F) n))
    _ _ _ v
  intro p
  rw [liftABprime_column]
  exact gridTensorPoint_two_mem n t ht (p.2, some p.1)

theorem mappedPairs (n t : ℕ) (hn : 0 < n) (ht : t ≤ n) (i : Fin 3) (l : Dual n t i) :
    Realization.mapPairs (algebraMap F (RatFunc F)) (pairs n t hn ht) i l =
      Realization.basisVector (fun j : {j // j ≠ i} => pairPoint n t hn ht i l j.val) := by
  ext x
  simp only [Realization.mapPairs, pairs, Realization.basisVector]
  split_ifs <;> simp

theorem frameSpans (n t : ℕ) (hn : 0 < n) (ht : t ≤ n) :
    Realization.FrameSpans (Realization.mapPairs (algebraMap F (RatFunc F)) (pairs n t hn ht))
      (basePoint (F := F) n t ht) := by
  intro i l
  change _ ∈ oppositeSpan n t ht i
  rw [mappedPairs, ← Realization.oppositeSimple_basisVector (F := RatFunc F) (pairPoint n t hn ht i l) i]
  fin_cases i
  · rcases l with ⟨b, c⟩ | k
    · have hh : BigCentroid.oppositeSimple (fun i => Realization.basisVector (F := RatFunc F)
          (pairPoint n t hn ht 0 (Sum.inl (b, c)) i)) 0 =
          BigCentroid.oppositeSimple (gridTensorPoint (F := F) n t (b, c)) 0 := by
        ext x
        erw [Realization.oppositeSimple_zero, Realization.oppositeSimple_zero]
        rfl
      erw [hh]
      exact gridTensorPoint_zero_mem n t ht (b, c)
    · have hh : BigCentroid.oppositeSimple (fun i => Realization.basisVector (F := RatFunc F)
          (pairPoint n t hn ht 0 (Sum.inr k) i)) 0 =
          BigCentroid.oppositeSimple (extraPoint (F := F) n t ht k) 0 := by
        ext x
        erw [Realization.oppositeSimple_zero, Realization.oppositeSimple_zero]
        rfl
      erw [hh]
      exact extraPoint_mem n t ht 0 k
  · rcases l with ⟨a, c⟩
    have hh : BigCentroid.oppositeSimple (fun i => Realization.basisVector (F := RatFunc F)
        (pairPoint n t hn ht 1 (a, c) i)) 1 = liftAC n t (Realization.basisVector (a, c)) := by
      ext x
      erw [Realization.oppositeSimple_one]
      let a₀ : Fin n := x ⟨0, by decide⟩
      let c₀ : Option (Fin n) ⊕ Fin t := x ⟨2, by decide⟩
      change Realization.basisVector a a₀ * Realization.basisVector (Sum.inl c) c₀ =
        Sum.elim (fun d => Realization.basisVector (a, c) (a₀, d)) (fun _ => 0) c₀
      cases c₀ <;> simp [Realization.basisVector, mul_ite, eq_comm]
      split_ifs <;> simp_all
    erw [hh]
    exact liftAC_mem n t ht (Realization.basisVector (a, c))
  · rcases l with ⟨a, _ | b⟩
    · have hh : BigCentroid.oppositeSimple (fun i => Realization.basisVector (F := RatFunc F)
          (pairPoint n t hn ht 2 (a, none) i)) 2 = liftABzero n t (Realization.basisVector a) := by
        ext x
        erw [Realization.oppositeSimple_two]
        rfl
      erw [hh]
      exact liftABzero_mem n t ht (Realization.basisVector a)
    · have hh : BigCentroid.oppositeSimple (fun i => Realization.basisVector (F := RatFunc F)
          (pairPoint n t hn ht 2 (a, some b) i)) 2 =
          liftABprime n t (Realization.basisVector (a, b)) := by
        ext x
        erw [Realization.oppositeSimple_two]
        let a₀ : Fin n := x ⟨0, by decide⟩
        let b₀ : Option (Fin n) ⊕ Fin t := x ⟨1, by decide⟩
        change Realization.basisVector a a₀ * Realization.basisVector (Sum.inl (some b)) b₀ =
          Sum.elim (fun d => Option.elim d 0 (fun d => Realization.basisVector (a, b) (a₀, d)))
            (fun _ => 0) b₀
        rcases b₀ with (_ | b₀) | b₀ <;> simp [Realization.basisVector, mul_ite, eq_comm]
        split_ifs <;> simp_all
      erw [hh]
      exact liftABprime_mem n t ht (Realization.basisVector (a, b))

end

end Lemmata.Centroid.Construction.Rectangular
