module

public import Lemmata.Centroid.Proof.Construction.HookFrames
public import Lemmata.Centroid.Proof.Construction.CircuitSpans

@[expose] public section

open scoped BigOperators
open Classical

namespace Lemmata.Centroid.Construction.Hook

noncomputable section

variable {F : Type*} [Field F]

def oppositeSpan (n t : ℕ) (ht : t ≤ n) (i : Fin 3) :=
  Submodule.span (RatFunc F) (Set.range (fun p => BigCentroid.oppositeSimple (basePoint (F := F) n t ht p) i))

theorem oldPoint_mem (n t : ℕ) (ht : t ≤ n) (i : Fin 3) (p : Option (Fin n) × Fin n) :
    BigCentroid.oppositeSimple (oldPoint (F := F) n t ht p) i ∈ oppositeSpan (F := F) n t ht i :=
  Submodule.subset_span ⟨Sum.inl (Sum.inl p), rfl⟩

theorem rowPoint_mem (n t : ℕ) (ht : t ≤ n) (i : Fin 3) (j : Fin t) :
    BigCentroid.oppositeSimple (rowPoint (F := F) n t ht j) i ∈ oppositeSpan (F := F) n t ht i :=
  Submodule.subset_span ⟨Sum.inl (Sum.inr j), rfl⟩

def liftACzero (n : ℕ) : (Fin n → RatFunc F) →ₗ[RatFunc F]
    (BigCentroid.Opposite (Core n) 1 → RatFunc F) where
  toFun f x := liftCore f (x ⟨0, by decide⟩) * Realization.basisVector none (x ⟨2, by decide⟩)
  map_add' f g := by
    ext x
    cases h : x ⟨0, by decide⟩ <;> simp [liftCore, h, add_mul]
  map_smul' c f := by
    ext x
    cases h : x ⟨0, by decide⟩ <;> simp [liftCore, h, mul_assoc]

def extraAC (n : ℕ) (k : Fin n) : BigCentroid.Opposite (Core n) 1 → RatFunc F :=
  fun x => Realization.basisVector none (x ⟨0, by decide⟩) * fVector (F := F) n k (x ⟨2, by decide⟩)

def extraAB (n : ℕ) (j : Option (Fin n)) : BigCentroid.Opposite (Core n) 2 → RatFunc F :=
  fun x => Realization.basisVector none (x ⟨0, by decide⟩) * Realization.basisVector j (x ⟨1, by decide⟩)

theorem sum_columnNu_scalar (n t : ℕ) (ht₀ : 0 < t) (ht : t ≤ n) :
    (∑ k, columnNu (F := F) n t ht k) = 1 := by
  have h := sum_columnNu (F := F) n t ht (fun _ => (1 : RatFunc F))
  simpa only [smul_eq_mul, mul_one, sum_eta (F := F) t ht₀] using h

theorem sum_rowEta_scalar (n t : ℕ) (ht₀ : 0 < t) (ht : t ≤ n) :
    (∑ j, rowEta (F := F) n t ht j) = 1 := by
  have h := sum_rowEta (F := F) n t ht (fun _ => (1 : RatFunc F))
  simpa only [smul_eq_mul, mul_one, sum_eta (F := F) t ht₀] using h

theorem rowPoint_one (n t : ℕ) (ht : t ≤ n) (j : Fin t) :
    BigCentroid.oppositeSimple (rowPoint (F := F) n t ht j) 1 =
      liftACzero (F := F) n (g (F := F) n t (some (j.castLE ht))) := by
  ext x
  erw [Realization.oppositeSimple_one]
  rfl

theorem row_relation (n t : ℕ) (ht₀ : 0 < t) (ht : t ≤ n) (j : Fin t) :
    (∑ k, BigCentroid.oppositeSimple (oldPoint (F := F) n t ht (some (j.castLE ht), k)) 2) -
      BigCentroid.oppositeSimple (rowPoint (F := F) n t ht j) 2 =
      -eta (F := F) t j • extraAB (F := F) n (some (j.castLE ht)) := by
  ext x
  simp only [Finset.sum_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  simp_rw [Realization.oppositeSimple_two]
  let a : Option (Fin n) := x ⟨0, by decide⟩
  let b : Option (Fin n) := x ⟨1, by decide⟩
  change (∑ k, (liftCore (gridPoint (F := F) n t (some (j.castLE ht)) k) a -
      (rowEta (F := F) n t ht (some (j.castLE ht)) * columnNu (F := F) n t ht k) *
        Realization.basisVector none a) * Realization.basisVector (some (j.castLE ht)) b) -
      liftCore (g (F := F) n t (some (j.castLE ht))) a * Realization.basisVector (some (j.castLE ht)) b =
    -eta (F := F) t j * (Realization.basisVector none a * Realization.basisVector (some (j.castLE ht)) b)
  rw [rowEta_selected]
  have hg : (∑ k, liftCore (gridPoint (F := F) n t (some (j.castLE ht)) k) a) =
      liftCore (g (F := F) n t (some (j.castLE ht))) a := by
    cases a with
    | none => simp [liftCore]
    | some a =>
      have h := congrFun (sum_grid_row (F := F) n t (some (j.castLE ht))) a
      erw [Finset.sum_apply] at h
      exact h
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hg]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  rw [← Finset.sum_mul, sum_columnNu_scalar (F := F) n t ht₀ ht]
  ring

theorem extraAB_mem (n t : ℕ) (ht₀ : 0 < t) (ht : t ≤ n) (j : Fin t) :
    extraAB (F := F) n (some (j.castLE ht)) ∈ oppositeSpan (F := F) n t ht 2 := by
  have hm : (∑ k, BigCentroid.oppositeSimple (oldPoint (F := F) n t ht (some (j.castLE ht), k)) 2) -
      BigCentroid.oppositeSimple (rowPoint (F := F) n t ht j) 2 ∈ oppositeSpan (F := F) n t ht 2 :=
    Submodule.sub_mem _ (Submodule.sum_mem _ (fun k _ => oldPoint_mem (F := F) n t ht 2 _)) (rowPoint_mem (F := F) n t ht 2 j)
  rw [row_relation (F := F) n t ht₀ ht] at hm
  have h := Submodule.smul_mem _ (-eta (F := F) t j)⁻¹ hm
  rwa [smul_smul, inv_mul_cancel₀ (neg_ne_zero.mpr (eta_ne_zero (F := F) t j)), one_smul] at h

theorem columnNu_unselected (n t : ℕ) (ht : t ≤ n) (k : Fin n) (hk : ¬ k.val < t) :
    columnNu (F := F) n t ht k = 0 := by
  apply Finset.sum_eq_zero
  intro r hr
  apply ite_eq_right
  intro he
  have hv := congrArg Fin.val he
  change k.val = r.val at hv
  have hr := r.isLt
  exact hk (by omega)

theorem column_relation (n t : ℕ) (ht₀ : 0 < t) (ht : t ≤ n) (k : Fin n) :
    (∑ j, BigCentroid.oppositeSimple (oldPoint (F := F) n t ht (j, k)) 1) =
      -liftACzero (F := F) n (d (F := F) n t ht k) - columnNu (F := F) n t ht k • extraAC (F := F) n k := by
  ext x
  let a : Option (Fin n) := x ⟨0, by decide⟩
  let c : Option (Fin n) := x ⟨2, by decide⟩
  have hcol : (∑ j, liftCore (gridPoint (F := F) n t j k) a) = 0 := by
    cases a with
    | none => simp [liftCore]
    | some a =>
      have h := congrFun (sum_grid_column (F := F) n t k) a
      erw [Finset.sum_apply, Pi.zero_apply] at h
      exact h
  have hsel : (∑ j, if SelectedRow ht j then liftCore (gridPoint (F := F) n t j k) a else 0) =
      liftCore (d (F := F) n t ht k) a := by
    rw [selected_sum]
    cases a with
    | none => simp [liftCore]
    | some a =>
      have h := congrFun (sum_grid_selected (F := F) n t ht k) a
      erw [Finset.sum_apply] at h
      exact h
  have hs : (∑ j, rowEta (F := F) n t ht j * splitC (F := F) n t ht j k c) =
      fVector (F := F) n k c := by
    have h := sum_rowEta (F := F) n t ht (fun j => splitC (F := F) n t ht j k c)
    simpa only [smul_eq_mul, splitC_selected, ← Finset.sum_mul, sum_eta (F := F) t ht₀, one_mul] using h
  have hpoint (j : Option (Fin n)) :
      liftCore (gridPoint (F := F) n t j k) a * splitC (F := F) n t ht j k c =
      liftCore (gridPoint (F := F) n t j k) a * Realization.basisVector (some k) c -
        (if SelectedRow ht j then liftCore (gridPoint (F := F) n t j k) a else 0) *
          Realization.basisVector none c := by
    unfold splitC
    split_ifs
    · change _ * (Realization.basisVector (F := RatFunc F) (some k) c -
        Realization.basisVector (F := RatFunc F) none c) = _
      ring
    · ring
  have hc : (∑ j, liftCore (gridPoint (F := F) n t j k) a * splitC (F := F) n t ht j k c) =
      -(liftCore (d (F := F) n t ht k) a * Realization.basisVector none c) := by
    simp_rw [hpoint]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_mul, hcol, hsel, zero_mul, zero_sub]
  simp only [Finset.sum_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  simp_rw [Realization.oppositeSimple_one]
  change (∑ j, (liftCore (gridPoint (F := F) n t j k) a -
      (rowEta (F := F) n t ht j * columnNu (F := F) n t ht k) * Realization.basisVector none a) *
        splitC (F := F) n t ht j k c) = _
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib, hc]
  have he : (∑ j, (rowEta (F := F) n t ht j * columnNu (F := F) n t ht k) *
      Realization.basisVector none a * splitC (F := F) n t ht j k c) =
      columnNu (F := F) n t ht k * Realization.basisVector none a * fVector (F := F) n k c := by
    rw [← hs, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [he]
  change -(liftCore (d (F := F) n t ht k) a * Realization.basisVector none c) -
      columnNu (F := F) n t ht k * Realization.basisVector none a * fVector (F := F) n k c =
    -(liftCore (d (F := F) n t ht k) a * Realization.basisVector none c) -
      columnNu (F := F) n t ht k * (Realization.basisVector none a * fVector (F := F) n k c)
  ring

theorem liftACzero_d_mem (n t : ℕ) (ht₀ : 0 < t) (ht : t ≤ n) (k : Fin n) (hk : ¬ k.val < t) :
    liftACzero (F := F) n (d (F := F) n t ht k) ∈ oppositeSpan (F := F) n t ht 1 := by
  have hm : (∑ j, BigCentroid.oppositeSimple (oldPoint (F := F) n t ht (j, k)) 1) ∈ oppositeSpan (F := F) n t ht 1 :=
    Submodule.sum_mem _ (fun j _ => oldPoint_mem (F := F) n t ht 1 _)
  rw [column_relation (F := F) n t ht₀ ht, columnNu_unselected (F := F) n t ht k hk, zero_smul, sub_zero] at hm
  exact (Submodule.neg_mem_iff _).mp hm

theorem liftACzero_mem (n t : ℕ) (ht₀ : 0 < t) (ht : t ≤ n) (u : Fin n → RatFunc F) :
    liftACzero (F := F) n u ∈ oppositeSpan (F := F) n t ht 1 := by
  apply Circuit.span_lift_mem _ (mixedPoint_span (F := F) n t ht₀ ht) _ _ _ u
  intro j
  by_cases hj : j.val < t
  · let r : Fin t := ⟨j.val, hj⟩
    have hr : r.castLE ht = j := Fin.ext rfl
    have hm := rowPoint_mem (F := F) n t ht 1 r
    rw [rowPoint_one, hr] at hm
    simpa only [mixedPoint, hj, ite_true] using hm
  · simpa only [mixedPoint, hj, ite_false] using liftACzero_d_mem (F := F) n t ht₀ ht j hj

theorem extraAC_mem (n t : ℕ) (ht₀ : 0 < t) (ht : t ≤ n) (k : Fin t) :
    extraAC (F := F) n (k.castLE ht) ∈ oppositeSpan (F := F) n t ht 1 := by
  have hm : (∑ j, BigCentroid.oppositeSimple (oldPoint (F := F) n t ht (j, k.castLE ht)) 1) ∈ oppositeSpan (F := F) n t ht 1 :=
    Submodule.sum_mem _ (fun j _ => oldPoint_mem (F := F) n t ht 1 _)
  rw [column_relation (F := F) n t ht₀ ht] at hm
  have h := Submodule.add_mem _ hm (liftACzero_mem (F := F) n t ht₀ ht (d (F := F) n t ht (k.castLE ht)))
  have he : (-liftACzero (F := F) n (d (F := F) n t ht (k.castLE ht)) -
      columnNu (F := F) n t ht (k.castLE ht) • extraAC (F := F) n (k.castLE ht)) +
      liftACzero (F := F) n (d (F := F) n t ht (k.castLE ht)) =
      -columnNu (F := F) n t ht (k.castLE ht) • extraAC (F := F) n (k.castLE ht) := by
    simp only [neg_smul]
    abel
  rw [he, columnNu_selected] at h
  have h' := Submodule.smul_mem _ (-eta (F := F) t k)⁻¹ h
  rwa [smul_smul, inv_mul_cancel₀ (neg_ne_zero.mpr (eta_ne_zero (F := F) t k)), one_smul] at h'

def liftABrow (n : ℕ) (j : Option (Fin n)) : (Fin n → RatFunc F) →ₗ[RatFunc F]
    (BigCentroid.Opposite (Core n) 2 → RatFunc F) where
  toFun f x := liftCore f (x ⟨0, by decide⟩) * Realization.basisVector j (x ⟨1, by decide⟩)
  map_add' f g := by
    ext x
    cases h : x ⟨0, by decide⟩ <;> simp [liftCore, h, add_mul]
  map_smul' c f := by
    ext x
    cases h : x ⟨0, by decide⟩ <;> simp [liftCore, h, mul_assoc]

def liftACcolumn (n : ℕ) (k : Fin n) : (Fin n → RatFunc F) →ₗ[RatFunc F]
    (BigCentroid.Opposite (Core n) 1 → RatFunc F) where
  toFun f x := liftCore f (x ⟨0, by decide⟩) * Realization.basisVector (some k) (x ⟨2, by decide⟩)
  map_add' f g := by
    ext x
    cases h : x ⟨0, by decide⟩ <;> simp [liftCore, h, add_mul]
  map_smul' c f := by
    ext x
    cases h : x ⟨0, by decide⟩ <;> simp [liftCore, h, mul_assoc]

theorem rowEta_unselected (n t : ℕ) (ht : t ≤ n) (j : Option (Fin n)) (hj : ¬ SelectedRow ht j) :
    rowEta (F := F) n t ht j = 0 := by
  apply Finset.sum_eq_zero
  intro r hr
  exact ite_eq_right (fun he => hj ⟨r, he⟩)

theorem liftABrow_grid_mem (n t : ℕ) (ht₀ : 0 < t) (ht : t ≤ n)
    (j : Option (Fin n)) (k : Fin n) :
    liftABrow (F := F) n j (gridPoint (F := F) n t j k) ∈ oppositeSpan (F := F) n t ht 2 := by
  have he : liftABrow (F := F) n j (gridPoint (F := F) n t j k) =
      BigCentroid.oppositeSimple (oldPoint (F := F) n t ht (j, k)) 2 +
        (rowEta (F := F) n t ht j * columnNu (F := F) n t ht k) • extraAB (F := F) n j := by
    ext x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    erw [Realization.oppositeSimple_two]
    let a := liftCore (gridPoint (F := F) n t j k) (x ⟨0, by decide⟩)
    let b := Realization.basisVector (F := RatFunc F) j (x ⟨1, by decide⟩)
    let c := Realization.basisVector (F := RatFunc F) none (x ⟨0, by decide⟩)
    let d := rowEta (F := F) n t ht j * columnNu (F := F) n t ht k
    change a * b = (a - d * c) * b + d * (c * b)
    ring
  rw [he]
  apply Submodule.add_mem _ (oldPoint_mem (F := F) n t ht 2 _)
  by_cases hj : SelectedRow ht j
  · obtain ⟨r, rfl⟩ := hj
    exact Submodule.smul_mem _ _ (extraAB_mem (F := F) n t ht₀ ht r)
  · rw [rowEta_unselected (F := F) n t ht j hj, zero_mul, zero_smul]
    exact Submodule.zero_mem _

theorem liftABrow_mem (n t : ℕ) (ht₀ : 0 < t) (ht : t ≤ n)
    (j : Option (Fin n)) (u : Fin n → RatFunc F) :
    liftABrow (F := F) n j u ∈ oppositeSpan (F := F) n t ht 2 := by
  apply Circuit.span_lift_mem _ (grid_row_span (F := F) n t j) _ _ _ u
  intro k
  exact liftABrow_grid_mem (F := F) n t ht₀ ht j k

theorem weightedExtraAC_mem (n t : ℕ) (ht₀ : 0 < t) (ht : t ≤ n) (k : Fin n) :
    columnNu (F := F) n t ht k • extraAC (F := F) n k ∈ oppositeSpan (F := F) n t ht 1 := by
  by_cases hk : k.val < t
  · let r : Fin t := ⟨k.val, hk⟩
    have hr : r.castLE ht = k := Fin.ext rfl
    rw [← hr]
    exact Submodule.smul_mem _ _ (extraAC_mem (F := F) n t ht₀ ht r)
  · rw [columnNu_unselected (F := F) n t ht k hk, zero_smul]
    exact Submodule.zero_mem _

theorem liftACcolumn_grid_mem (n t : ℕ) (ht₀ : 0 < t) (ht : t ≤ n)
    (j : Option (Fin n)) (k : Fin n) :
    liftACcolumn (F := F) n k (gridPoint (F := F) n t j k) ∈ oppositeSpan (F := F) n t ht 1 := by
  by_cases hj : SelectedRow ht j
  · have he : liftACcolumn (F := F) n k (gridPoint (F := F) n t j k) =
        BigCentroid.oppositeSimple (oldPoint (F := F) n t ht (j, k)) 1 +
          liftACzero (F := F) n (gridPoint (F := F) n t j k) +
          rowEta (F := F) n t ht j • (columnNu (F := F) n t ht k • extraAC (F := F) n k) := by
      ext x
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      erw [Realization.oppositeSimple_one]
      simp only [oldPoint, factors_zero, factors_two, splitC, hj, ite_true]
      let a : Option (Fin n) := x ⟨0, by decide⟩
      let c : Option (Fin n) := x ⟨2, by decide⟩
      change liftCore (gridPoint (F := F) n t j k) a * Realization.basisVector (some k) c =
        (liftCore (gridPoint (F := F) n t j k) a -
          (rowEta (F := F) n t ht j * columnNu (F := F) n t ht k) * Realization.basisVector none a) *
          (Realization.basisVector (some k) c - Realization.basisVector none c) +
          liftCore (gridPoint (F := F) n t j k) a * Realization.basisVector none c +
          rowEta (F := F) n t ht j * (columnNu (F := F) n t ht k *
            (Realization.basisVector none a * (Realization.basisVector (some k) c - Realization.basisVector none c)))
      ring
    rw [he]
    exact Submodule.add_mem _
      (Submodule.add_mem _ (oldPoint_mem (F := F) n t ht 1 _) (liftACzero_mem (F := F) n t ht₀ ht _))
      (Submodule.smul_mem _ _ (weightedExtraAC_mem (F := F) n t ht₀ ht k))
  · have he : liftACcolumn (F := F) n k (gridPoint (F := F) n t j k) =
        BigCentroid.oppositeSimple (oldPoint (F := F) n t ht (j, k)) 1 := by
      ext x
      erw [Realization.oppositeSimple_one]
      simp only [oldPoint, factors_zero, factors_two, splitC, hj, ite_false,
        rowEta_unselected (F := F) n t ht j hj, zero_mul, zero_smul, sub_zero]
      rfl
    rw [he]
    exact oldPoint_mem (F := F) n t ht 1 _

theorem liftACcolumn_mem (n t : ℕ) (ht₀ : 0 < t) (ht : t ≤ n)
    (k : Fin n) (u : Fin n → RatFunc F) :
    liftACcolumn (F := F) n k u ∈ oppositeSpan (F := F) n t ht 1 := by
  apply Circuit.span_lift_mem _ (grid_column_span (F := F) n t k) _ _ _ u
  intro j
  exact liftACcolumn_grid_mem (F := F) n t ht₀ ht (some j) k

end

end Lemmata.Centroid.Construction.Hook
