module

public import Lemmata.Centroid.Proof.Construction.CircuitFrames

@[expose] public section

open scoped BigOperators
open Classical

namespace Lemmata.Centroid.Construction.Circuit

noncomputable section

variable {F : Type*} [Field F]

def oppositeSpan (q ν : ℕ)
    (e : (A q ν → RatFunc F) ≃ₗ[RatFunc F] (A q ν → RatFunc F)) (i : Fin 3) :=
  Submodule.span (RatFunc F) (Set.range (fun p => BigCentroid.oppositeSimple (basePoint q ν e p) i))

theorem oldPoint_mem (q ν : ℕ)
    (e : (A q ν → RatFunc F) ≃ₗ[RatFunc F] (A q ν → RatFunc F))
    (i : Fin 3) (p : A q ν × A q ν) :
    BigCentroid.oppositeSimple (oldPoint q ν e p) i ∈ oppositeSpan q ν e i :=
  Submodule.subset_span ⟨Sum.inl p, rfl⟩

theorem extraPoint_mem (q ν : ℕ)
    (e : (A q ν → RatFunc F) ≃ₗ[RatFunc F] (A q ν → RatFunc F))
    (i : Fin 3) (j : Fin (q + 1)) :
    BigCentroid.oppositeSimple (extraPoint q ν e j) i ∈ oppositeSpan q ν e i :=
  Submodule.subset_span ⟨Sum.inr j, rfl⟩

theorem gridPoint_mem (q ν : ℕ)
    (e : (A q ν → RatFunc F) ≃ₗ[RatFunc F] (A q ν → RatFunc F))
    (i : Fin 3) (p : A q ν × A q ν) :
    BigCentroid.oppositeSimple (gridPoint q ν e p) i ∈ oppositeSpan q ν e i := by
  by_cases hd : p.1 = p.2 ∧ p.1.isLeft
  · obtain ⟨hjk, hj⟩ := hd
    rcases p with ⟨j, k⟩
    dsimp only at hjk hj
    subst k
    cases j with
    | inr j => simp at hj
    | inl j =>
      have h0 : BigCentroid.oppositeSimple (gridPoint q ν e (Sum.inl j, Sum.inl j)) 0 =
          BigCentroid.oppositeSimple (oldPoint q ν e (Sum.inl j, Sum.inl j)) 0 +
            BigCentroid.oppositeSimple (extraPoint q ν e j) 0 := by
        ext x
        simp only [Pi.add_apply]
        erw [Realization.oppositeSimple_zero, Realization.oppositeSimple_zero,
          Realization.oppositeSimple_zero]
        simp only [gridPoint, oldPoint, extraPoint, factors_one, factors_two,
          diagonalCoefficient, and_self, Sum.isLeft_inl, ite_true, one_smul]
        let b := Realization.basisVector (F := RatFunc F) (Sum.inl (Sum.inl j)) (x ⟨1, by decide⟩)
        let c := Realization.basisVector (F := RatFunc F) (Sum.inl (Sum.inl j)) (x ⟨2, by decide⟩)
        let d := Realization.basisVector (F := RatFunc F) (Sum.inr none) (x ⟨2, by decide⟩)
        change b * c = b * (c - d) + b * d
        ring
      have h1 : BigCentroid.oppositeSimple (gridPoint q ν e (Sum.inl j, Sum.inl j)) 1 =
          BigCentroid.oppositeSimple (oldPoint q ν e (Sum.inl j, Sum.inl j)) 1 +
            BigCentroid.oppositeSimple (extraPoint q ν e j) 1 := by
        ext x
        simp only [Pi.add_apply]
        erw [Realization.oppositeSimple_one, Realization.oppositeSimple_one,
          Realization.oppositeSimple_one]
        simp only [gridPoint, oldPoint, extraPoint, factors_zero, factors_two,
          diagonalCoefficient, and_self, Sum.isLeft_inl, ite_true, one_smul]
        let a := normalizedPoint q ν e (Sum.inl j) (Sum.inl j) (x ⟨0, by decide⟩)
        let c := Realization.basisVector (F := RatFunc F) (Sum.inl (Sum.inl j)) (x ⟨2, by decide⟩)
        let d := Realization.basisVector (F := RatFunc F) (Sum.inr none) (x ⟨2, by decide⟩)
        change a * c = a * (c - d) + a * d
        ring
      have h2 : BigCentroid.oppositeSimple (gridPoint q ν e (Sum.inl j, Sum.inl j)) 2 =
          BigCentroid.oppositeSimple (oldPoint q ν e (Sum.inl j, Sum.inl j)) 2 := by
        ext x
        erw [Realization.oppositeSimple_two, Realization.oppositeSimple_two]
        rfl
      fin_cases i
      · change BigCentroid.oppositeSimple (gridPoint q ν e (Sum.inl j, Sum.inl j)) 0 ∈ oppositeSpan q ν e 0
        rw [h0]
        exact Submodule.add_mem _ (oldPoint_mem q ν e 0 _) (extraPoint_mem q ν e 0 j)
      · change BigCentroid.oppositeSimple (gridPoint q ν e (Sum.inl j, Sum.inl j)) 1 ∈ oppositeSpan q ν e 1
        rw [h1]
        exact Submodule.add_mem _ (oldPoint_mem q ν e 1 _) (extraPoint_mem q ν e 1 j)
      · change BigCentroid.oppositeSimple (gridPoint q ν e (Sum.inl j, Sum.inl j)) 2 ∈ oppositeSpan q ν e 2
        rw [h2]
        exact oldPoint_mem q ν e 2 _
  · have heq : oldPoint q ν e p = gridPoint q ν e p := by
      simp only [oldPoint, diagonalCoefficient, ite_eq_right hd, zero_smul, sub_zero]
      rfl
    rw [← heq]
    exact oldPoint_mem q ν e i p

def liftAC (q ν : ℕ) : ((A q ν × A q ν) → RatFunc F) →ₗ[RatFunc F]
    (BigCentroid.Opposite (Core q ν) 1 → RatFunc F) where
  toFun f x := Sum.elim (fun c => f (x ⟨0, by decide⟩, c)) (fun _ => 0) (x ⟨2, by decide⟩)
  map_add' f g := by
    ext x
    let a : A q ν := x ⟨0, by decide⟩
    let c : A q ν ⊕ Option (Fin q) := x ⟨2, by decide⟩
    change Sum.elim (fun c => f (a, c) + g (a, c)) (fun _ => 0) c =
      Sum.elim (fun c => f (a, c)) (fun _ => 0) c + Sum.elim (fun c => g (a, c)) (fun _ => 0) c
    cases c <;> simp
  map_smul' c f := by
    ext x
    let a : A q ν := x ⟨0, by decide⟩
    let b : A q ν ⊕ Option (Fin q) := x ⟨2, by decide⟩
    change Sum.elim (fun b => c * f (a, b)) (fun _ => 0) b =
      c * Sum.elim (fun b => f (a, b)) (fun _ => 0) b
    cases b <;> simp

def liftAB (q ν : ℕ) : ((A q ν × A q ν) → RatFunc F) →ₗ[RatFunc F]
    (BigCentroid.Opposite (Core q ν) 2 → RatFunc F) where
  toFun f x := Sum.elim (fun b => f (x ⟨0, by decide⟩, b)) (fun _ => 0) (x ⟨1, by decide⟩)
  map_add' f g := by
    ext x
    let a : A q ν := x ⟨0, by decide⟩
    let b : A q ν ⊕ Unit := x ⟨1, by decide⟩
    change Sum.elim (fun b => f (a, b) + g (a, b)) (fun _ => 0) b =
      Sum.elim (fun b => f (a, b)) (fun _ => 0) b + Sum.elim (fun b => g (a, b)) (fun _ => 0) b
    cases b <;> simp
  map_smul' c f := by
    ext x
    let a : A q ν := x ⟨0, by decide⟩
    let b : A q ν ⊕ Unit := x ⟨1, by decide⟩
    change Sum.elim (fun b => c * f (a, b)) (fun _ => 0) b =
      c * Sum.elim (fun b => f (a, b)) (fun _ => 0) b
    cases b <;> simp

theorem span_lift_mem {K V W J : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (v : J → V)
    (hv : Submodule.span K (Set.range v) = ⊤) (L : V →ₗ[K] W) (S : Submodule K W)
    (hL : ∀ j, L (v j) ∈ S) (x : V) : L x ∈ S := by
  have hle : Submodule.span K (Set.range v) ≤ S.comap L :=
    Submodule.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact hL j)
  exact hle (by rw [hv]; trivial)

theorem liftAC_column (q ν : ℕ)
    (e : (A q ν → RatFunc F) ≃ₗ[RatFunc F] (A q ν → RatFunc F))
    (p : A q ν × A q ν) :
    liftAC q ν (normalizedColumn e (M q ν) (H q ν) p) =
      BigCentroid.oppositeSimple (gridPoint q ν e p) 1 := by
  ext x
  erw [Realization.oppositeSimple_one]
  let a : A q ν := x ⟨0, by decide⟩
  let c : A q ν ⊕ Option (Fin q) := x ⟨2, by decide⟩
  let v := normalizedPoint q ν e p.1 p.2 a
  change Sum.elim (fun c => v * Realization.basisVector p.2 c) (fun _ => 0) c =
    v * Realization.basisVector (Sum.inl p.2) c
  cases c <;> simp [Realization.basisVector]

theorem liftAB_column (q ν : ℕ)
    (e : (A q ν → RatFunc F) ≃ₗ[RatFunc F] (A q ν → RatFunc F))
    (p : A q ν × A q ν) :
    liftAB q ν (normalizedColumn e (H q ν) (M q ν) p) =
      BigCentroid.oppositeSimple (gridPoint q ν e p.swap) 2 := by
  ext x
  erw [Realization.oppositeSimple_two]
  let a : A q ν := x ⟨0, by decide⟩
  let b : A q ν ⊕ Unit := x ⟨1, by decide⟩
  have hv : e (fun a => H (F := F) q ν a p.1 * M q ν a p.2) =
      normalizedPoint q ν e p.2 p.1 := by
    congr 1
    ext a
    exact mul_comm _ _
  change Sum.elim (fun b => e (fun a => H (F := F) q ν a p.1 * M q ν a p.2) a *
    Realization.basisVector p.2 b) (fun _ => 0) b =
      normalizedPoint q ν e p.2 p.1 a * Realization.basisVector (Sum.inl p.2) b
  rw [hv]
  cases b <;> simp [Realization.basisVector]

theorem liftAC_mem (q ν : ℕ) (hq : 0 < q)
    (e : (A q ν → RatFunc F) ≃ₗ[RatFunc F] (A q ν → RatFunc F))
    (x : A q ν × A q ν → RatFunc F) : liftAC q ν x ∈ oppositeSpan q ν e 1 := by
  apply span_lift_mem _ (normalized_columns_span e (M q ν) (M_isUnit (F := F) q ν)
    (H q ν) (H_ne_zero (F := F) q ν hq)) _ _ _ x
  intro p
  rw [liftAC_column]
  exact gridPoint_mem (F := F) q ν e 1 p

theorem liftAB_mem (q ν : ℕ)
    (e : (A q ν → RatFunc F) ≃ₗ[RatFunc F] (A q ν → RatFunc F))
    (x : A q ν × A q ν → RatFunc F) : liftAB q ν x ∈ oppositeSpan q ν e 2 := by
  apply span_lift_mem _ (normalized_columns_span e (H q ν) (H_isUnit (F := F) q ν)
    (M q ν) (M_ne_zero (F := F) q ν)) _ _ _ x
  intro p
  rw [liftAB_column]
  exact gridPoint_mem (F := F) q ν e 2 p.swap

theorem mappedPairs (q ν : ℕ) (i : Fin 3) (l : Dual q ν i) :
    Realization.mapPairs (algebraMap F (RatFunc F)) (pairs q ν) i l =
      Realization.basisVector (fun j : {j // j ≠ i} => pairPoint q ν i l j.val) := by
  ext x
  simp only [Realization.mapPairs, pairs, Realization.basisVector]
  split_ifs <;> simp

theorem normalizedPoint_active (q ν : ℕ)
    (e : (A q ν → RatFunc F) ≃ₗ[RatFunc F] (A q ν → RatFunc F))
    (he : ∀ j : Fin q, e (hadamardColumn (F := F) q ν j.castSucc) =
      Pi.single (Sum.inl j.castSucc) 1) (j : Fin q) :
    normalizedPoint q ν e (Sum.inl j.castSucc) (Sum.inl j.castSucc) =
      Realization.basisVector (Sum.inl j.castSucc) := by
  have hh : (fun a => M (F := F) q ν a (Sum.inl j.castSucc) *
      H (F := F) q ν a (Sum.inl j.castSucc)) = hadamardColumn q ν j.castSucc := by
    ext a
    exact (map_mul (algebraMap (Polynomial F) (RatFunc F)) _ _).symm
  rw [normalizedPoint, hh, he]
  ext a
  simp [Pi.single_apply, Realization.basisVector]

theorem frameSpans (q ν : ℕ) (hq : 0 < q)
    (e : (A q ν → RatFunc F) ≃ₗ[RatFunc F] (A q ν → RatFunc F))
    (he : ∀ j : Fin q, e (hadamardColumn (F := F) q ν j.castSucc) =
      Pi.single (Sum.inl j.castSucc) 1) :
    Realization.FrameSpans (Realization.mapPairs (algebraMap F (RatFunc F)) (pairs q ν))
      (basePoint q ν e) := by
  intro i l
  change _ ∈ oppositeSpan q ν e i
  rw [mappedPairs, ← Realization.oppositeSimple_basisVector (F := RatFunc F) (pairPoint q ν i l) i]
  fin_cases i
  · rcases l with ⟨b, c⟩ | j
    · have hh : BigCentroid.oppositeSimple (fun k => Realization.basisVector (F := RatFunc F)
          (pairPoint q ν 0 (Sum.inl (b, c)) k)) 0 =
          BigCentroid.oppositeSimple (gridPoint q ν e (b, c)) 0 := by
        ext x
        erw [Realization.oppositeSimple_zero, Realization.oppositeSimple_zero]
        rfl
      erw [hh]
      exact gridPoint_mem (F := F) q ν e 0 (b, c)
    · have hh : BigCentroid.oppositeSimple (fun k => Realization.basisVector (F := RatFunc F)
          (pairPoint q ν 0 (Sum.inr j) k)) 0 =
          BigCentroid.oppositeSimple (extraPoint q ν e j) 0 := by
        ext x
        erw [Realization.oppositeSimple_zero, Realization.oppositeSimple_zero]
        rfl
      erw [hh]
      exact extraPoint_mem (F := F) q ν e 0 j
  · rcases l with ⟨a, c⟩ | j
    · have hh : BigCentroid.oppositeSimple (fun k => Realization.basisVector (F := RatFunc F)
          (pairPoint q ν 1 (Sum.inl (a, c)) k)) 1 =
          liftAC q ν (Realization.basisVector (a, c)) := by
        ext x
        erw [Realization.oppositeSimple_one]
        let a₀ : A q ν := x ⟨0, by decide⟩
        let c₀ : A q ν ⊕ Option (Fin q) := x ⟨2, by decide⟩
        change Realization.basisVector a a₀ * Realization.basisVector (Sum.inl c) c₀ =
          Sum.elim (fun d => Realization.basisVector (a, c) (a₀, d)) (fun _ => 0) c₀
        cases c₀ <;> simp [Realization.basisVector, mul_ite, eq_comm]
        split_ifs <;> simp_all
      erw [hh]
      exact liftAC_mem (F := F) q ν hq e (Realization.basisVector (a, c))
    · have hh : BigCentroid.oppositeSimple (fun k => Realization.basisVector (F := RatFunc F)
          (pairPoint q ν 1 (Sum.inr j) k)) 1 =
          BigCentroid.oppositeSimple (extraPoint q ν e j.castSucc) 1 := by
        ext x
        erw [Realization.oppositeSimple_one, Realization.oppositeSimple_one]
        simp only [extraPoint, factors_zero, factors_two, normalizedPoint_active q ν e he]
        rfl
      erw [hh]
      exact extraPoint_mem (F := F) q ν e 1 j.castSucc
  · rcases l with ⟨a, b⟩
    have hh : BigCentroid.oppositeSimple (fun k => Realization.basisVector (F := RatFunc F)
        (pairPoint q ν 2 (a, b) k)) 2 = liftAB q ν (Realization.basisVector (a, b)) := by
      ext x
      erw [Realization.oppositeSimple_two]
      let a₀ : A q ν := x ⟨0, by decide⟩
      let b₀ : A q ν ⊕ Unit := x ⟨1, by decide⟩
      change Realization.basisVector a a₀ * Realization.basisVector (Sum.inl b) b₀ =
        Sum.elim (fun d => Realization.basisVector (a, b) (a₀, d)) (fun _ => 0) b₀
      cases b₀ <;> simp [Realization.basisVector, mul_ite, eq_comm]
      split_ifs <;> simp_all
    erw [hh]
    exact liftAB_mem (F := F) q ν e (Realization.basisVector (a, b))

end

end Lemmata.Centroid.Construction.Circuit
