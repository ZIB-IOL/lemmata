module

public import Lemmata.Centroid.Proof.Construction.ThreeParty
public import Lemmata.Centroid.Proof.Construction.HookMatrix

@[expose] public section

open scoped BigOperators
open Classical

namespace Lemmata.Centroid.Construction.Hook

noncomputable section

variable {F : Type*} [Field F]

def factors {R : Type*} (n : ℕ) (a b c : Option (Fin n) → R) : ∀ i, Core n i → R :=
  Tensor.point a b c

@[simp] theorem factors_zero {R : Type*} (n : ℕ) (a b c : Option (Fin n) → R) : factors n a b c 0 = a := rfl
@[simp] theorem factors_one {R : Type*} (n : ℕ) (a b c : Option (Fin n) → R) : factors n a b c 1 = b := rfl
@[simp] theorem factors_two {R : Type*} (n : ℕ) (a b c : Option (Fin n) → R) : factors n a b c 2 = c := rfl

def liftCore {R : Type*} [Zero R] {n : ℕ} (u : Fin n → R) : Option (Fin n) → R :=
  fun x => Option.elim x 0 u

def fVector (n : ℕ) (k : Fin n) : Option (Fin n) → RatFunc F :=
  Realization.basisVector (some k) - Realization.basisVector none

def SelectedRow {n t : ℕ} (ht : t ≤ n) (j : Option (Fin n)) : Prop :=
  ∃ r : Fin t, j = some (r.castLE ht)

theorem selected_sum {W : Type*} [AddCommMonoid W] (n t : ℕ) (ht : t ≤ n)
    (v : Option (Fin n) → W) :
    (∑ j, if SelectedRow ht j then v j else 0) = ∑ r : Fin t, v (some (r.castLE ht)) := by
  have he (j : Option (Fin n)) : (if SelectedRow ht j then v j else 0) =
      ∑ r : Fin t, if j = some (r.castLE ht) then v j else 0 := by
    by_cases hs : SelectedRow ht j
    · obtain ⟨r, rfl⟩ := hs
      have hr (k : Fin t) : some (r.castLE ht) = some (k.castLE ht) ↔ k = r := by
        simp [Fin.ext_iff, eq_comm]
      rw [ite_eq_left (show SelectedRow ht (some (r.castLE ht)) from ⟨r, rfl⟩)]
      simp only [hr, Fintype.sum_ite_eq']
    · simp only [hs, ite_false]
      symm
      apply Finset.sum_eq_zero
      intro r hr
      exact ite_eq_right (fun h => hs ⟨r, h⟩)
  simp_rw [he]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  exact Fintype.sum_ite_eq' _ _

def rowEta (n t : ℕ) (ht : t ≤ n) (j : Option (Fin n)) : RatFunc F :=
  ∑ r : Fin t, if j = some (r.castLE ht) then eta (F := F) t r else 0

def columnNu (n t : ℕ) (ht : t ≤ n) (k : Fin n) : RatFunc F :=
  ∑ r : Fin t, if k = r.castLE ht then eta (F := F) t r else 0

theorem rowEta_selected (n t : ℕ) (ht : t ≤ n) (j : Fin t) :
    rowEta (F := F) n t ht (some (j.castLE ht)) = eta (F := F) t j := by
  have he (r : Fin t) : some (j.castLE ht) = some (r.castLE ht) ↔ r = j := by
    simp [Fin.ext_iff, eq_comm]
  simp [rowEta, he]

theorem columnNu_selected (n t : ℕ) (ht : t ≤ n) (j : Fin t) :
    columnNu (F := F) n t ht (j.castLE ht) = eta (F := F) t j := by
  have he (r : Fin t) : j.castLE ht = r.castLE ht ↔ r = j := by simp [Fin.ext_iff, eq_comm]
  simp [columnNu, he]

theorem sum_rowEta {W : Type*} [AddCommGroup W] [Module (RatFunc F) W]
    (n t : ℕ) (ht : t ≤ n) (v : Option (Fin n) → W) :
    (∑ j, rowEta (F := F) n t ht j • v j) = ∑ r : Fin t, eta (F := F) t r • v (some (r.castLE ht)) := by
  simp only [rowEta, Finset.sum_smul, ite_smul, zero_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  exact Fintype.sum_ite_eq' (some (r.castLE ht)) (fun j => eta (F := F) t r • v j)

theorem sum_columnNu {W : Type*} [AddCommGroup W] [Module (RatFunc F) W]
    (n t : ℕ) (ht : t ≤ n) (v : Fin n → W) :
    (∑ k, columnNu (F := F) n t ht k • v k) = ∑ r : Fin t, eta (F := F) t r • v (r.castLE ht) := by
  simp only [columnNu, Finset.sum_smul, ite_smul, zero_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  exact Fintype.sum_ite_eq' (r.castLE ht) (fun k => eta (F := F) t r • v k)

def splitC (n t : ℕ) (ht : t ≤ n) (j : Option (Fin n)) (k : Fin n) : Option (Fin n) → RatFunc F :=
  if SelectedRow ht j then fVector (F := F) n k else Realization.basisVector (some k)

theorem splitC_selected (n t : ℕ) (ht : t ≤ n) (j : Fin t) (k : Fin n) :
    splitC (F := F) n t ht (some (j.castLE ht)) k = fVector (F := F) n k := by
  exact ite_eq_left ⟨j, rfl⟩

def oldPoint (n t : ℕ) (ht : t ≤ n) (p : Option (Fin n) × Fin n) : ∀ i, Core n i → RatFunc F :=
  factors n (liftCore (gridPoint (F := F) n t p.1 p.2) -
      (rowEta (F := F) n t ht p.1 * columnNu (F := F) n t ht p.2) • Realization.basisVector none)
    (Realization.basisVector p.1) (splitC (F := F) n t ht p.1 p.2)

def rowPoint (n t : ℕ) (ht : t ≤ n) (j : Fin t) : ∀ i, Core n i → RatFunc F :=
  factors n (liftCore (g (F := F) n t (some (j.castLE ht))))
    (Realization.basisVector (some (j.castLE ht))) (Realization.basisVector none)

def cornerB (n t : ℕ) (ht : t ≤ n) : Option (Fin n) → RatFunc F :=
  ∑ j : Fin t, eta (F := F) t j • Realization.basisVector (some (j.castLE ht))

def cornerC (n t : ℕ) (ht : t ≤ n) : Option (Fin n) → RatFunc F :=
  ∑ k : Fin t, eta (F := F) t k • fVector (F := F) n (k.castLE ht)

def cornerPoint (n t : ℕ) (ht : t ≤ n) : ∀ i, Core n i → RatFunc F :=
  factors n (Realization.basisVector none) (cornerB (F := F) n t ht) (cornerC (F := F) n t ht)

abbrev PointIndex (n t : ℕ) := ((Option (Fin n) × Fin n) ⊕ Fin t) ⊕ Unit

def basePoint (n t : ℕ) (ht : t ≤ n) : PointIndex n t → ∀ i, Core n i → RatFunc F :=
  Sum.elim (Sum.elim (oldPoint (F := F) n t ht) (rowPoint (F := F) n t ht)) (fun _ => cornerPoint (F := F) n t ht)

def gridTensorPoint (n t : ℕ) (p : Option (Fin n) × Fin n) : ∀ i, Core n i → RatFunc F :=
  factors n (liftCore (gridPoint (F := F) n t p.1 p.2))
    (Realization.basisVector p.1) (Realization.basisVector (some p.2))

def splitGridPoint (n t : ℕ) (ht : t ≤ n) (p : Option (Fin n) × Fin n) : ∀ i, Core n i → RatFunc F :=
  factors n (liftCore (gridPoint (F := F) n t p.1 p.2)) (Realization.basisVector p.1) (splitC (F := F) n t ht p.1 p.2)

def cornerGridPoint (n t : ℕ) (ht : t ≤ n) (p : Option (Fin n) × Fin n) : ∀ i, Core n i → RatFunc F :=
  factors n (Realization.basisVector none) (Realization.basisVector p.1) (splitC (F := F) n t ht p.1 p.2)

theorem oldPoint_simple (n t : ℕ) (ht : t ≤ n) (p : Option (Fin n) × Fin n) :
    Tensor.simple (oldPoint (F := F) n t ht p) = Tensor.simple (splitGridPoint (F := F) n t ht p) -
      (rowEta (F := F) n t ht p.1 * columnNu (F := F) n t ht p.2) • Tensor.simple (cornerGridPoint (F := F) n t ht p) := by
  ext x
  simp only [Tensor.simple, Fin.prod_univ_three, oldPoint, splitGridPoint, cornerGridPoint,
    factors_zero, factors_one, factors_two, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Lemmata.TensorRank.Tensor.pure]
  ring

def lowRankPoint (n t : ℕ) (a : Fin n) : ∀ i, Core n i → RatFunc F :=
  factors n (Realization.basisVector (some a)) (M (F := F) n t a) (liftCore (fun k => H (F := F) n a k))

theorem grid_sum (n t : ℕ) :
    (∑ p, Tensor.simple (gridTensorPoint (F := F) n t p)) = ∑ a, Tensor.simple (lowRankPoint (F := F) n t a) := by
  ext x
  simp only [Tensor.simple, Fin.prod_univ_three, gridTensorPoint, lowRankPoint,
    factors_zero, factors_one, factors_two, Finset.sum_apply,
    Lemmata.TensorRank.Tensor.pure]
  rcases hx₀ : x 0 with _ | a <;> rcases hx₂ : x 2 with _ | c
  · simp [liftCore, Realization.basisVector]
  · simp [liftCore, Realization.basisVector]
  · simp [liftCore, Realization.basisVector]
  · simp only [liftCore, Option.elim_some, Realization.basisVector,
      Option.some.injEq, Fintype.sum_prod_type]
    simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true, gridPoint, one_mul]

end

end Lemmata.Centroid.Construction.Hook
