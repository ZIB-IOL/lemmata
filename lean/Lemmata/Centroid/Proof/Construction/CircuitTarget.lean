module

public import Lemmata.Centroid.Proof.Construction.CircuitMatrix
public import Lemmata.Centroid.Proof.Construction.Monomial
public import Lemmata.Centroid.Def.Bounds

@[expose] public section

open scoped BigOperators
open Classical

namespace Lemmata.Centroid.Construction.Circuit

noncomputable section

variable {F : Type*} [Field F]

abbrev A (q ν : ℕ) := Fin (q + 1) ⊕ Fin ν

abbrev Core (q ν : ℕ) : Fin 3 → Type :=
  ![A q ν, A q ν ⊕ Unit, A q ν ⊕ Option (Fin q)]

abbrev Dual (q ν : ℕ) : Fin 3 → Type :=
  ![(A q ν × A q ν) ⊕ Fin (q + 1), (A q ν × A q ν) ⊕ Fin q, A q ν × A q ν]

instance coreFintype (q ν : ℕ) (i : Fin 3) : Fintype (Core q ν i) := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun j => Fin.elim0 j))) i
  all_goals dsimp [Core]; infer_instance

instance dualFintype (q ν : ℕ) (i : Fin 3) : Fintype (Dual q ν i) := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun j => Fin.elim0 j))) i
  all_goals dsimp [Dual]; infer_instance

instance coreNonempty (q ν : ℕ) (i : Fin 3) : Nonempty (Core q ν i) := by
  fin_cases i <;> dsimp [Core, A] <;> infer_instance

def assignment (q ν : ℕ) (a : A q ν) (b : A q ν ⊕ Unit)
    (c : A q ν ⊕ Option (Fin q)) : ∀ i, Core q ν i := by
  exact Fin.cases a (Fin.cases b (Fin.cases c (fun j => Fin.elim0 j)))

@[simp] theorem assignment_zero (q ν : ℕ) (a : A q ν) (b : A q ν ⊕ Unit)
    (c : A q ν ⊕ Option (Fin q)) : assignment q ν a b c 0 = a := rfl

@[simp] theorem assignment_one (q ν : ℕ) (a : A q ν) (b : A q ν ⊕ Unit)
    (c : A q ν ⊕ Option (Fin q)) : assignment q ν a b c 1 = b := rfl

@[simp] theorem assignment_two (q ν : ℕ) (a : A q ν) (b : A q ν ⊕ Unit)
    (c : A q ν ⊕ Option (Fin q)) : assignment q ν a b c 2 = c := rfl

def pairPoint (q ν : ℕ) (i : Fin 3) (l : Dual q ν i) : ∀ j, Core q ν j := by
  revert l
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun j => Fin.elim0 j))) i
  · intro l
    change (A q ν × A q ν) ⊕ Fin (q + 1) at l
    exact match l with
      | Sum.inl p => assignment q ν (Sum.inl 0) (Sum.inl p.1) (Sum.inl p.2)
      | Sum.inr j => assignment q ν (Sum.inl 0) (Sum.inl (Sum.inl j)) (Sum.inr none)
  · intro l
    change (A q ν × A q ν) ⊕ Fin q at l
    exact match l with
      | Sum.inl p => assignment q ν p.1 (Sum.inr ()) (Sum.inl p.2)
      | Sum.inr j => assignment q ν (Sum.inl j.castSucc) (Sum.inr ()) (Sum.inr none)
  · intro l
    change A q ν × A q ν at l
    exact assignment q ν l.1 (Sum.inl l.2) (Sum.inr none)

def pairs (q ν : ℕ) : Realization.PairFamily F (Core q ν) (Dual q ν) :=
  fun i l => Realization.basisVector (fun j : {j // j ≠ i} => pairPoint q ν i l j.val)

@[simp] theorem pairPoint_zero_old (q ν : ℕ) (b c : A q ν) (j : Fin 3) :
    pairPoint q ν 0 (Sum.inl (b, c)) j =
      assignment q ν (Sum.inl 0) (Sum.inl b) (Sum.inl c) j := rfl

@[simp] theorem pairPoint_zero_new (q ν : ℕ) (k : Fin (q + 1)) (j : Fin 3) :
    pairPoint q ν 0 (Sum.inr k) j =
      assignment q ν (Sum.inl 0) (Sum.inl (Sum.inl k)) (Sum.inr none) j := rfl

@[simp] theorem pairPoint_one_old (q ν : ℕ) (a c : A q ν) (j : Fin 3) :
    pairPoint q ν 1 (Sum.inl (a, c)) j =
      assignment q ν a (Sum.inr ()) (Sum.inl c) j := rfl

@[simp] theorem pairPoint_one_new (q ν : ℕ) (k : Fin q) (j : Fin 3) :
    pairPoint q ν 1 (Sum.inr k) j =
      assignment q ν (Sum.inl k.castSucc) (Sum.inr ()) (Sum.inr none) j := rfl

@[simp] theorem pairPoint_two (q ν : ℕ) (a b : A q ν) (j : Fin 3) :
    pairPoint q ν 2 (a, b) j = assignment q ν a (Sum.inl b) (Sum.inr none) j := rfl

def tau (q ν : ℕ) : Tensor F (Fin 3) (Core q ν) :=
  ∑ j : Fin q, Realization.basisVector
    (assignment q ν (Sum.inl j.castSucc) (Sum.inr ()) (Sum.inr (some j)))

def tensor (q ν : ℕ) : Tensor F (Fin 3) (Realization.Coordinates (Core q ν) (Dual q ν)) :=
  Realization.tensor (pairs q ν) (tau q ν)

abbrev Cell (q ν : ℕ) := (A q ν × A q ν × A q ν) ⊕ (Fin q × Fin (q + 1))

def cell (q ν : ℕ) : Cell q ν → ∀ i, Core q ν i
  | Sum.inl p => assignment q ν p.1 (Sum.inl p.2.1) (Sum.inl p.2.2)
  | Sum.inr p => assignment q ν (Sum.inl p.1.castSucc) (Sum.inl (Sum.inl p.2)) (Sum.inr none)

theorem cell_injective (q ν : ℕ) : Function.Injective (cell q ν) := by
  intro x y h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  cases x with
  | inl x =>
    cases y with
    | inl y =>
      simp only [cell, assignment_zero, assignment_one, assignment_two] at h0 h1 h2
      exact congrArg Sum.inl (Prod.ext h0 (Prod.ext (Sum.inl.inj h1) (Sum.inl.inj h2)))
    | inr y => simp [cell] at h2
  | inr x =>
    cases y with
    | inl y => simp [cell] at h2
    | inr y =>
      simp only [cell, assignment_zero, assignment_one] at h0 h1
      have hx : x.1 = y.1 := by
        have he : x.1.castSucc = y.1.castSucc := Sum.inl.inj h0
        exact Fin.ext (congrArg (fun i : Fin (q + 1) => i.val) he)
      have hy : x.2 = y.2 := Sum.inl.inj (Sum.inl.inj h1)
      exact congrArg Sum.inr (Prod.ext hx hy)

theorem pairs_contain_cell (q ν : ℕ) (x : Cell q ν) (i : Fin 3) :
    ∃ l, pairs (F := F) q ν i l = Realization.basisVector
      (fun j : {j // j ≠ i} => cell q ν x j.val) := by
  cases x with
  | inl x =>
    fin_cases i
    · refine ⟨Sum.inl (x.2.1, x.2.2), ?_⟩
      apply congrArg (fun p => Realization.basisVector (F := F) p)
      funext ⟨j, hj⟩
      fin_cases j <;> first | exact False.elim (hj rfl) | rfl
    · refine ⟨Sum.inl (x.1, x.2.2), ?_⟩
      apply congrArg (fun p => Realization.basisVector (F := F) p)
      funext ⟨j, hj⟩
      fin_cases j <;> first | exact False.elim (hj rfl) | rfl
    · refine ⟨(x.1, x.2.1), ?_⟩
      apply congrArg (fun p => Realization.basisVector (F := F) p)
      funext ⟨j, hj⟩
      fin_cases j <;> first | exact False.elim (hj rfl) | rfl
  | inr x =>
    fin_cases i
    · refine ⟨Sum.inr x.2, ?_⟩
      apply congrArg (fun p => Realization.basisVector (F := F) p)
      funext ⟨j, hj⟩
      fin_cases j <;> first | exact False.elim (hj rfl) | rfl
    · refine ⟨Sum.inr x.1, ?_⟩
      apply congrArg (fun p => Realization.basisVector (F := F) p)
      funext ⟨j, hj⟩
      fin_cases j <;> first | exact False.elim (hj rfl) | rfl
    · refine ⟨(Sum.inl x.1.castSucc, Sum.inl x.2), ?_⟩
      apply congrArg (fun p => Realization.basisVector (F := F) p)
      funext ⟨j, hj⟩
      fin_cases j <;> first | exact False.elim (hj rfl) | rfl

theorem centroid_lower_bound (q ν : ℕ) :
    ((q + 1 + ν) ^ 3 + q * (q + 1)) + 1 ≤
      Module.finrank F (Tensor.centroid (tensor (F := F) q ν)) := by
  have h := Realization.monomial_centroid_lower_bound (pairs (F := F) q ν) (tau q ν)
    (cell q ν) (cell_injective q ν) (pairs_contain_cell q ν)
  have hc : Fintype.card (Cell q ν) = (q + 1 + ν) ^ 3 + q * (q + 1) := by
    simp only [Cell, A, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
    ring
  rw [hc] at h
  rw [Nat.add_comm ((q + 1 + ν) ^ 3 + q * (q + 1)) 1]
  exact h

theorem coordinate_card (q ν : ℕ) (i : Fin 3) :
    Fintype.card (Realization.Coordinates (Core q ν) (Dual q ν) i) =
      (q + 1 + ν) * (q + 2 + ν) + (q + 1) := by
  fin_cases i <;>
    simp only [Realization.Coordinates, Core, Dual, Fintype.card_eq_nat_card] <;>
    simp [A] <;> ring

end

end Lemmata.Centroid.Construction.Circuit
