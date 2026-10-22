module

public import Lemmata.Centroid.Proof.Construction.Monomial
public import Mathlib.Tactic.Ring

@[expose] public section

open scoped BigOperators
open Classical

namespace Lemmata.Centroid.Construction.Rectangular

noncomputable section

variable {F : Type*} [Field F]

abbrev Core (n t : ℕ) : Fin 3 → Type :=
  ![Fin n, Option (Fin n) ⊕ Fin t, Option (Fin n) ⊕ Fin t]

abbrev Dual (n t : ℕ) : Fin 3 → Type :=
  ![(Fin n × Option (Fin n)) ⊕ Option (Fin t), Fin n × Option (Fin n), Fin n × Option (Fin n)]

instance coreFintype (n t : ℕ) (i : Fin 3) : Fintype (Core n t i) := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun j => Fin.elim0 j))) i
  all_goals dsimp [Core]; infer_instance

instance dualFintype (n t : ℕ) (i : Fin 3) : Fintype (Dual n t i) := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun j => Fin.elim0 j))) i
  all_goals dsimp [Dual]; infer_instance

def assignment (n t : ℕ) (a : Fin n) (b c : Option (Fin n) ⊕ Fin t) : ∀ i, Core n t i :=
  Fin.cases a (Fin.cases b (Fin.cases c (fun j => Fin.elim0 j)))

@[simp] theorem assignment_zero (n t : ℕ) (a : Fin n) (b c : Option (Fin n) ⊕ Fin t) :
    assignment n t a b c 0 = a := rfl

@[simp] theorem assignment_one (n t : ℕ) (a : Fin n) (b c : Option (Fin n) ⊕ Fin t) :
    assignment n t a b c 1 = b := rfl

@[simp] theorem assignment_two (n t : ℕ) (a : Fin n) (b c : Option (Fin n) ⊕ Fin t) :
    assignment n t a b c 2 = c := rfl

def selected {n t : ℕ} (ht : t ≤ n) : Option (Fin t) → Option (Fin n) :=
  Option.map (Fin.castLE ht)

theorem selected_injective {n t : ℕ} (ht : t ≤ n) : Function.Injective (selected ht) := by
  intro x y h
  cases x with
  | none =>
    cases y with
    | none => rfl
    | some _ => simp [selected] at h
  | some x =>
    cases y with
    | none => simp [selected] at h
    | some y =>
      apply congrArg some
      apply Fin.ext
      have hh : x.castLE ht = y.castLE ht := Option.some.inj h
      exact congrArg (fun i : Fin n => i.val) hh

def pairPoint (n t : ℕ) (hn : 0 < n) (ht : t ≤ n) (i : Fin 3) :
    Dual n t i → ∀ j, Core n t j := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun j => Fin.elim0 j))) i
  · exact Sum.elim
      (fun p => assignment n t ⟨0, hn⟩ (Sum.inl (some p.1)) (Sum.inl p.2))
      (fun j => assignment n t ⟨0, hn⟩ (Sum.inl none) (Sum.inl (selected ht j)))
  · exact fun p => assignment n t p.1 (Sum.inl none) (Sum.inl p.2)
  · exact fun p => assignment n t p.1 (Sum.inl p.2) (Sum.inl none)

def pairs (n t : ℕ) (hn : 0 < n) (ht : t ≤ n) : Realization.PairFamily F (Core n t) (Dual n t) :=
  fun i l => Realization.basisVector (fun j : {j // j ≠ i} => pairPoint n t hn ht i l j.val)

def tau (n t : ℕ) : Tensor F (Fin 3) (Core n t) :=
  ∑ j : Fin t, ∑ a : Fin n, Realization.basisVector (assignment n t a (Sum.inr j) (Sum.inr j))

def tensor (n t : ℕ) (hn : 0 < n) (ht : t ≤ n) :
    Tensor F (Fin 3) (Realization.Coordinates (Core n t) (Dual n t)) :=
  Realization.tensor (pairs n t hn ht) (tau n t)

abbrev Cell (n t : ℕ) := Fin n × ((Fin n × Option (Fin n)) ⊕ Option (Fin t))

def cell (n t : ℕ) (ht : t ≤ n) : Cell n t → ∀ i, Core n t i
  | (a, Sum.inl (b, c)) => assignment n t a (Sum.inl (some b)) (Sum.inl c)
  | (a, Sum.inr j) => assignment n t a (Sum.inl none) (Sum.inl (selected ht j))

theorem cell_injective (n t : ℕ) (ht : t ≤ n) : Function.Injective (cell n t ht) := by
  intro x y h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  rcases x with ⟨a, ⟨b, c⟩ | j⟩ <;> rcases y with ⟨d, ⟨e, f⟩ | k⟩
  · simp only [cell, assignment_zero, assignment_one, assignment_two] at h0 h1 h2
    exact Prod.ext h0 (congrArg Sum.inl (Prod.ext (Option.some.inj (Sum.inl.inj h1)) (Sum.inl.inj h2)))
  · simp [cell] at h1
  · simp [cell] at h1
  · simp only [cell, assignment_zero, assignment_two] at h0 h2
    exact Prod.ext h0 (congrArg Sum.inr (selected_injective ht (Sum.inl.inj h2)))

theorem pairs_contain_cell (n t : ℕ) (hn : 0 < n) (ht : t ≤ n)
    (x : Cell n t) (i : Fin 3) :
    ∃ l, pairs (F := F) n t hn ht i l = Realization.basisVector
      (fun j : {j // j ≠ i} => cell n t ht x j.val) := by
  rcases x with ⟨a, ⟨b, c⟩ | j⟩
  · fin_cases i
    · refine ⟨Sum.inl (b, c), ?_⟩
      apply congrArg (fun p => Realization.basisVector (F := F) p)
      funext ⟨k, hk⟩
      fin_cases k <;> first | exact False.elim (hk rfl) | rfl
    · refine ⟨(a, c), ?_⟩
      apply congrArg (fun p => Realization.basisVector (F := F) p)
      funext ⟨k, hk⟩
      fin_cases k <;> first | exact False.elim (hk rfl) | rfl
    · refine ⟨(a, some b), ?_⟩
      apply congrArg (fun p => Realization.basisVector (F := F) p)
      funext ⟨k, hk⟩
      fin_cases k <;> first | exact False.elim (hk rfl) | rfl
  · fin_cases i
    · refine ⟨Sum.inr j, ?_⟩
      apply congrArg (fun p => Realization.basisVector (F := F) p)
      funext ⟨k, hk⟩
      fin_cases k <;> first | exact False.elim (hk rfl) | rfl
    · refine ⟨(a, selected ht j), ?_⟩
      apply congrArg (fun p => Realization.basisVector (F := F) p)
      funext ⟨k, hk⟩
      fin_cases k <;> first | exact False.elim (hk rfl) | rfl
    · refine ⟨(a, none), ?_⟩
      apply congrArg (fun p => Realization.basisVector (F := F) p)
      funext ⟨k, hk⟩
      fin_cases k <;> first | exact False.elim (hk rfl) | rfl

theorem centroid_lower_bound (n t : ℕ) (hn : 0 < n) (ht : t ≤ n) :
    n ^ 3 + n * (n + 1 + t) + 1 ≤
      Module.finrank F (Tensor.centroid (tensor (F := F) n t hn ht)) := by
  have : ∀ i, Nonempty (Core n t i) := by
    intro i
    fin_cases i
    · exact ⟨⟨0, hn⟩⟩
    · exact ⟨Sum.inl none⟩
    · exact ⟨Sum.inl none⟩
  have h := Realization.monomial_centroid_lower_bound (pairs (F := F) n t hn ht) (tau n t)
    (cell n t ht) (cell_injective n t ht) (pairs_contain_cell n t hn ht)
  have hc : Fintype.card (Cell n t) = n ^ 3 + n * (n + 1 + t) := by
    simp only [Cell, Fintype.card_sum, Fintype.card_prod, Fintype.card_option, Fintype.card_fin]
    ring
  rw [hc] at h
  rw [Nat.add_comm (n ^ 3 + n * (n + 1 + t)) 1]
  exact h

theorem coordinate_card (n t : ℕ) (i : Fin 3) :
    Fintype.card (Realization.Coordinates (Core n t) (Dual n t) i) = (n + 1) ^ 2 + t := by
  fin_cases i <;>
    simp only [Realization.Coordinates, Core, Dual, Fintype.card_eq_nat_card] <;>
    simp <;> ring

end

end Lemmata.Centroid.Construction.Rectangular
