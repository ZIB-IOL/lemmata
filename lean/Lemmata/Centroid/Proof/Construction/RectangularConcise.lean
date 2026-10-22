module

public import Lemmata.Centroid.Proof.Construction.RectangularTarget
public import Lemmata.Centroid.Proof.Construction.ThreeParty

@[expose] public section

open scoped BigOperators
open Classical

namespace Lemmata.Centroid.Construction.Rectangular

noncomputable section

variable {F : Type*} [Field F]

abbrev Coordinates (n t : ℕ) := Realization.Coordinates (Core n t) (Dual n t)
abbrev point (n t : ℕ) := Tensor.point (V := Coordinates n t)

def corePoint (n t : ℕ) (a : ∀ i, Core n t i) : ∀ i, Coordinates n t i :=
  point n t (Sum.inl (a 0)) (Sum.inl (a 1)) (Sum.inl (a 2))

def entry {X Y : Type*} (x : X ⊕ Y) (a : X) : F := match x with
  | Sum.inl b => if a = b then 1 else 0
  | Sum.inr _ => 0

theorem pairPoint_zero_old (n t : ℕ) (hn : 0 < n) (ht : t ≤ n)
    (b : Fin n) (c : Option (Fin n)) (j : Fin 3) :
    pairPoint n t hn ht 0 (Sum.inl (b, c)) j =
      assignment n t ⟨0, hn⟩ (Sum.inl (some b)) (Sum.inl c) j := rfl

theorem pairPoint_zero_new (n t : ℕ) (hn : 0 < n) (ht : t ≤ n)
    (k : Option (Fin t)) (j : Fin 3) :
    pairPoint n t hn ht 0 (Sum.inr k) j =
      assignment n t ⟨0, hn⟩ (Sum.inl none) (Sum.inl (selected ht k)) j := rfl

theorem pairPoint_one (n t : ℕ) (hn : 0 < n) (ht : t ≤ n)
    (a : Fin n) (c : Option (Fin n)) (j : Fin 3) :
    pairPoint n t hn ht 1 (a, c) j = assignment n t a (Sum.inl none) (Sum.inl c) j := rfl

theorem pairPoint_two (n t : ℕ) (hn : 0 < n) (ht : t ≤ n)
    (a : Fin n) (b : Option (Fin n)) (j : Fin 3) :
    pairPoint n t hn ht 2 (a, b) j = assignment n t a (Sum.inl b) (Sum.inl none) j := rfl

theorem tau_embedding (n t : ℕ) (x : ∀ i, Coordinates n t i) :
    Realization.coreEmbedding (tau (F := F) n t) x =
      ∑ j : Fin t, ∑ a : Fin n, Realization.coreEntry 0 (x 0) a *
        Realization.coreEntry 1 (x 1) (Sum.inr j) * Realization.coreEntry 2 (x 2) (Sum.inr j) := by
  simp only [tau, map_sum, Finset.sum_apply, Realization.coreEmbedding_basisVector,
    Fin.prod_univ_three, assignment_zero, assignment_one, assignment_two]

theorem tensor_point (n t : ℕ) (hn : 0 < n) (ht : t ≤ n)
    (a : Fin n ⊕ ((Fin n × Option (Fin n)) ⊕ Option (Fin t)))
    (b : (Option (Fin n) ⊕ Fin t) ⊕ (Fin n × Option (Fin n)))
    (c : (Option (Fin n) ⊕ Fin t) ⊕ (Fin n × Option (Fin n))) :
    tensor (F := F) n t hn ht (point n t a b c) =
      (match a with
      | Sum.inl _ => 0
      | Sum.inr (Sum.inl p) => entry b (Sum.inl (some p.1)) * entry c (Sum.inl p.2)
      | Sum.inr (Sum.inr j) => entry b (Sum.inl none) * entry c (Sum.inl (selected ht j))) +
      (match b with
      | Sum.inl _ => 0
      | Sum.inr p => entry a p.1 * entry c (Sum.inl p.2)) +
      (match c with
      | Sum.inl _ => 0
      | Sum.inr p => entry a p.1 * entry b (Sum.inl p.2)) +
      ∑ j : Fin t, ∑ i : Fin n, entry a i * entry b (Sum.inr j) * entry c (Sum.inr j) := by
  have h := Realization.tensor_basisPairs_apply (F := F) (pairPoint n t hn ht)
    (tau n t) (point n t a b c)
  rw [tau_embedding] at h
  convert h using 1 <;> rcases a with a | a | a <;> cases b <;> cases c <;> rfl

def columnZero (n t : ℕ) (hn : 0 < n) (ht : t ≤ n) : Coordinates n t 0 → ∀ i, Coordinates n t i
  | Sum.inl a => point n t (Sum.inl ⟨0, hn⟩) (Sum.inr (a, none)) (Sum.inl (Sum.inl none))
  | Sum.inr l => corePoint n t (pairPoint n t hn ht 0 l)

def columnOne (n t : ℕ) (hn : 0 < n) (ht : t ≤ n) : Coordinates n t 1 → ∀ i, Coordinates n t i
  | Sum.inl (Sum.inl b) => point n t (Sum.inl ⟨0, hn⟩) (Sum.inl (Sum.inl none)) (Sum.inr (⟨0, hn⟩, b))
  | Sum.inl (Sum.inr j) => point n t (Sum.inl ⟨0, hn⟩) (Sum.inl (Sum.inl none)) (Sum.inl (Sum.inr j))
  | Sum.inr l => corePoint n t (pairPoint n t hn ht 1 l)

def columnTwo (n t : ℕ) (hn : 0 < n) (ht : t ≤ n) : Coordinates n t 2 → ∀ i, Coordinates n t i
  | Sum.inl (Sum.inl c) => point n t (Sum.inr (Sum.inl (⟨0, hn⟩, c)))
      (Sum.inl (Sum.inl (some ⟨0, hn⟩))) (Sum.inl (Sum.inl none))
  | Sum.inl (Sum.inr j) => point n t (Sum.inl ⟨0, hn⟩) (Sum.inl (Sum.inr j)) (Sum.inl (Sum.inl none))
  | Sum.inr l => corePoint n t (pairPoint n t hn ht 2 l)

theorem tensor_column_zero [DecidableEq (Fin 3)] (n t : ℕ) (hn : 0 < n) (ht : t ≤ n)
    (r s : Coordinates n t 0) :
    tensor (F := F) n t hn ht (Function.update (columnZero n t hn ht s) 0 r) = if r = s then 1 else 0 := by
  change Fin n ⊕ ((Fin n × Option (Fin n)) ⊕ Option (Fin t)) at r s
  rcases r with r | ⟨r₁, r₂⟩ | r <;> rcases s with s | ⟨s₁, s₂⟩ | s <;>
    simp only [columnZero, corePoint]
  all_goals erw [Tensor.update_point_zero, tensor_point]
  all_goals simp only [pairPoint_zero_old, pairPoint_zero_new, assignment_one, assignment_two]
  all_goals simp [entry, (selected_injective ht).eq_iff,
    Sum.inl.injEq, Sum.inr_ne_inl]
  all_goals try (split_ifs <;> simp_all)
  all_goals try intro h
  all_goals injections
  all_goals subst_vars
  all_goals first | rfl | contradiction

theorem tensor_column_one [DecidableEq (Fin 3)] (n t : ℕ) (hn : 0 < n) (ht : t ≤ n)
    (r s : Coordinates n t 1) :
    tensor (F := F) n t hn ht (Function.update (columnOne n t hn ht s) 1 r) = if r = s then 1 else 0 := by
  change (Option (Fin n) ⊕ Fin t) ⊕ (Fin n × Option (Fin n)) at r s
  rcases r with (r | r) | ⟨r₁, r₂⟩ <;> rcases s with (s | s) | ⟨s₁, s₂⟩ <;>
    simp only [columnOne, corePoint]
  all_goals erw [Tensor.update_point_one, tensor_point]
  all_goals simp only [pairPoint_one, assignment_zero, assignment_two]
  all_goals simp [entry, Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl]
  all_goals try (split_ifs <;> simp_all)
  all_goals try intro h
  all_goals injections
  all_goals subst_vars
  all_goals first | rfl | contradiction | (convert Fintype.sum_ite_eq' (⟨0, hn⟩ : Fin n) (fun _ => (1 : F)) using 1; congr 1; ext x; split_ifs <;> rfl)

theorem tensor_column_two [DecidableEq (Fin 3)] (n t : ℕ) (hn : 0 < n) (ht : t ≤ n)
    (r s : Coordinates n t 2) :
    tensor (F := F) n t hn ht (Function.update (columnTwo n t hn ht s) 2 r) = if r = s then 1 else 0 := by
  change (Option (Fin n) ⊕ Fin t) ⊕ (Fin n × Option (Fin n)) at r s
  rcases r with (r | r) | ⟨r₁, r₂⟩ <;> rcases s with (s | s) | ⟨s₁, s₂⟩ <;>
    simp only [columnTwo, corePoint]
  all_goals erw [Tensor.update_point_two, tensor_point]
  all_goals simp only [pairPoint_two, assignment_zero, assignment_one]
  all_goals simp [entry, Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl]
  all_goals try (split_ifs <;> simp_all)
  all_goals try intro h
  all_goals injections
  all_goals subst_vars
  all_goals first | rfl | contradiction | (convert Fintype.sum_ite_eq' (⟨0, hn⟩ : Fin n) (fun _ => (1 : F)) using 1; congr 1; ext x; split_ifs <;> rfl)

theorem concise (n t : ℕ) (hn : 0 < n) (ht : t ≤ n) : Tensor.Concise (tensor (F := F) n t hn ht) := by
  intro i f g h
  fin_cases i
  · ext a
    have hh := congrFun h (columnZero n t hn ht a)
    simpa [Tensor.contraction_apply, tensor_column_zero, mul_ite] using hh
  · ext a
    have hh := congrFun h (columnOne n t hn ht a)
    simpa [Tensor.contraction_apply, tensor_column_one, mul_ite] using hh
  · ext a
    have hh := congrFun h (columnTwo n t hn ht a)
    simpa [Tensor.contraction_apply, tensor_column_two, mul_ite] using hh

end

end Lemmata.Centroid.Construction.Rectangular
