module

public import Lemmata.Centroid.Proof.Construction.HookTarget
public import Lemmata.Centroid.Proof.Construction.ThreeParty

@[expose] public section

open scoped BigOperators
open Classical

namespace Lemmata.Centroid.Construction.Hook

noncomputable section

variable {F : Type*} [Field F]

abbrev Coordinates (n t : ℕ) := Realization.Coordinates (Core n) (Dual n t)
abbrev point (n t : ℕ) := Tensor.point (V := Coordinates n t)

@[simp] theorem point_zero (n t : ℕ) (a : Coordinates n t 0) (b : Coordinates n t 1) (c : Coordinates n t 2) :
    point n t a b c 0 = a := rfl
@[simp] theorem point_one (n t : ℕ) (a : Coordinates n t 0) (b : Coordinates n t 1) (c : Coordinates n t 2) :
    point n t a b c 1 = b := rfl
@[simp] theorem point_two (n t : ℕ) (a : Coordinates n t 0) (b : Coordinates n t 1) (c : Coordinates n t 2) :
    point n t a b c 2 = c := rfl

def entry {X Y : Type*} (x : X ⊕ Y) (a : X) : F := match x with
  | Sum.inl b => if a = b then 1 else 0
  | Sum.inr _ => 0

private theorem pairEmbedding_sub {U L : Fin 3 → Type*} [∀ i, Fintype (U i)]
    (i : Fin 3) (P Q : Realization.Opposite U i → F) (x : ∀ i, Realization.Coordinates U L i) :
    Realization.pairEmbedding i (P - Q) x =
      Realization.pairEmbedding i P x - Realization.pairEmbedding i Q x := by
  simp [Realization.pairEmbedding, sub_mul, Finset.sum_sub_distrib]

private theorem correction_embedding (n t : ℕ) (x : ∀ i, Coordinates n t i) :
    Realization.pairEmbedding 1
      (Realization.basisVector (F := F) (fun _ : {r : Fin 3 // r ≠ 1} => (none : Option (Fin n)))) x =
      Realization.coreEntry 0 (x 0) none * Realization.coreEntry 2 (x 2) none := by
  rw [Realization.pairEmbedding_basisVector]
  convert Realization.prod_other_one (F := F)
    (fun i => Realization.coreEntry i (x i) (none : Core n i)) using 1
  congr 1
  ext i
  simp

private theorem tensor_base_correction (n t : ℕ) (ht : t ≤ n) (x : ∀ i, Coordinates n t i) :
    tensor (F := F) n t ht x = Realization.tensor (basePairs n t ht) 0 x -
      (match x 1 with
      | Sum.inr (Sum.inr _) => Realization.coreEntry 0 (x 0) none * Realization.coreEntry 2 (x 2) none
      | _ => 0) := by
  simp only [tensor, Realization.tensor, Fin.sum_univ_three, Pi.add_apply, map_zero,
    Pi.zero_apply, add_zero]
  have h₀ : Realization.sector (pairs (F := F) n t ht) 0 x =
      Realization.sector (basePairs n t ht) 0 x := rfl
  have h₂ : Realization.sector (pairs (F := F) n t ht) 2 x =
      Realization.sector (basePairs n t ht) 2 x := rfl
  rw [h₀, h₂]
  cases hx : x 1 with
  | inl a => simp [Realization.sector, hx]
  | inr l =>
    cases l with
    | inl p =>
      have hp : pairs (F := F) n t ht 1 (Sum.inl p) = basePairs n t ht 1 (Sum.inl p) := rfl
      simp only [Realization.sector, hx, hp, sub_zero]
    | inr k =>
      have hp : pairs (F := F) n t ht 1 (Sum.inr k) = basePairs n t ht 1 (Sum.inr k) -
          Realization.basisVector (fun _ : {r : Fin 3 // r ≠ 1} => (none : Option (Fin n))) := rfl
      simp only [Realization.sector, hx, hp]
      rw [pairEmbedding_sub, correction_embedding]
      ring

private theorem base_tensor_point (n t : ℕ) (ht : t ≤ n)
    (a : Option (Fin n) ⊕ ((Option (Fin n) × Fin n) ⊕ Fin t))
    (b c : Option (Fin n) ⊕ ((Fin n × Option (Fin n)) ⊕ Fin t)) :
    Realization.tensor (basePairs (F := F) n t ht) 0 (point n t a b c) =
      (match a with
      | Sum.inl _ => 0
      | Sum.inr (Sum.inl p) => entry b p.1 * entry c (some p.2)
      | Sum.inr (Sum.inr j) => entry b (some (j.castLE ht)) * entry c none) +
      (match b with
      | Sum.inl _ => 0
      | Sum.inr (Sum.inl p) => entry a (some p.1) * entry c p.2
      | Sum.inr (Sum.inr k) => entry a none * entry c (some (k.castLE ht))) +
      (match c with
      | Sum.inl _ => 0
      | Sum.inr (Sum.inl p) => entry a (some p.1) * entry b p.2
      | Sum.inr (Sum.inr j) => entry a none * entry b (some (j.castLE ht))) := by
  have h := Realization.tensor_basisPairs_apply (F := F) (pairPoint n t ht) 0 (point n t a b c)
  simp only [map_zero, Pi.zero_apply, add_zero] at h
  convert h using 1 <;>
    rcases a with a | a | a <;> rcases b with b | b | b <;> rcases c with c | c | c <;> rfl

theorem tensor_point (n t : ℕ) (ht : t ≤ n)
    (a : Option (Fin n) ⊕ ((Option (Fin n) × Fin n) ⊕ Fin t))
    (b c : Option (Fin n) ⊕ ((Fin n × Option (Fin n)) ⊕ Fin t)) :
    tensor (F := F) n t ht (point n t a b c) =
      (match a with
      | Sum.inl _ => 0
      | Sum.inr (Sum.inl p) => entry b p.1 * entry c (some p.2)
      | Sum.inr (Sum.inr j) => entry b (some (j.castLE ht)) * entry c none) +
      (match b with
      | Sum.inl _ => 0
      | Sum.inr (Sum.inl p) => entry a (some p.1) * entry c p.2
      | Sum.inr (Sum.inr k) => entry a none * (entry c (some (k.castLE ht)) - entry c none)) +
      (match c with
      | Sum.inl _ => 0
      | Sum.inr (Sum.inl p) => entry a (some p.1) * entry b p.2
      | Sum.inr (Sum.inr j) => entry a none * entry b (some (j.castLE ht))) := by
  have hc : (match point n t a b c 1 with
      | Sum.inr (Sum.inr _) => Realization.coreEntry (F := F) 0 (point n t a b c 0) none *
          Realization.coreEntry 2 (point n t a b c 2) none
      | _ => 0) = (match b with
      | Sum.inr (Sum.inr _) => entry (F := F) a none * entry c none
      | _ => 0) := by
    rcases a with a | a | a <;> rcases b with b | b | b <;> rcases c with c | c | c <;> rfl
  rw [tensor_base_correction, base_tensor_point, hc]
  rcases a with a | a | a <;> rcases b with b | b | b <;> rcases c with c | c | c <;>
    dsimp only <;> ring

def corePoint (n t : ℕ) (a : ∀ i, Core n i) : ∀ i, Coordinates n t i :=
  point n t (Sum.inl (a 0)) (Sum.inl (a 1)) (Sum.inl (a 2))

def columnZero (n t : ℕ) (hn : 0 < n) (ht₀ : 0 < t) (ht : t ≤ n) :
    Coordinates n t 0 → ∀ i, Coordinates n t i
  | Sum.inl none => point n t (Sum.inl none) (Sum.inr (Sum.inr ⟨0, ht₀⟩))
      (Sum.inl (some ((⟨0, ht₀⟩ : Fin t).castLE ht)))
  | Sum.inl (some a) => point n t (Sum.inl none)
      (Sum.inl (some ⟨0, hn⟩)) (Sum.inr (Sum.inl (a, some ⟨0, hn⟩)))
  | Sum.inr l => corePoint n t (pairPoint n t ht 0 l)

def columnOne (n t : ℕ) (hn : 0 < n) (ht : t ≤ n) :
    Coordinates n t 1 → ∀ i, Coordinates n t i
  | Sum.inl b => point n t (Sum.inl (some ⟨0, hn⟩)) (Sum.inl none)
      (Sum.inr (Sum.inl (⟨0, hn⟩, b)))
  | Sum.inr l => corePoint n t (pairPoint n t ht 1 l)

def columnTwo (n t : ℕ) (_hn : 0 < n) (ht₀ : 0 < t) (ht : t ≤ n) :
    Coordinates n t 2 → ∀ i, Coordinates n t i
  | Sum.inl none => point n t (Sum.inr (Sum.inr ⟨0, ht₀⟩))
      (Sum.inl (some ((⟨0, ht₀⟩ : Fin t).castLE ht))) (Sum.inl none)
  | Sum.inl (some c) => point n t (Sum.inr (Sum.inl (none, c))) (Sum.inl none) (Sum.inl none)
  | Sum.inr l => corePoint n t (pairPoint n t ht 2 l)

theorem tensor_column_zero [DecidableEq (Fin 3)] (n t : ℕ) (hn : 0 < n) (ht₀ : 0 < t) (ht : t ≤ n)
    (r s : Coordinates n t 0) :
    tensor (F := F) n t ht (Function.update (columnZero n t hn ht₀ ht s) 0 r) = if r = s then 1 else 0 := by
  change Option (Fin n) ⊕ ((Option (Fin n) × Fin n) ⊕ Fin t) at r s
  rcases r with _ | ⟨r₁, r₂⟩ | r <;> rcases s with (_ | s) | ⟨s₁, s₂⟩ | s <;>
    simp only [columnZero, corePoint]
  all_goals erw [Tensor.update_point_zero, tensor_point]
  all_goals simp [entry, Fin.ext_iff]
  all_goals try (split_ifs <;> simp_all)
  all_goals try intro h
  all_goals injections
  all_goals subst_vars
  all_goals first | rfl | contradiction | (have heq := Fin.ext (by assumption); cases heq; first | rfl | contradiction)

theorem tensor_column_one [DecidableEq (Fin 3)] (n t : ℕ) (hn : 0 < n) (ht : t ≤ n)
    (r s : Coordinates n t 1) :
    tensor (F := F) n t ht (Function.update (columnOne n t hn ht s) 1 r) = if r = s then 1 else 0 := by
  change Option (Fin n) ⊕ ((Fin n × Option (Fin n)) ⊕ Fin t) at r s
  rcases r with r | ⟨r₁, r₂⟩ | r <;> rcases s with s | ⟨s₁, s₂⟩ | s <;>
    simp only [columnOne, corePoint]
  all_goals erw [Tensor.update_point_one, tensor_point]
  all_goals simp [entry, Fin.ext_iff]
  all_goals try (split_ifs <;> simp_all)
  all_goals try intro h
  all_goals injections
  all_goals subst_vars
  all_goals first | rfl | contradiction | (have heq := Fin.ext (by assumption); cases heq; first | rfl | contradiction)

theorem tensor_column_two [DecidableEq (Fin 3)] (n t : ℕ) (hn : 0 < n) (ht₀ : 0 < t) (ht : t ≤ n)
    (r s : Coordinates n t 2) :
    tensor (F := F) n t ht (Function.update (columnTwo n t hn ht₀ ht s) 2 r) = if r = s then 1 else 0 := by
  change Option (Fin n) ⊕ ((Fin n × Option (Fin n)) ⊕ Fin t) at r s
  rcases r with r | ⟨r₁, r₂⟩ | r <;> rcases s with (_ | s) | ⟨s₁, s₂⟩ | s <;>
    simp only [columnTwo, corePoint]
  all_goals erw [Tensor.update_point_two, tensor_point]
  all_goals simp [entry, Fin.ext_iff]
  all_goals try (split_ifs <;> simp_all)
  all_goals try intro h
  all_goals injections
  all_goals subst_vars
  all_goals first | rfl | contradiction | (have heq := Fin.ext (by assumption); cases heq; first | rfl | contradiction)

theorem concise (n t : ℕ) (hn : 0 < n) (ht₀ : 0 < t) (ht : t ≤ n) :
    Tensor.Concise (tensor (F := F) n t ht) := by
  let _ : DecidableEq (Fin 3) := Classical.decEq _
  intro i f g h
  fin_cases i
  · ext a
    have hh := congrFun h (columnZero n t hn ht₀ ht a)
    simpa [Tensor.contraction_apply, tensor_column_zero, mul_ite] using hh
  · ext a
    have hh := congrFun h (columnOne n t hn ht a)
    simpa [Tensor.contraction_apply, tensor_column_one, mul_ite] using hh
  · ext a
    have hh := congrFun h (columnTwo n t hn ht₀ ht a)
    simpa [Tensor.contraction_apply, tensor_column_two, mul_ite] using hh

end

end Lemmata.Centroid.Construction.Hook
