module

public import Lemmata.Centroid.Proof.Construction.CircuitTarget
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

open scoped BigOperators
open Classical

namespace Lemmata.Centroid.Construction.Circuit

noncomputable section

variable {F : Type*} [Field F]

theorem sector_zero (q ν : ℕ)
    (x : ∀ i, Realization.Coordinates (Core q ν) (Dual q ν) i) :
    Realization.sector (pairs (F := F) q ν) 0 x =
      match x 0 with
      | Sum.inl _ => 0
      | Sum.inr l => Realization.coreEntry 1 (x 1) (pairPoint q ν 0 l 1) *
          Realization.coreEntry 2 (x 2) (pairPoint q ν 0 l 2) := by
  unfold Realization.sector
  cases x 0 with
  | inl _ => rfl
  | inr l =>
    change Realization.pairEmbedding 0 (Realization.basisVector
      (fun j : {j : Fin 3 // j ≠ 0} => pairPoint q ν 0 l j.val)) x = _
    rw [Realization.pairEmbedding_basisVector]
    convert Realization.prod_other_zero (F := F)
      (fun j => Realization.coreEntry (F := F) j (x j) (pairPoint q ν 0 l j))
      using 1
    congr 1
    ext j
    simp

theorem sector_one (q ν : ℕ)
    (x : ∀ i, Realization.Coordinates (Core q ν) (Dual q ν) i) :
    Realization.sector (pairs (F := F) q ν) 1 x =
      match x 1 with
      | Sum.inl _ => 0
      | Sum.inr l => Realization.coreEntry 0 (x 0) (pairPoint q ν 1 l 0) *
          Realization.coreEntry 2 (x 2) (pairPoint q ν 1 l 2) := by
  unfold Realization.sector
  cases x 1 with
  | inl _ => rfl
  | inr l =>
    change Realization.pairEmbedding 1 (Realization.basisVector
      (fun j : {j : Fin 3 // j ≠ 1} => pairPoint q ν 1 l j.val)) x = _
    rw [Realization.pairEmbedding_basisVector]
    convert Realization.prod_other_one (F := F)
      (fun j => Realization.coreEntry (F := F) j (x j) (pairPoint q ν 1 l j))
      using 1
    congr 1
    ext j
    simp

theorem sector_two (q ν : ℕ)
    (x : ∀ i, Realization.Coordinates (Core q ν) (Dual q ν) i) :
    Realization.sector (pairs (F := F) q ν) 2 x =
      match x 2 with
      | Sum.inl _ => 0
      | Sum.inr l => Realization.coreEntry 0 (x 0) (pairPoint q ν 2 l 0) *
          Realization.coreEntry 1 (x 1) (pairPoint q ν 2 l 1) := by
  unfold Realization.sector
  cases x 2 with
  | inl _ => rfl
  | inr l =>
    change Realization.pairEmbedding 2 (Realization.basisVector
      (fun j : {j : Fin 3 // j ≠ 2} => pairPoint q ν 2 l j.val)) x = _
    rw [Realization.pairEmbedding_basisVector]
    convert Realization.prod_other_two (F := F)
      (fun j => Realization.coreEntry (F := F) j (x j) (pairPoint q ν 2 l j))
      using 1
    congr 1
    ext j
    simp

theorem tau_embedding (q ν : ℕ)
    (x : ∀ i, Realization.Coordinates (Core q ν) (Dual q ν) i) :
    Realization.coreEmbedding (tau (F := F) q ν) x =
      ∑ j : Fin q, Realization.coreEntry 0 (x 0) (Sum.inl j.castSucc) *
        Realization.coreEntry 1 (x 1) (Sum.inr ()) *
        Realization.coreEntry 2 (x 2) (Sum.inr (some j)) := by
  simp only [tau, map_sum, Finset.sum_apply, Realization.coreEmbedding_basisVector,
    Fin.prod_univ_three, assignment_zero, assignment_one, assignment_two]

theorem tensor_apply (q ν : ℕ)
    (x : ∀ i, Realization.Coordinates (Core q ν) (Dual q ν) i) :
    tensor (F := F) q ν x =
      (match x 0 with
      | Sum.inl _ => 0
      | Sum.inr l => Realization.coreEntry 1 (x 1) (pairPoint q ν 0 l 1) *
          Realization.coreEntry 2 (x 2) (pairPoint q ν 0 l 2)) +
      (match x 1 with
      | Sum.inl _ => 0
      | Sum.inr l => Realization.coreEntry 0 (x 0) (pairPoint q ν 1 l 0) *
          Realization.coreEntry 2 (x 2) (pairPoint q ν 1 l 2)) +
      (match x 2 with
      | Sum.inl _ => 0
      | Sum.inr l => Realization.coreEntry 0 (x 0) (pairPoint q ν 2 l 0) *
          Realization.coreEntry 1 (x 1) (pairPoint q ν 2 l 1)) +
      ∑ j : Fin q, Realization.coreEntry 0 (x 0) (Sum.inl j.castSucc) *
        Realization.coreEntry 1 (x 1) (Sum.inr ()) *
        Realization.coreEntry 2 (x 2) (Sum.inr (some j)) := by
  simp only [tensor, Realization.tensor, Pi.add_apply,
    Fin.sum_univ_three, sector_zero, sector_one, sector_two, tau_embedding]

abbrev Coordinates (q ν : ℕ) := Realization.Coordinates (Core q ν) (Dual q ν)

def point (q ν : ℕ) (a : Coordinates q ν 0) (b : Coordinates q ν 1)
    (c : Coordinates q ν 2) : ∀ i, Coordinates q ν i :=
  Fin.cases a (Fin.cases b (Fin.cases c (fun j => Fin.elim0 j)))

@[simp] theorem point_zero (q ν : ℕ) (a : Coordinates q ν 0) (b : Coordinates q ν 1)
    (c : Coordinates q ν 2) : point q ν a b c 0 = a := rfl

@[simp] theorem point_one (q ν : ℕ) (a : Coordinates q ν 0) (b : Coordinates q ν 1)
    (c : Coordinates q ν 2) : point q ν a b c 1 = b := rfl

@[simp] theorem point_two (q ν : ℕ) (a : Coordinates q ν 0) (b : Coordinates q ν 1)
    (c : Coordinates q ν 2) : point q ν a b c 2 = c := rfl

def entry {X Y : Type*} (x : X ⊕ Y) (a : X) : F :=
  match x with
  | Sum.inl b => if a = b then 1 else 0
  | Sum.inr _ => 0

theorem tensor_point (q ν : ℕ)
    (a : A q ν ⊕ ((A q ν × A q ν) ⊕ Fin (q + 1)))
    (b : (A q ν ⊕ Unit) ⊕ ((A q ν × A q ν) ⊕ Fin q))
    (c : (A q ν ⊕ Option (Fin q)) ⊕ (A q ν × A q ν)) :
    tensor (F := F) q ν (point q ν a b c) =
      (match a with
      | Sum.inl _ => 0
      | Sum.inr (Sum.inl p) => entry b (Sum.inl p.1) * entry c (Sum.inl p.2)
      | Sum.inr (Sum.inr j) => entry b (Sum.inl (Sum.inl j)) * entry c (Sum.inr none)) +
      (match b with
      | Sum.inl _ => 0
      | Sum.inr (Sum.inl p) => entry a p.1 * entry c (Sum.inl p.2)
      | Sum.inr (Sum.inr j) => entry a (Sum.inl j.castSucc) * entry c (Sum.inr none)) +
      (match c with
      | Sum.inl _ => 0
      | Sum.inr p => entry a p.1 * entry b (Sum.inl p.2)) +
      ∑ j : Fin q, entry a (Sum.inl j.castSucc) * entry b (Sum.inr ()) *
        entry c (Sum.inr (some j)) := by
  have h := tensor_apply (F := F) q ν (point q ν a b c)
  change _ = _ at h
  convert h using 1
  rcases a with a | a | a <;> rcases b with b | b | b <;> rcases c with c | c <;> rfl

@[simp] theorem update_point_zero [DecidableEq (Fin 3)] (q ν : ℕ)
    (a r : Coordinates q ν 0) (b : Coordinates q ν 1) (c : Coordinates q ν 2) :
    Function.update (point q ν a b c) 0 r = point q ν r b c := by
  funext i
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun j => Fin.elim0 j))) i
  · exact Function.update_self _ _ _
  · exact Function.update_of_ne (fun h => (by decide : (1 : ℕ) ≠ 0) (congrArg Fin.val h)) _ _
  · exact Function.update_of_ne (fun h => (by decide : (2 : ℕ) ≠ 0) (congrArg Fin.val h)) _ _

@[simp] theorem update_point_one [DecidableEq (Fin 3)] (q ν : ℕ)
    (a : Coordinates q ν 0) (b r : Coordinates q ν 1) (c : Coordinates q ν 2) :
    Function.update (point q ν a b c) 1 r = point q ν a r c := by
  funext i
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun j => Fin.elim0 j))) i
  · exact Function.update_of_ne (fun h => (by decide : (0 : ℕ) ≠ 1) (congrArg Fin.val h)) _ _
  · exact Function.update_self _ _ _
  · exact Function.update_of_ne (fun h => (by decide : (2 : ℕ) ≠ 1) (congrArg Fin.val h)) _ _

@[simp] theorem update_point_two [DecidableEq (Fin 3)] (q ν : ℕ)
    (a : Coordinates q ν 0) (b : Coordinates q ν 1) (c r : Coordinates q ν 2) :
    Function.update (point q ν a b c) 2 r = point q ν a b r := by
  funext i
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun j => Fin.elim0 j))) i
  · exact Function.update_of_ne (fun h => (by decide : (0 : ℕ) ≠ 2) (congrArg Fin.val h)) _ _
  · exact Function.update_of_ne (fun h => (by decide : (1 : ℕ) ≠ 2) (congrArg Fin.val h)) _ _
  · exact Function.update_self _ _ _

def corePoint (q ν : ℕ) (a : ∀ i, Core q ν i) : ∀ i, Coordinates q ν i :=
  point q ν (Sum.inl (a 0)) (Sum.inl (a 1)) (Sum.inl (a 2))

def columnZero (q ν : ℕ) : Coordinates q ν 0 → ∀ i, Coordinates q ν i
  | Sum.inl a => point q ν (Sum.inl (Sum.inl 0))
      (Sum.inr (Sum.inl (a, Sum.inl 0))) (Sum.inl (Sum.inl (Sum.inl 0)))
  | Sum.inr l => corePoint q ν (pairPoint q ν 0 l)

def columnOne (q ν : ℕ) (hq : 0 < q) : Coordinates q ν 1 → ∀ i, Coordinates q ν i
  | Sum.inl (Sum.inl b) => point q ν (Sum.inl (Sum.inl 0))
      (Sum.inl (Sum.inr ())) (Sum.inr (Sum.inl 0, b))
  | Sum.inl (Sum.inr _) => corePoint q ν
      (assignment q ν (Sum.inl (⟨0, hq⟩ : Fin q).castSucc) (Sum.inr ()) (Sum.inr (some ⟨0, hq⟩)))
  | Sum.inr l => corePoint q ν (pairPoint q ν 1 l)

def columnTwo (q ν : ℕ) : Coordinates q ν 2 → ∀ i, Coordinates q ν i
  | Sum.inl (Sum.inl c) => point q ν (Sum.inr (Sum.inl (Sum.inl 0, c)))
      (Sum.inl (Sum.inl (Sum.inl 0))) (Sum.inl (Sum.inr none))
  | Sum.inl (Sum.inr none) => point q ν (Sum.inr (Sum.inr 0))
      (Sum.inl (Sum.inl (Sum.inl 0))) (Sum.inl (Sum.inr none))
  | Sum.inl (Sum.inr (some j)) => corePoint q ν
      (assignment q ν (Sum.inl j.castSucc) (Sum.inr ()) (Sum.inr none))
  | Sum.inr l => corePoint q ν (pairPoint q ν 2 l)

theorem tensor_column_zero [d : DecidableEq (Fin 3)] (q ν : ℕ)
    (r s : Coordinates q ν 0) :
    tensor (F := F) q ν (Function.update (columnZero q ν s) 0 r) = if r = s then 1 else 0 := by
  change A q ν ⊕ ((A q ν × A q ν) ⊕ Fin (q + 1)) at r s
  rcases r with r | ⟨r₁, r₂⟩ | r <;> rcases s with s | ⟨s₁, s₂⟩ | s <;>
    simp only [columnZero, corePoint]
  all_goals erw [update_point_zero]
  all_goals erw [tensor_point]
  all_goals simp only [pairPoint_zero_old, pairPoint_zero_new, assignment_one, assignment_two]
  all_goals simp [entry, Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl]
  all_goals try (split_ifs <;> simp_all)
  all_goals try intro h
  all_goals injections
  all_goals subst_vars
  all_goals contradiction

theorem tensor_column_one [d : DecidableEq (Fin 3)] (q ν : ℕ) (hq : 0 < q)
    (r s : Coordinates q ν 1) :
    tensor (F := F) q ν (Function.update (columnOne q ν hq s) 1 r) = if r = s then 1 else 0 := by
  change (A q ν ⊕ Unit) ⊕ ((A q ν × A q ν) ⊕ Fin q) at r s
  rcases r with (r | ⟨⟩) | (⟨r₁, r₂⟩ | r) <;>
    rcases s with (s | ⟨⟩) | (⟨s₁, s₂⟩ | s) <;>
    simp only [columnOne, corePoint]
  all_goals erw [update_point_one]
  all_goals erw [tensor_point]
  all_goals simp only [pairPoint_one_old, pairPoint_one_new, assignment_zero, assignment_two]
  all_goals simp [entry, Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl]
  all_goals try (split_ifs <;> simp_all)
  all_goals try intro h
  all_goals injections
  all_goals subst_vars
  all_goals first | rfl | contradiction

theorem tensor_column_two [d : DecidableEq (Fin 3)] (q ν : ℕ)
    (r s : Coordinates q ν 2) :
    tensor (F := F) q ν (Function.update (columnTwo q ν s) 2 r) = if r = s then 1 else 0 := by
  change (A q ν ⊕ Option (Fin q)) ⊕ (A q ν × A q ν) at r s
  rcases r with (r | (_ | r)) | ⟨r₁, r₂⟩ <;>
    rcases s with (s | (_ | s)) | ⟨s₁, s₂⟩ <;>
    simp only [columnTwo, corePoint]
  all_goals erw [update_point_two]
  all_goals erw [tensor_point]
  all_goals simp only [pairPoint_two, assignment_zero, assignment_one]
  all_goals simp [entry, Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl]
  all_goals try (split_ifs <;> simp_all)
  all_goals try intro h
  all_goals injections
  all_goals subst_vars
  all_goals first | rfl | contradiction

theorem concise (q ν : ℕ) (hq : 0 < q) : Tensor.Concise (tensor (F := F) q ν) := by
  intro i f g h
  fin_cases i
  · ext a
    have hh := congrFun h (columnZero q ν a)
    simpa [Tensor.contraction_apply, tensor_column_zero, mul_ite] using hh
  · ext a
    have hh := congrFun h (columnOne q ν hq a)
    simpa [Tensor.contraction_apply, tensor_column_one, mul_ite] using hh
  · ext a
    have hh := congrFun h (columnTwo q ν a)
    simpa [Tensor.contraction_apply, tensor_column_two, mul_ite] using hh

end

end Lemmata.Centroid.Construction.Circuit
