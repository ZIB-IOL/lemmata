module

public import Mathlib.Data.Bool.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.List.Basic

@[expose] public section

set_option Elab.async false

namespace Lemmata.CocubicCovering.CoveringDAG

def check {n : ℕ} (valid : Fin n → Bool) (premises : Fin n → List (Fin n)) : Bool :=
  (List.finRange n).all fun i =>
    valid i && (premises i).all fun j => decide (j.val < i.val)

theorem check_sound {State : Type*} {n : ℕ} (state : Fin n → State)
    (valid : Fin n → Bool) (premises : Fin n → List (Fin n)) (bad : State → Prop)
    (hstep : ∀ i, valid i = true → bad (state i) →
      ∃ j ∈ premises i, bad (state j))
    (accepted : check valid premises = true) :
    ∀ i, ¬bad (state i) := by
  have hall := List.all_eq_true.mp accepted
  have hgood : ∀ k (hk : k < n), ¬bad (state ⟨k, hk⟩) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro hk hbad
        have hnode := hall ⟨k, hk⟩ (List.mem_finRange _)
        obtain ⟨hvalid, hchildren⟩ := Bool.and_eq_true_iff.mp hnode
        obtain ⟨j, hj, hjbad⟩ := hstep ⟨k, hk⟩ hvalid hbad
        have hlt : j.val < k := of_decide_eq_true ((List.all_eq_true.mp hchildren) j hj)
        exact ih j.val hlt j.isLt hjbad
  intro i
  exact hgood i.val i.isLt

end Lemmata.CocubicCovering.CoveringDAG
