module

public import Mathlib.Data.Fintype.Basic

@[expose] public section

namespace Lemmata.RM59

structure DerivationStep (α : Type*) where
  value : α
  parent : Option (Nat × Nat)

def DerivationStepValid {α : Type*} (seeds : List α) (moves : Array (α → α))
    (steps : Array (DerivationStep α)) (i : Fin steps.size) : Prop :=
  match steps[i.val].parent with
  | none => steps[i.val].value ∈ seeds
  | some (j, k) =>
    if hj : j < i.val then
      if hk : k < moves.size then
        steps[i.val].value = moves[k] (steps[j]'(hj.trans i.isLt)).value
      else False
    else False

def DerivationValid {α : Type*} (seeds : List α) (moves : Array (α → α))
    (steps : Array (DerivationStep α)) : Prop :=
  ∀ i : Fin steps.size, DerivationStepValid seeds moves steps i

instance {α : Type*} [DecidableEq α] (seeds : List α) (moves : Array (α → α))
    (steps : Array (DerivationStep α)) (i : Fin steps.size) :
    Decidable (DerivationStepValid seeds moves steps i) := by
  unfold DerivationStepValid
  split <;> infer_instance

instance {α : Type*} [DecidableEq α] (seeds : List α) (moves : Array (α → α))
    (steps : Array (DerivationStep α)) :
    Decidable (DerivationValid seeds moves steps) :=
  Fintype.decidableForallFintype

theorem derivation_sound {α : Type*} (P : α → Prop) (seeds : List α)
    (moves : Array (α → α)) (steps : Array (DerivationStep α))
    (hvalid : DerivationValid seeds moves steps)
    (hseeds : ∀ x ∈ seeds, P x)
    (hmoves : ∀ k : Fin moves.size, ∀ x, P x → P (moves[k] x)) :
    ∀ i : Fin steps.size, P steps[i.val].value := by
  have h : ∀ n, ∀ hn : n < steps.size, P (steps[n]'hn).value := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      have hv := hvalid ⟨n, hn⟩
      cases hp : (steps[n]'hn).parent with
      | none =>
        apply hseeds
        simpa only [DerivationStepValid, hp] using hv
      | some parent =>
        obtain ⟨j, k⟩ := parent
        by_cases hj : j < n
        · by_cases hk : k < moves.size
          · have heq :
                (steps[n]'hn).value =
                  moves[k] (steps[j]'(hj.trans hn)).value := by
              simpa only [DerivationStepValid, hp, dif_pos hj, dif_pos hk] using hv
            rw [heq]
            exact hmoves ⟨k, hk⟩ _ (ih j hj (hj.trans hn))
          · simp only [DerivationStepValid, hp, dif_pos hj, dif_neg hk] at hv
        · simp only [DerivationStepValid, hp, dif_neg hj] at hv
  exact fun i => h i.val i.isLt

theorem derivation_covers {α : Type*} (P : α → Prop) (seeds : List α)
    (moves : Array (α → α)) (steps : Array (DerivationStep α))
    (hvalid : DerivationValid seeds moves steps)
    (hseeds : ∀ x ∈ seeds, P x)
    (hmoves : ∀ k : Fin moves.size, ∀ x, P x → P (moves[k] x))
    (x : α) (hcovered : ∃ i : Fin steps.size, steps[i.val].value = x) : P x := by
  obtain ⟨i, rfl⟩ := hcovered
  exact derivation_sound P seeds moves steps hvalid hseeds hmoves i

end Lemmata.RM59
