module

public import Lemmata.RM59.Proof.Reachability

@[expose] public section

namespace Lemmata.RM59

def IndexedDerivationStepValid {α : Type*} (seeds : Array α) (moves : Array (α → α))
    (steps : Array (DerivationStep α)) (roots : Array Nat) (i : Fin steps.size) : Prop :=
  match steps[i.val].parent with
  | none => seeds[roots[i.val]?.getD 0]? = some steps[i.val].value
  | some (j, k) =>
    if hj : j < i.val then
      if hk : k < moves.size then
        steps[i.val].value = moves[k] (steps[j]'(hj.trans i.isLt)).value
      else False
    else False

instance {α : Type*} [DecidableEq α] (seeds : Array α) (moves : Array (α → α))
    (steps : Array (DerivationStep α)) (roots : Array Nat) (i : Fin steps.size) :
    Decidable (IndexedDerivationStepValid seeds moves steps roots i) := by
  unfold IndexedDerivationStepValid
  split <;> infer_instance

def indexedDerivationCheck {α : Type*} [DecidableEq α] (seeds : List α)
    (moves : Array (α → α)) (steps : Array (DerivationStep α)) (roots : Array Nat) : Bool :=
  let seedArray := seeds.toArray
  (List.finRange steps.size).all fun i =>
    decide (IndexedDerivationStepValid seedArray moves steps roots i)

theorem indexedDerivationStepValid_sound {α : Type*} (seeds : List α)
    (moves : Array (α → α)) (steps : Array (DerivationStep α)) (roots : Array Nat)
    (i : Fin steps.size) (h : IndexedDerivationStepValid seeds.toArray moves steps roots i) :
    DerivationStepValid seeds moves steps i := by
  cases hp : steps[i.val].parent with
  | none =>
    have hindex : seeds.toArray[roots[i.val]?.getD 0]? = some steps[i.val].value := by
      simpa only [IndexedDerivationStepValid, hp] using h
    simpa only [DerivationStepValid, hp] using
      List.mem_toArray.mp (Array.mem_of_getElem? hindex)
  | some parent =>
    simpa only [IndexedDerivationStepValid, DerivationStepValid, hp] using h

theorem indexedDerivationCheck_sound {α : Type*} [DecidableEq α] (seeds : List α)
    (moves : Array (α → α)) (steps : Array (DerivationStep α)) (roots : Array Nat)
    (h : indexedDerivationCheck seeds moves steps roots = true) :
    DerivationValid seeds moves steps := by
  intro i
  have hi := List.all_eq_true.mp h i (List.mem_finRange i)
  exact indexedDerivationStepValid_sound seeds moves steps roots i (of_decide_eq_true hi)

end Lemmata.RM59
