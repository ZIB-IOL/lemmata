module

public import Lemmata.RM59.Proof.SupportChecks
public import Lemmata.RM59.Proof.FieldData
public meta import Lemmata.RM59.Proof.SupportChecks
public meta import Lemmata.RM59.Proof.FieldData
public meta import Lean.Elab.Tactic.Decide

@[expose] public section

namespace Lemmata.RM59.HeavyFamilies

private theorem heavy_family_data : ∀ i : Fin 348,
    ((Certificate.seed (i.val + 1)).length = 30 → i.val + 1 = 35 ∨ i.val + 1 = 49) ∧
    ((Certificate.seed (i.val + 1)).length = 32 → i.val + 1 = 53) := by
  native_decide

theorem weight30_family (i : Fin 348) (h : (Certificate.seed (i.val + 1)).length = 30) :
    i.val + 1 = 35 ∨ i.val + 1 = 49 := (heavy_family_data i).1 h

theorem weight32_family (i : Fin 348) (h : (Certificate.seed (i.val + 1)).length = 32) :
    i.val + 1 = 53 := (heavy_family_data i).2 h

theorem seed35_eq_support35 : Certificate.seed 35 = FieldData.support35 := by native_decide

theorem seed53_eq_support53 : Certificate.seed 53 = FieldData.support53 := by native_decide

theorem decoded_seed35_eq_support35 :
    Packed.decodeWord (Certificate.seed 35) = Packed.decodeWord FieldData.support35 :=
  congrArg Packed.decodeWord seed35_eq_support35

theorem decoded_seed53_eq_support53 :
    Packed.decodeWord (Certificate.seed 53) = Packed.decodeWord FieldData.support53 :=
  congrArg Packed.decodeWord seed53_eq_support53

end Lemmata.RM59.HeavyFamilies
