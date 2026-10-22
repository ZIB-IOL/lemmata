module

public import Lemmata.Centroid.Proof.Tensor.Support

@[expose] public section

open scoped BigOperators Matrix
open Classical

noncomputable section

namespace Lemmata.Centroid.Tensor

variable {F ι : Type*} [Field F] {V : ι → Type*} [∀ i, Fintype (V i)]

theorem legAction_eq_self_of_slices {T : Tensor F ι V} {i : ι}
    {P : Matrix (V i) (V i) F}
    (hP : ∀ x, P *ᵥ oneSlice i x T = oneSlice i x T) : legAction T i P = T := by
  funext x
  have h := congrFun (hP x) (x i)
  simpa only [Matrix.mulVec, dotProduct, oneSlice_apply, Function.update_eq_self,
    legAction_apply] using h

theorem legAction_eq_self_of_oneSupport {S : Submodule F (Tensor F ι V)}
    {T : Tensor F ι V} {i : ι}
    {P : Matrix (V i) (V i) F}
    (hP : P * P = P)
    (hS : oneSupportAt S i ≤ (Matrix.mulVecLin P).range) (hT : T ∈ S) :
    legAction T i P = T := by
  apply legAction_eq_self_of_slices
  intro x
  have hx : oneSlice i x T ∈ oneSupportAt S i := by
    exact Submodule.mem_iSup_of_mem x
      (Submodule.mem_map.mpr ⟨T, hT, rfl⟩)
  obtain ⟨v, hv⟩ := hS hx
  change P *ᵥ v = oneSlice i x T at hv
  rw [← hv, Matrix.mulVec_mulVec, hP]

end Lemmata.Centroid.Tensor
