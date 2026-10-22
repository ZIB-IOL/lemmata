module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.LinearIndependent.BaseChange

@[expose] public section

open scoped BigOperators Matrix
open Classical

noncomputable section

namespace Lemmata.Centroid.Linear

variable {F K ι κ : Type*} [Field F] [Field K] [Fintype ι] [Fintype κ]

theorem matrix_rank_map (φ : F →+* K) (M : Matrix κ ι F) :
    (M.map φ).rank = M.rank := by
  let := φ.toAlgebra
  let b := Module.finBasis F (LinearMap.range M.mulVecLin)
  choose u hu using fun i => (b i).property
  let v : Fin M.rank → (κ → K) := fun i => φ ∘ (b i).val
  have hli : LinearIndependent K v := by
    have hi := b.linearIndependent.map' (LinearMap.range M.mulVecLin).subtype
      (Submodule.ker_subtype _)
    exact (linearIndependent_algebraMap_comp_iff (R := F) (S := K)).mpr hi
  have hleft : Submodule.span K (Set.range v) ≤ LinearMap.range (M.map φ).mulVecLin := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    refine ⟨φ ∘ u i, ?_⟩
    funext j
    change (M.map φ *ᵥ (φ ∘ u i)) j = φ ((b i).val j)
    rw [← RingHom.map_mulVec]
    exact congrArg (fun x : κ → F => φ (x j)) (hu i)
  have hright : LinearMap.range (M.map φ).mulVecLin ≤ Submodule.span K (Set.range v) := by
    rw [Matrix.range_mulVecLin]
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    let x : LinearMap.range M.mulVecLin :=
      ⟨M *ᵥ Pi.single j 1, LinearMap.mem_range_self M.mulVecLin _⟩
    have hx : (M.map φ).col j = ∑ i, φ (b.repr x i) • v i := by
      funext k
      have h := congrArg (fun y : LinearMap.range M.mulVecLin => φ (y.val k)) (b.sum_repr x)
      have h' : (∑ i, φ (b.repr x i) * φ ((b i).val k)) = φ (x.val k) := by
        simpa only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply,
          Pi.smul_apply, smul_eq_mul, map_sum, map_mul] using h
      have hxval : x.val = M.col j := by simp [x]
      simp only [Matrix.col_apply, Matrix.map_apply, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul, v, Function.comp_apply]
      change φ (M k j) = ∑ i, φ (b.repr x i) * φ ((b i).val k)
      rw [h', hxval]
      rfl
    rw [hx]
    exact Submodule.sum_mem _ (fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
  change Module.finrank K (LinearMap.range (M.map φ).mulVecLin) = _
  rw [le_antisymm hleft hright |>.symm, finrank_span_eq_card hli, Fintype.card_fin]

theorem matrix_kernel_finrank_map (φ : F →+* K) (M : Matrix κ ι F) :
    Module.finrank K (LinearMap.ker (M.map φ).mulVecLin) =
      Module.finrank F (LinearMap.ker M.mulVecLin) := by
  have h := M.mulVecLin.finrank_range_add_finrank_ker
  have h' := (M.map φ).mulVecLin.finrank_range_add_finrank_ker
  change M.rank + _ = _ at h
  change (M.map φ).rank + _ = _ at h'
  rw [matrix_rank_map] at h'
  simp only [Module.finrank_pi] at h h'
  omega

end Lemmata.Centroid.Linear
