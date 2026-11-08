module

public import Lemmata.RM59.Proof.Model
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public meta import Lean.Elab.Tactic.Omega

@[expose] public section

namespace Lemmata.RM59.RankSelection

variable {M N : Type*} [AddCommGroup M] [Module Field M] [FiniteDimensional Field M]
  [AddCommGroup N] [Module Field N] [FiniteDimensional Field N]

theorem image_rank_bound {ι : Type*} [Fintype ι] (v : ι → M)
    (hv : LinearIndependent Field v) (f : M →ₗ[Field] N) :
    Fintype.card ι ≤ Module.finrank Field (Submodule.span Field (Set.range (f ∘ v))) +
      Module.finrank Field (LinearMap.ker f) := by
  let S := Submodule.span Field (Set.range v)
  let g := f.domRestrict S
  let k : LinearMap.ker g →ₗ[Field] LinearMap.ker f := {
    toFun := fun x => ⟨x.val.val, x.property⟩
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  have hk : Function.Injective k := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : LinearMap.ker f => z.val) h
  have hker := LinearMap.finrank_le_finrank_of_injective hk
  have hrange : LinearMap.range g = Submodule.span Field (Set.range (f ∘ v)) := by
    rw [LinearMap.range_domRestrict, ← Submodule.span_image]
    congr 1
    exact (Set.range_comp f v).symm
  have hr := g.finrank_range_add_finrank_ker
  have hS : Module.finrank Field S = Fintype.card ι := finrank_span_eq_card hv
  rw [hrange, hS] at hr
  omega

theorem independent_subfamily {ι : Type*} [Fintype ι] (v : ι → M)
    (hv : LinearIndependent Field v) (f : M →ₗ[Field] N) (k : Nat)
    (hk : k + Module.finrank Field (LinearMap.ker f) ≤ Fintype.card ι) :
    ∃ selection : Fin k → ι, LinearIndependent Field (f ∘ v ∘ selection) := by
  classical
  have hdim := image_rank_bound v hv f
  have hkr : k ≤ Module.finrank Field (Submodule.span Field (Set.range (f ∘ v))) := by omega
  obtain ⟨g, hgmem, _, hg⟩ := Submodule.exists_fun_fin_finrank_span_eq Field (Set.range (f ∘ v))
  have hgk := hg.comp (Fin.castLE hkr) (Fin.castLE_injective hkr)
  let selection : Fin k → ι := fun i => Classical.choose (hgmem (Fin.castLE hkr i))
  have he : f ∘ v ∘ selection = fun i => g (Fin.castLE hkr i) :=
    funext fun i => Classical.choose_spec (hgmem (Fin.castLE hkr i))
  refine ⟨selection, ?_⟩
  rw [he]
  exact hgk

end Lemmata.RM59.RankSelection
