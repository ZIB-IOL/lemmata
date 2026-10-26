module

public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Lean.Elab.Tactic.Omega

@[expose] public section

set_option Elab.async false

namespace Lemmata.CocubicCovering.Covering

open Module LinearMap
open LinearMap (BilinForm)
open scoped BigOperators

variable {K E Q : Type*} [Field K] [AddCommGroup E] [Module K E]
  [AddCommGroup Q] [Module K Q]

def gram (B : BilinForm K E) (e : Q →ₗ[K] E) : BilinForm K Q :=
  (B.compl₂ e).comp e

@[simp] theorem gram_apply (B : BilinForm K E) (e : Q →ₗ[K] E) (q q' : Q) :
    gram B e q q' = B (e q) (e q') := rfl

variable [FiniteDimensional K E]

omit [FiniteDimensional K E] in
theorem gram_rank_linearEquiv (B : BilinForm K E) (e : Q ≃ₗ[K] E) :
    finrank K (LinearMap.range (gram B e.toLinearMap)) =
      finrank K (LinearMap.range B) := by
  let f : Q →ₗ[K] Module.Dual K E := LinearMap.comp B e.toLinearMap
  have he : gram B e.toLinearMap =
      e.dualMap.toLinearMap.comp f := by
    ext q q'
    rfl
  have hf : LinearMap.range f = LinearMap.range B :=
    LinearMap.range_comp_of_range_eq_top B (LinearEquiv.range e)
  rw [he, LinearMap.range_comp, hf]
  exact e.dualMap.finrank_map_eq _

/-- Self-orthogonality and an evaluated Gram matrix give a dimension bound. -/
theorem twice_finrank_add_gram_rank_le (B : BilinForm K E) (hB : B.Nondegenerate)
    (V : Submodule K E) (hV : V ≤ B.orthogonal V)
    (e : Q →ₗ[K] E) (he : LinearMap.range e ≤ B.orthogonal V) :
    2 * finrank K V + finrank K (LinearMap.range (gram B e)) ≤ finrank K E := by
  let W := B.orthogonal V
  let f : W →ₗ[K] Module.Dual K Q := (B.compl₂ e).comp W.subtype
  let g : Q →ₗ[K] W := e.codRestrict W fun q => he ⟨q, rfl⟩
  let i : V →ₗ[K] LinearMap.ker f :=
    (Submodule.inclusion hV).codRestrict (LinearMap.ker f) fun v => by
      rw [LinearMap.mem_ker]
      ext q
      change B v (e q) = 0
      exact he ⟨q, rfl⟩ v v.property
  have hi : Function.Injective i := by
    intro v w hvw
    apply Subtype.ext
    exact congrArg (fun z : LinearMap.ker f => ((z : W) : E)) hvw
  have hker : finrank K V ≤ finrank K (LinearMap.ker f) :=
    LinearMap.finrank_le_finrank_of_injective hi
  have hgram : gram B e = f.comp g := rfl
  have hrank : finrank K (LinearMap.range (gram B e)) ≤
      finrank K (LinearMap.range f) := by
    rw [hgram]
    exact Submodule.finrank_mono (LinearMap.range_comp_le_range g f)
  have hsum := f.finrank_range_add_finrank_ker
  have horth : finrank K W = finrank K E - finrank K V :=
    LinearMap.BilinForm.finrank_orthogonal hB V
  have hdim := V.finrank_le
  omega

theorem dotProductBilin_nondegenerate {Ω : Type*} [Fintype Ω] :
    (dotProductBilin K K : BilinForm K (Ω → K)).Nondegenerate := by
  constructor
  · intro x hx
    exact dotProduct_eq_zero x hx
  · intro x hx
    apply dotProduct_eq_zero x
    intro y
    exact (dotProduct_comm x y).trans (hx y)

theorem twice_finrank_add_gram_rank_le_card {Ω : Type*} [Fintype Ω]
    (V : Submodule K (Ω → K)) (e : Q →ₗ[K] (Ω → K))
    (hV : ∀ v ∈ V, ∀ w ∈ V, ∑ x, v x * w x = 0)
    (he : ∀ v ∈ V, ∀ q, ∑ x, v x * e q x = 0) :
    2 * finrank K V +
      finrank K (LinearMap.range (gram (dotProductBilin K K) e)) ≤ Fintype.card Ω := by
  have h := twice_finrank_add_gram_rank_le
    (dotProductBilin K K) dotProductBilin_nondegenerate V
    (fun w hw v hv => hV v hv w hw) e (by
      rintro _ ⟨q, rfl⟩ v hv
      exact he v hv q)
  simpa using h

omit [FiniteDimensional K E] in
theorem restrict_kernel_map (B : BilinForm K E) (hB : B.IsRefl)
    (N : Submodule K E) :
    (LinearMap.ker (B.restrict N)).map N.subtype = N ⊓ B.orthogonal N := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.property, ?_⟩
    intro z hz
    apply hB
    exact LinearMap.congr_fun hy ⟨z, hz⟩
  · rintro ⟨hx, horth⟩
    refine ⟨⟨x, hx⟩, ?_, rfl⟩
    change (B.restrict N) ⟨x, hx⟩ = 0
    ext y
    exact hB _ _ (horth y y.property)

/-- The radical cross-block contributes twice its rank beyond the restricted form. -/
theorem restrict_rank_add_twice_cross_rank_le (B : BilinForm K E) (hB : B.IsRefl)
    (N : Submodule K E) :
    finrank K (LinearMap.range (B.restrict N)) +
      2 * finrank K (LinearMap.range (B.domRestrict (N ⊓ B.orthogonal N))) ≤
      finrank K (LinearMap.range B) := by
  let R := N ⊓ B.orthogonal N
  have hR : finrank K R = finrank K (LinearMap.ker (B.restrict N)) := by
    change finrank K (N ⊓ B.orthogonal N : Submodule K E) = _
    rw [← restrict_kernel_map B hB N]
    exact Submodule.finrank_map_subtype_eq N _
  have hRK : R ⊓ LinearMap.ker B = N ⊓ LinearMap.ker B := by
    ext x
    constructor
    · intro hx
      exact ⟨hx.1.1, hx.2⟩
    · intro hx
      refine ⟨⟨hx.1, ?_⟩, hx.2⟩
      intro y hy
      apply hB
      exact LinearMap.congr_fun hx.2 y
  have hC : finrank K (LinearMap.ker (B.domRestrict R)) =
      finrank K (N ⊓ LinearMap.ker B : Submodule K E) := by
    rw [← Submodule.finrank_map_subtype_eq R (LinearMap.ker (B.domRestrict R)),
      B.toLin_restrict_ker_eq_inf_ker R, hRK]
  have hle : N ⊔ LinearMap.ker B ≤ B.orthogonal R := by
    apply sup_le
    · intro x hx r hr
      exact hB _ _ (hr.2 x hx)
    · intro x hx r hr
      apply hB
      exact LinearMap.congr_fun hx r
  have hdim := Submodule.finrank_mono hle
  have hsup := N.finrank_sup_add_finrank_inf_eq (LinearMap.ker B)
  have horth := LinearMap.BilinForm.finrank_add_finrank_orthogonal' (B := B) R
  rw [hRK] at horth
  have hA := (B.restrict N).finrank_range_add_finrank_ker
  have hcross := (B.domRestrict R).finrank_range_add_finrank_ker
  have hfull := B.finrank_range_add_finrank_ker
  change finrank K (LinearMap.range (B.restrict N)) +
    2 * finrank K (LinearMap.range (B.domRestrict R)) ≤
    finrank K (LinearMap.range B)
  omega

theorem exists_new_kernel_direction (R H K₀ C : Submodule K E)
    (hH : H ≤ R) (hK : K₀ ≤ R) (hHC : H ⊓ C = ⊥)
    (hdim : finrank K R < finrank K H + finrank K K₀) :
    ∃ v : E, v ∈ H ∧ v ∈ K₀ ∧ v ≠ 0 ∧ v ∉ C := by
  have hne : H ⊓ K₀ ≠ ⊥ := by
    intro hinf
    have hsum := H.finrank_sup_add_finrank_inf_eq K₀
    rw [hinf, finrank_bot, add_zero] at hsum
    have hsup := Submodule.finrank_mono (sup_le hH hK)
    omega
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  refine ⟨v, hv.1, hv.2, hv0, ?_⟩
  intro hvc
  have hbot : v ∈ (⊥ : Submodule K E) := by
    rw [← hHC]
    exact ⟨hv.1, hvc⟩
  exact hv0 (by simpa using hbot)

theorem twice_finrank_le_rank_add_restrict_rank_add_twice_kernel
    (B : BilinForm K E) (hB : B.IsRefl) (N : Submodule K E) :
    2 * finrank K N ≤ finrank K (LinearMap.range B) +
      finrank K (LinearMap.range (B.restrict N)) +
      2 * finrank K (N ⊓ LinearMap.ker B : Submodule K E) := by
  let R := N ⊓ B.orthogonal N
  have hA := (B.restrict N).finrank_range_add_finrank_ker
  have hR : finrank K (LinearMap.ker (B.restrict N)) = finrank K R := by
    rw [← Submodule.finrank_map_subtype_eq N (LinearMap.ker (B.restrict N)),
      restrict_kernel_map B hB N]
  have hRK : R ⊓ LinearMap.ker B = N ⊓ LinearMap.ker B := by
    have hK : LinearMap.ker B ≤ B.orthogonal N := by
      intro x hx y hy
      exact hB _ _ (LinearMap.congr_fun hx y)
    change (N ⊓ B.orthogonal N) ⊓ LinearMap.ker B = _
    rw [inf_assoc, inf_eq_right.mpr hK]
  have hC := (B.domRestrict R).finrank_range_add_finrank_ker
  have hCK : finrank K (LinearMap.ker (B.domRestrict R)) =
      finrank K (N ⊓ LinearMap.ker B : Submodule K E) := by
    rw [← Submodule.finrank_map_subtype_eq R (LinearMap.ker (B.domRestrict R)),
      B.toLin_restrict_ker_eq_inf_ker R, hRK]
  have hblock := restrict_rank_add_twice_cross_rank_le B hB N
  change finrank K (LinearMap.range (B.restrict N)) +
    2 * finrank K (LinearMap.range (B.domRestrict R)) ≤
    finrank K (LinearMap.range B) at hblock
  omega

end Lemmata.CocubicCovering.Covering
