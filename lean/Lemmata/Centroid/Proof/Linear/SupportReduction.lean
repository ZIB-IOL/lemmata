module

public import Lemmata.Centroid.Proof.Linear.SupportPolynomial

@[expose] public section

open scoped BigOperators
open Classical

noncomputable section

namespace Lemmata.Centroid.Linear

variable {F α β γ σ : Type*} [Field F] [Fintype α] [Fintype β] [Fintype γ]

def polynomialFunctional (w : γ → MvPolynomial σ F) : (γ → F) →ₗ[F] MvPolynomial σ F :=
  Fintype.linearCombination F w

theorem polynomialFunctional_apply (w : γ → MvPolynomial σ F) (v : γ → F) :
    polynomialFunctional w v = ∑ c, v c • w c := rfl

def pairPolynomialMap (w : γ → MvPolynomial σ F) :
    (β × γ → F) →ₗ[F] (β → MvPolynomial σ F) :=
  LinearMap.pi fun b => (polynomialFunctional w).comp (arraySlice b)

def triplePolynomialMap (w : γ → MvPolynomial σ F) :
    (α × (β × γ) → F) →ₗ[F] (α → β → MvPolynomial σ F) :=
  LinearMap.pi fun a => (pairPolynomialMap w).comp (arraySlice a)

theorem polynomialFunctional_ne_zero (w : γ → MvPolynomial σ F) (hw : w ≠ 0) :
    polynomialFunctional w ≠ 0 := by
  intro h
  apply hw
  funext c
  have he := LinearMap.congr_fun h (Pi.single c 1)
  simpa [polynomialFunctional, Fintype.linearCombination_apply] using he

omit [Fintype β] in
theorem pairPolynomialMap_image_ne_bot (P : Submodule F (β × γ → F))
    (hP : arraySupport P = ⊤) (w : γ → MvPolynomial σ F) (hw : w ≠ 0) :
    P.map (pairPolynomialMap w) ≠ ⊥ := by
  intro hz
  have hker : arraySupport P ≤ (polynomialFunctional w).ker := by
    apply iSup_le
    intro b
    rintro _ ⟨v, hv, rfl⟩
    have he : pairPolynomialMap w v = 0 := by
      have hm : pairPolynomialMap w v ∈ P.map (pairPolynomialMap w) := ⟨v, hv, rfl⟩
      rw [hz] at hm
      exact hm
    exact congrFun he b
  have hzero : polynomialFunctional w = 0 := by
    apply LinearMap.ext
    intro v
    exact hker (hP.symm ▸ Submodule.mem_top)
  exact polynomialFunctional_ne_zero w hw hzero

def supportKernel (S : Submodule F (α × (β × γ) → F)) (w : γ → MvPolynomial σ F) :
    Submodule F (α × (β × γ) → F) := S ⊓ (triplePolynomialMap w).ker

omit [Fintype α] [Fintype β] in
theorem supportKernel_first_support_le (S : Submodule F (α × (β × γ) → F))
    (w : γ → MvPolynomial σ F) :
    arraySupport (supportKernel S w) ≤ arraySupport S ⊓ (pairPolynomialMap w).ker := by
  apply iSup_le
  intro a
  rintro _ ⟨v, hv, rfl⟩
  refine ⟨Submodule.mem_iSup_of_mem a ⟨v, hv.1, rfl⟩, ?_⟩
  exact congrFun hv.2 a

omit [Fintype α] in
theorem supportKernel_first_rank_bound (S : Submodule F (α × (β × γ) → F))
    (w : γ → MvPolynomial σ F) :
    Module.finrank F (arraySupport (supportKernel S w)) +
      Module.finrank F ((arraySupport S).map (pairPolynomialMap w)) ≤
        Module.finrank F (arraySupport S) := by
  have hle := Submodule.finrank_mono (supportKernel_first_support_le S w)
  have hd := finrank_inf_ker_add_finrank_map (arraySupport S) (pairPolynomialMap w)
  omega

theorem supportKernel_split_rank (S : Submodule F (α × (β × γ) → F))
    (w : γ → MvPolynomial σ F) :
    Module.finrank F (supportKernel S w) + Module.finrank F (S.map (triplePolynomialMap w)) =
      Module.finrank F S := finrank_inf_ker_add_finrank_map S (triplePolynomialMap w)

omit [Fintype α] [Fintype β] [Fintype γ] in
theorem arraySupport_twice_swap (S : Submodule F (α × (β × γ) → F)) :
    arraySupport (arraySupport (S.map swapFirstTwo.toLinearMap)) = arraySupport (arraySupport S) := by
  simp only [arraySupport, Submodule.map_iSup, ← Submodule.map_comp]
  rw [iSup_comm]
  apply iSup_congr
  intro a
  apply iSup_congr
  intro b
  congr 1

omit [Fintype α] [Fintype β] in
theorem supportKernel_swap (S : Submodule F (α × (β × γ) → F)) (w : γ → MvPolynomial σ F) :
    (supportKernel S w).map swapFirstTwo.toLinearMap =
      supportKernel (S.map swapFirstTwo.toLinearMap) w := by
  ext v
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨⟨u, hu.1, rfl⟩, ?_⟩
    funext b a
    exact congrFun (congrFun hu.2 a) b
  · rintro ⟨⟨u, hu, rfl⟩, hv⟩
    refine ⟨u, ⟨hu, ?_⟩, rfl⟩
    funext a b
    exact congrFun (congrFun hv b) a

omit [Fintype β] in
theorem supportKernel_second_rank_bound (S : Submodule F (α × (β × γ) → F))
    (w : γ → MvPolynomial σ F) :
    Module.finrank F (arraySupport ((supportKernel S w).map swapFirstTwo.toLinearMap)) +
      Module.finrank F ((arraySupport (S.map swapFirstTwo.toLinearMap)).map (pairPolynomialMap w)) ≤
        Module.finrank F (arraySupport (S.map swapFirstTwo.toLinearMap)) := by
  rw [supportKernel_swap]
  exact supportKernel_first_rank_bound _ w

def supportImageLift (S : Submodule F (α × (β × γ) → F)) (w : γ → MvPolynomial σ F) :
    S.map (triplePolynomialMap w) →ₗ[F] (α → (arraySupport S).map (pairPolynomialMap w)) where
  toFun v a := ⟨v.val a, by
    obtain ⟨u, hu, he⟩ := v.property
    exact ⟨arraySlice a u, Submodule.mem_iSup_of_mem a ⟨u, hu, rfl⟩, congrFun he a⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Fintype α] [Fintype β] in
theorem supportImageLift_injective (S : Submodule F (α × (β × γ) → F))
    (w : γ → MvPolynomial σ F) : Function.Injective (supportImageLift S w) := by
  intro v u h
  apply Subtype.ext
  funext a
  exact congrArg Subtype.val (congrFun h a)

omit [Fintype β] in
theorem supportImageLift_mem_kernel (S : Submodule F (α × (β × γ) → F))
    (w : γ → MvPolynomial α F)
    (hw : ∀ m : α →₀ ℕ, (fun p : α × γ => (MvPolynomial.X p.1 * w p.2).coeff m) ∈
      coordinateOrthogonal (arraySupport (S.map swapFirstTwo.toLinearMap)))
    (v : S.map (triplePolynomialMap w)) :
    supportImageLift S w v ∈ (polynomialVariableExpansionMap
      ((arraySupport S).map (pairPolynomialMap w))).ker := by
  obtain ⟨u, hu, he⟩ := v.property
  change polynomialVariableExpansionMap _ (supportImageLift S w v) = 0
  funext b
  apply MvPolynomial.ext
  intro m
  have hum : (fun p : α × γ => u (p.1, b, p.2)) ∈
      arraySupport (S.map swapFirstTwo.toLinearMap) :=
    Submodule.mem_iSup_of_mem b ⟨swapFirstTwo u, ⟨u, hu, rfl⟩, rfl⟩
  have hann := (mem_coordinateOrthogonal _ _).mp (hw m) _ hum
  change (∑ a, MvPolynomial.X a * v.val a b).coeff m = (0 : MvPolynomial α F).coeff m
  rw [← he]
  change (∑ a, MvPolynomial.X a * ∑ c, u (a, b, c) • w c).coeff m = 0
  simp only [Finset.mul_sum, MvPolynomial.coeff_sum, mul_smul_comm,
    MvPolynomial.coeff_smul, smul_eq_mul]
  rw [Fintype.sum_prod_type] at hann
  simpa only [mul_comm] using hann

theorem supportImage_rank_bound (S : Submodule F (α × (β × γ) → F))
    (w : γ → MvPolynomial α F)
    (hw : ∀ m : α →₀ ℕ, (fun p : α × γ => (MvPolynomial.X p.1 * w p.2).coeff m) ∈
      coordinateOrthogonal (arraySupport (S.map swapFirstTwo.toLinearMap))) :
    Module.finrank F (S.map (triplePolynomialMap w)) +
      Module.finrank F (polynomialVariableExpansion ((arraySupport S).map (pairPolynomialMap w))) ≤
        Fintype.card α * Module.finrank F ((arraySupport S).map (pairPolynomialMap w)) := by
  let L := (arraySupport S).map (pairPolynomialMap w)
  let E := polynomialVariableExpansionMap L
  let g : S.map (triplePolynomialMap w) →ₗ[F] E.ker :=
    (supportImageLift S w).codRestrict _ (supportImageLift_mem_kernel S w hw)
  have hg : Function.Injective g := fun x y h => supportImageLift_injective S w
    (congrArg Subtype.val h)
  have hle := LinearMap.finrank_le_finrank_of_injective hg
  have hd := E.finrank_range_add_finrank_ker
  rw [Module.finrank_pi_fintype] at hd
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hd
  change Module.finrank F (polynomialVariableExpansion L) + Module.finrank F E.ker =
    Fintype.card α * Module.finrank F L at hd
  change Module.finrank F (S.map (triplePolynomialMap w)) +
    Module.finrank F (polynomialVariableExpansion L) ≤ Fintype.card α * Module.finrank F L
  omega

end Lemmata.Centroid.Linear
