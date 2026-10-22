module

public import Lemmata.Centroid.Proof.Linear.SupportLemma
public import Mathlib.LinearAlgebra.Projection

@[expose] public section

open Classical

noncomputable section

namespace Lemmata.Centroid.Linear

variable {F α β γ δ : Type*} [Field F]

def arrayTranspose : (α × β → F) ≃ₗ[F] (β × α → F) where
  toFun v p := v (p.2, p.1)
  invFun v p := v (p.2, p.1)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def cycleArray : (α × (β × γ) → F) ≃ₗ[F] (β × (γ × α) → F) where
  toFun v p := v (p.2.2, p.1, p.2.1)
  invFun v p := v (p.2.1, p.2.2, p.1)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def firstArraySupport (S : Submodule F (α × (β × γ) → F)) : Submodule F (α → F) :=
  arraySupport (arraySupport (S.map cycleArray.toLinearMap))

def secondArraySupport (S : Submodule F (α × (β × γ) → F)) : Submodule F (β → F) :=
  arraySupport ((arraySupport S).map arrayTranspose.toLinearMap)

theorem firstArraySupport_eq (S : Submodule F (α × (β × γ) → F)) :
    firstArraySupport S = arraySupport
      ((arraySupport (S.map swapFirstTwo.toLinearMap)).map arrayTranspose.toLinearMap) := by
  simp only [firstArraySupport, arraySupport, Submodule.map_iSup, ← Submodule.map_comp]
  rfl

theorem firstArraySupport_eq_transpose (S : Submodule F (α × (β × γ) → F)) :
    firstArraySupport S = arraySupport (S.map arrayTranspose.toLinearMap) := by
  simp only [firstArraySupport, arraySupport, Submodule.map_iSup, ← Submodule.map_comp,
    iSup_prod]
  rw [iSup_comm]
  rfl

def arrayMapRight (g : (β → F) →ₗ[F] (γ → F)) :
    (α × β → F) →ₗ[F] (α × γ → F) where
  toFun v p := g (arraySlice p.1 v) p.2
  map_add' v w := by ext p; exact congrFun (g.map_add _ _) p.2
  map_smul' c v := by ext p; exact congrFun (g.map_smul c _) p.2

def arrayMapLeft (g : (α → F) →ₗ[F] (γ → F)) :
    (α × β → F) →ₗ[F] (γ × β → F) where
  toFun v p := g (fun a => v (a, p.2)) p.1
  map_add' v w := by ext p; exact congrFun (g.map_add _ _) p.1
  map_smul' c v := by ext p; exact congrFun (g.map_smul c _) p.1

theorem arraySupport_map_left_le [Fintype α] (S : Submodule F (α × β → F))
    (g : (α → F) →ₗ[F] (γ → F)) :
    arraySupport (S.map (arrayMapLeft g)) ≤ arraySupport S := by
  apply iSup_le
  intro c v hv
  obtain ⟨w, ⟨u, hu, rfl⟩, rfl⟩ := hv
  have heq : arraySlice c (arrayMapLeft g u) =
      ∑ a, g (Pi.single a 1) c • arraySlice a u := by
    funext b
    have hcol : (fun a => u (a, b)) = ∑ a, u (a, b) • Pi.single a 1 := by
      ext a
      simp [Finset.sum_apply, Pi.single_apply]
    change g (fun a => u (a, b)) c = _
    rw [hcol, map_sum]
    simp [Finset.sum_apply, arraySlice, mul_comm]
  rw [heq]
  exact Submodule.sum_mem _ fun a _ =>
    Submodule.smul_mem _ _ (Submodule.mem_iSup_of_mem a ⟨u, hu, rfl⟩)

theorem arraySupport_map_left_eq [Fintype α] [Fintype γ]
    (S : Submodule F (α × β → F)) (g : (α → F) →ₗ[F] (γ → F))
    (j : (γ → F) →ₗ[F] (α → F))
    (h : ∀ v ∈ S, arrayMapLeft j (arrayMapLeft g v) = v) :
    arraySupport (S.map (arrayMapLeft g)) = arraySupport S := by
  apply le_antisymm (arraySupport_map_left_le S g)
  have heq : (S.map (arrayMapLeft g)).map (arrayMapLeft j) = S := by
    apply le_antisymm
    · rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
      rw [h v hv]
      exact hv
    · intro v hv
      exact ⟨_, ⟨v, hv, rfl⟩, h v hv⟩
  have hh := arraySupport_map_left_le (S.map (arrayMapLeft g)) j
  rw [heq] at hh
  exact hh

theorem transpose_map_right (S : Submodule F (α × β → F))
    (g : (β → F) →ₗ[F] (γ → F)) :
    (S.map (arrayMapRight g)).map arrayTranspose.toLinearMap =
      (S.map arrayTranspose.toLinearMap).map (arrayMapLeft g) := by
  simp only [← Submodule.map_comp]
  congr 1

@[simp] theorem arrayMapRight_apply (g : (β → F) →ₗ[F] (γ → F))
    (v : α × β → F) (a : α) (c : γ) :
    arrayMapRight g v (a, c) = g (arraySlice a v) c := rfl

theorem arraySupport_map_right (S : Submodule F (α × β → F))
    (g : (β → F) →ₗ[F] (γ → F)) :
    arraySupport (S.map (arrayMapRight g)) = (arraySupport S).map g := by
  simp only [arraySupport, Submodule.map_iSup, ← Submodule.map_comp]
  congr 1

theorem finrank_map_eq_of_leftInverse_on {M N : Type*}
    [AddCommGroup M] [Module F M] [AddCommGroup N] [Module F N]
    (S : Submodule F M) [FiniteDimensional F S]
    (g : M →ₗ[F] N) (j : N →ₗ[F] M) (h : ∀ v ∈ S, j (g v) = v) :
    Module.finrank F (S.map g) = Module.finrank F S := by
  rw [← LinearMap.range_domRestrict]
  apply LinearMap.finrank_range_of_inj
  intro v w hvw
  apply Subtype.ext
  exact (h v v.property).symm.trans ((congrArg j hvw).trans (h w w.property))

theorem arrayMapRight_leftInverse_on (S : Submodule F (α × β → F))
    (g : (β → F) →ₗ[F] (γ → F)) (j : (γ → F) →ₗ[F] (β → F))
    (h : ∀ v ∈ arraySupport S, j (g v) = v) :
    ∀ v ∈ S, arrayMapRight j (arrayMapRight g v) = v := by
  intro v hv
  funext p
  exact congrFun (h (arraySlice p.1 v)
    (Submodule.mem_iSup_of_mem p.1 ⟨v, hv, rfl⟩)) p.2

theorem arrayMapLeft_leftInverse_on (S : Submodule F (α × β → F))
    (g : (α → F) →ₗ[F] (γ → F)) (j : (γ → F) →ₗ[F] (α → F))
    (h : ∀ v ∈ arraySupport (S.map arrayTranspose.toLinearMap), j (g v) = v) :
    ∀ v ∈ S, arrayMapLeft j (arrayMapLeft g v) = v := by
  intro v hv
  funext p
  exact congrFun (h (arraySlice p.2 (arrayTranspose v))
    (Submodule.mem_iSup_of_mem p.2 ⟨arrayTranspose v, ⟨v, hv, rfl⟩, rfl⟩)) p.1

theorem arraySupport_transpose_map_right_eq [Fintype β] [Fintype γ]
    (S : Submodule F (α × β → F))
    (g : (β → F) →ₗ[F] (γ → F)) (j : (γ → F) →ₗ[F] (β → F))
    (h : ∀ v ∈ S, arrayMapRight j (arrayMapRight g v) = v) :
    arraySupport ((S.map (arrayMapRight g)).map arrayTranspose.toLinearMap) =
      arraySupport (S.map arrayTranspose.toLinearMap) := by
  rw [transpose_map_right]
  apply arraySupport_map_left_eq _ g j
  rintro _ ⟨v, hv, rfl⟩
  change arrayTranspose (arrayMapRight j (arrayMapRight g v)) = arrayTranspose v
  rw [h v hv]

theorem arraySupport_map_third (S : Submodule F (α × (β × γ) → F))
    (g : (γ → F) →ₗ[F] (δ → F)) :
    arraySupport (S.map (arrayMapRight (arrayMapRight g))) =
      (arraySupport S).map (arrayMapRight g) := arraySupport_map_right S _

theorem map_third_swap (S : Submodule F (α × (β × γ) → F))
    (g : (γ → F) →ₗ[F] (δ → F)) :
    (S.map (arrayMapRight (arrayMapRight g))).map swapFirstTwo.toLinearMap =
      (S.map swapFirstTwo.toLinearMap).map (arrayMapRight (arrayMapRight g)) := by
  simp only [← Submodule.map_comp]
  congr 1

theorem map_first_swap (S : Submodule F (α × (β × γ) → F))
    (g : (α → F) →ₗ[F] (δ → F)) :
    (S.map (arrayMapLeft g)).map swapFirstTwo.toLinearMap =
      (S.map swapFirstTwo.toLinearMap).map (arrayMapRight (arrayMapLeft g)) := by
  simp only [← Submodule.map_comp]
  congr 1

theorem map_second_swap (S : Submodule F (α × (β × γ) → F))
    (g : (β → F) →ₗ[F] (δ → F)) :
    (S.map (arrayMapRight (arrayMapLeft g))).map swapFirstTwo.toLinearMap =
      (S.map swapFirstTwo.toLinearMap).map (arrayMapLeft g) := by
  simp only [← Submodule.map_comp]
  congr 1

theorem exists_support_coordinates [Fintype γ] (R : Submodule F (γ → F)) :
    ∃ (g : (γ → F) →ₗ[F] (Fin (Module.finrank F R) → F))
      (j : (Fin (Module.finrank F R) → F) →ₗ[F] (γ → F)),
      (∀ v ∈ R, j (g v) = v) ∧ R.map g = ⊤ := by
  obtain ⟨H, hH⟩ := R.exists_isCompl
  let b := Module.finBasis F R
  let g := b.equivFun.toLinearMap.comp (R.projectionOnto H hH)
  let j := R.subtype.comp b.equivFun.symm.toLinearMap
  refine ⟨g, j, ?_, ?_⟩
  · intro v hv
    change (b.equivFun.symm (b.equivFun (R.projectionOnto H hH v))).val = v
    rw [b.equivFun.symm_apply_apply, Submodule.projectionOnto_apply_of_mem_left hH hv]
  · apply top_unique
    intro v _
    refine ⟨(b.equivFun.symm v).val, (b.equivFun.symm v).property, ?_⟩
    change b.equivFun (R.projectionOnto H hH (b.equivFun.symm v).val) = v
    rw [Submodule.projectionOnto_apply_left, b.equivFun.apply_symm_apply]

theorem exists_third_support_coordinates [Fintype α] [Fintype β] [Fintype γ]
    (S : Submodule F (α × (β × γ) → F)) :
    ∃ U : Submodule F
        (α × (β × Fin (Module.finrank F (arraySupport (arraySupport S)))) → F),
      Module.finrank F U = Module.finrank F S ∧
      Module.finrank F (arraySupport U) = Module.finrank F (arraySupport S) ∧
      Module.finrank F (arraySupport (U.map swapFirstTwo.toLinearMap)) =
        Module.finrank F (arraySupport (S.map swapFirstTwo.toLinearMap)) ∧
      arraySupport (arraySupport U) = ⊤ := by
  obtain ⟨g, j, hleft, hfull⟩ := exists_support_coordinates (arraySupport (arraySupport S))
  let U := S.map (arrayMapRight (arrayMapRight g))
  have hP := arrayMapRight_leftInverse_on (arraySupport S) g j hleft
  have hS := arrayMapRight_leftInverse_on S (arrayMapRight g) (arrayMapRight j) hP
  have hQ : ∀ v ∈ arraySupport (S.map swapFirstTwo.toLinearMap),
      arrayMapRight j (arrayMapRight g v) = v := by
    apply arrayMapRight_leftInverse_on
    rwa [arraySupport_twice_swap]
  refine ⟨U, finrank_map_eq_of_leftInverse_on S _ _ hS, ?_, ?_, ?_⟩
  · rw [arraySupport_map_third]
    exact finrank_map_eq_of_leftInverse_on _ _ _ hP
  · rw [map_third_swap, arraySupport_map_third]
    exact finrank_map_eq_of_leftInverse_on _ _ _ hQ
  · rw [arraySupport_map_third, arraySupport_map_right, hfull]

theorem exists_first_support_coordinates [Fintype α] [Fintype β] [Fintype γ]
    (S : Submodule F (α × (β × γ) → F)) :
    ∃ U : Submodule F (Fin (Module.finrank F (firstArraySupport S)) × (β × γ) → F),
      Module.finrank F U = Module.finrank F S ∧
      arraySupport U = arraySupport S ∧
      Module.finrank F (arraySupport (U.map swapFirstTwo.toLinearMap)) ≤
        Module.finrank F (arraySupport (S.map swapFirstTwo.toLinearMap)) ∧
      secondArraySupport U = secondArraySupport S := by
  obtain ⟨g, j, hleft, _⟩ := exists_support_coordinates (firstArraySupport S)
  have hS := arrayMapLeft_leftInverse_on S g j (firstArraySupport_eq_transpose S ▸ hleft)
  let U := S.map (arrayMapLeft g)
  have hP : arraySupport U = arraySupport S := arraySupport_map_left_eq S g j hS
  refine ⟨U, finrank_map_eq_of_leftInverse_on S _ _ hS, hP, ?_, ?_⟩
  · rw [map_first_swap, arraySupport_map_right]
    exact Submodule.finrank_map_le _ _
  · unfold secondArraySupport
    rw [hP]

theorem exists_second_support_coordinates [Fintype α] [Fintype β] [Fintype γ]
    (S : Submodule F (α × (β × γ) → F)) :
    ∃ U : Submodule F (α × (Fin (Module.finrank F (secondArraySupport S)) × γ) → F),
      Module.finrank F U = Module.finrank F S ∧
      Module.finrank F (arraySupport U) ≤ Module.finrank F (arraySupport S) ∧
      arraySupport (U.map swapFirstTwo.toLinearMap) =
        arraySupport (S.map swapFirstTwo.toLinearMap) ∧
      arraySupport (arraySupport U) = arraySupport (arraySupport S) := by
  obtain ⟨g, j, hleft, _⟩ := exists_support_coordinates (secondArraySupport S)
  have hP := arrayMapLeft_leftInverse_on (arraySupport S) g j hleft
  have hS := arrayMapRight_leftInverse_on S (arrayMapLeft g) (arrayMapLeft j) hP
  let U := S.map (arrayMapRight (arrayMapLeft g))
  have hQ : arraySupport (U.map swapFirstTwo.toLinearMap) =
      arraySupport (S.map swapFirstTwo.toLinearMap) := by
    rw [map_second_swap]
    apply arraySupport_map_left_eq _ g j
    rintro _ ⟨v, hv, rfl⟩
    change swapFirstTwo (arrayMapRight (arrayMapLeft j) (arrayMapRight (arrayMapLeft g) v)) =
      swapFirstTwo v
    rw [hS v hv]
  refine ⟨U, finrank_map_eq_of_leftInverse_on S _ _ hS, ?_, hQ, ?_⟩
  · rw [arraySupport_map_right]
    exact Submodule.finrank_map_le _ _
  · rw [arraySupport_map_right]
    exact arraySupport_map_left_eq _ g j hP

private theorem support_small_ambient {n s d p r : ℕ}
    (hn : 1 ≤ n) (hsn : s ≤ n) (hd : d < n) (hp : p ≤ n ^ 2 + s)
    (hr : r ≤ d * p) : r ≤ n ^ 3 + s * (s - 1) := by
  have hbound := hr.trans (Nat.mul_le_mul (show d ≤ n - 1 by omega) hp)
  have hn' : n - 1 + 1 = n := Nat.sub_add_cancel hn
  have heq : (n - 1) * (n ^ 2 + s) + (n ^ 2 + s) = n ^ 3 + n * s := by
    calc
      _ = (n - 1 + 1) * (n ^ 2 + s) := by ring
      _ = _ := by rw [hn']; ring
  have hns := Nat.mul_le_mul_left n hsn
  nlinarith

theorem support_lemma_array_ambient [Fintype α] [Fintype β] [Fintype γ]
    (S : Submodule F (α × (β × γ) → F)) {n s : ℕ}
    (hα : Fintype.card α ≤ n) (hβ : Fintype.card β ≤ n) (hs : 2 ≤ s) (hsn : s ≤ n)
    (hW : n + s ≤ Module.finrank F (arraySupport (arraySupport S)))
    (hP : Module.finrank F (arraySupport S) ≤ n ^ 2 + s)
    (hQ : Module.finrank F (arraySupport (S.map swapFirstTwo.toLinearMap)) ≤ n ^ 2 + s) :
    Module.finrank F S ≤ n ^ 3 + s * (s - 1) := by
  by_cases ha : Fintype.card α < n
  · exact support_small_ambient (by omega) hsn ha hP (finrank_le_card_mul_arraySupport S)
  by_cases hb : Fintype.card β < n
  · have hr := finrank_le_card_mul_arraySupport (S.map swapFirstTwo.toLinearMap)
    rw [swapFirstTwo.finrank_map_eq] at hr
    exact support_small_ambient (by omega) hsn hb hQ hr
  obtain ⟨U, hr, hP', hQ', hfull⟩ := exists_third_support_coordinates S
  rw [← hr]
  apply support_lemma_array_full_card_eq U (by omega) (by omega) hs hsn hfull
  · simpa only [Fintype.card_fin] using hW
  · exact hP'.trans_le hP
  · exact hQ'.trans_le hQ

theorem support_lemma_array [Fintype α] [Fintype β] [Fintype γ]
    (S : Submodule F (α × (β × γ) → F)) {n s : ℕ}
    (hα : Module.finrank F (firstArraySupport S) ≤ n)
    (hβ : Module.finrank F (secondArraySupport S) ≤ n) (hs : 2 ≤ s) (hsn : s ≤ n)
    (hW : n + s ≤ Module.finrank F (arraySupport (arraySupport S)))
    (hP : Module.finrank F (arraySupport S) ≤ n ^ 2 + s)
    (hQ : Module.finrank F (arraySupport (S.map swapFirstTwo.toLinearMap)) ≤ n ^ 2 + s) :
    Module.finrank F S ≤ n ^ 3 + s * (s - 1) := by
  obtain ⟨S₁, hr₁, hP₁, hQ₁, hβ₁⟩ := exists_first_support_coordinates S
  obtain ⟨S₂, hr₂, hP₂, hQ₂, hW₂⟩ := exists_second_support_coordinates S₁
  have hβ' : Module.finrank F (secondArraySupport S₁) ≤ n :=
    (congrArg (fun R : Submodule F (β → F) => Module.finrank F R) hβ₁).trans_le hβ
  rw [← hr₁, ← hr₂]
  apply support_lemma_array_ambient S₂
  · simpa only [Fintype.card_fin] using hα
  · simpa only [Fintype.card_fin] using hβ'
  · exact hs
  · exact hsn
  · rwa [hW₂, hP₁]
  · exact hP₂.trans (hP₁ ▸ hP)
  · rw [hQ₂]
    exact hQ₁.trans hQ

end Lemmata.Centroid.Linear
