module

public import Lemmata.Centroid.Proof.Tensor.SupportBound
public import Lemmata.Centroid.Proof.Tensor.PartyEquiv
public import Lemmata.Centroid.Proof.Linear.SupportCoordinates

@[expose] public section

open Classical

noncomputable section

namespace Lemmata.Centroid.Tensor

variable {F : Type*} [Field F] {V : Fin 3 → Type*}

local instance arrayPartyDecidableEq : DecidableEq (Fin 3) := Classical.decEq _

def toArray : Tensor F (Fin 3) V ≃ₗ[F] (V 0 × (V 1 × V 2) → F) :=
  LinearEquiv.funCongrLeft F F (threeCoordinates V).symm

@[simp] theorem toArray_apply (T : Tensor F (Fin 3) V) (p : V 0 × (V 1 × V 2)) :
    toArray T p = T ((threeCoordinates V).symm p) := rfl

def arraySpace (S : Submodule F (Tensor F (Fin 3) V)) := S.map toArray.toLinearMap

theorem finrank_arraySpace (S : Submodule F (Tensor F (Fin 3) V)) :
    Module.finrank F (arraySpace S) = Module.finrank F S := toArray.finrank_map_eq S

@[simp] theorem threeCoordinates_symm_zero (p : V 0 × (V 1 × V 2)) :
    (threeCoordinates V).symm p 0 = p.1 :=
  congrArg Prod.fst ((threeCoordinates V).apply_symm_apply p)

@[simp] theorem threeCoordinates_symm_one (p : V 0 × (V 1 × V 2)) :
    (threeCoordinates V).symm p 1 = p.2.1 :=
  congrArg (fun q => q.2.1) ((threeCoordinates V).apply_symm_apply p)

@[simp] theorem threeCoordinates_symm_two (p : V 0 × (V 1 × V 2)) :
    (threeCoordinates V).symm p 2 = p.2.2 :=
  congrArg (fun q => q.2.2) ((threeCoordinates V).apply_symm_apply p)

def inflateZero : (V 1 × V 2 → F) →ₗ[F] Tensor F (Fin 3) V where
  toFun v x := v (x 1, x 2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def inflateOne : (V 0 × V 2 → F) →ₗ[F] Tensor F (Fin 3) V where
  toFun v x := v (x 0, x 2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem inflateZero_injective [Nonempty (V 0)] : Function.Injective (inflateZero (F := F) (V := V)) := by
  intro v w h
  funext p
  have hx := congrFun h ((threeCoordinates V).symm (Classical.choice inferInstance, p))
  simpa only [inflateZero, LinearMap.coe_mk, AddHom.coe_mk, threeCoordinates_symm_one,
    threeCoordinates_symm_two] using hx

theorem inflateOne_injective [Nonempty (V 1)] : Function.Injective (inflateOne (F := F) (V := V)) := by
  intro v w h
  funext p
  have hx := congrFun h ((threeCoordinates V).symm (p.1, Classical.choice inferInstance, p.2))
  simpa only [inflateOne, LinearMap.coe_mk, AddHom.coe_mk, threeCoordinates_symm_zero,
    threeCoordinates_symm_two] using hx

theorem inflateZero_slice (a : V 0) :
    (inflateZero (F := F) (V := V)).comp ((Linear.arraySlice a).comp toArray.toLinearMap) =
      oppositeSlice 0 a := by
  apply LinearMap.ext
  intro T
  funext x
  simp only [LinearMap.comp_apply, inflateZero, Linear.arraySlice, LinearMap.coe_mk,
    AddHom.coe_mk, LinearEquiv.coe_coe, toArray_apply, oppositeSlice_apply]
  change T ((threeCoordinates V).symm (a, x 1, x 2)) = T (Function.update x 0 a)
  apply congrArg T
  apply (threeCoordinates V).injective
  simp only [Equiv.apply_symm_apply, threeCoordinates_apply, Function.update_self,
    Function.update_of_ne (show (1 : Fin 3) ≠ 0 by omega),
    Function.update_of_ne (show (2 : Fin 3) ≠ 0 by omega)]

theorem inflateOne_slice (a : V 1) :
    (inflateOne (F := F) (V := V)).comp ((Linear.arraySlice a).comp
      (Linear.swapFirstTwo.toLinearMap.comp toArray.toLinearMap)) = oppositeSlice 1 a := by
  apply LinearMap.ext
  intro T
  funext x
  simp only [LinearMap.comp_apply, inflateOne, Linear.arraySlice, LinearMap.coe_mk,
    AddHom.coe_mk, LinearEquiv.coe_coe, Linear.swapFirstTwo_apply, toArray_apply, oppositeSlice_apply]
  change T ((threeCoordinates V).symm (x 0, a, x 2)) = T (Function.update x 1 a)
  apply congrArg T
  apply (threeCoordinates V).injective
  simp only [Equiv.apply_symm_apply, threeCoordinates_apply, Function.update_self,
    Function.update_of_ne (show (0 : Fin 3) ≠ 1 by omega),
    Function.update_of_ne (show (2 : Fin 3) ≠ 1 by omega)]

theorem array_opposite_zero (S : Submodule F (Tensor F (Fin 3) V)) :
    (Linear.arraySupport (arraySpace S)).map inflateZero = oppositeSupportAt S 0 := by
  simp only [Linear.arraySupport, arraySpace, oppositeSupportAt, Submodule.map_iSup,
    ← Submodule.map_comp, inflateZero_slice]

theorem array_opposite_one (S : Submodule F (Tensor F (Fin 3) V)) :
    (Linear.arraySupport ((arraySpace S).map Linear.swapFirstTwo.toLinearMap)).map inflateOne =
      oppositeSupportAt S 1 := by
  simp only [Linear.arraySupport, arraySpace, oppositeSupportAt, Submodule.map_iSup,
    ← Submodule.map_comp, inflateOne_slice]

theorem finrank_array_opposite_zero [Nonempty (V 0)] (S : Submodule F (Tensor F (Fin 3) V)) :
    Module.finrank F (Linear.arraySupport (arraySpace S)) = Module.finrank F (oppositeSupportAt S 0) := by
  rw [← array_opposite_zero]
  exact (Submodule.equivMapOfInjective inflateZero inflateZero_injective _).finrank_eq

theorem finrank_array_opposite_one [Nonempty (V 1)] (S : Submodule F (Tensor F (Fin 3) V)) :
    Module.finrank F (Linear.arraySupport ((arraySpace S).map Linear.swapFirstTwo.toLinearMap)) =
      Module.finrank F (oppositeSupportAt S 1) := by
  rw [← array_opposite_one]
  exact (Submodule.equivMapOfInjective inflateOne inflateOne_injective _).finrank_eq

theorem oneSlice_two_array (x : ∀ i, V i) :
    (Linear.arraySlice (x 1)).comp ((Linear.arraySlice (x 0)).comp toArray.toLinearMap) =
      oneSlice (F := F) 2 x := by
  apply LinearMap.ext
  intro T
  funext a
  simp only [LinearMap.comp_apply, Linear.arraySlice, LinearMap.coe_mk,
    AddHom.coe_mk, LinearEquiv.coe_coe, toArray_apply, oneSlice_apply]
  change T ((threeCoordinates V).symm (x 0, x 1, a)) = T (Function.update x 2 a)
  apply congrArg T
  apply (threeCoordinates V).injective
  simp only [Equiv.apply_symm_apply, threeCoordinates_apply, Function.update_self,
    Function.update_of_ne (show (0 : Fin 3) ≠ 2 by omega),
    Function.update_of_ne (show (1 : Fin 3) ≠ 2 by omega)]

theorem array_oneSupport_two [Nonempty (V 2)] (S : Submodule F (Tensor F (Fin 3) V)) :
    Linear.arraySupport (Linear.arraySupport (arraySpace S)) = oneSupportAt S 2 := by
  simp only [Linear.arraySupport, arraySpace, oneSupportAt, Submodule.map_iSup,
    ← Submodule.map_comp]
  apply le_antisymm
  · apply iSup_le
    intro b
    apply iSup_le
    intro a
    let x := (threeCoordinates V).symm (a, b, Classical.choice inferInstance)
    apply le_iSup_of_le x
    have h := oneSlice_two_array (F := F) x
    simp only [x, threeCoordinates_symm_zero, threeCoordinates_symm_one] at h
    rw [h]
  · apply iSup_le
    intro x
    apply le_iSup_of_le (x 1)
    apply le_iSup_of_le (x 0)
    rw [oneSlice_two_array]

theorem oneSlice_zero_array (x : ∀ i, V i) :
    (Linear.arraySlice (x 1, x 2)).comp
      (Linear.arrayTranspose.toLinearMap.comp toArray.toLinearMap) = oneSlice (F := F) 0 x := by
  apply LinearMap.ext
  intro T
  funext a
  simp only [LinearMap.comp_apply, Linear.arraySlice, LinearMap.coe_mk, AddHom.coe_mk,
    LinearEquiv.coe_coe, Linear.arrayTranspose, toArray_apply, oneSlice_apply]
  change T ((threeCoordinates V).symm (a, x 1, x 2)) = T (Function.update x 0 a)
  apply congrArg T
  apply (threeCoordinates V).injective
  simp only [Equiv.apply_symm_apply, threeCoordinates_apply, Function.update_self,
    Function.update_of_ne (show (1 : Fin 3) ≠ 0 by omega),
    Function.update_of_ne (show (2 : Fin 3) ≠ 0 by omega)]

theorem oneSlice_one_array (x : ∀ i, V i) :
    (Linear.arraySlice (x 2)).comp (Linear.arrayTranspose.toLinearMap.comp
      ((Linear.arraySlice (x 0)).comp toArray.toLinearMap)) = oneSlice (F := F) 1 x := by
  apply LinearMap.ext
  intro T
  funext a
  simp only [LinearMap.comp_apply, Linear.arraySlice, LinearMap.coe_mk, AddHom.coe_mk,
    LinearEquiv.coe_coe, Linear.arrayTranspose, toArray_apply, oneSlice_apply]
  change T ((threeCoordinates V).symm (x 0, a, x 2)) = T (Function.update x 1 a)
  apply congrArg T
  apply (threeCoordinates V).injective
  simp only [Equiv.apply_symm_apply, threeCoordinates_apply, Function.update_self,
    Function.update_of_ne (show (0 : Fin 3) ≠ 1 by omega),
    Function.update_of_ne (show (2 : Fin 3) ≠ 1 by omega)]

theorem array_oneSupport_zero [Nonempty (V 0)] (S : Submodule F (Tensor F (Fin 3) V)) :
    Linear.firstArraySupport (arraySpace S) = oneSupportAt S 0 := by
  rw [Linear.firstArraySupport_eq_transpose]
  simp only [Linear.arraySupport, arraySpace, oneSupportAt, ← Submodule.map_comp]
  apply le_antisymm
  · apply iSup_le
    intro p
    let x := (threeCoordinates V).symm (Classical.choice inferInstance, p.1, p.2)
    apply le_iSup_of_le x
    have h := oneSlice_zero_array (F := F) x
    simp only [x, threeCoordinates_symm_one, threeCoordinates_symm_two] at h
    rw [h]
  · apply iSup_le
    intro x
    apply le_iSup_of_le (x 1, x 2)
    rw [oneSlice_zero_array]

theorem array_oneSupport_one [Nonempty (V 1)] (S : Submodule F (Tensor F (Fin 3) V)) :
    Linear.secondArraySupport (arraySpace S) = oneSupportAt S 1 := by
  simp only [Linear.secondArraySupport, Linear.arraySupport, arraySpace, oneSupportAt,
    Submodule.map_iSup, ← Submodule.map_comp]
  apply le_antisymm
  · apply iSup_le
    intro c
    apply iSup_le
    intro a
    let x := (threeCoordinates V).symm (a, Classical.choice inferInstance, c)
    apply le_iSup_of_le x
    have h := oneSlice_one_array (F := F) x
    simp only [x, threeCoordinates_symm_zero, threeCoordinates_symm_two] at h
    rw [h]
  · apply iSup_le
    intro x
    apply le_iSup_of_le (x 2)
    apply le_iSup_of_le (x 0)
    rw [oneSlice_one_array]

theorem large_oneSupport_bound [∀ i, Fintype (V i)] [∀ i, Nonempty (V i)]
    (S : Submodule F (Tensor F (Fin 3) V)) {n s : ℕ}
    (h₀ : Module.finrank F (oneSupportAt S 0) ≤ n)
    (h₁ : Module.finrank F (oneSupportAt S 1) ≤ n) (hs : 2 ≤ s) (hsn : s ≤ n)
    (h₂ : n + s ≤ Module.finrank F (oneSupportAt S 2))
    (hP : Module.finrank F (oppositeSupportAt S 0) ≤ n ^ 2 + s)
    (hQ : Module.finrank F (oppositeSupportAt S 1) ≤ n ^ 2 + s) :
    Module.finrank F S ≤ n ^ 3 + s * (s - 1) := by
  have h := Linear.support_lemma_array (n := n) (s := s) (arraySpace S)
  rw [array_oneSupport_zero, array_oneSupport_one, array_oneSupport_two,
    finrank_array_opposite_zero, finrank_array_opposite_one, finrank_arraySpace] at h
  exact h h₀ h₁ hs hsn h₂ hP hQ

theorem large_oneSupport_bound_at [∀ i, Fintype (V i)] [∀ i, Nonempty (V i)]
    (S : Submodule F (Tensor F (Fin 3) V)) {n s : ℕ} (i j k : Fin 3)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hⱼ : Module.finrank F (oneSupportAt S j) ≤ n)
    (hₖ : Module.finrank F (oneSupportAt S k) ≤ n) (hs : 2 ≤ s) (hsn : s ≤ n)
    (hᵢ : n + s ≤ Module.finrank F (oneSupportAt S i))
    (hP : Module.finrank F (oppositeSupportAt S j) ≤ n ^ 2 + s)
    (hQ : Module.finrank F (oppositeSupportAt S k) ≤ n ^ 2 + s) :
    Module.finrank F S ≤ n ^ 3 + s * (s - 1) := by
  let σ : Fin 3 → Fin 3 := ![j, k, i]
  have hσ : Function.Injective σ := by
    intro a b h
    have ha : a = 0 ∨ a = 1 ∨ a = 2 := by omega
    have hb : b = 0 ∨ b = 1 ∨ b = 2 := by omega
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
    · rfl
    · exact (hjk h).elim
    · exact (hij h.symm).elim
    · exact (hjk h.symm).elim
    · rfl
    · exact (hik h.symm).elim
    · exact (hij h).elim
    · exact (hik h).elim
    · rfl
  let π : Fin 3 ≃ Fin 3 := Equiv.ofBijective σ ⟨hσ, Finite.surjective_of_injective hσ⟩
  let S' := S.map (reorder π.symm).toLinearMap
  have h : Module.finrank F S' ≤ n ^ 3 + s * (s - 1) := by
    apply large_oneSupport_bound (n := n) (s := s) S'
    · change Module.finrank F (oneSupportAt (S.map (reorder π.symm).toLinearMap) 0) ≤ n
      rw [oneSupportAt_reorder]
      change Module.finrank F (oneSupportAt S j) ≤ n
      exact hⱼ
    · change Module.finrank F (oneSupportAt (S.map (reorder π.symm).toLinearMap) 1) ≤ n
      rw [oneSupportAt_reorder]
      change Module.finrank F (oneSupportAt S k) ≤ n
      exact hₖ
    · exact hs
    · exact hsn
    · change n + s ≤ Module.finrank F (oneSupportAt (S.map (reorder π.symm).toLinearMap) 2)
      rw [oneSupportAt_reorder]
      change n + s ≤ Module.finrank F (oneSupportAt S i)
      exact hᵢ
    · change Module.finrank F (oppositeSupportAt (S.map (reorder π.symm).toLinearMap) 0) ≤ n ^ 2 + s
      rw [finrank_oppositeSupportAt_reorder]
      change Module.finrank F (oppositeSupportAt S j) ≤ n ^ 2 + s
      exact hP
    · change Module.finrank F (oppositeSupportAt (S.map (reorder π.symm).toLinearMap) 1) ≤ n ^ 2 + s
      rw [finrank_oppositeSupportAt_reorder]
      change Module.finrank F (oppositeSupportAt S k) ≤ n ^ 2 + s
      exact hQ
  simpa only [S', (reorder π.symm).finrank_map_eq] using h

end Lemmata.Centroid.Tensor
