module

public import Lemmata.Centroid.Proof.Linear.Expansion
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.LinearAlgebra.Finsupp.Pi
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Algebra.MonoidAlgebra.Module

@[expose] public section

open scoped BigOperators Matrix
open Classical

noncomputable section

namespace Lemmata.Centroid.Linear

variable {F B C σ : Type*} [Field F] [Fintype B] [Fintype C]

def polynomialFunctionsEquiv : ModulePolynomial F B σ ≃ₗ[F] (B → MvPolynomial σ F) :=
  ((Finsupp.curryLinearEquiv F).trans
    (Finsupp.mapRange.linearEquiv (AddMonoidAlgebra.coeffLinearEquiv F).symm)).trans
      (Finsupp.linearEquivFunOnFinite F _ B)

theorem polynomialFunctionsEquiv_coeff (p : ModulePolynomial F B σ) (b : B) (m : σ →₀ ℕ) :
    (polynomialFunctionsEquiv p b).coeff m = p (b, m) := rfl

def polynomialMap (g : (B → F) →ₗ[F] (C → F)) :
    (B → MvPolynomial σ F) →ₗ[MvPolynomial σ F] (C → MvPolynomial σ F) :=
  ((LinearMap.toMatrix' g).map MvPolynomial.C).mulVecLin

omit [Fintype C] in
theorem polynomialMap_coeff (g : (B → F) →ₗ[F] (C → F))
    (p : B → MvPolynomial σ F) (m : σ →₀ ℕ) (c : C) :
    (polynomialMap g p c).coeff m = g (fun b => (p b).coeff m) c := by
  change (∑ b, MvPolynomial.C (LinearMap.toMatrix' g c b) * p b).coeff m = _
  rw [MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_C_mul]
  exact congrFun (LinearMap.toMatrix'_mulVec g (fun b => (p b).coeff m)) c

omit [Fintype C] in
theorem polynomialMap_injective (g : (B → F) →ₗ[F] (C → F)) (hg : Function.Injective g) :
    Function.Injective (polynomialMap (σ := σ) g) := by
  intro p q h
  funext b
  apply MvPolynomial.ext
  intro m
  have he : g (fun b => (p b).coeff m) = g (fun b => (q b).coeff m) := by
    funext c
    simpa only [← polynomialMap_coeff] using congrArg (fun r : C → MvPolynomial σ F =>
      (r c).coeff m) h
  exact congrFun (hg he) b

omit [Fintype C] in
theorem polynomialFunctionsEquiv_single (b : B) (m : σ →₀ ℕ) (c : F) (b' : B) :
    polynomialFunctionsEquiv (Finsupp.single (b, m) c) b' =
      if b = b' then MvPolynomial.monomial m c else 0 := by
  classical
  apply MvPolynomial.ext
  intro n
  rw [polynomialFunctionsEquiv_coeff]
  by_cases h : b = b'
  · subst b'
    simp [Finsupp.single_apply, MvPolynomial.coeff_monomial]
  · simp [h, Prod.mk.injEq]

omit [Fintype C] in
theorem polynomialFunctionsEquiv_variable (i : σ) (p : ModulePolynomial F B σ) :
    polynomialFunctionsEquiv (variableMultiplication i p) =
      fun b => MvPolynomial.X i * polynomialFunctionsEquiv p b := by
  classical
  funext b
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, Pi.add_apply, mul_add, hp, hq]
  | single a c =>
    rcases a with ⟨a, m⟩
    rw [variableMultiplication, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
    simp only [variableShift, polynomialFunctionsEquiv_single]
    by_cases h : a = b
    · simp only [h, ite_true, MvPolynomial.X, MvPolynomial.monomial_mul_monomial, one_mul]
      rw [add_comm]
    · simp [h]

theorem polynomialMap_comp {D : Type*} [Fintype D]
    (g : (B → F) →ₗ[F] (C → F)) (h : (C → F) →ₗ[F] (D → F))
    (p : B → MvPolynomial σ F) :
    polynomialMap h (polynomialMap g p) = polynomialMap (h.comp g) p := by
  funext d
  apply MvPolynomial.ext
  intro m
  simp only [polynomialMap_coeff, LinearMap.comp_apply]

omit [Fintype C] in
theorem polynomialMap_eq_zero_iff (g : (B → F) →ₗ[F] (C → F))
    (p : B → MvPolynomial σ F) :
    polynomialMap g p = 0 ↔ ∀ m, g (fun b => (p b).coeff m) = 0 := by
  constructor
  · intro h m
    funext c
    have he := congrArg (fun q : C → MvPolynomial σ F => (q c).coeff m) h
    simpa only [polynomialMap_coeff, Pi.zero_apply, AddMonoidAlgebra.coeff_zero,
      Finsupp.zero_apply] using he
  · intro h
    funext c
    apply MvPolynomial.ext
    intro m
    rw [polynomialMap_coeff, h m]
    rfl

section VariableExpansion

variable [Fintype σ]

def polynomialVariableExpansionMap (L : Submodule F (B → MvPolynomial σ F)) :
    (σ → L) →ₗ[F] (B → MvPolynomial σ F) where
  toFun v b := ∑ i, MvPolynomial.X i * (v i).val b
  map_add' v w := by
    funext b
    simp only [Pi.add_apply, Submodule.coe_add, mul_add, Finset.sum_add_distrib]
  map_smul' r v := by
    funext b
    simp only [Pi.smul_apply, Submodule.coe_smul_of_tower, RingHom.id_apply,
      Finset.smul_sum, mul_smul_comm]

def polynomialVariableExpansion (L : Submodule F (B → MvPolynomial σ F)) :
    Submodule F (B → MvPolynomial σ F) :=
  (polynomialVariableExpansionMap L).range

instance finite_polynomialVariableExpansion (L : Submodule F (B → MvPolynomial σ F))
    [FiniteDimensional F L] : FiniteDimensional F (polynomialVariableExpansion L) := by
  unfold polynomialVariableExpansion
  infer_instance

omit [Fintype C] in
theorem variableExpansion_polynomialFunctions_le (L : Submodule F (B → MvPolynomial σ F)) :
    (variableExpansion (L.map polynomialFunctionsEquiv.symm.toLinearMap)).map
      polynomialFunctionsEquiv.toLinearMap ≤ polynomialVariableExpansion L := by
  rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
  have hv (i : σ) : polynomialFunctionsEquiv (v i).val ∈ L := by
    obtain ⟨p, hp, he⟩ := (v i).property
    rw [← he, LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply]
    exact hp
  refine ⟨fun i => ⟨polynomialFunctionsEquiv (v i).val, hv i⟩, ?_⟩
  funext b
  change (∑ i, MvPolynomial.X i * polynomialFunctionsEquiv (v i).val b) =
    polynomialFunctionsEquiv (variableExpansionMap _ v) b
  simp only [variableExpansionMap, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, Submodule.subtype_apply, map_sum, polynomialFunctionsEquiv_variable,
    Finset.sum_apply]

omit [Fintype C] in
theorem polynomial_variable_expansion_bound
    (L : Submodule F (B → MvPolynomial σ F)) [FiniteDimensional F L]
    (h : ℕ) (hh : h ≤ Module.finrank F L) :
    Fintype.card σ * h ≤ Module.finrank F (polynomialVariableExpansion L) + h.choose 2 := by
  let : LinearOrder B := LinearOrder.lift' (Fintype.equivFin B) (Fintype.equivFin B).injective
  let : LinearOrder σ := LinearOrder.lift' (Fintype.equivFin σ) (Fintype.equivFin σ).injective
  let L' := L.map polynomialFunctionsEquiv.symm.toLinearMap
  have hd : Module.finrank F L' = Module.finrank F L := polynomialFunctionsEquiv.symm.finrank_map_eq L
  have hexp := variable_expansion_bound (MonomialOrder.lex : MonomialOrder σ) L' h (hd ▸ hh)
  have hle := Submodule.finrank_mono (variableExpansion_polynomialFunctions_le L)
  rw [polynomialFunctionsEquiv.finrank_map_eq] at hle
  exact hexp.trans (Nat.add_le_add_right hle _)

omit [Fintype C] in
theorem polynomial_variable_expansion_bound_fin {n : ℕ}
    (L : Submodule F (B → MvPolynomial (Fin n) F)) [FiniteDimensional F L]
    (h : ℕ) (hh : h ≤ Module.finrank F L) :
    n * h ≤ Module.finrank F (polynomialVariableExpansion L) + h.choose 2 := by
  simpa using polynomial_variable_expansion_bound L h hh

end VariableExpansion

theorem exists_polynomial_pencil_kernel [Fintype σ]
    (L : σ → ((B → F) →ₗ[F] (C → F))) (h : Fintype.card C < Fintype.card B) :
    ∃ p : B → MvPolynomial σ F, p ≠ 0 ∧
      ∑ i, polynomialMap (L i) (fun b => MvPolynomial.X i * p b) = 0 := by
  let M : Matrix C B (MvPolynomial σ F) :=
    fun c b => ∑ i, MvPolynomial.X i * MvPolynomial.C (LinearMap.toMatrix' (L i) c b)
  obtain ⟨p, hp, hMp⟩ := matrix_kernel_of_card_lt M h
  refine ⟨p, hp, ?_⟩
  funext c
  have he := congrFun hMp c
  change (∑ b, (∑ i, MvPolynomial.X i * MvPolynomial.C (LinearMap.toMatrix' (L i) c b)) * p b) = 0 at he
  simp only [Finset.sum_apply, Pi.zero_apply, polynomialMap, Matrix.mulVecLin_apply,
    Matrix.mulVec, dotProduct, Matrix.map_apply]
  change (∑ i, ∑ b, MvPolynomial.C (LinearMap.toMatrix' (L i) c b) * (MvPolynomial.X i * p b)) = 0
  simp only [Finset.sum_mul] at he
  rw [Finset.sum_comm] at he
  convert he using 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro b _
  ring

end Lemmata.Centroid.Linear
