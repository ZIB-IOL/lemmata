module

public import Lemmata.Centroid.Proof.Construction.Frames
public import Mathlib.Logic.Equiv.Fin.Rotate

@[expose] public section

open scoped BigOperators
open Classical

namespace Lemmata.Centroid.Construction.Circuit

open Module

noncomputable section

variable {F : Type*} [Field F]

def denominator (q : ℕ) : Polynomial F :=
  1 + Polynomial.C ((q + 1 : ℕ) : F) * Polynomial.X

def activeM (q : ℕ) : Matrix (Fin (q + 1)) (Fin (q + 1)) (Polynomial F) :=
  fun i j => Polynomial.C (if i = j then 1 else 0) + Polynomial.X

def activeH (q : ℕ) : Matrix (Fin (q + 1)) (Fin (q + 1)) (Polynomial F) :=
  fun i j => denominator q * Polynomial.C (if i = finRotate (q + 1) j then 1 else 0) -
    Polynomial.X

theorem rotate_ne (q : ℕ) (hq : 0 < q) (j : Fin (q + 1)) :
    finRotate (q + 1) j ≠ j := by
  by_cases hj : j = Fin.last q
  · subst j
    rw [finRotate_last]
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_zero, Fin.val_last] at hv
    omega
  · intro h
    have hv := coe_finRotate_of_ne_last hj
    rw [h] at hv
    omega

def normalizedEntry (q : ℕ) (i j : Fin (q + 1)) : Polynomial F :=
  Polynomial.C ((if i = finRotate (q + 1) j then 1 else 0) - (if i = j then 1 else 0)) +
    Polynomial.X * Polynomial.C
      (((q + 1 : ℕ) : F) * (if i = finRotate (q + 1) j then 1 else 0) - 1)

theorem active_product (q : ℕ) (hq : 0 < q) (i j : Fin (q + 1)) :
    activeM (F := F) q i j * activeH q i j = Polynomial.X * normalizedEntry q i j := by
  have hn := rotate_ne q hq j
  unfold activeM activeH normalizedEntry denominator
  by_cases hij : i = j <;> by_cases hir : i = finRotate (q + 1) j
  · exact False.elim (hn (hir.symm.trans hij))
  · simp only [ite_eq_left hij, ite_eq_right hir, Polynomial.C_1, Polynomial.C_0,
      zero_sub, mul_zero, zero_sub, Polynomial.C_neg]
    ring
  · simp only [ite_eq_right hij, ite_eq_left hir, Polynomial.C_1, Polynomial.C_0,
      sub_zero, mul_one]
    rw [Polynomial.C_sub, Polynomial.C_1]
    ring
  · simp only [ite_eq_right hij, ite_eq_right hir, Polynomial.C_0, sub_self, mul_zero,
      zero_sub, Polynomial.C_neg, Polynomial.C_1]
    ring

def pathMatrix (q : ℕ) : Matrix (Fin q) (Fin q) F :=
  fun i j => (if i.val = j.val + 1 then 1 else 0) - (if i = j then 1 else 0)

theorem pathMatrix_lowerTriangular (q : ℕ) : (pathMatrix (F := F) q).IsLowerTriangular := by
  intro i j hij
  change i < j at hij
  have hne : i ≠ j := ne_of_lt hij
  have hs : i.val ≠ j.val + 1 := by have := Fin.lt_def.mp hij; omega
  simp [pathMatrix, hne, hs]

theorem pathMatrix_det (q : ℕ) : (pathMatrix (F := F) q).det = (-1) ^ q := by
  rw [Matrix.det_of_isLowerTriangular _ (pathMatrix_lowerTriangular q)]
  have hd (i : Fin q) : pathMatrix (F := F) q i i = -1 := by
    simp [pathMatrix]
  simp [hd]

def normalizedPrincipal (q : ℕ) : Matrix (Fin q) (Fin q) (Polynomial F) :=
  fun i j => normalizedEntry q i.castSucc j.castSucc

theorem normalizedPrincipal_at_zero (q : ℕ) :
    (Polynomial.evalRingHom (0 : F)).mapMatrix (normalizedPrincipal q) = pathMatrix q := by
  ext i j
  have hr : finRotate (q + 1) j.castSucc = j.succ := finRotate_of_lt j.isLt
  have hs : i.castSucc = j.succ ↔ i.val = j.val + 1 := by simp [Fin.ext_iff]
  simp [normalizedPrincipal, normalizedEntry, Polynomial.coe_evalRingHom,
    hr, hs, pathMatrix]
  split_ifs <;> simp

theorem normalizedPrincipal_ratFunc_det_ne_zero (q : ℕ) :
    ((algebraMap (Polynomial F) (RatFunc F)).mapMatrix (normalizedPrincipal q)).det ≠ 0 := by
  have hdet : (normalizedPrincipal (F := F) q).det ≠ 0 := by
    intro hz
    have he := congrArg (Polynomial.evalRingHom (0 : F)) hz
    rw [RingHom.map_det, normalizedPrincipal_at_zero, pathMatrix_det, map_zero] at he
    exact (pow_ne_zero q (neg_ne_zero.mpr one_ne_zero)) he
  rw [← RingHom.map_det]
  exact RatFunc.algebraMap_ne_zero hdet

def activePrincipal (q : ℕ) : Matrix (Fin q) (Fin q) (RatFunc F) :=
  fun i j => algebraMap (Polynomial F) (RatFunc F)
    (activeM (F := F) q i.castSucc j.castSucc * activeH q i.castSucc j.castSucc)

theorem activePrincipal_det_ne_zero (q : ℕ) (hq : 0 < q) :
    (activePrincipal (F := F) q).det ≠ 0 := by
  have he : activePrincipal (F := F) q = (RatFunc.X : RatFunc F) •
      (algebraMap (Polynomial F) (RatFunc F)).mapMatrix (normalizedPrincipal q) := by
    ext i j
    change algebraMap (Polynomial F) (RatFunc F)
      (activeM q i.castSucc j.castSucc * activeH q i.castSucc j.castSucc) = _
    rw [active_product q hq, map_mul]
    rfl
  rw [he, Matrix.det_smul]
  exact mul_ne_zero (pow_ne_zero _ RatFunc.X_ne_zero) (normalizedPrincipal_ratFunc_det_ne_zero q)

theorem active_columns_independent (q : ℕ) (hq : 0 < q) :
    LinearIndependent (RatFunc F)
      (fun j : Fin q => fun i : Fin (q + 1) => algebraMap (Polynomial F) (RatFunc F)
        (activeM q i j.castSucc * activeH q i j.castSucc)) := by
  let L : (Fin (q + 1) → RatFunc F) →ₗ[RatFunc F] (Fin q → RatFunc F) := {
    toFun := fun f i => f i.castSucc
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  apply LinearIndependent.of_comp L
  exact Matrix.linearIndependent_cols_of_isUnit
    ((Matrix.isUnit_iff_isUnit_det _).mpr
      (isUnit_iff_ne_zero.mpr (activePrincipal_det_ne_zero q hq)))

def eta (q : ℕ) (j : Fin (q + 1)) : Polynomial F :=
  1 + (if j = 0 then Polynomial.X - 1 else 0) +
    (if j = Fin.last q then -Polynomial.X - Polynomial.C (q : F) else 0)

theorem eta_sum (q : ℕ) : (∑ j, eta (F := F) q j) = 0 := by
  simp [eta, Finset.sum_add_distrib]
  ring

theorem denominator_ne_zero (q : ℕ) : denominator (F := F) q ≠ 0 := by
  intro h
  have hc := congrArg (fun p : Polynomial F => p.coeff 0) h
  simp [denominator] at hc

theorem eta_ne_zero (q : ℕ) (hq : 0 < q) (j : Fin (q + 1)) : eta (F := F) q j ≠ 0 := by
  have hlast : (0 : Fin (q + 1)) ≠ Fin.last q := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_zero, Fin.val_last] at hv
    omega
  by_cases hj0 : j = 0
  · subst j
    intro h
    have hc := congrArg (fun p : Polynomial F => p.coeff 1) h
    simp [eta, hlast] at hc
  · by_cases hjl : j = Fin.last q
    · intro h
      have hc := congrArg (fun p : Polynomial F => p.coeff 1) h
      simp [eta, hjl, Nat.ne_of_gt hq, Polynomial.coeff_one] at hc
    · intro h
      have hc := congrArg (fun p : Polynomial F => p.coeff 0) h
      simp [eta, hj0, hjl] at hc

theorem activeM_ne_zero (q : ℕ) (i j : Fin (q + 1)) : activeM (F := F) q i j ≠ 0 := by
  intro h
  have hc := congrArg (fun p : Polynomial F => p.coeff 1) h
  by_cases hij : i = j <;> simp [activeM, hij, Polynomial.coeff_one] at hc

theorem activeH_ne_zero (q : ℕ) (i j : Fin (q + 1)) : activeH (F := F) q i j ≠ 0 := by
  by_cases hij : i = finRotate (q + 1) j
  · intro h
    have hc := congrArg (fun p : Polynomial F => p.coeff 0) h
    simp [activeH, denominator, hij] at hc
  · intro h
    have hc := congrArg (fun p : Polynomial F => p.coeff 1) h
    simp only [activeH, ite_eq_right hij, Polynomial.C_0, mul_zero, zero_sub,
      Polynomial.coeff_neg, Polynomial.coeff_X, Polynomial.coeff_zero] at hc
    exact neg_ne_zero.mpr one_ne_zero hc

def matrixM (q ν : ℕ) : Matrix (Fin (q + 1) ⊕ Fin ν) (Fin (q + 1) ⊕ Fin ν) (Polynomial F) :=
  fun i j => match i, j with
    | Sum.inl i, Sum.inl j => activeM q i j
    | Sum.inl _, Sum.inr _ => Polynomial.X
    | Sum.inr _, Sum.inl _ => 1
    | Sum.inr i, Sum.inr j => Polynomial.C (if i = j then 1 else 0) + Polynomial.X

def matrixH (q ν : ℕ) : Matrix (Fin (q + 1) ⊕ Fin ν) (Fin (q + 1) ⊕ Fin ν) (Polynomial F) :=
  fun i j => match i, j with
    | Sum.inl i, Sum.inl j => activeH q i j
    | Sum.inl _, Sum.inr _ => denominator q * Polynomial.X
    | Sum.inr _, Sum.inl j => denominator q * eta q j
    | Sum.inr i, Sum.inr j =>
      denominator q * (Polynomial.C (if i = j then 1 else 0) + Polynomial.X)

theorem matrixM_ne_zero (q ν : ℕ) (i j : Fin (q + 1) ⊕ Fin ν) :
    matrixM (F := F) q ν i j ≠ 0 := by
  cases i with
  | inl i =>
    cases j with
    | inl j => exact activeM_ne_zero q i j
    | inr j => exact Polynomial.X_ne_zero
  | inr i =>
    cases j with
    | inl j => exact one_ne_zero
    | inr j =>
      intro h
      have hc := congrArg (fun p : Polynomial F => p.coeff 1) h
      by_cases hij : i = j <;> simp [matrixM, hij, Polynomial.coeff_one] at hc

theorem matrixH_ne_zero (q ν : ℕ) (hq : 0 < q) (i j : Fin (q + 1) ⊕ Fin ν) :
    matrixH (F := F) q ν i j ≠ 0 := by
  cases i with
  | inl i =>
    cases j with
    | inl j => exact activeH_ne_zero q i j
    | inr j => exact mul_ne_zero (denominator_ne_zero q) Polynomial.X_ne_zero
  | inr i =>
    cases j with
    | inl j => exact mul_ne_zero (denominator_ne_zero q) (eta_ne_zero q hq j)
    | inr j =>
      apply mul_ne_zero (denominator_ne_zero q)
      intro h
      have hc := congrArg (fun p : Polynomial F => p.coeff 1) h
      by_cases hij : i = j <;> simp [hij, Polynomial.coeff_one] at hc

theorem active_hadamard_sum (q ν : ℕ) (hq : 0 < q) (i : Fin (q + 1) ⊕ Fin ν) :
    (∑ j : Fin (q + 1), matrixM (F := F) q ν i (Sum.inl j) *
      matrixH q ν i (Sum.inl j)) = 0 := by
  cases i with
  | inl i =>
    have hp : (∑ j : Fin (q + 1), if i = finRotate (q + 1) j then (1 : F) else 0) = 1 := by
      rw [Equiv.sum_comp (finRotate (q + 1)) (fun j => if i = j then (1 : F) else 0)]
      simp
    have ha : (∑ j : Fin (q + 1),
        ((if i = finRotate (q + 1) j then (1 : F) else 0) -
          (if i = j then 1 else 0))) = 0 := by
      rw [Finset.sum_sub_distrib, hp]
      simp
    have hb : (∑ j : Fin (q + 1), (((q + 1 : ℕ) : F) *
        (if i = finRotate (q + 1) j then 1 else 0) - 1)) = 0 := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hp]
      simp
    have hn : (∑ j, normalizedEntry (F := F) q i j) = 0 := by
      unfold normalizedEntry
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← map_sum, ← map_sum, ha, hb]
      simp
    simp only [matrixM, matrixH]
    simp_rw [active_product q hq]
    rw [← Finset.mul_sum, hn, mul_zero]
  | inr i =>
    simp only [matrixM, matrixH, one_mul]
    rw [← Finset.mul_sum, eta_sum, mul_zero]

theorem ratFunc_det_ne_zero_of_eval {J : Type*} [Fintype J] [DecidableEq J]
    (P : Matrix J J (Polynomial F))
    (hP : ((Polynomial.evalRingHom (0 : F)).mapMatrix P).det ≠ 0) :
    ((algebraMap (Polynomial F) (RatFunc F)).mapMatrix P).det ≠ 0 := by
  have hd : P.det ≠ 0 := by
    intro h
    apply hP
    rw [← RingHom.map_det, h, map_zero]
  rw [← RingHom.map_det]
  exact RatFunc.algebraMap_ne_zero hd

theorem matrixM_ratFunc_det_ne_zero (q ν : ℕ) :
    ((algebraMap (Polynomial F) (RatFunc F)).mapMatrix (matrixM q ν)).det ≠ 0 := by
  let B : Matrix (Fin ν) (Fin (q + 1)) F := fun _ _ => 1
  have he : (Polynomial.evalRingHom (0 : F)).mapMatrix (matrixM q ν) =
      Matrix.fromBlocks 1 0 B 1 := by
    ext i j
    cases i <;> cases j <;>
      simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.one_apply, Matrix.zero_apply]
    all_goals simp [matrixM, activeM, Polynomial.coe_evalRingHom, B]
    all_goals split_ifs <;> simp
  apply ratFunc_det_ne_zero_of_eval
  rw [he, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, Matrix.det_one, one_mul]
  exact one_ne_zero

theorem matrixH_ratFunc_det_ne_zero (q ν : ℕ) :
    ((algebraMap (Polynomial F) (RatFunc F)).mapMatrix (matrixH q ν)).det ≠ 0 := by
  let P : Matrix (Fin (q + 1)) (Fin (q + 1)) F :=
    fun i j => if i = finRotate (q + 1) j then 1 else 0
  let B : Matrix (Fin ν) (Fin (q + 1)) F := fun _ j => (eta (F := F) q j).eval 0
  have hp : P = (1 : Matrix (Fin (q + 1)) (Fin (q + 1)) F).submatrix id (finRotate (q + 1)) := by
    ext i j
    rfl
  have hdet : P.det ≠ 0 := by
    rw [hp, Matrix.det_permute', Matrix.det_one, mul_one]
    exact (Units.map (Int.castRingHom F).toMonoidHom (Equiv.Perm.sign (finRotate (q + 1)))).ne_zero
  have he : (Polynomial.evalRingHom (0 : F)).mapMatrix (matrixH q ν) =
      Matrix.fromBlocks P 0 B 1 := by
    ext i j
    cases i <;> cases j <;>
      simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.one_apply, Matrix.zero_apply]
    all_goals simp [matrixH, activeH, denominator, Polynomial.coe_evalRingHom, P, B]
    all_goals split_ifs <;> simp
  apply ratFunc_det_ne_zero_of_eval
  rw [he, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, mul_one]
  exact hdet

def hadamardColumn (q ν : ℕ) (j : Fin (q + 1)) :
    (Fin (q + 1) ⊕ Fin ν) → RatFunc F :=
  fun i => algebraMap (Polynomial F) (RatFunc F)
    (matrixM q ν i (Sum.inl j) * matrixH q ν i (Sum.inl j))

theorem hadamardColumn_sum (q ν : ℕ) (hq : 0 < q) :
    (∑ j, hadamardColumn (F := F) q ν j) = 0 := by
  ext i
  simp only [Finset.sum_apply, hadamardColumn, Pi.zero_apply]
  rw [← map_sum, active_hadamard_sum q ν hq i, map_zero]

theorem hadamardColumn_independent (q ν : ℕ) (hq : 0 < q) :
    LinearIndependent (RatFunc F) (fun j : Fin q => hadamardColumn (F := F) q ν j.castSucc) := by
  let L : ((Fin (q + 1) ⊕ Fin ν) → RatFunc F) →ₗ[RatFunc F] (Fin (q + 1) → RatFunc F) := {
    toFun := fun f i => f (Sum.inl i)
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  apply LinearIndependent.of_comp L
  exact active_columns_independent (F := F) q hq

theorem exists_normalizing_equiv {K J V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (v w : J → V)
    (hv : LinearIndependent K v) (hw : LinearIndependent K w) :
    ∃ e : V ≃ₗ[K] V, ∀ j, e (v j) = w j := by
  let f := (Basis.span hv).equiv (Basis.span hw) (Equiv.refl J)
  obtain ⟨e, he⟩ := Submodule.exists_linearEquiv_restrict_eq f
  refine ⟨e, fun j => ?_⟩
  have hh := he ((Basis.span hv) j)
  simpa only [f, Basis.equiv_apply, Equiv.refl_apply, Basis.coe_span_apply] using hh.symm

theorem exists_circuit_normalizer (q ν : ℕ) (hq : 0 < q) :
    ∃ e : ((Fin (q + 1) ⊕ Fin ν) → RatFunc F) ≃ₗ[RatFunc F]
        ((Fin (q + 1) ⊕ Fin ν) → RatFunc F),
      ∀ j : Fin q, e (hadamardColumn (F := F) q ν j.castSucc) = Pi.single (Sum.inl j.castSucc) 1 := by
  apply exists_normalizing_equiv _ _ (hadamardColumn_independent (F := F) q ν hq)
  exact (Pi.linearIndependent_single_one (Fin (q + 1) ⊕ Fin ν) (RatFunc F)).comp
    (fun j : Fin q => Sum.inl j.castSucc) (by
      intro i j h
      have h' : i.castSucc = j.castSucc := Sum.inl.inj h
      exact Fin.ext (congrArg (fun k : Fin (q + 1) => k.val) h'))

end

end Lemmata.Centroid.Construction.Circuit
