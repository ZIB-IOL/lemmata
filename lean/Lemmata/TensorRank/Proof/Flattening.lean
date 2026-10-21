module

public import Lemmata.TensorRank.Def.Flattening
public import Lemmata.TensorRank.Proof.Basic

@[expose] public section

set_option autoImplicit false

open scoped BigOperators
open Classical

namespace Lemmata.TensorRank.Tensor

universe u v w z

variable {F : Type u} [Field F] {I : Type v}
variable {V : I → Type w}

@[simp] theorem joinCut_mem (S : Finset I) (a : CutRow V S) (b : CutColumn V S)
    {i : I} (hi : i ∈ S) : joinCut S a b i = a ⟨i, hi⟩ := by
  simp [joinCut, hi]

@[simp] theorem joinCut_not_mem (S : Finset I) (a : CutRow V S) (b : CutColumn V S)
    {i : I} (hi : i ∉ S) : joinCut S a b i = b ⟨i, hi⟩ := by
  simp [joinCut, hi]

variable [Fintype I]

theorem pure_joinCut (v : ∀ i, V i → F) (S : Finset I)
    (a : CutRow V S) (b : CutColumn V S) :
    pure v (joinCut S a b) =
      (∏ i : {i // i ∈ S}, v i.val (a i)) *
        ∏ i : {i // i ∉ S}, v i.val (b i) := by
  classical
  rw [pure]
  let e := Equiv.sumCompl (fun i => i ∈ S)
  rw [← e.prod_comp, Fintype.prod_sum_type]
  congr 1 <;> apply Finset.prod_congr rfl <;> intro i _ <;> simp [e, i.property]

variable [∀ i, Fintype (V i)]

theorem RankLE.flatRank_le {T : Tensor F I V} {r : ℕ} (hT : RankLE T r)
    (S : Finset I) : flatRank T S ≤ r := by
  classical
  obtain ⟨c, v, rfl⟩ := hT
  let A : Matrix (CutRow V S) (Fin r) F :=
    fun a j => c j * ∏ i : {i // i ∈ S}, v j i.val (a i)
  let B : Matrix (Fin r) (CutColumn V S) F :=
    fun j b => ∏ i : {i // i ∉ S}, v j i.val (b i)
  have h : flatten (fun x => ∑ j, c j * pure (v j) x) S = A * B := by
    funext a b
    simp only [flatten, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [pure_joinCut]
    simp only [A, B, mul_assoc]
  change (flatten _ S).rank ≤ r
  rw [h]
  exact (Matrix.rank_mul_le_left A B).trans (by simpa using Matrix.rank_le_card_width A)

theorem flatRank_le_rank (T : Tensor F I V) (S : Finset I) : flatRank T S ≤ rank T :=
  (rankLE_rank T).flatRank_le S

theorem card_le_rank_of_identity {J : Type z} [Fintype J] [DecidableEq J]
    (T : Tensor F I V) (S : Finset I) (a : J → CutRow V S) (b : J → CutColumn V S)
    (h : (flatten T S).submatrix a b = 1) : Fintype.card J ≤ rank T := by
  classical
  have hm := Matrix.rank_submatrix_le (flatten T S) a b
  rw [h, Matrix.rank_one] at hm
  exact hm.trans (flatRank_le_rank T S)

omit [Fintype I] [∀ i, Fintype (V i)] in
theorem power_identity_minor {J : Type z} [Fintype J] [DecidableEq J]
    (T : Tensor F I V) (S : Finset I) (a : J → CutRow V S) (b : J → CutColumn V S)
    (h : (flatten T S).submatrix a b = 1) (q : ℕ) :
    (flatten (power T q) S).submatrix
      (fun x : Fin q → J => fun i j => a (x j) i)
      (fun x : Fin q → J => fun i j => b (x j) i) = 1 := by
  classical
  funext x y
  change (∏ j, T (fun i =>
    joinCut (V := fun i => Fin q → V i) S
      (fun i j => a (x j) i) (fun i j => b (y j) i) i j)) =
      if x = y then 1 else 0
  calc
    _ = ∏ j, (if x j = y j then (1 : F) else 0) := by
      apply Finset.prod_congr rfl
      intro j _
      have he : (fun i =>
          joinCut (V := fun i => Fin q → V i) S
            (fun i j => a (x j) i) (fun i j => b (y j) i) i j) =
          joinCut S (a (x j)) (b (y j)) := by
        funext i
        by_cases hi : i ∈ S <;> simp [joinCut, hi]
      rw [he]
      simpa only [flatten, Matrix.submatrix_apply, Matrix.one_apply] using
        congrFun (congrFun h (x j)) (y j)
    _ = _ := by simp only [Fintype.prod_boole, ← funext_iff]

theorem card_pow_le_rank_of_identity {J : Type z} [Fintype J] [DecidableEq J]
    (T : Tensor F I V) (S : Finset I) (a : J → CutRow V S) (b : J → CutColumn V S)
    (h : (flatten T S).submatrix a b = 1) (q : ℕ) :
    Fintype.card J ^ q ≤ rank (power T q) := by
  simpa using card_le_rank_of_identity (J := Fin q → J) (power T q) S _ _
    (power_identity_minor T S a b h q)

theorem card_le_asymptoticRank_of_identity {J : Type z} [Fintype J] [DecidableEq J]
    (T : Tensor F I V) (S : Finset I) (a : J → CutRow V S) (b : J → CutColumn V S)
    (h : (flatten T S).submatrix a b = 1) :
    (Fintype.card J : ℝ) ≤ asymptoticRank T := by
  apply le_ciInf
  intro q
  have hq := card_pow_le_rank_of_identity T S a b h (q + 1)
  have hp : (0 : ℝ) < q + 1 := by positivity
  have hq' : (Fintype.card J : ℝ) ^ (q + 1) ≤ (rank (power T (q + 1)) : ℝ) := by
    exact_mod_cast hq
  have hr := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ (Fintype.card J : ℝ) ^ (q + 1))
    hq' (inv_nonneg.mpr hp.le)
  have he : ((Fintype.card J : ℝ) ^ (q + 1)) ^ ((q + 1 : ℝ)⁻¹) = Fintype.card J := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
    simp only [Nat.cast_add, Nat.cast_one, mul_inv_cancel₀ hp.ne', Real.rpow_one]
  rw [he] at hr
  exact hr

end Lemmata.TensorRank.Tensor
