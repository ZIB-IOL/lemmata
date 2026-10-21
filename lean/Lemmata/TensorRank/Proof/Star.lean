module

public import Lemmata.TensorRank.Def.Star
public import Lemmata.TensorRank.Proof.WeightedBound
public import Lemmata.TensorRank.Proof.Maps
public import Mathlib.Logic.Equiv.Option

@[expose] public section

set_option autoImplicit false

open scoped BigOperators
open Classical

namespace Lemmata.TensorRank

def weightedAssignment {k : ℕ} {d : Edge k → ℕ} (z : ∀ e, Fin (d e))
    (i : Fin k) : WeightedCoordinate d i := fun a => z a.val

theorem weightedAssignment_injective {k : ℕ} {d : Edge k → ℕ} :
    Function.Injective (weightedAssignment (d := d)) := by
  intro z w h
  funext e
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (show 0 < e.val.card by rw [e.prop]; decide)
  exact congrFun (congrFun h i) ⟨e, hi⟩

theorem weightedComplete_eq_sum {k : ℕ} (d : Edge k → ℕ) :
    weightedComplete d = ∑ z : ∀ e, Fin (d e),
      Tensor.pure (fun i x => if x = weightedAssignment z i then (1 : ℂ) else 0) := by
  funext x
  simp only [Finset.sum_apply, Tensor.pure, Fintype.prod_boole, ← funext_iff]
  by_cases hx : ∀ (e : Edge k) (i j : Fin k) (hi : i ∈ e.val) (hj : j ∈ e.val),
      x i ⟨e, hi⟩ = x j ⟨e, hj⟩
  · choose vertex hv using fun e : Edge k =>
      Finset.card_pos.mp (show 0 < e.val.card by rw [e.prop]; decide)
    let z : ∀ e, Fin (d e) := fun e => x (vertex e) ⟨e, hv e⟩
    have hz : x = weightedAssignment z := by
      funext i a
      exact hx a.val i (vertex a.val) a.prop (hv a.val)
    rw [show weightedComplete d x = 1 from ite_eq_left hx, hz]
    simp [weightedAssignment_injective.eq_iff]
  · have hn (z : ∀ e, Fin (d e)) : x ≠ weightedAssignment z := by
      intro h
      apply hx
      subst x
      intros
      rfl
    rw [show weightedComplete d x = 0 from ite_eq_right hx]
    simp [hn]

theorem localMap_weightedComplete {k : ℕ} {d : Edge k → ℕ} {W : Fin k → Type*}
    (A : ∀ i, W i → WeightedCoordinate d i → ℂ) :
    Tensor.localMap A (weightedComplete d) =
      fun x => ∑ z : ∀ e, Fin (d e), ∏ i, A i (x i) (weightedAssignment z i) := by
  rw [weightedComplete_eq_sum, Tensor.localMap_sum]
  simp_rw [Tensor.localMap_pure]
  funext x
  simp [Tensor.pure]

noncomputable def starLabelEquiv {k : ℕ} (c : Fin k) (n : ℕ) :
    (∀ e, Fin (starDimensions c n e)) ≃ WeightedCoordinate (starDimensions c n) c where
  toFun z a := z a.val
  invFun x e := if h : c ∈ e.val then x ⟨e, h⟩ else ⟨0, by simp [starDimensions, h]⟩
  left_inv z := by
    funext e
    change (if h : c ∈ e.val then z e else ⟨0, by simp [starDimensions, h]⟩) = z e
    split_ifs with h
    · rfl
    · apply Fin.ext
      have hz : (z e).val < 1 := by simpa [starDimensions, h] using (z e).isLt
      change 0 = (z e).val
      omega
  right_inv x := by funext a; simp [a.prop]

noncomputable def starCenterCoordinate {k : ℕ} (c : Fin k) (n : ℕ) :
    WeightedCoordinate (starDimensions c n) c ≃ (Neighbors c → Fin n) where
  toFun x j := Fin.cast (by simp [starDimensions, neighborIncident_val, edgeBetween])
    (x (neighborIncident c j))
  invFun x a := Fin.cast (by simp [starDimensions, a.prop]) (x ((neighborIncident c).symm a))
  left_inv x := by
    funext a
    obtain ⟨j, rfl⟩ := (neighborIncident c).surjective a
    apply Fin.ext
    simp only [Fin.cast]
    exact congrArg (fun a => (x a).val) ((neighborIncident c).apply_symm_apply _)
  right_inv x := by funext j; apply Fin.ext; simp [Fin.cast]

def starLeafValue {k : ℕ} (c : Fin k) (n : ℕ) (j : Neighbors c)
    (x : WeightedCoordinate (starDimensions c n) j.val) : Fin n :=
  Fin.cast (by simp [starDimensions, edgeBetween])
    (x ⟨edgeBetween c j.val j.prop, by simp [edgeBetween]⟩)

theorem starLeafValue_assignment {k : ℕ} (c : Fin k) (n : ℕ) (j : Neighbors c)
    (z : ∀ e, Fin (starDimensions c n e)) :
    starLeafValue c n j (weightedAssignment z j.val) =
      starCenterCoordinate c n (starLabelEquiv c n z) j := by
  apply Fin.ext
  rfl

def starReconstruct {k n : ℕ} (c : Fin k) (a : Fin n) (f : Neighbors c → Fin n) :
    Fin k → Fin n := fun i => if hi : i = c then a else f ⟨i, hi⟩

@[simp] theorem starReconstruct_self {k n : ℕ} (c : Fin k) (x : Fin k → Fin n) :
    starReconstruct c (x c) (fun j => x j.val) = x := by
  funext i
  simp only [starReconstruct]
  split_ifs with h
  · exact congrArg x h.symm
  · rfl

noncomputable def starKernel {k n : ℕ} (c : Fin k)
    (T : Tensor ℂ (Fin k) (fun _ => Fin n)) :
    ∀ i, Fin n → WeightedCoordinate (starDimensions c n) i → ℂ :=
  fun i y a => if hi : i = c then
    T (starReconstruct c y (starCenterCoordinate c n (hi ▸ a)))
  else if starLeafValue c n ⟨i, hi⟩ a = y then 1 else 0

@[simp] theorem starKernel_center {k n : ℕ} (c : Fin k)
    (T : Tensor ℂ (Fin k) (fun _ => Fin n)) (y : Fin n)
    (a : WeightedCoordinate (starDimensions c n) c) :
    starKernel c T c y a = T (starReconstruct c y (starCenterCoordinate c n a)) := by
  simp [starKernel]

@[simp] theorem starKernel_leaf {k n : ℕ} (c : Fin k)
    (T : Tensor ℂ (Fin k) (fun _ => Fin n)) (j : Neighbors c) (y : Fin n)
    (a : WeightedCoordinate (starDimensions c n) j.val) :
    starKernel c T j.val y a = if starLeafValue c n j a = y then 1 else 0 := by
  simp [starKernel, j.prop]

theorem localMap_star {k n : ℕ} (c : Fin k) (T : Tensor ℂ (Fin k) (fun _ => Fin n)) :
    Tensor.localMap (starKernel c T) (weightedComplete (starDimensions c n)) = T := by
  funext x
  rw [localMap_weightedComplete]
  let e := (starLabelEquiv c n).trans (starCenterCoordinate c n)
  have hp (z : ∀ a, Fin (starDimensions c n a)) :
      (∏ i, starKernel c T i (x i) (weightedAssignment z i)) =
      T (starReconstruct c (x c) (e z)) * if e z = (fun j => x j.val) then 1 else 0 := by
    calc
      _ = ∏ p : Option (Neighbors c), starKernel c T (Equiv.optionSubtypeNe c p)
          (x (Equiv.optionSubtypeNe c p)) (weightedAssignment z (Equiv.optionSubtypeNe c p)) :=
        (Fintype.prod_equiv (Equiv.optionSubtypeNe c) _ _ (fun _ => rfl)).symm
      _ = _ := by
        simp only [Fintype.prod_option, Equiv.optionSubtypeNe_none, Equiv.optionSubtypeNe_some,
          starKernel_center, starKernel_leaf, starLeafValue_assignment, Fintype.prod_boole,
          ← funext_iff]
        rfl
  simp_rw [hp]
  rw [Fintype.sum_equiv e _ (fun f =>
    T (starReconstruct c (x c) f) * if f = (fun j => x j.val) then 1 else 0) (fun _ => rfl)]
  simp

theorem restricts_star {k n : ℕ} (c : Fin k) (T : Tensor ℂ (Fin k) (fun _ => Fin n)) :
    Tensor.Restricts T (weightedComplete (starDimensions c n)) :=
  ⟨starKernel c T, (localMap_star c T).symm⟩

namespace Tensor

theorem localMap_indexedProduct {R I J : Type*} [CommSemiring R] [Fintype I] [Fintype J]
    [DecidableEq J]
    {V W : J → I → Type*} [∀ j i, Fintype (V j i)]
    (A : ∀ j i, W j i → V j i → R) (T : ∀ j, Tensor R I (V j)) :
    localMap (fun i y x => ∏ j, A j i (y j) (x j)) (indexedProduct T) =
      indexedProduct (fun j => localMap (A j) (T j)) := by
  funext y
  simp only [localMap, indexedProduct]
  rw [Fintype.prod_sum]
  apply Fintype.sum_equiv (Equiv.piComm (fun i j => V j i))
  intro x
  simp only [Equiv.piComm_apply]
  rw [Finset.prod_comm]
  exact (Finset.prod_mul_distrib : _).symm

theorem Restricts.indexedProduct {R I J : Type*} [CommSemiring R] [Fintype I] [Fintype J]
    [DecidableEq J]
    {V W : J → I → Type*} [∀ j i, Fintype (V j i)]
    {T : ∀ j, Tensor R I (V j)} {S : ∀ j, Tensor R I (W j)}
    (h : ∀ j, Restricts (S j) (T j)) : Restricts (indexedProduct S) (indexedProduct T) := by
  choose A hA using h
  refine ⟨fun i y x => ∏ j, A j i (y j) (x j), ?_⟩
  rw [localMap_indexedProduct]
  funext y
  exact Finset.prod_congr rfl (fun j _ => congrFun (hA j) _)

end Tensor

theorem prod_starDimensions {k : ℕ} (n : ℕ) (e : Edge k) :
    (∏ c : Fin k, starDimensions c n e) = n ^ 2 := by
  simp [starDimensions, e.prop]

theorem restricts_indexed_stars {k n : ℕ}
    (T : Fin k → Tensor ℂ (Fin k) (fun _ => Fin n)) :
    Tensor.Restricts (Tensor.indexedProduct T) (weightedComplete (fun _ : Edge k => n ^ 2)) := by
  classical
  have h := Tensor.Restricts.indexedProduct (fun c => restricts_star c (T c))
  have hs := Tensor.reindex_restricts
    (fun i => weightedIndexedCoordinate (fun c : Fin k => starDimensions c n) i)
    (weightedComplete (fun e => ∏ c : Fin k, starDimensions c n e))
  rw [weighted_indexedProduct_reindex] at hs
  have hd : (fun e => ∏ c : Fin k, starDimensions c n e) =
      (fun _ : Edge k => n ^ 2) := funext (prod_starDimensions n)
  rw [hd] at hs
  exact h.trans hs

theorem asymptoticRank_le_graphExponent {k n : ℕ} (hk : 2 ≤ k) (hn : 1 ≤ n)
    (T : Tensor ℂ (Fin k) (fun _ => Fin n)) :
    Tensor.asymptoticRank T ≤ (n : ℝ) ^ (2 * graphExponent k / k) := by
  have hk0 : 0 < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hgraph : Tensor.asymptoticRank (completeGraph k (n ^ 2)) =
      (n : ℝ) ^ (2 * graphExponent k) := by
    by_cases h1 : n = 1
    · subst n
      simp only [Nat.cast_one, Real.one_rpow]
      change Tensor.asymptoticRank (completeGraph k 1) = 1
      exact asymptoticRank_completeGraph_one k
    · have h2 : 2 ≤ n ^ 2 :=
        (show 2 ≤ n by omega).trans (le_self_pow hn (by decide : 2 ≠ 0))
      rw [asymptoticRank_completeGraph h2, Nat.cast_pow,
        ← Real.rpow_natCast_mul (Nat.cast_nonneg n)]
      norm_num
  have hp := (restricts_indexed_stars (fun _ : Fin k => T)).asymptoticRank_le
  change Tensor.asymptoticRank (Tensor.power T k) ≤ _ at hp
  rw [Tensor.asymptoticRank_power, asymptoticRank_weighted_constant, hgraph] at hp
  apply (Real.rpow_le_rpow_iff (Tensor.asymptoticRank_nonneg T)
    (Real.rpow_nonneg (Nat.cast_nonneg n) _) hk0).mp
  rwa [Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n),
    div_mul_cancel₀ _ (ne_of_gt hk0)]

end Lemmata.TensorRank
