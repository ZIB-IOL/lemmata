module

public import Lemmata.Centroid.Proof.BorderRank
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.BigOperators.Option
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Data.Fintype.Lattice

@[expose] public section

open scoped BigOperators

namespace Lemmata.Centroid.BigCentroid

noncomputable section
open Classical

universe u v w

variable {F : Type u} {ι : Type v} {U : ι → Type w}
variable [Field F] [Fintype ι]

abbrev Opposite (U : ι → Type w) (i : ι) := ∀ j : {j // j ≠ i}, U j.val

abbrev Coordinates (U : ι → Type w) (i : ι) := U i ⊕ Opposite U i

def pairCoefficient (i : ι) (p : Opposite U i) (x : ∀ j, Coordinates U j) : F :=
  ∏ j : {j // j ≠ i}, match x j.val with
    | Sum.inl a => if a = p j then 1 else 0
    | Sum.inr _ => 0

def sector (i : ι) (x : ∀ j, Coordinates U j) : F :=
  match x i with
  | Sum.inl _ => 0
  | Sum.inr p => pairCoefficient i p x

/-- The sum of the opposite-pair identity tensors. -/
def tensor : Tensor F ι (Coordinates U) := fun x => ∑ i, sector i x

theorem sector_eq_zero_of_other_dual (i j : ι) (hji : j ≠ i)
    (x : ∀ k, Coordinates U k) (p : Opposite U j) (hx : x j = Sum.inr p) :
    sector (F := F) i x = 0 := by
  unfold sector
  split
  · rfl
  · rename_i q hq
    unfold pairCoefficient
    apply Finset.prod_eq_zero (Finset.mem_univ (⟨j, hji⟩ : {k // k ≠ i}))
    simp [hx]

theorem tensor_eq_zero_of_two_duals (i j : ι) (hij : i ≠ j)
    (x : ∀ k, Coordinates U k) (p : Opposite U i) (q : Opposite U j)
    (hi : x i = Sum.inr p) (hj : x j = Sum.inr q) : tensor (F := F) x = 0 := by
  apply Finset.sum_eq_zero
  intro k hk
  by_cases hki : k = i
  · subst k
    exact sector_eq_zero_of_other_dual i j (Ne.symm hij) x q hj
  · exact sector_eq_zero_of_other_dual k i (Ne.symm hki) x p hi

theorem tensor_eq_zero_of_all_core (a : ∀ i, U i) :
    tensor (F := F) (fun i => Sum.inl (a i)) = 0 := by
  simp [tensor, sector]

theorem tensor_eq_pairCoefficient (i : ι) (p : Opposite U i)
    (x : ∀ j, Coordinates U j) (hx : x i = Sum.inr p) :
    tensor (F := F) x = pairCoefficient i p x := by
  rw [tensor, Finset.sum_eq_single i]
  · simp [sector, hx]
  · intro j hj hji
    exact sector_eq_zero_of_other_dual j i (Ne.symm hji) x p hx
  · simp

def corePoint (i : ι) (q : Opposite U i) (a : ∀ j, U j) :
    ∀ j, Coordinates U j :=
  fun j => if h : j = i then Sum.inl (a j) else Sum.inl (q ⟨j, h⟩)

theorem pairCoefficient_corePoint (i : ι) (p q : Opposite U i) (a : ∀ j, U j)
    (v : Coordinates U i) :
    pairCoefficient (F := F) i p (Function.update (corePoint i q a) i v) =
      if p = q then 1 else 0 := by
  have heq : pairCoefficient (F := F) i p (Function.update (corePoint i q a) i v) =
      ∏ j : {j // j ≠ i}, if q j = p j then (1 : F) else 0 := by
    unfold pairCoefficient
    apply Finset.prod_congr rfl
    intro j hj
    simp [corePoint, j.property]
  rw [heq]
  by_cases hpq : p = q
  · subst q
    simp
  · rw [ite_eq_right hpq]
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hpq
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    simp [Ne.symm hj]

theorem tensor_corePoint_dual (i : ι) (p q : Opposite U i) (a : ∀ j, U j) :
    tensor (F := F) (Function.update (corePoint i q a) i (Sum.inr p)) =
      if p = q then 1 else 0 := by
  rw [tensor_eq_pairCoefficient i p _ (Function.update_self _ _ _)]
  exact pairCoefficient_corePoint i p q a _

def dualColumn (i j : ι) (a : ∀ k, U k) (u : U i) :
    ∀ k, Coordinates U k :=
  let c := Function.update a i u
  Function.update (fun k => Sum.inl (c k)) j (Sum.inr (fun k => c k.val))

theorem tensor_dualColumn_core (i j : ι) (hij : i ≠ j)
    (a : ∀ k, U k) (u v : U i) :
    tensor (F := F) (Function.update (dualColumn i j a v) i (Sum.inl u)) =
      if u = v then 1 else 0 := by
  have hj : Function.update (dualColumn i j a v) i (Sum.inl u) j =
      Sum.inr (fun k : {k // k ≠ j} => Function.update a i v k.val) := by
    simp [Function.update_of_ne (Ne.symm hij), dualColumn]
  rw [tensor_eq_pairCoefficient j _ _ hj]
  unfold pairCoefficient
  rw [Finset.prod_eq_single (⟨i, hij⟩ : {k // k ≠ j})]
  · simp
  · intro k hk hki
    have hne : k.val ≠ i := by
      intro h
      exact hki (Subtype.ext h)
    simp [dualColumn,
      Function.update_of_ne k.property, Function.update_of_ne hne]
  · simp

def minorColumn (i j : ι) (a : ∀ k, U k) :
    Coordinates U i → ∀ k, Coordinates U k
  | Sum.inl u => dualColumn i j a u
  | Sum.inr p => corePoint i p a

theorem flatteningMinor_identity (i j : ι) (hij : i ≠ j)
    (a : ∀ k, U k) :
    Tensor.flatteningMinor (tensor (F := F) (U := U)) i id (minorColumn i j a) =
      (1 : Matrix (Coordinates U i) (Coordinates U i) F) := by
  funext r c
  simp only [Tensor.flatteningMinor, id_eq, Matrix.one_apply]
  cases r with
  | inl u =>
    cases c with
    | inl v => simpa [minorColumn] using tensor_dualColumn_core i j hij a u v
    | inr p =>
      rw [ite_eq_right (by simp)]
      apply Finset.sum_eq_zero
      intro k hk
      unfold sector
      by_cases hki : k = i
      · subst k
        simp
      · simp [minorColumn, corePoint, hki]
  | inr p =>
    cases c with
    | inl v =>
      rw [ite_eq_right (by simp)]
      apply tensor_eq_zero_of_two_duals i j hij _ p
        (fun k => Function.update a i v k.val)
      · simp
      · simp [Function.update_of_ne (Ne.symm hij), minorColumn, dualColumn]
    | inr q => simpa [minorColumn] using tensor_corePoint_dual (F := F) i p q a

theorem rationalBorderRank_lower [∀ i, Fintype (U i)] [∀ i, Nonempty (U i)]
    (i j : ι) (hij : i ≠ j) {r : ℕ}
    (h : Tensor.RationalBorderRankAtMost (tensor (F := F) (U := U)) r) :
    Fintype.card (U i) + ∏ j : {j // j ≠ i}, Fintype.card (U j.val) ≤ r := by
  let a : ∀ k, U k := fun k => Classical.choice inferInstance
  have hm := h.card_le_of_flatteningMinor i id (minorColumn i j a) (by
    rw [flatteningMinor_identity i j hij a, Matrix.det_one]
    exact one_ne_zero)
  simpa only [Fintype.card_sum, Fintype.card_pi] using hm

section Frames

variable {V : ι → Type*}

def firstVariation (u v : ∀ i, V i → F) : Tensor F ι V :=
  fun x => ∑ i, v i (x i) * ∏ j ∈ Finset.univ.erase i, u j (x j)

theorem coeff_one_simple_variation (u v : ∀ i, V i → F) (x : ∀ i, V i) :
    (Tensor.simple (fun i a => Polynomial.C (u i a) +
      Polynomial.X * Polynomial.C (v i a)) x).coeff 1 = firstVariation u v x := by
  let p := Tensor.simple (fun i a => Polynomial.C (u i a) +
    Polynomial.X * Polynomial.C (v i a)) x
  have hc : p.derivative.eval 0 = p.coeff 1 := by
    rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative]
    simp
  rw [← hc]
  dsimp [p, Tensor.simple, Lemmata.TensorRank.Tensor.pure]
  rw [Polynomial.derivative_prod_finset]
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_prod,
    Polynomial.derivative_add, Polynomial.derivative_C, Polynomial.derivative_mul,
    Polynomial.derivative_X, zero_add, one_mul, mul_zero, add_zero,
    Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X, zero_mul]
  unfold firstVariation
  apply Finset.sum_congr rfl
  intro i hi
  exact mul_comm _ _

theorem first_order_polynomial_certificate [Nonempty ι] [∀ i, Fintype (V i)]
    {r w : ℕ} (u v : Fin r → ∀ i, V i → F) (T : Tensor F ι V)
    (hQ : Tensor.RankAtMost (∑ q, Tensor.simple (u q)) w)
    (hT : (∑ q, firstVariation (u q) (v q)) = T) :
    ∃ D, Nonempty (PolynomialApproximation T (r + w) 1 D) := by
  let Q := ∑ q, Tensor.simple (u q)
  let P : Tensor (Polynomial F) ι V :=
    (∑ q, Tensor.simple (fun i a => Polynomial.C (u q i a) +
      Polynomial.X * Polynomial.C (v q i a))) +
      (-1 : Polynomial F) • Tensor.mapCoefficients Polynomial.C Q
  have hr : Tensor.RankAtMost P (r + w) := by
    apply Tensor.RankAtMost.add
    · exact ⟨_, rfl⟩
    · exact (hQ.mapCoefficients Polynomial.C).smul (-1)
  have hzero (x : ∀ i, V i) : (P x).coeff 0 = 0 := by
    simp [P, Q, Tensor.simple, Tensor.mapCoefficients,
      Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_finsetSum, Polynomial.eval_prod]
  have hone (x : ∀ i, V i) : (P x).coeff 1 = T x := by
    have hx := congrFun hT x
    simpa only [P, Pi.add_apply, Finset.sum_apply, Polynomial.finsetSum_coeff,
      Pi.smul_apply, smul_eq_mul, neg_one_mul, Polynomial.coeff_add,
      Polynomial.coeff_neg, Tensor.mapCoefficients, Polynomial.coeff_C,
      one_ne_zero, ite_false, neg_zero, add_zero, coeff_one_simple_variation] using hx
  let D := Finset.univ.sup (fun x : ∀ i, V i => (P x).natDegree)
  refine ⟨D, ⟨⟨P, hr, ?_, hone, ?_⟩⟩⟩
  · intro x k hk
    have hk0 : k = 0 := Nat.lt_one_iff.mp hk
    simpa only [hk0] using hzero x
  · intro x
    exact Polynomial.degree_le_of_natDegree_le
      (Finset.le_sup (f := fun x : ∀ i, V i => (P x).natDegree) (Finset.mem_univ x))

theorem rational_first_order_frame [Nonempty ι] [∀ i, Fintype (V i)]
    {r w : ℕ} (u v : Fin r → ∀ i, V i → RatFunc F) (T : Tensor F ι V)
    (hQ : Tensor.RankAtMost (∑ q, Tensor.simple (u q)) w)
    (hT : (∑ q, firstVariation (u q) (v q)) =
      Tensor.mapCoefficients (algebraMap F (RatFunc F)) T) :
    Tensor.RationalBorderRankAtMost T (r + w) := by
  obtain ⟨D, ⟨A⟩⟩ := first_order_polynomial_certificate u v _ hQ hT
  exact A.rationalBorderRankAtMost_of_ratFunc

end Frames

def coreFactor (u : ∀ i, U i → F) : ∀ i, Coordinates U i → F :=
  fun i => Sum.elim (u i) (fun _ => 0)

def dualFactor (l : ∀ i, Opposite U i → F) : ∀ i, Coordinates U i → F :=
  fun i => Sum.elim (fun _ => 0) (l i)

theorem frame_variation {r : ℕ} (u : Fin r → ∀ i, U i → F)
    (l : Fin r → ∀ i, Opposite U i → F)
    (hspan : ∀ i p (x : ∀ j, Coordinates U j),
      (∑ q, l q i p * ∏ j ∈ Finset.univ.erase i, coreFactor (u q) j (x j)) =
        pairCoefficient i p x) :
    (∑ q, firstVariation (coreFactor (u q)) (dualFactor (l q))) =
      tensor (F := F) (U := U) := by
  funext x
  simp only [Finset.sum_apply, firstVariation]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  cases hx : x i with
  | inl a => simp [dualFactor, sector, hx]
  | inr p => simpa [dualFactor, sector, hx] using hspan i p x

theorem map_tensor {K : Type*} [Field K] (φ : F →+* K) :
    Tensor.mapCoefficients φ (tensor (F := F) (U := U)) = tensor (F := K) := by
  funext x
  simp only [Tensor.mapCoefficients, tensor, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  unfold sector
  cases x i with
  | inl a => exact map_zero _
  | inr p =>
    simp only [pairCoefficient, map_prod]
    apply Finset.prod_congr rfl
    intro j hj
    cases x j.val <;> simp

section Transport

variable {κ : Type*} {W : κ → Type*} [Fintype κ]

def otherParties (e : ι ≃ κ) (i : ι) :
    {j : ι // j ≠ i} ≃ {j : κ // j ≠ e i} where
  toFun j := ⟨e j.val, fun h => j.property (e.injective h)⟩
  invFun j := ⟨e.symm j.val, fun h => j.property (by simpa using congrArg e h)⟩
  left_inv j := Subtype.ext (e.symm_apply_apply j.val)
  right_inv j := Subtype.ext (e.apply_symm_apply j.val)

def oppositeEquiv (e : ι ≃ κ) (c : ∀ i, U i ≃ W (e i)) (i : ι) :
    Opposite U i ≃ Opposite W (e i) :=
  (otherParties e i).piCongr (fun j => c j.val)

def coordinateEquiv (e : ι ≃ κ) (c : ∀ i, U i ≃ W (e i)) (i : ι) :
    Coordinates U i ≃ Coordinates W (e i) :=
  Equiv.sumCongr (c i) (oppositeEquiv e c i)

theorem pairCoefficient_transport (e : ι ≃ κ) (c : ∀ i, U i ≃ W (e i))
    (i : ι) (p : Opposite U i) (x : ∀ j, Coordinates U j) :
    pairCoefficient (F := F) (e i) (oppositeEquiv e c i p)
      (e.piCongr (coordinateEquiv e c) x) = pairCoefficient (F := F) i p x := by
  unfold pairCoefficient
  trans ∏ j : {j : ι // j ≠ i},
    match e.piCongr (coordinateEquiv e c) x (otherParties e i j).val with
    | Sum.inl a => if a = oppositeEquiv e c i p (otherParties e i j) then (1 : F) else 0
    | Sum.inr _ => 0
  · convert ((otherParties e i).prod_comp (fun j : {j : κ // j ≠ e i} =>
      match e.piCongr (coordinateEquiv e c) x j.val with
      | Sum.inl a => if a = oppositeEquiv e c i p j then (1 : F) else 0
      | Sum.inr _ => 0)).symm using 1
    all_goals
      congr 1
      ext j
      simp
    all_goals split <;> simp_all
  apply Finset.prod_congr rfl
  intro j hj
  have hx : e.piCongr (coordinateEquiv e c) x (otherParties e i j).val =
      coordinateEquiv e c j.val (x j.val) := Equiv.piCongr_apply_apply _ _ _ _
  have hp : oppositeEquiv e c i p (otherParties e i j) = c j.val (p j) :=
    Equiv.piCongr_apply_apply _ _ _ _
  rw [hx, hp]
  cases x j.val with
  | inl a =>
    by_cases ha : a = p j
    · subst a
      simp [coordinateEquiv]
      rfl
    · have hn : c j.val a ≠ c j.val (p j) := fun h => ha ((c j.val).injective h)
      simp [coordinateEquiv, ha]
      exact hn
  | inr q => rfl

theorem transport_tensor (e : ι ≃ κ) (c : ∀ i, U i ≃ W (e i)) :
    Tensor.transport e (coordinateEquiv e c) (tensor (F := F) (U := U)) =
      tensor (F := F) (U := W) := by
  funext y
  obtain ⟨x, rfl⟩ := (e.piCongr (coordinateEquiv e c)).surjective y
  simp only [Tensor.transport, Equiv.symm_apply_apply, tensor]
  rw [← e.sum_comp (fun j => sector (F := F) j (e.piCongr (coordinateEquiv e c) x))]
  apply Finset.sum_congr rfl
  intro i hi
  have hx := Equiv.piCongr_apply_apply e (coordinateEquiv e c) x i
  unfold sector
  rw [hx]
  cases hxi : x i with
  | inl a => simp [coordinateEquiv]
  | inr p =>
    simp only [coordinateEquiv, Equiv.sumCongr_apply, Sum.map_inr]
    exact (pairCoefficient_transport e c i p x).symm

end Transport

theorem rational_realization_frame [Nonempty ι] [∀ i, Fintype (U i)]
    {r w : ℕ} (u : Fin r → ∀ i, U i → RatFunc F)
    (l : Fin r → ∀ i, Opposite U i → RatFunc F)
    (hQ : Tensor.RankAtMost (∑ q, Tensor.simple (coreFactor (u q))) w)
    (hspan : ∀ i p (x : ∀ j, Coordinates U j),
      (∑ q, l q i p * ∏ j ∈ Finset.univ.erase i, coreFactor (u q) j (x j)) =
        pairCoefficient i p x) :
    Tensor.RationalBorderRankAtMost (tensor (F := F) (U := U)) (r + w) := by
  apply rational_first_order_frame (fun q => coreFactor (u q))
    (fun q => dualFactor (l q)) _ hQ
  rw [map_tensor]
  exact frame_variation u l hspan

abbrev oppositeSimple (u : ∀ i, U i → F) (i : ι) : Opposite U i → F :=
  Tensor.simple (fun j : {j // j ≠ i} => u j.val)

def FrameSpans {J : Type*} (u : J → ∀ i, U i → F) : Prop :=
  ∀ i, Submodule.span F (Set.range (fun q => oppositeSimple (u q) i)) = ⊤

theorem coreFactor_sum_rank [∀ i, Fintype (U i)] {J : Type*} [Fintype J]
    (u : J → ∀ i, U i → F) {w : ℕ}
    (h : Tensor.RankAtMost (∑ q, Tensor.simple (u q)) w) :
    Tensor.RankAtMost (∑ q, Tensor.simple (coreFactor (u q))) w := by
  let A : ∀ i, Coordinates U i → U i → F :=
    fun i x a => match x with
      | Sum.inl b => if a = b then 1 else 0
      | Sum.inr _ => 0
  have hs (v : ∀ i, U i → F) :
      Tensor.localMap A (Tensor.simple v) = Tensor.simple (coreFactor v) := by
    rw [Tensor.localMap_simple]
    congr 1
    funext i x
    cases x <;> simp [A, coreFactor]
  have hh := h.localMap A
  simpa only [Tensor.localMap_sum, hs] using hh

theorem FrameSpans.exists_dualFactor [∀ i, Fintype (U i)]
    {J : Type*} [Fintype J] (u : J → ∀ i, U i → F) (h : FrameSpans u) :
    ∃ l : J → ∀ i, Opposite U i → F, ∀ i p (x : ∀ j, Coordinates U j),
      (∑ q, l q i p * ∏ j ∈ Finset.univ.erase i, coreFactor (u q) j (x j)) =
        pairCoefficient i p x := by
  have hex (i : ι) (p : Opposite U i) : ∃ l : J → F,
      (∑ q, l q • oppositeSimple (u q) i) =
        Tensor.simple (fun (j : {j // j ≠ i}) a => if a = p j then 1 else 0) := by
    apply (Submodule.mem_span_range_iff_exists_fun F).mp
    rw [h i]
    trivial
  choose l hl using hex
  refine ⟨fun q i p => l i p q, fun i p x => ?_⟩
  let A : ∀ j : {j // j ≠ i}, Coordinates U j.val → U j.val → F :=
    fun j x a => match x with
      | Sum.inl b => if a = b then 1 else 0
      | Sum.inr _ => 0
  have hs (v : ∀ j : {j // j ≠ i}, U j.val → F) :
      Tensor.localMap A (Tensor.simple v) = Tensor.simple
        (fun j => Sum.elim (v j) (fun _ => 0)) := by
    rw [Tensor.localMap_simple]
    congr 1
    funext j y
    cases y <;> simp [A]
  have hh := congrArg (Tensor.localMap A) (hl i p)
  simp only [Tensor.localMap_sum, Tensor.localMap_smul, oppositeSimple, hs] at hh
  have hv := congrFun hh (fun j : {j // j ≠ i} => x j.val)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Tensor.simple,
    Lemmata.TensorRank.Tensor.pure] at hv
  rw [show (∑ q, l i p q * ∏ j ∈ Finset.univ.erase i, coreFactor (u q) j (x j)) =
      ∑ q, l i p q * ∏ j : {j // j ≠ i}, coreFactor (u q) j.val (x j.val) from by
        congr 1
        funext q
        rw [Finset.prod_subtype (p := fun j => j ≠ i) _ (by simp)]]
  convert hv using 1
  · unfold coreFactor
    rfl
  · unfold pairCoefficient
    apply Finset.prod_congr rfl
    intro j hj
    cases x j.val <;> rfl

theorem rational_spanning_frame [Nonempty ι] [∀ i, Fintype (U i)]
    {J : Type*} [Fintype J] (u : J → ∀ i, U i → RatFunc F) {w : ℕ}
    (hQ : Tensor.RankAtMost (∑ q, Tensor.simple (u q)) w) (hs : FrameSpans u) :
    Tensor.RationalBorderRankAtMost (tensor (F := F) (U := U)) (Fintype.card J + w) := by
  obtain ⟨l, hl⟩ := FrameSpans.exists_dualFactor u hs
  let e : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  apply rational_realization_frame (fun q => u (e q)) (fun q => l (e q))
  · have hh := coreFactor_sum_rank u hQ
    rw [show (∑ q, Tensor.simple (coreFactor (u (e q)))) =
      ∑ q : J, Tensor.simple (coreFactor (u q)) from
        e.sum_comp (fun q => Tensor.simple (coreFactor (u q)))]
    exact hh
  · intro i p x
    rw [show (∑ q, l (e q) i p * ∏ j ∈ Finset.univ.erase i,
      coreFactor (u (e q)) j (x j)) = ∑ q : J,
      l q i p * ∏ j ∈ Finset.univ.erase i, coreFactor (u q) j (x j) from
        e.sum_comp (fun q => l q i p * ∏ j ∈ Finset.univ.erase i,
          coreFactor (u q) j (x j))]
    exact hl i p x

namespace Grid

variable {κ : Type*} [Fintype κ]

abbrev Core (a : ℕ) (n : κ → ℕ) : Option κ → Type
  | none => Fin a
  | some i => Fin (n i)

instance coreFintype (a : ℕ) (n : κ → ℕ) (i : Option κ) : Fintype (Core a n i) := by
  cases i <;> exact inferInstance

abbrev matrix (a b : ℕ) : Matrix (Fin a) (Fin b) (RatFunc F) :=
  fun h j => (if h.val = j.val then 1 else 0) + RatFunc.X

theorem matrix_ne_zero (a b : ℕ) (h : Fin a) (j : Fin b) :
    matrix (F := F) a b h j ≠ 0 := by
  unfold matrix
  split_ifs
  · have hp : (1 + Polynomial.X : Polynomial F) ≠ 0 := by
      intro hz
      have hh := congrArg (fun p : Polynomial F => p.coeff 0) hz
      simp at hh
    have hn : algebraMap (Polynomial F) (RatFunc F) (1 + Polynomial.X) ≠ 0 :=
      RatFunc.algebraMap_ne_zero hp
    simpa using hn
  · simpa using (RatFunc.X_ne_zero (K := F))

theorem matrix_square_surjective (a : ℕ) :
    Function.Surjective (Matrix.mulVec (matrix (F := F) a a)) := by
  let P : Matrix (Fin a) (Fin a) (Polynomial F) :=
    fun h j => Polynomial.C (if h.val = j.val then 1 else 0) + Polynomial.X
  have hP : (Polynomial.evalRingHom (0 : F)).mapMatrix P = 1 := by
    funext h j
    change (Polynomial.evalRingHom (0 : F)) (P h j) = (1 : Matrix (Fin a) (Fin a) F) h j
    simp only [P, Matrix.one_apply, Polynomial.coe_evalRingHom, Polynomial.eval_add,
      Polynomial.eval_X, add_zero]
    split_ifs <;> simp_all [Fin.ext_iff]
  have hdet : P.det ≠ 0 := by
    intro hz
    have hh := congrArg (Polynomial.evalRingHom (0 : F)) hz
    rw [RingHom.map_det, hP, Matrix.det_one, map_zero] at hh
    exact one_ne_zero hh
  have hmap : (algebraMap (Polynomial F) (RatFunc F)).mapMatrix P = matrix a a := by
    funext h j
    change algebraMap (Polynomial F) (RatFunc F) (P h j) = matrix a a h j
    simp [P, matrix]
  have hd : (matrix (F := F) a a).det ≠ 0 := by
    rw [← hmap, ← RingHom.map_det]
    exact RatFunc.algebraMap_ne_zero hdet
  exact Matrix.mulVec_surjective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hd))

theorem matrix_rows_independent (a b : ℕ) (hab : a ≤ b) :
    LinearIndependent (RatFunc F) (fun h : Fin a => fun j : Fin b =>
      matrix (F := F) a b h j) := by
  let L : (Fin b → RatFunc F) →ₗ[RatFunc F] (Fin a → RatFunc F) := {
    toFun := fun f j => f (Fin.castLE hab j)
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  apply LinearIndependent.of_comp L
  have hs := Matrix.linearIndependent_rows_of_isUnit
    (Matrix.mulVec_surjective_iff_isUnit.mp (matrix_square_surjective (F := F) a))
  convert hs using 1
  funext h j
  rfl

theorem block_rows_independent {K α β γ : Type*} [Field K]
    [Fintype α] [Fintype β] [Fintype γ]
    (M : α → γ → K) (hM : LinearIndependent K M) (D : α → β → K)
    (hD : ∀ a b, D a b ≠ 0) :
    LinearIndependent K (fun p : α × β => fun q : γ × β =>
      if p.2 = q.2 then D p.1 p.2 * M p.1 q.1 else 0) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc p
  have hz : (∑ a, (c (a, p.2) * D a p.2) • M a) = 0 := by
    funext j
    have hh := congrFun hc (j, p.2)
    simpa [Fintype.sum_prod_type, Pi.smul_apply, smul_eq_mul, mul_assoc,
      mul_ite, Fintype.sum_ite_eq'] using hh
  have hh := (Fintype.linearIndependent_iff.mp hM) _ hz p.1
  exact (mul_eq_zero.mp hh).resolve_right (hD p.1 p.2)

abbrev point (a : ℕ) (n : κ → ℕ) (J : ∀ i, Fin (n i)) :
    ∀ i, Core a n i → RatFunc F
  | none => fun h => ∏ i, matrix a (n i) h (J i)
  | some i => fun j => if j = J i then 1 else 0

def lowRankPoint (a : ℕ) (n : κ → ℕ) (h : Fin a) :
    ∀ i, Core a n i → RatFunc F
  | none => fun j => if j = h then 1 else 0
  | some i => fun j => matrix a (n i) h j

theorem point_sum (a : ℕ) (n : κ → ℕ) :
    (∑ J : ∀ i, Fin (n i), Tensor.simple (point (F := F) a n J)) =
      ∑ h : Fin a, Tensor.simple (lowRankPoint a n h) := by
  funext x
  simp only [Finset.sum_apply, Tensor.simple, Fintype.prod_option, point, lowRankPoint,
    Lemmata.TensorRank.Tensor.pure]
  have he (J : ∀ i, Fin (n i)) :
      (∏ i, if x (some i) = J i then (1 : RatFunc F) else 0) =
        if (fun i => x (some i)) = J then 1 else 0 := by
    rw [Fintype.prod_ite_zero]
    simp only [Finset.prod_const_one]
    congr 1
    exact propext ⟨fun h => funext h, fun h i => congrFun h i⟩
  simp_rw [he]
  simp only [mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul,
    ]
  change (∑ J : ∀ i, Fin (n i), if (fun i => x (some i)) = J then
    ∏ i, matrix (F := F) a (n i) (x none) (J i) else 0) =
      ∑ h : Fin a, if x none = h then
        ∏ i, matrix (F := F) a (n i) h (x (some i)) else 0
  rw [Fintype.sum_ite_eq (fun i => x (some i))
    (fun J : ∀ i, Fin (n i) => ∏ i, matrix (F := F) a (n i) (x none) (J i)),
    Fintype.sum_ite_eq (x none)
    (fun h : Fin a => ∏ i, matrix (F := F) a (n i) h (x (some i)))]

def indicesNone : κ ≃ {j : Option κ // j ≠ none} where
  toFun i := ⟨some i, by simp⟩
  invFun j := match j with
    | ⟨none, h⟩ => False.elim (h rfl)
    | ⟨some i, _⟩ => i
  left_inv _ := rfl
  right_inv j := by
    rcases j with ⟨j, hj⟩
    cases j with
    | none => exact False.elim (hj rfl)
    | some i => rfl

def indicesSome (i : κ) : Option {k : κ // k ≠ i} ≃ {j : Option κ // j ≠ some i} where
  toFun j := match j with
    | none => ⟨none, by simp⟩
    | some k => ⟨some k.val, by simp [k.property]⟩
  invFun j := match j with
    | ⟨none, _⟩ => none
    | ⟨some k, h⟩ => some ⟨k, fun hk => h (congrArg some hk)⟩
  left_inv j := by cases j <;> rfl
  right_inv j := by
    rcases j with ⟨j, hj⟩
    cases j <;> rfl

def oppositeNone (a : ℕ) (n : κ → ℕ) :
    Opposite (Core a n) none ≃ (∀ i, Fin (n i)) where
  toFun p i := p ⟨some i, by simp⟩
  invFun J j := match j with
    | ⟨none, h⟩ => False.elim (h rfl)
    | ⟨some i, _⟩ => J i
  left_inv p := by
    funext j
    rcases j with ⟨j, hj⟩
    cases j with
    | none => exact False.elim (hj rfl)
    | some i => rfl
  right_inv _ := rfl

def oppositeSome (a : ℕ) (n : κ → ℕ) (i : κ) :
    Opposite (Core a n) (some i) ≃
      Fin a × (∀ k : {k : κ // k ≠ i}, Fin (n k.val)) where
  toFun p := ⟨p ⟨none, by simp⟩, fun k => p ⟨some k.val, by simp [k.property]⟩⟩
  invFun p j := match j with
    | ⟨none, _⟩ => p.1
    | ⟨some k, h⟩ => p.2 ⟨k, fun hk => h (congrArg some hk)⟩
  left_inv p := by
    funext j
    rcases j with ⟨j, hj⟩
    cases j <;> rfl
  right_inv _ := rfl

theorem oppositeSimple_none (a : ℕ) (n : κ → ℕ) (J : ∀ i, Fin (n i))
    (p : Opposite (Core a n) none) :
    oppositeSimple (point (F := F) a n J) none p =
      if oppositeNone a n p = J then 1 else 0 := by
  unfold oppositeSimple Tensor.simple Lemmata.TensorRank.Tensor.pure
  dsimp only
  trans ∏ k : κ, point (F := F) a n J (indicesNone k).val (p (indicesNone k))
  · convert ((indicesNone (κ := κ)).prod_comp
      (fun j => point (F := F) a n J j.val (p j))).symm using 1
    congr 1
    ext j
    simp
  change (∏ i, if p ⟨some i, by simp⟩ = J i then (1 : RatFunc F) else 0) = _
  rw [Fintype.prod_ite_zero]
  simp only [Finset.prod_const_one]
  congr 1
  exact propext ⟨fun h => funext h, fun h i => congrFun h i⟩

theorem oppositeSimple_some (a : ℕ) (n : κ → ℕ) (J : ∀ i, Fin (n i))
    (i : κ) (p : Opposite (Core a n) (some i)) :
    oppositeSimple (point (F := F) a n J) (some i) p =
      (∏ k, matrix a (n k) (oppositeSome a n i p).1 (J k)) *
        if (oppositeSome a n i p).2 = (fun k : {k // k ≠ i} => J k.val) then 1 else 0 := by
  unfold oppositeSimple Tensor.simple Lemmata.TensorRank.Tensor.pure
  dsimp only
  trans ∏ k : Option {k // k ≠ i},
    point (F := F) a n J (indicesSome i k).val (p (indicesSome i k))
  · convert ((indicesSome i).prod_comp
      (fun j => point (F := F) a n J j.val (p j))).symm using 1
    congr 1
    ext j
    simp
  rw [Fintype.prod_option]
  change (∏ k, matrix a (n k) (p ⟨none, by simp⟩) (J k)) *
    (∏ k : {k // k ≠ i}, if p ⟨some k.val, by simp [k.property]⟩ = J k.val
      then (1 : RatFunc F) else 0) = _
  congr 1
  rw [Fintype.prod_ite_zero]
  simp only [Finset.prod_const_one]
  congr 1
  exact propext ⟨fun h => funext h, fun h k => congrFun h k⟩

def blockWeight (a : ℕ) (n : κ → ℕ) (i : κ) (h : Fin a)
    (R : ∀ k : {k // k ≠ i}, Fin (n k.val)) : RatFunc F :=
  ∏ k : {k // k ≠ i}, matrix a (n k.val) h (R k)

theorem oppositeSimple_block (a : ℕ) (n : κ → ℕ) (i : κ)
    (p : Fin a × (∀ k : {k // k ≠ i}, Fin (n k.val)))
    (q : Fin (n i) × (∀ k : {k // k ≠ i}, Fin (n k.val))) :
    oppositeSimple (point (F := F) a n ((Equiv.piSplitAt i (fun k => Fin (n k))).symm q))
      (some i) ((oppositeSome a n i).symm p) =
        if p.2 = q.2 then blockWeight a n i p.1 p.2 * matrix a (n i) p.1 q.1 else 0 := by
  rw [oppositeSimple_some, Equiv.apply_symm_apply]
  have hrest : (fun k : {k // k ≠ i} =>
      (Equiv.piSplitAt i (fun k => Fin (n k))).symm q k.val) = q.2 := by
    funext k
    simp [Equiv.piSplitAt, k.property]
  rw [hrest]
  by_cases hpq : p.2 = q.2
  · rw [ite_eq_left hpq, mul_one, ite_eq_left hpq]
    rw [Fintype.prod_eq_mul_prod_subtype_ne _ i]
    have hs : (∏ k : {k // k ≠ i},
        matrix (F := F) a (n k.val) p.1
          ((Equiv.piSplitAt i (fun k => Fin (n k))).symm q k.val)) =
        blockWeight a n i p.1 p.2 := by
      rw [show p.2 = q.2 from hpq]
      unfold blockWeight
      apply Finset.prod_congr rfl
      intro k hk
      simp [Equiv.piSplitAt, k.property]
    rw [hs]
    simp [Equiv.piSplitAt, mul_comm]
  · simp [hpq]

theorem point_spans_none (a : ℕ) (n : κ → ℕ) :
    Submodule.span (RatFunc F)
      (Set.range (fun J => oppositeSimple (point (F := F) a n J) none)) = ⊤ := by
  apply span_flip_eq_top_iff_linearIndependent.mpr
  apply (linearIndependent_equiv (oppositeNone a n).symm).mp
  change LinearIndependent (RatFunc F) (fun p : ∀ i, Fin (n i) =>
    fun J : ∀ i, Fin (n i) => oppositeSimple (point a n J) none ((oppositeNone a n).symm p))
  simp_rw [oppositeSimple_none, Equiv.apply_symm_apply]
  rw [Fintype.linearIndependent_iff]
  intro c hc J
  have h := congrFun hc J
  simpa [Pi.smul_apply, smul_eq_mul, mul_ite, Fintype.sum_ite_eq'] using h

theorem point_spans_some (a : ℕ) (n : κ → ℕ) (i : κ) (hn : a ≤ n i) :
    Submodule.span (RatFunc F)
      (Set.range (fun J => oppositeSimple (point (F := F) a n J) (some i))) = ⊤ := by
  apply span_flip_eq_top_iff_linearIndependent.mpr
  apply (linearIndependent_equiv (oppositeSome a n i).symm).mp
  let L : ((∀ k, Fin (n k)) → RatFunc F) →ₗ[RatFunc F]
      ((Fin (n i) × (∀ k : {k // k ≠ i}, Fin (n k.val))) → RatFunc F) := {
    toFun := fun f q => f ((Equiv.piSplitAt i (fun k => Fin (n k))).symm q)
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  apply LinearIndependent.of_comp L
  change LinearIndependent (RatFunc F) (fun p => fun q =>
    oppositeSimple (point a n ((Equiv.piSplitAt i (fun k => Fin (n k))).symm q))
      (some i) ((oppositeSome a n i).symm p))
  simp_rw [oppositeSimple_block]
  convert block_rows_independent (K := RatFunc F)
    (α := Fin a) (β := ∀ k : {k // k ≠ i}, Fin (n k.val)) (γ := Fin (n i))
    (matrix (F := F) a (n i)) (matrix_rows_independent (F := F) a (n i) hn)
    (blockWeight (F := F) a n i)
    (fun h R => Finset.prod_ne_zero_iff.mpr fun k _ => matrix_ne_zero (F := F) a (n k.val) h (R k)) using 1
  funext p q
  split_ifs <;> rfl

theorem point_spans (a : ℕ) (n : κ → ℕ) (hn : ∀ i, a ≤ n i) :
    FrameSpans (point (F := F) a n) := by
  intro i
  cases i with
  | none => exact point_spans_none a n
  | some i => exact point_spans_some a n i (hn i)

theorem rationalBorderRankAtMost (a : ℕ) (n : κ → ℕ) (hn : ∀ i, a ≤ n i) :
    Tensor.RationalBorderRankAtMost (tensor (F := F) (U := Core a n))
      (a + ∏ i, n i) := by
  have hQ : Tensor.RankAtMost (∑ J, Tensor.simple (point (F := F) a n J)) a := by
    rw [point_sum]
    exact ⟨lowRankPoint a n, rfl⟩
  have hh := rational_spanning_frame (point (F := F) a n) hQ (point_spans a n hn)
  simpa only [Fintype.card_pi, Fintype.card_fin, Nat.add_comm] using hh

theorem minimal_border_rank [Nonempty κ] (a : ℕ) (n : κ → ℕ)
    (ha : 0 < a) (hn : ∀ i, a ≤ n i) :
    Tensor.rationalBorderRank (tensor (F := F) (U := Core a n)) = a + ∏ i, n i := by
  let : ∀ i, Nonempty (Core a n i) := fun i => by
    cases i with
    | none => exact ⟨⟨0, ha⟩⟩
    | some i => exact ⟨⟨0, lt_of_lt_of_le ha (hn i)⟩⟩
  apply le_antisymm
  · exact (Tensor.rationalBorderRank_le_iff _ _).mpr (rationalBorderRankAtMost a n hn)
  · let i : κ := Classical.choice inferInstance
    have hh := rationalBorderRank_lower (F := F) (U := Core a n) none (some i)
      (by simp) (Tensor.rationalBorderRankAtMost_rank _)
    have hp : (∏ j : {j : Option κ // j ≠ none}, Fintype.card (Core a n j.val)) =
        ∏ j : κ, n j := by
      trans ∏ j : κ, Fintype.card (Core a n (indicesNone j).val)
      · exact ((indicesNone (κ := κ)).prod_comp
          (fun j => Fintype.card (Core a n j.val))).symm
      · apply Finset.prod_congr rfl
        intro j hj
        rw [Fintype.card_eq_nat_card]
        exact Nat.card_fin (n j)
    have hh' : Fintype.card (Core a n none) +
        (∏ j : {j : Option κ // j ≠ none}, Fintype.card (Core a n j.val)) ≤
        Tensor.rationalBorderRank (tensor (F := F) (U := Core a n)) := by
      convert hh using 1
      congr 2
      ext j
      simp
    simpa only [Core, coreFintype, Fintype.card_fin, hp] using hh'

end Grid

def normalizedCoreEquiv (n : ι → ℕ) (m : ι) (i : Option {j : ι // j ≠ m}) :
    Grid.Core (n m) (fun j : {j : ι // j ≠ m} => n j.val) i ≃
      Fin (n (Equiv.optionSubtypeNe m i)) := by
  cases i <;> exact Equiv.refl _

theorem normalized_upper (n : ι → ℕ) (m : ι) (hmin : ∀ i, n m ≤ n i) :
    Tensor.RationalBorderRankAtMost (tensor (F := F) (U := fun i => Fin (n i)))
      (n m + ∏ j : {j : ι // j ≠ m}, n j.val) := by
  let e := Equiv.optionSubtypeNe m
  let c := normalizedCoreEquiv n m
  have h := Grid.rationalBorderRankAtMost (F := F) (n m)
    (fun j : {j : ι // j ≠ m} => n j.val) (fun j => hmin j.val)
  have hh := h.transport e (coordinateEquiv (W := fun i : ι => Fin (n i)) e c)
  rw [transport_tensor] at hh
  exact hh

def maximumSide (n : ι → ℕ) : ℕ :=
  Finset.univ.sup (fun i => n i + ∏ j : {j : ι // j ≠ i}, n j.val)

/-- Rectangular big-centroid tensors have minimal rational border rank over every field. -/
theorem minimal_border_rank [Nontrivial ι] (n : ι → ℕ) (hn : ∀ i, 0 < n i) :
    Tensor.rationalBorderRank (tensor (F := F) (U := fun i => Fin (n i))) =
      maximumSide n := by
  let : ∀ i, Nonempty (Fin (n i)) := fun i => ⟨⟨0, hn i⟩⟩
  apply le_antisymm
  · obtain ⟨m, hmin⟩ := Finite.exists_min n
    have h := normalized_upper (F := F) n m hmin
    exact ((Tensor.rationalBorderRank_le_iff _ _).mpr h).trans
      (Finset.le_sup (f := fun i => n i + ∏ j : {j : ι // j ≠ i}, n j.val)
        (Finset.mem_univ m))
  · apply Finset.sup_le
    intro i hi
    obtain ⟨j, hji⟩ := exists_ne i
    have h := rationalBorderRank_lower (F := F) (U := fun i => Fin (n i)) i j
      (Ne.symm hji) (Tensor.rationalBorderRankAtMost_rank _)
    simpa only [Fintype.card_fin] using h

end

end Lemmata.Centroid.BigCentroid
