module

public import Lemmata.TensorRank.Def.DirectSum
public import Lemmata.TensorRank.Proof.Maps
public import Lemmata.TensorRank.Proof.Asymptotic
public import Lemmata.TensorRank.Proof.Flattening
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Tactic.Linarith

@[expose] public section

set_option autoImplicit false

open Filter
open scoped BigOperators
open scoped Topology
open Classical

namespace Lemmata.TensorRank.Tensor

universe u v w

variable {R : Type u} [CommSemiring R] {I : Type v} {V : I → Type w}

theorem diagonal_const (l : ℕ) (a : Fin l) :
    diagonal (R := R) (I := I) l (fun _ => a) = 1 := by
  simp only [diagonal, ite_eq_left (show ∃ c : Fin l, ∀ _i : I, a = c from ⟨a, fun _ => rfl⟩)]

theorem diagonal_eq_zero_of_ne {l : ℕ} (x : I → Fin l) (i j : I) (h : x i ≠ x j) :
    diagonal (R := R) l x = 0 := by
  rw [diagonal, ite_eq_right]
  rintro ⟨a, ha⟩
  exact h ((ha i).trans (ha j).symm)

theorem diagonal_one (x : I → Fin 1) : diagonal (R := R) 1 x = 1 := by
  rw [diagonal, ite_eq_left]
  exact ⟨0, fun _ => Subsingleton.elim _ _⟩

theorem copies_apply (l : ℕ) (T : Tensor R I V) (x : ∀ i, Fin l × V i) :
    copies l T x = if ∃ a : Fin l, ∀ i, (x i).1 = a then T (fun i => (x i).2) else 0 := by
  simp [copies, product, diagonal, ite_mul]

variable [Fintype I] [Nonempty I]

theorem diagonal_eq_sum (l : ℕ) :
    diagonal (R := R) (I := I) l =
      ∑ a : Fin l, pure (fun _ x => if x = a then 1 else 0) := by
  funext x
  let i₀ : I := Classical.arbitrary I
  have hc : (∃ a : Fin l, ∀ i, x i = a) ↔ ∀ i, x i = x i₀ := by
    constructor
    · rintro ⟨a, ha⟩ i
      exact (ha i).trans (ha i₀).symm
    · intro h
      exact ⟨x i₀, h⟩
  simp only [diagonal, hc, Finset.sum_apply, pure, Fintype.prod_boole]
  by_cases h : ∀ i, x i = x i₀
  · simp [h]
  · have he (a : Fin l) : ¬∀ i, x i = a :=
      fun ha => h (fun i => (ha i).trans (ha i₀).symm)
    simp [h, he]

theorem rankLE_diagonal (l : ℕ) : RankLE (diagonal (R := R) (I := I) l) l := by
  refine ⟨fun _ => 1, fun a _ x => if x = a then 1 else 0, ?_⟩
  funext x
  simpa only [one_mul, Finset.sum_apply] using congrFun (diagonal_eq_sum (R := R) (I := I) l) x

theorem localMap_diagonal {W : I → Type*} (l : ℕ) (A : ∀ i, W i → Fin l → R) :
    localMap A (diagonal l) = ∑ a : Fin l, pure (fun i y => A i y a) := by
  rw [diagonal_eq_sum, localMap_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [localMap_pure]
  congr 1
  funext i y
  simp

theorem rankLE_iff_restricts_diagonal (T : Tensor R I V) (l : ℕ) :
    RankLE T l ↔ Restricts T (diagonal (R := R) (I := I) l) := by
  constructor
  · intro h
    obtain ⟨v, h⟩ := (rankLE_iff_sum_pure T l).mp h
    refine ⟨fun i y a => v a i y, ?_⟩
    rw [localMap_diagonal]
    funext x
    simpa only [Finset.sum_apply] using congrFun h x
  · rintro ⟨A, rfl⟩
    exact (rankLE_diagonal l).localMap A

variable [∀ i, Fintype (V i)]

theorem restricts_diagonal_rank (T : Tensor R I V) :
    Restricts T (diagonal (R := R) (I := I) (rank T)) :=
  (rankLE_iff_restricts_diagonal T _).mp (rankLE_rank T)

theorem rank_diagonal_le (l : ℕ) : rank (diagonal (R := R) (I := I) l) ≤ l :=
  (rank_le_iff _ _).mpr (rankLE_diagonal l)

omit [Fintype I] [Nonempty I] [∀ i, Fintype (V i)] in
@[simp] theorem copies_zero (l : ℕ) : copies l (0 : Tensor R I V) = 0 := by
  funext x
  simp [copies, product]

omit [Nonempty I] in
theorem diagonal_apply (l : ℕ) (x : I → Fin l) (i₀ : I) :
    diagonal (R := R) l x = if ∀ i, x i = x i₀ then 1 else 0 := by
  have hc : (∃ a : Fin l, ∀ i, x i = a) ↔ ∀ i, x i = x i₀ := by
    constructor
    · rintro ⟨a, ha⟩ i
      exact (ha i).trans (ha i₀).symm
    · exact fun h => ⟨x i₀, h⟩
  simp only [diagonal, hc]

noncomputable def labelWord (l q : ℕ) : (Fin q → Fin l) ≃ Fin (l ^ q) :=
  Fintype.equivFinOfCardEq (by simp)

theorem diagonal_power_reindex (l q : ℕ) :
    reindex (fun _ : I => labelWord l q) (diagonal (R := R) (I := I) (l ^ q)) =
      power (diagonal (R := R) (I := I) l) q := by
  funext x
  let i₀ : I := Classical.arbitrary I
  have hc : (∀ i, labelWord l q (x i) = labelWord l q (x i₀)) ↔
      ∀ t, ∀ i, x i t = x i₀ t := by
    simp only [(labelWord l q).injective.eq_iff, funext_iff]
    exact forall_comm
  change diagonal (l ^ q) (fun i => labelWord l q (x i)) = ∏ t, diagonal l (fun i => x i t)
  simp only [diagonal_apply _ _ i₀, Fintype.prod_boole, hc]
  split_ifs <;> rfl

omit [Nonempty I] [∀ i, Fintype (V i)] in
private theorem inverse_reindex_restricts {W : I → Type*} [∀ i, Fintype (W i)]
    (e : ∀ i, W i ≃ V i) (T : Tensor R I V) : Restricts T (reindex (fun i => e i) T) := by
  have h := reindex_restricts (fun i => (e i).symm) (reindex (fun i => e i) T)
  have hid : reindex (fun i => (e i).symm) (reindex (fun i => e i) T) = T := by
    funext x
    change T (fun i => e i ((e i).symm (x i))) = T x
    congr 1
    funext i
    exact (e i).apply_symm_apply (x i)
  rwa [hid] at h

theorem diagonal_power_restricts (l q : ℕ) :
    Restricts (diagonal (R := R) (I := I) (l ^ q)) (power (diagonal l) q) := by
  have h := inverse_reindex_restricts (fun _ : I => labelWord l q)
    (diagonal (R := R) (I := I) (l ^ q))
  rwa [diagonal_power_reindex] at h

omit [Nonempty I] in
theorem restricts_copies (l : ℕ) (hl : 0 < l) (T : Tensor R I V) : Restricts T (copies l T) := by
  have h := reindex_restricts (fun i (x : V i) => (⟨0, hl⟩, x)) (copies l T)
  have he : reindex (fun i (x : V i) => (⟨0, hl⟩, x)) (copies l T) = T := by
    funext x
    simp [copies, reindex, product, diagonal_const]
  rwa [he] at h

theorem power_restricts_copies_power (l h s : ℕ) (T : Tensor R I V)
    (hr : rank (power T h) ≤ l ^ s) : Restricts (power T (h + s)) (power (copies l T) s) := by
  have ht : Restricts (power T h) (diagonal (R := R) (I := I) (l ^ s)) :=
    (rankLE_iff_restricts_diagonal _ _).mp ((rank_le_iff _ _).mp hr)
  have hproduct := (ht.trans (diagonal_power_restricts l s)).product (Restricts.refl (power T s))
  have hadd := inverse_reindex_restricts (fun i => (Fin.appendEquiv h s :
    ((Fin h → V i) × (Fin s → V i)) ≃ (Fin (h + s) → V i))) (power T (h + s))
  rw [power_add_reindex] at hadd
  have hcopies := inverse_reindex_restricts
    (fun i => Equiv.arrowProdEquivProdArrow (Fin s) (fun _ => Fin l) (fun _ => V i))
    (product (power (diagonal (R := R) (I := I) l) s) (power T s))
  rw [power_product_reindex] at hcopies
  exact (hadd.trans hproduct).trans hcopies

theorem localMap_copies {W : I → Type*} (l : ℕ)
    (A : ∀ i, W i → (Fin l × V i) → R) (T : Tensor R I V) :
    localMap A (copies l T) = ∑ a : Fin l, localMap (fun i y v => A i y (a, v)) T := by
  let K (a : Fin l) (i : I) (y : Fin l × V i) (v : V i) : R :=
    (if y.1 = a then 1 else 0) * (if v = y.2 then 1 else 0)
  have hinc (a : Fin l) : localMap (K a) T =
      product (pure (fun _ x => if x = a then 1 else 0)) T := by
    funext y
    simp only [localMap, K, Finset.prod_mul_distrib, Fintype.prod_boole, product, pure]
    simp [← funext_iff, mul_ite, ite_mul]
  have hsum : copies l T = ∑ a : Fin l, localMap (K a) T := by
    simp_rw [hinc]
    rw [copies, diagonal_eq_sum]
    funext y
    simp only [product, Finset.sum_apply, Finset.sum_mul]
  rw [hsum, localMap_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [localMap_comp]
  congr 1
  funext i y v
  simp [K, Fintype.sum_prod_type, mul_ite]

section Field

variable {F : Type u} [Field F]

omit [Fintype I] [Nonempty I] in
theorem diagonal_identity_minor (l : ℕ) (i j : I) (hji : j ≠ i) :
    (flatten (diagonal (R := F) (I := I) l) {i}).submatrix
      (fun a : Fin l => fun _ => a) (fun a : Fin l => fun _ => a) = 1 := by
  funext a b
  change diagonal l (joinCut {i} (fun _ => a) (fun _ => b)) = if a = b then (1 : F) else 0
  by_cases hab : a = b
  · subst b
    have hconst : joinCut (V := fun _ : I => Fin l) {i} (fun _ => a) (fun _ => a) =
        fun _ => a := by
      funext p
      by_cases hp : p ∈ ({i} : Finset I) <;> simp [joinCut, hp]
    rw [hconst, diagonal_const]
    simp
  · rw [ite_eq_right hab]
    apply diagonal_eq_zero_of_ne _ i j
    simpa [joinCut, hji] using hab

theorem rank_diagonal (l : ℕ) (i j : I) (hji : j ≠ i) :
    rank (diagonal (R := F) (I := I) l) = l := by
  apply le_antisymm (rank_diagonal_le l)
  simpa using card_le_rank_of_identity (diagonal (R := F) (I := I) l) {i}
    (fun a : Fin l => fun _ => a) (fun a : Fin l => fun _ => a)
    (diagonal_identity_minor l i j hji)

theorem asymptoticRank_diagonal (l : ℕ) (i j : I) (hji : j ≠ i) :
    asymptoticRank (diagonal (R := F) (I := I) l) = l := by
  apply le_antisymm
  · exact (asymptoticRank_le_rank _).trans (by exact_mod_cast rank_diagonal_le (R := F) (I := I) l)
  · simpa using card_le_asymptoticRank_of_identity (diagonal (R := F) (I := I) l) {i}
      (fun a : Fin l => fun _ => a) (fun a : Fin l => fun _ => a)
      (diagonal_identity_minor l i j hji)

theorem rank_power_diagonal (l q : ℕ) (i j : I) (hji : j ≠ i) :
    rank (power (diagonal (R := F) (I := I) l) q) = l ^ q := by
  apply le_antisymm
  · calc
      rank (power (diagonal (R := F) (I := I) l) q) ≤
          rank (diagonal (R := F) (I := I) l) ^ q := rank_power_le _ q
      _ = l ^ q := by rw [rank_diagonal l i j hji]
  · simpa using card_pow_le_rank_of_identity (diagonal (R := F) (I := I) l) {i}
      (fun a : Fin l => fun _ => a) (fun a : Fin l => fun _ => a)
      (diagonal_identity_minor l i j hji) q

theorem diagonal_one_restricts {T : Tensor F I V} (hT : T ≠ 0) :
    Restricts (diagonal (R := F) (I := I) 1) T := by
  obtain ⟨x, hx⟩ : ∃ x, T x ≠ 0 := by
    by_contra h
    push Not at h
    exact hT (funext h)
  let i₀ : I := Classical.arbitrary I
  refine ⟨fun i _a v => (if i = i₀ then (T x)⁻¹ else 1) * (if v = x i then 1 else 0), ?_⟩
  funext y
  rw [diagonal_one]
  simp only [localMap, Finset.prod_mul_distrib, Fintype.prod_boole]
  simp [← funext_iff, hx]

theorem diagonal_restricts_copies (l : ℕ) {T : Tensor F I V} (hT : T ≠ 0) :
    Restricts (diagonal (R := F) (I := I) l) (copies l T) := by
  have hp := (Restricts.refl (diagonal (R := F) (I := I) l)).product (diagonal_one_restricts hT)
  have hr := reindex_restricts (fun _ (a : Fin l) => (a, (0 : Fin 1)))
    (product (diagonal (R := F) (I := I) l) (diagonal (R := F) (I := I) 1))
  have he : reindex (fun _ (a : Fin l) => (a, (0 : Fin 1)))
      (product (diagonal (R := F) (I := I) l) (diagonal (R := F) (I := I) 1)) =
        diagonal (R := F) (I := I) l := by
    funext x
    simp [reindex, product, diagonal_one]
  rw [he] at hr
  exact hr.trans hp

theorem asymptoticRank_copies_le (l : ℕ) (T : Tensor F I V) :
    asymptoticRank (copies l T) ≤ (l : ℝ) * asymptoticRank T := by
  apply (asymptoticRank_product_le (diagonal (R := F) (I := I) l) T).trans
  apply mul_le_mul_of_nonneg_right _ (asymptoticRank_nonneg T)
  exact (asymptoticRank_le_rank _).trans (by exact_mod_cast rank_diagonal_le (R := F) (I := I) l)

private theorem tendsto_ceil_quotient (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) (x : ℝ)
    (ht : Tendsto (fun n : ℕ => f n / ((n : ℝ) + 1)) atTop (𝓝 x)) :
    Tendsto (fun n : ℕ => (⌈f n⌉₊ : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 x) := by
  have hi : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have hd : Tendsto (fun n : ℕ => ((⌈f n⌉₊ : ℝ) - f n) / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    apply squeeze_zero _ _ hi
    · intro n
      exact div_nonneg (sub_nonneg.mpr (Nat.le_ceil _)) (by positivity)
    · intro n
      apply div_le_div_of_nonneg_right _ (by positivity)
      have h := Nat.ceil_lt_add_one (hf n)
      linarith
  have h := (hd.add ht).congr (fun n => show
    ((⌈f n⌉₊ : ℝ) - f n) / ((n : ℝ) + 1) + f n / ((n : ℝ) + 1) =
      (⌈f n⌉₊ : ℝ) / ((n : ℝ) + 1) by ring)
  simpa using h

theorem asymptoticRank_copies (l : ℕ) (hl : 0 < l) (T : Tensor F I V)
    (i j : I) (hji : j ≠ i) : asymptoticRank (copies l T) = (l : ℝ) * asymptoticRank T := by
  apply le_antisymm (asymptoticRank_copies_le l T)
  by_cases hT : T = 0
  · subst T
    simp
  have hmono := (restricts_copies l hl T).asymptoticRank_le
  by_cases hl1 : l = 1
  · subst l
    simpa using hmono
  let ρ := asymptoticRank T
  let A := asymptoticRank (copies l T)
  change (l : ℝ) * ρ ≤ A
  have hρ1 : 1 ≤ ρ := one_le_asymptoticRank hT
  have hρpos : 0 < ρ := zero_lt_one.trans_le hρ1
  have hApos : 0 < A := hρpos.trans_le hmono
  by_cases hρ : ρ = 1
  · have hbase := (diagonal_restricts_copies l hT).asymptoticRank_le
    rw [asymptoticRank_diagonal l i j hji] at hbase
    simpa only [hρ, mul_one] using hbase
  have hlpos : 0 < (l : ℝ) := by exact_mod_cast hl
  have hlogl : 0 < Real.log (l : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < l))
  have hlogρ : 0 < Real.log ρ := Real.log_pos (lt_of_le_of_ne hρ1 (Ne.symm hρ))
  have hr1 (n : ℕ) : 1 ≤ rank (power T (n + 1)) := by
    apply Nat.one_le_iff_ne_zero.mpr
    exact fun hz => power_ne_zero hT n ((rank_eq_zero_iff _).mp hz)
  have hrpos (n : ℕ) : 0 < (rank (power T (n + 1)) : ℝ) := by
    exact_mod_cast zero_lt_one.trans_le (hr1 n)
  let f (n : ℕ) : ℝ := Real.log (rank (power T (n + 1)) : ℝ) / Real.log (l : ℝ)
  let q (n : ℕ) : ℕ := ⌈f n⌉₊
  have hf (n : ℕ) : 0 ≤ f n :=
    div_nonneg (Real.log_nonneg (by exact_mod_cast hr1 n)) hlogl.le
  have hnorm : Tendsto (fun n : ℕ => Real.log (rank (power T (n + 1)) : ℝ) /
      ((n : ℝ) + 1)) atTop (𝓝 (Real.log ρ)) := by
    apply ((tendsto_rankRoot T).log hρpos.ne').congr
    intro n
    rw [rankRoot, Real.log_rpow (hrpos n), div_eq_mul_inv, mul_comm]
  have hflim : Tendsto (fun n : ℕ => f n / ((n : ℝ) + 1))
      atTop (𝓝 (Real.log ρ / Real.log (l : ℝ))) := by
    apply (hnorm.div_const (Real.log (l : ℝ))).congr
    intro n
    dsimp [f]
    ring
  have hqlim := tendsto_ceil_quotient f hf _ hflim
  have hbound (n : ℕ) : rank (power T (n + 1)) ≤ l ^ q n := by
    have hlog := mul_le_mul_of_nonneg_right (Nat.le_ceil (f n)) hlogl.le
    change (Real.log (rank (power T (n + 1)) : ℝ) / Real.log (l : ℝ)) * Real.log (l : ℝ) ≤ _ at hlog
    rw [div_mul_cancel₀ _ hlogl.ne'] at hlog
    have hr : (rank (power T (n + 1)) : ℝ) ≤ (l : ℝ) ^ q n :=
      (Real.log_le_log_iff (hrpos n) (pow_pos hlpos _)).mp
        (by simpa only [Real.log_pow] using hlog)
    exact_mod_cast hr
  have hseq (n : ℕ) : Real.log ρ ≤ ((q n : ℝ) / ((n : ℝ) + 1)) * (Real.log A - Real.log ρ) := by
    have h := (power_restricts_copies_power l (n + 1) (q n) T (hbound n)).asymptoticRank_le
    rw [asymptoticRank_power, asymptoticRank_power] at h
    change ρ ^ (n + 1 + q n) ≤ A ^ q n at h
    have he := Real.log_le_log (pow_pos hρpos _) h
    rw [Real.log_pow, Real.log_pow] at he
    simp only [Nat.cast_add, Nat.cast_one] at he
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by positivity : 0 < (n : ℝ) + 1)).mpr
    nlinarith
  have hlim : Real.log ρ ≤ (Real.log ρ / Real.log (l : ℝ)) * (Real.log A - Real.log ρ) :=
    ge_of_tendsto' (hqlim.mul_const (Real.log A - Real.log ρ)) hseq
  have hh := mul_le_mul_of_nonneg_right hlim hlogl.le
  have he : (Real.log ρ / Real.log (l : ℝ)) * (Real.log A - Real.log ρ) * Real.log (l : ℝ) =
      Real.log ρ * (Real.log A - Real.log ρ) := by
    calc
      _ = (Real.log ρ / Real.log (l : ℝ)) * Real.log (l : ℝ) * (Real.log A - Real.log ρ) := by ring
      _ = _ := by rw [div_mul_cancel₀ _ hlogl.ne']
  rw [he] at hh
  have hlogs := (mul_le_mul_iff_right₀ hlogρ).mp hh
  apply (Real.log_le_log_iff (mul_pos hlpos hρpos) hApos).mp
  rw [Real.log_mul hlpos.ne' hρpos.ne']
  linarith

end Field

end Lemmata.TensorRank.Tensor
