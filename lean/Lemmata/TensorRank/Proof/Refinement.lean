module

public import Lemmata.TensorRank.Proof.Star
public import Lemmata.TensorRank.Proof.Consequence
public import Lemmata.TensorRank.Proof.GraphCut
public import Mathlib.Algebra.Order.Floor.Semiring

@[expose] public section

set_option autoImplicit false

open Filter
open scoped Topology BigOperators
open Classical

namespace Lemmata.TensorRank.Tensor

def group {R I : Type*} {J : I → Type*} {V : (p : Sigma J) → Type*}
    (T : Tensor R (Sigma J) V) : Tensor R I (fun i => ∀ j, V ⟨i, j⟩) :=
  fun x => T (fun p => x p.1 p.2)

theorem RankLE.group {R I : Type*} [CommSemiring R] [Fintype I]
    {J : I → Type*} [∀ i, Fintype (J i)] {V : (p : Sigma J) → Type*}
    {T : Tensor R (Sigma J) V} {r : ℕ} (h : RankLE T r) : RankLE (group T) r := by
  obtain ⟨c, v, h⟩ := h
  refine ⟨c, fun a i x => ∏ j, v a ⟨i, j⟩ (x j), ?_⟩
  funext x
  change T (fun p => x p.1 p.2) = _
  rw [congrFun h]
  simp only [pure, Fintype.prod_sigma]

theorem power_group_reindex {R I : Type*} [CommMonoid R] {J : I → Type*}
    {V : (p : Sigma J) → Type*} (T : Tensor R (Sigma J) V) (n : ℕ) :
    reindex (fun i => Equiv.piComm (fun (_ : Fin n) j => V ⟨i, j⟩))
      (group (power T n)) = power (group T) n := rfl

theorem rank_group_le {R I : Type*} [CommSemiring R] [Fintype I]
    {J : I → Type*} [∀ i, Fintype (J i)] [∀ i, DecidableEq (J i)]
    {V : (p : Sigma J) → Type*} [∀ p, Fintype (V p)] (T : Tensor R (Sigma J) V) :
    rank (group T) ≤ rank T :=
  (rank_le_iff _ _).mpr (rankLE_rank T).group

theorem asymptoticRank_group_le {R I : Type*} [CommSemiring R] [Fintype I]
    {J : I → Type*} [∀ i, Fintype (J i)] [∀ i, DecidableEq (J i)]
    {V : (p : Sigma J) → Type*} [∀ p, Fintype (V p)] (T : Tensor R (Sigma J) V) :
    asymptoticRank (group T) ≤ asymptoticRank T := by
  apply ciInf_mono ⟨0, by rintro _ ⟨n, rfl⟩; exact rankRoot_nonneg _ n⟩
  intro n
  apply Real.rpow_le_rpow (Nat.cast_nonneg _)
  · have h := rank_group_le (power T (n + 1))
    rw [← rank_reindex (fun i => Equiv.piComm (fun (_ : Fin (n + 1)) j => V ⟨i, j⟩)),
      power_group_reindex] at h
    exact_mod_cast h
  · positivity

noncomputable def pad {R I : Type*} [Zero R] {V W : I → Type*}
    (e : ∀ i, V i ↪ W i) (T : Tensor R I V) : Tensor R I W :=
  Function.extend (fun x i => e i (x i)) T 0

theorem reindex_pad {R I : Type*} [Zero R] {V W : I → Type*}
    (e : ∀ i, V i ↪ W i) (T : Tensor R I V) : reindex (fun i => e i) (pad e T) = T := by
  have hinj : Function.Injective (fun (x : ∀ i, V i) i => e i (x i)) := by
    intro x y h
    exact funext (fun i => (e i).injective (congrFun h i))
  exact funext (fun x => hinj.extend_apply T 0 x)

end Lemmata.TensorRank.Tensor

namespace Lemmata.TensorRank

private theorem binary_bound
    (hg : ∀ k, 2 ≤ k → graphExponent k ≤ (k : ℝ) ^ 2 / 4)
    {k : ℕ} (hk : 2 ≤ k) (T : Tensor ℂ (Fin k) (fun _ => Fin 2)) :
    Tensor.asymptoticRank T ≤ (2 : ℝ) ^ ((k : ℝ) / 2) := by
  apply (asymptoticRank_le_graphExponent hk (by decide) T).trans
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
  have hk0 : 0 < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  apply (div_le_iff₀ hk0).mpr
  nlinarith [hg k hk]

private theorem binary_refinement
    (hg : ∀ k, 2 ≤ k → graphExponent k ≤ (k : ℝ) ^ 2 / 4)
    {I : Type} [Fintype I] {V : I → Type} [∀ i, Fintype (V i)]
    (b : I → ℕ) (hb : 2 ≤ ∑ i, b i) (e : ∀ i, V i ↪ (Fin (b i) → Fin 2))
    (T : Tensor ℂ I V) :
    Tensor.asymptoticRank T ≤ (2 : ℝ) ^ (((∑ i, b i : ℕ) : ℝ) / 2) := by
  let P := Sigma (fun i => Fin (b i))
  let U : Tensor ℂ P (fun _ => Fin 2) := fun x => Tensor.pad e T (fun i j => x ⟨i, j⟩)
  have hpad : Tensor.group U = Tensor.pad e T := rfl
  have hT := (Tensor.reindex_restricts (fun i => e i) (Tensor.pad e T)).asymptoticRank_le
  rw [Tensor.reindex_pad] at hT
  have hgroup := Tensor.asymptoticRank_group_le U
  rw [hpad] at hgroup
  let f := (Fintype.equivFin P).symm
  have hc : Fintype.card P = ∑ i, b i := by simp [P]
  have hbin := binary_bound hg (show 2 ≤ Fintype.card P by omega) (Tensor.relabel f U)
  have hb' : Tensor.asymptoticRank U ≤ (2 : ℝ) ^ ((Fintype.card P : ℝ) / 2) :=
    (Tensor.asymptoticRank_relabel f U).symm.trans_le hbin
  rw [hc] at hb'
  exact hT.trans (hgroup.trans hb')

noncomputable def bitBudget (n q : ℕ) : ℕ :=
  2 + ⌈(q : ℝ) * Real.log n / Real.log 2⌉₊

theorem bitBudget_size {n : ℕ} (hn : 0 < n) (q : ℕ) :
    n ^ q ≤ 2 ^ bitBudget n q := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hc := (div_le_iff₀ hl).mp (Nat.le_ceil ((q : ℝ) * Real.log n / Real.log 2))
  have hb : (⌈(q : ℝ) * Real.log n / Real.log 2⌉₊ : ℝ) ≤ bitBudget n q := by
    exact_mod_cast (show ⌈(q : ℝ) * Real.log n / Real.log 2⌉₊ ≤ bitBudget n q by
      unfold bitBudget
      omega)
  have hlog : Real.log ((n : ℝ) ^ q) ≤ Real.log ((2 : ℝ) ^ bitBudget n q) := by
    rw [Real.log_pow, Real.log_pow]
    exact hc.trans (mul_le_mul_of_nonneg_right hb hl.le)
  exact_mod_cast (Real.log_le_log_iff (pow_pos hn' _) (pow_pos (by norm_num) _)).mp hlog

theorem bitBudget_log_le {n : ℕ} (hn : 0 < n) (q : ℕ) :
    (bitBudget n q : ℝ) * Real.log 2 ≤ (q : ℝ) * Real.log n + 3 * Real.log 2 := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hnonneg : 0 ≤ (q : ℝ) * Real.log n / Real.log 2 :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg _)
      (Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega)))) hl.le
  have hc := mul_le_mul_of_nonneg_right (Nat.ceil_lt_add_one hnonneg).le hl.le
  rw [add_mul, div_mul_cancel₀ _ hl.ne'] at hc
  dsimp only [bitBudget]
  push_cast
  linarith

noncomputable def embeddingOfSize {A B : Type*} [Fintype A] [Fintype B]
    (h : Fintype.card A ≤ Fintype.card B) : A ↪ B :=
  (Fintype.equivFin A).toEmbedding.trans
    ((Fin.castLEEmb h).trans (Fintype.equivFin B).symm.toEmbedding)

theorem squareRoot_of_graphExponentBound
    (hg : ∀ k, 2 ≤ k → graphExponent k ≤ (k : ℝ) ^ 2 / 4) : SquareRootBound := by
  intro I _ _ V _ T
  by_cases hT : T = 0
  · rw [hT, Tensor.asymptoticRank_zero]
    exact Real.sqrt_nonneg _
  have hd (i : I) : 0 < Fintype.card (V i) := by
    by_contra hi
    have he := Fintype.card_eq_zero_iff.mp (show Fintype.card (V i) = 0 by omega)
    apply hT
    exact funext (fun x => (he.false (x i)).elim)
  have ha : 0 < Tensor.asymptoticRank T :=
    zero_lt_one.trans_le (Tensor.one_le_asymptoticRank hT)
  let L : ℝ := ∑ i, Real.log (Fintype.card (V i))
  let C : ℝ := 3 * Fintype.card I * Real.log 2 / 2
  have hfinite (q : ℕ) (hq : 0 < q) :
      Real.log (Tensor.asymptoticRank T) ≤ L / 2 + C / q := by
    let b (i : I) := bitBudget (Fintype.card (V i)) q
    have hb : 2 ≤ ∑ i, b i := by
      let i : I := Classical.arbitrary I
      have hi : b i ≤ ∑ j, b j := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      have hbi : 2 ≤ b i := by dsimp [b, bitBudget]; omega
      exact hbi.trans hi
    let enc (i : I) : (Fin q → V i) ↪ (Fin (b i) → Fin 2) :=
      embeddingOfSize (by simpa only [Fintype.card_fun, Fintype.card_fin] using bitBudget_size (hd i) q)
    have h := binary_refinement hg b hb enc (Tensor.power T q)
    rw [Tensor.asymptoticRank_power] at h
    have hlog := Real.log_le_log (pow_pos ha q) h
    rw [Real.log_pow, Real.log_rpow (by norm_num : (0 : ℝ) < 2)] at hlog
    have hs : ((∑ i, b i : ℕ) : ℝ) * Real.log 2 ≤ (q : ℝ) * L + 2 * C := by
      rw [Nat.cast_sum, Finset.sum_mul]
      calc
        _ ≤ ∑ i, ((q : ℝ) * Real.log (Fintype.card (V i)) + 3 * Real.log 2) :=
          Finset.sum_le_sum (fun i _ => bitBudget_log_le (hd i) q)
        _ = _ := by
          simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
            Finset.card_univ, nsmul_eq_mul, L, C]
          ring
    have hq' : 0 < (q : ℝ) := by exact_mod_cast hq
    have hdiv : (L / 2 + C / (q : ℝ)) * q = (q : ℝ) * L / 2 + C := by
      field_simp [ne_of_gt hq']
    apply (mul_le_mul_iff_left₀ hq').mp
    rw [hdiv]
    nlinarith
  have hlim : Tendsto (fun q : ℕ => L / 2 + C / (q : ℝ)) atTop (𝓝 (L / 2)) := by
    have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => L / 2) atTop (𝓝 (L / 2))).add
      (tendsto_one_div_atTop_nhds_zero_nat.const_mul C)
    simpa [div_eq_mul_inv] using h
  have hlog : Real.log (Tensor.asymptoticRank T) ≤ L / 2 :=
    ge_of_tendsto hlim (by
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with q hq
      exact hfinite q hq)
  have hp : 0 < ∏ i, (Fintype.card (V i) : ℝ) :=
    Finset.prod_pos (fun i _ => by exact_mod_cast hd i)
  apply (Real.log_le_log_iff ha (Real.sqrt_pos.mpr hp)).mp
  rw [Real.log_sqrt hp.le, Real.log_prod (fun i _ => by exact_mod_cast (Nat.ne_of_gt (hd i)))]
  exact hlog

theorem completeGraphBounds_of_graphExponentBound
    (hg : ∀ k, 2 ≤ k → graphExponent k ≤ (k : ℝ) ^ 2 / 4) : CompleteGraphBounds := by
  intro k n hk hn
  refine ⟨completeGraph_balanced_lower (by omega), ?_⟩
  by_cases h1 : n = 1
  · subst n
    simp only [Nat.cast_one, Real.one_rpow]
    exact (asymptoticRank_completeGraph_one k).le
  · rw [asymptoticRank_completeGraph (show 2 ≤ n by omega)]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (hg k hk)

theorem evenCompleteGraphRank_of_graphExponentBound
    (hg : ∀ k, 2 ≤ k → graphExponent k ≤ (k : ℝ) ^ 2 / 4) : EvenCompleteGraphRank := by
  intro r n hr hn
  have h := completeGraphBounds_of_graphExponentBound hg (2 * r) n (by omega) hn
  have he : (2 * r) * (2 * r) / 4 = r ^ 2 := by
    have hp : (2 * r) * (2 * r) = 4 * r ^ 2 := by ring
    rw [hp]
    omega
  apply le_antisymm
  · calc
      _ ≤ (n : ℝ) ^ (((2 * r : ℕ) : ℝ) ^ 2 / 4) := h.2
      _ = (n : ℝ) ^ (r ^ 2) := by
        rw [← Real.rpow_natCast (n : ℝ) (r ^ 2)]
        congr 1
        push_cast
        ring
  · simpa only [he, Real.rpow_natCast] using h.1

end Lemmata.TensorRank
