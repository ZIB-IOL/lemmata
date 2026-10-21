module

public import Lemmata.TensorRank.Proof.GraphRank
public import Lemmata.TensorRank.Proof.Growth
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Tactic.Ring

@[expose] public section

set_option autoImplicit false

open Filter Set
open scoped Topology
open Classical

namespace Lemmata.TensorRank

theorem one_le_rank_completeGraph {k n : ℕ} (hn : 0 < n) :
    1 ≤ Tensor.rank (completeGraph k n) := by
  apply Nat.one_le_iff_ne_zero.mpr
  exact fun h => completeGraph_ne_zero hn ((Tensor.rank_eq_zero_iff _).mp h)

private theorem ratio_nonneg (k : ℕ) {n : ℕ} (hn : 2 ≤ n) :
    0 ≤ Real.log (Tensor.rank (completeGraph k n) : ℝ) / Real.log (n : ℝ) := by
  have hn0 : 0 < n := lt_of_lt_of_le (by decide : 0 < (2 : ℕ)) hn
  exact div_nonneg (Real.log_nonneg (by exact_mod_cast one_le_rank_completeGraph hn0))
    (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n)))

theorem graphExponent_nonneg (k : ℕ) : 0 ≤ graphExponent k := by
  let : Nonempty {n : ℕ // 2 ≤ n} := ⟨⟨2, by decide⟩⟩
  apply le_ciInf
  intro n
  exact ratio_nonneg k n.prop

theorem graphExponent_le_log_rank (k : ℕ) {n : ℕ} (hn : 2 ≤ n) :
    graphExponent k ≤ Real.log (Tensor.rank (completeGraph k n) : ℝ) / Real.log (n : ℝ) := by
  unfold graphExponent
  refine ciInf_le (f := fun d : {n : ℕ // 2 ≤ n} =>
    Real.log (Tensor.rank (completeGraph k d.val) : ℝ) / Real.log (d.val : ℝ)) ?_ ⟨n, hn⟩
  refine ⟨0, ?_⟩
  rintro x ⟨d, rfl⟩
  exact ratio_nonneg k d.prop

private theorem asymptoticRank_completeGraph_le_rank_power {k b d : ℕ}
    (hb : 2 ≤ b) (hd : 2 ≤ d) :
    Tensor.asymptoticRank (completeGraph k b) ≤
      (b : ℝ) ^ (Real.log (Tensor.rank (completeGraph k d) : ℝ) / Real.log (d : ℝ)) := by
  have hb0 : 0 < b := by omega
  have hd0 : 0 < d := by omega
  have hbpos : 0 < (b : ℝ) := by exact_mod_cast hb0
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast hd0
  have hlb : 0 < Real.log (b : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < b))
  have hld : 0 < Real.log (d : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < d))
  let r : ℝ := Tensor.rank (completeGraph k d)
  let a : ℝ := Real.log (b : ℝ) / Real.log (d : ℝ)
  have hr : 1 ≤ r := by
    change 1 ≤ (Tensor.rank (completeGraph k d) : ℝ)
    exact_mod_cast one_le_rank_completeGraph hd0
  have hrpos : 0 < r := zero_lt_one.trans_le hr
  have ha : 0 < a := div_pos hlb hld
  have hbound : ∀ n : ℕ, 0 < n → (Tensor.rank (Tensor.power (completeGraph k b) n) : ℝ) ≤
      r * ((n : ℝ) + 1) ^ 0 * (r ^ a) ^ n := by
    intro n _
    let q : ℕ := ⌈(n : ℝ) * a⌉₊
    have hdim : b ^ n ≤ d ^ q := by
      have hlog : (n : ℝ) * Real.log (b : ℝ) ≤ (q : ℝ) * Real.log (d : ℝ) := by
        have h := mul_le_mul_of_nonneg_right (Nat.le_ceil ((n : ℝ) * a)) hld.le
        change (n : ℝ) * (Real.log (b : ℝ) / Real.log (d : ℝ)) * Real.log (d : ℝ) ≤ _ at h
        rw [mul_assoc, div_mul_cancel₀ _ hld.ne'] at h
        exact h
      have hreal : (b : ℝ) ^ n ≤ (d : ℝ) ^ q :=
        (Real.log_le_log_iff (pow_pos hbpos n) (pow_pos hdpos q)).mp
          (by simpa only [Real.log_pow] using hlog)
      exact_mod_cast hreal
    have hrank : Tensor.rank (Tensor.power (completeGraph k b) n) ≤
        Tensor.rank (completeGraph k d) ^ q := by
      calc
        Tensor.rank (Tensor.power (completeGraph k b) n) =
            Tensor.rank (completeGraph k (b ^ n)) := (rank_completeGraph_power k b n).symm
        _ ≤ Tensor.rank (completeGraph k (d ^ q)) := rank_completeGraph_mono hdim
        _ = Tensor.rank (Tensor.power (completeGraph k d) q) := rank_completeGraph_power k d q
        _ ≤ Tensor.rank (completeGraph k d) ^ q := Tensor.rank_power_le _ q
    have hcast : (Tensor.rank (Tensor.power (completeGraph k b) n) : ℝ) ≤ r ^ q := by
      change (Tensor.rank (Tensor.power (completeGraph k b) n) : ℝ) ≤
        (Tensor.rank (completeGraph k d) : ℝ) ^ q
      exact_mod_cast hrank
    have hq : (q : ℝ) ≤ (n : ℝ) * a + 1 :=
      (Nat.ceil_lt_add_one (mul_nonneg (Nat.cast_nonneg n) ha.le)).le
    have hpow : r ^ q ≤ r * (r ^ a) ^ n := by
      calc
        r ^ q = r ^ (q : ℝ) := (Real.rpow_natCast r q).symm
        _ ≤ r ^ ((n : ℝ) * a + 1) := Real.rpow_le_rpow_of_exponent_le hr hq
        _ = r * (r ^ a) ^ n := by
          rw [Real.rpow_add hrpos, Real.rpow_one, mul_comm (n : ℝ) a,
            Real.rpow_mul_natCast hrpos.le a n, mul_comm]
    simpa only [pow_zero, mul_one] using hcast.trans hpow
  have h := Tensor.asymptoticRank_le_of_polynomial_power_bound (completeGraph k b)
    r (r ^ a) hrpos (Real.rpow_nonneg hrpos.le _) 0 hbound
  have he : r ^ a = (b : ℝ) ^ (Real.log r / Real.log (d : ℝ)) := by
    rw [Real.rpow_def_of_pos hrpos, Real.rpow_def_of_pos hbpos]
    congr 1
    dsimp [a]
    ring
  exact h.trans_eq he

theorem graphExponent_le_log_asymptoticRank {k b : ℕ} (hb : 2 ≤ b) :
    graphExponent k ≤
      Real.log (Tensor.asymptoticRank (completeGraph k b)) / Real.log (b : ℝ) := by
  have hb0 : 0 < b := by omega
  have hlb : Real.log (b : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast (by omega : 1 < b)))
  have ht := Tensor.tendsto_rankRoot (completeGraph k b)
  have hpos : 0 < Tensor.asymptoticRank (completeGraph k b) :=
    zero_lt_one.trans_le (Tensor.one_le_asymptoticRank (completeGraph_ne_zero hb0))
  apply ge_of_tendsto' ((ht.log hpos.ne').div_const (Real.log (b : ℝ)))
  intro n
  have hbn : 2 ≤ b ^ (n + 1) := hb.trans (Nat.le_self_pow (Nat.succ_ne_zero n) b)
  have hr1 := one_le_rank_completeGraph (k := k) (pow_pos hb0 (n + 1))
  rw [rank_completeGraph_power] at hr1
  have hrpos : 0 < (Tensor.rank (Tensor.power (completeGraph k b) (n + 1)) : ℝ) := by
    exact_mod_cast zero_lt_one.trans_le hr1
  calc
    graphExponent k ≤ Real.log (Tensor.rank (completeGraph k (b ^ (n + 1))) : ℝ) /
        Real.log ((b ^ (n + 1) : ℕ) : ℝ) := graphExponent_le_log_rank k hbn
    _ = Real.log (Tensor.rankRoot (completeGraph k b) n) / Real.log (b : ℝ) := by
      rw [rank_completeGraph_power, Nat.cast_pow, Real.log_pow,
        Tensor.rankRoot, Real.log_rpow hrpos, Nat.cast_add, Nat.cast_one]
      field_simp

theorem graphExponent_eq_log_asymptoticRank {k b : ℕ} (hb : 2 ≤ b) :
    graphExponent k =
      Real.log (Tensor.asymptoticRank (completeGraph k b)) / Real.log (b : ℝ) := by
  apply le_antisymm (graphExponent_le_log_asymptoticRank hb)
  let : Nonempty {n : ℕ // 2 ≤ n} := ⟨⟨2, by decide⟩⟩
  apply le_ciInf
  intro d
  have hb0 : 0 < (b : ℝ) := by exact_mod_cast (by omega : 0 < b)
  have hlb : 0 < Real.log (b : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < b))
  have hpos : 0 < Tensor.asymptoticRank (completeGraph k b) :=
    zero_lt_one.trans_le (Tensor.one_le_asymptoticRank (completeGraph_ne_zero (by omega)))
  apply (div_le_iff₀ hlb).mpr
  have h := Real.log_le_log hpos (asymptoticRank_completeGraph_le_rank_power hb d.prop)
  rwa [Real.log_rpow hb0] at h

theorem asymptoticRank_completeGraph {k b : ℕ} (hb : 2 ≤ b) :
    Tensor.asymptoticRank (completeGraph k b) = (b : ℝ) ^ graphExponent k := by
  have hb0 : 0 < (b : ℝ) := by exact_mod_cast (by omega : 0 < b)
  have hlb : Real.log (b : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast (by omega : 1 < b)))
  have hpos : 0 < Tensor.asymptoticRank (completeGraph k b) :=
    zero_lt_one.trans_le (Tensor.one_le_asymptoticRank (completeGraph_ne_zero (by omega)))
  rw [Real.rpow_def_of_pos hb0, graphExponent_eq_log_asymptoticRank hb,
    mul_comm, div_mul_cancel₀ _ hlb, Real.exp_log hpos]

theorem edgeExponent_nonneg (k : ℕ) : 0 ≤ edgeExponent k :=
  div_nonneg (graphExponent_nonneg k) (Nat.cast_nonneg _)

theorem edgeExponent_le_iff {k : ℕ} (hk : 2 ≤ k) (a : ℝ) :
    edgeExponent k ≤ a ↔ graphExponent k ≤ (k.choose 2 : ℝ) * a := by
  have hpos : 0 < (k.choose 2 : ℝ) := by exact_mod_cast Nat.choose_pos hk
  simpa only [edgeExponent, mul_comm] using (div_le_iff₀ hpos :
    graphExponent k / (k.choose 2 : ℝ) ≤ a ↔ graphExponent k ≤ a * (k.choose 2 : ℝ))

end Lemmata.TensorRank
