module

public import Lemmata.FishburnReedsClassicalBound.Statement
public import Lemmata.FishburnReedsClassicalBound.Envelope
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.SplitIfs

/-! # The fixed-shift classical upper bound in every order

Maximize over Bob's signs first: `value ≤ ∑ⱼ |3 yⱼ - 4 aⱼ|` with `y = V p`, `p = Vᵀ a`.
For a sign `aⱼ`, `|3 y - 4 aⱼ| = max 4 (6 aⱼ y - 4) - 3 aⱼ y`, and `∑ⱼ aⱼ yⱼ = ‖p‖²`.
Every coordinate of `p` is even, being a sum of `2(d-1)` signs, so the envelope
`∑ⱼ max 4 (6 |yⱼ| - 4) - 3 ‖p‖²` is the quantity bounded in `Envelope.lean`. Its single
excess, two vanishing coordinates, forces a row whose sign disagrees with its value, and that
row loses at least four. -/

@[expose] public section

namespace Lemmata.FishburnReedsClassicalBound

open scoped BigOperators
open Envelope

/-- The lower index of a pair, as a coordinate. -/
def low {d : ℕ} (i : Fin d) (j : Fin i.val) : Fin d := ⟨j.val, lt_trans j.isLt i.isLt⟩

theorem low_lt {d : ℕ} (i : Fin d) (j : Fin i.val) : low i j < i := j.isLt

/-- Integer version of the root rows `e_i ± e_j`. -/
def rootsZ (d : ℕ) (r : Root d) (k : Fin d) : ℤ :=
  (if k = r.1 then 1 else 0) + (if k.val = r.2.1.val then (if r.2.2 then 1 else -1) else 0)

theorem roots_cast (d : ℕ) (r : Root d) (k : Fin d) : roots d r k = (rootsZ d r k : ℝ) := by
  unfold roots rootsZ
  split_ifs <;> norm_num

theorem rootsZ_pair (d : ℕ) (i : Fin d) (j : Fin i.val) (b : Bool) (k : Fin d) :
    rootsZ d ⟨i, (j, b)⟩ k =
      (if k = i then 1 else 0) + (if k = low i j then (if b then 1 else -1) else 0) := by
  unfold rootsZ low
  simp only [Fin.ext_iff]

theorem sum_root {M : Type*} [AddCommMonoid M] {d : ℕ} (f : Root d → M) :
    ∑ r, f r = ∑ i : Fin d, ∑ j : Fin i.val, (f ⟨i, (j, true)⟩ + f ⟨i, (j, false)⟩) := by
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_bool]

/-- The signed row sums `p = Vᵀ a`, for integer signs. -/
def pZ (d : ℕ) (a : Root d → ℤ) (k : Fin d) : ℤ := ∑ r, a r * rootsZ d r k

/-- The row values `y = V p`. -/
def yZ (d : ℕ) (a : Root d → ℤ) (r : Root d) : ℤ := ∑ k, rootsZ d r k * pZ d a k

theorem yZ_pair (d : ℕ) (a : Root d → ℤ) (i : Fin d) (j : Fin i.val) (b : Bool) :
    yZ d a ⟨i, (j, b)⟩ = pZ d a i + (if b then 1 else -1) * pZ d a (low i j) := by
  unfold yZ
  simp_rw [rootsZ_pair, add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- Each pair of rows contributes an even amount to every coordinate of `p`. -/
theorem pZ_even (d : ℕ) (a : Root d → ℤ) (ha : ∀ r, a r = 1 ∨ a r = -1) (k : Fin d) :
    2 ∣ pZ d a k := by
  unfold pZ
  rw [sum_root]
  refine Finset.dvd_sum fun i _ => Finset.dvd_sum fun j _ => ?_
  rw [rootsZ_pair, rootsZ_pair]
  rcases ha ⟨i, (j, true)⟩ with h1 | h1 <;> rcases ha ⟨i, (j, false)⟩ with h2 | h2 <;>
    rw [h1, h2] <;> split_ifs <;> decide

/-! ### The envelope of one pair of rows -/

/-- For `p_i = 2u`, `p_j = 2v`, the two rows `e_i ± e_j` contribute `pairW |u| |v|`. -/
theorem pair_envelope (u v : ℤ) :
    max 4 (6 * |2 * u + 1 * (2 * v)| - 4) + max 4 (6 * |2 * u + -1 * (2 * v)| - 4) =
      pairW u.natAbs v.natAbs := by
  unfold pairW
  push_cast
  simp only [Int.abs_eq_natAbs]
  split_ifs <;> omega

/-- The pair sums of `Envelope` over the rows of the root matrix. -/
theorem pairSum_ofFn {g : ℕ → ℕ → ℤ} (hg : ∀ x y, g x y = g y x) :
    ∀ (d : ℕ) (n : Fin d → ℕ),
      ∑ i : Fin d, ∑ j : Fin i.val, g (n i) (n (low i j)) = pairSum g (List.ofFn n) := by
  intro d
  induction d with
  | zero => intro n; simp [pairSum]
  | succ d ih =>
    intro n
    rw [Fin.sum_univ_castSucc, List.ofFn_succ', List.concat_eq_append, pairSum_append]
    have h1 : ∑ i : Fin d, ∑ j : Fin (Fin.castSucc i).val,
        g (n i.castSucc) (n (low i.castSucc j)) = pairSum g (List.ofFn fun i => n i.castSucc) := by
      rw [← ih]
      rfl
    have h2 : ∑ j : Fin (Fin.last d).val, g (n (Fin.last d)) (n (low (Fin.last d) j)) =
        ((List.ofFn fun i => n i.castSucc).map
          fun x => ([n (Fin.last d)].map (g x)).sum).sum := by
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
        List.map_ofFn, List.sum_ofFn, Function.comp_def]
      exact Finset.sum_congr rfl fun j _ => hg _ _
    rw [h1, h2]
    simp [pairSum]

theorem count_ofFn {d : ℕ} (n : Fin d → ℕ) (c : ℕ) :
    (List.ofFn n).count c = (Finset.univ.filter fun k => n k = c).card := by
  rw [Finset.card_filter]
  induction d with
  | zero => simp
  | succ d ih =>
    rw [List.ofFn_succ, List.count_cons, ih, Fin.sum_univ_succ]
    simp only [beq_iff_eq]
    omega

/-! ### Agreement and the two-zero case -/

/-- The contribution of the two rows of the pair `(i, j)` to the coordinate `k` of `p`. -/
def pairPart (d : ℕ) (a : Root d → ℤ) (i : Fin d) (j : Fin i.val) (k : Fin d) : ℤ :=
  a ⟨i, (j, true)⟩ * rootsZ d ⟨i, (j, true)⟩ k + a ⟨i, (j, false)⟩ * rootsZ d ⟨i, (j, false)⟩ k

theorem pZ_eq_pairs (d : ℕ) (a : Root d → ℤ) (k : Fin d) :
    pZ d a k = ∑ i : Fin d, ∑ j : Fin i.val, pairPart d a i j k := by
  unfold pZ pairPart
  rw [sum_root]

/-- If every row's sign agrees with its value, a pair through a vanishing coordinate `k`
whose other end does not vanish contributes nothing to `p_k`. -/
theorem pairPart_vanish (d : ℕ) (a : Root d → ℤ) (ha : ∀ r, a r = 1 ∨ a r = -1)
    (hagree : ∀ r, 0 ≤ a r * yZ d a r) (k : Fin d) (hk : pZ d a k = 0)
    (i : Fin d) (j : Fin i.val)
    (h : (i = k ∧ pZ d a (low i j) ≠ 0) ∨ (low i j = k ∧ pZ d a i ≠ 0) ∨
      (i ≠ k ∧ low i j ≠ k)) :
    pairPart d a i j k = 0 := by
  have hne : low i j ≠ i := ne_of_lt (low_lt i j)
  have ht := hagree ⟨i, (j, true)⟩
  have hf := hagree ⟨i, (j, false)⟩
  rw [yZ_pair] at ht hf
  unfold pairPart
  rw [rootsZ_pair, rootsZ_pair]
  rcases h with ⟨rfl, hp⟩ | ⟨rfl, hp⟩ | ⟨h1, h2⟩
  · rw [hk] at ht hf
    simp only [hne.symm, ite_true, ite_false, Bool.false_eq_true, add_zero, zero_add]
      at ht hf ⊢
    rcases ha ⟨i, (j, true)⟩ with h1 | h1 <;> rcases ha ⟨i, (j, false)⟩ with h2 | h2 <;>
      simp only [h1, h2] at ht hf ⊢ <;> omega
  · rw [hk] at ht hf
    simp only [hne, ite_true, ite_false, Bool.false_eq_true, add_zero, zero_add, mul_zero]
      at ht hf ⊢
    rcases ha ⟨i, (j, true)⟩ with h1 | h1 <;> rcases ha ⟨i, (j, false)⟩ with h2 | h2 <;>
      simp only [h1, h2] at ht hf ⊢ <;> omega
  · simp [h1, h2, Ne.symm h1, Ne.symm h2]

/-- With exactly two vanishing coordinates, some row's sign disagrees with its value. -/
theorem two_zero_disagree (d : ℕ) (a : Root d → ℤ) (ha : ∀ r, a r = 1 ∨ a r = -1)
    (lo hi : Fin d) (hlt : lo < hi) (hlo : pZ d a lo = 0) (hhi : pZ d a hi = 0)
    (honly : ∀ k, pZ d a k = 0 → k = lo ∨ k = hi) :
    ∃ r, a r * yZ d a r ≤ -2 := by
  by_contra hcon
  push_neg at hcon
  have hagree : ∀ r, 0 ≤ a r * yZ d a r := by
    intro r
    have h2 := hcon r
    have hev : 2 ∣ yZ d a r := by
      obtain ⟨i, j, b⟩ := r
      rw [yZ_pair]
      have e1 := pZ_even d a ha i
      have e2 := pZ_even d a ha (low i j)
      split_ifs <;> omega
    rcases ha r with h | h <;> rw [h] at h2 ⊢ <;> omega
  let lo' : Fin hi.val := ⟨lo.val, hlt⟩
  have hlow : low hi lo' = lo := Fin.ext rfl
  have hj_ne : ∀ j : Fin hi.val, j ≠ lo' → low hi j ≠ lo := fun j hj h =>
    hj (Fin.ext (by simpa [low, lo'] using congrArg Fin.val h))
  have hsum_hi : pZ d a hi = pairPart d a hi lo' hi := by
    rw [pZ_eq_pairs, Finset.sum_eq_single hi]
    · rw [Finset.sum_eq_single lo']
      · intro j _ hj
        refine pairPart_vanish d a ha hagree hi hhi hi j (Or.inl ⟨rfl, fun h0 => ?_⟩)
        rcases honly _ h0 with h | h
        · exact hj_ne j hj h
        · exact ne_of_lt (low_lt hi j) h
      · simp
    · intro i _ hi'
      refine Finset.sum_eq_zero fun j _ => ?_
      refine pairPart_vanish d a ha hagree hi hhi i j ?_
      by_cases hl : low i j = hi
      · refine Or.inr (Or.inl ⟨hl, fun h0 => ?_⟩)
        rcases honly _ h0 with h | h
        · have := low_lt i j
          rw [hl, h] at this
          exact absurd hlt (not_lt.mpr this.le)
        · exact hi' h
      · exact Or.inr (Or.inr ⟨hi', hl⟩)
    · simp
  have hsum_lo : pZ d a lo = pairPart d a hi lo' lo := by
    rw [pZ_eq_pairs, Finset.sum_eq_single hi]
    · rw [Finset.sum_eq_single lo']
      · intro j _ hj
        exact pairPart_vanish d a ha hagree lo hlo hi j
          (Or.inr (Or.inr ⟨ne_of_gt hlt, hj_ne j hj⟩))
      · simp
    · intro i _ hi'
      refine Finset.sum_eq_zero fun j _ => ?_
      refine pairPart_vanish d a ha hagree lo hlo i j ?_
      by_cases hil : i = lo
      · refine Or.inl ⟨hil, fun h0 => ?_⟩
        rcases honly _ h0 with h | h
        · exact ne_of_lt (low_lt i j) (h.trans hil.symm)
        · have := low_lt i j
          rw [h, hil] at this
          exact absurd hlt (not_lt.mpr this.le)
      · by_cases hl : low i j = lo
        · refine Or.inr (Or.inl ⟨hl, fun h0 => ?_⟩)
          rcases honly _ h0 with h | h
          · exact hil h
          · exact hi' h
        · exact Or.inr (Or.inr ⟨hil, hl⟩)
    · simp
  unfold pairPart at hsum_hi hsum_lo
  rw [rootsZ_pair, rootsZ_pair, hlow] at hsum_hi hsum_lo
  have hne : lo ≠ hi := ne_of_lt hlt
  simp only [hne, hne.symm, ite_true, ite_false, Bool.false_eq_true, add_zero, zero_add]
    at hsum_hi hsum_lo
  rw [hhi] at hsum_hi
  rw [hlo] at hsum_lo
  rcases ha ⟨hi, (lo', true)⟩ with h1 | h1 <;> rcases ha ⟨hi, (lo', false)⟩ with h2 | h2 <;>
    simp only [h1, h2] at hsum_hi hsum_lo <;> omega

/-! ### The upper bound -/

/-- The fixed-shift bound in integer form: every sign vector `b` against `F₄ a`. -/
theorem upperZ (d : ℕ) (a b : Root d → ℤ) (ha : ∀ r, a r = 1 ∨ a r = -1)
    (hb : ∀ r, b r = 1 ∨ b r = -1) :
    ∑ r, b r * (3 * yZ d a r - 4 * a r) ≤ bound d := by
  -- Bob's best response
  have s1 : ∑ r, b r * (3 * yZ d a r - 4 * a r) ≤ ∑ r, |3 * yZ d a r - 4 * a r| := by
    refine Finset.sum_le_sum fun r _ => ?_
    rcases hb r with h | h <;> rw [h]
    · simpa using le_abs_self (3 * yZ d a r - 4 * a r)
    · simpa using neg_le_abs (3 * yZ d a r - 4 * a r)
  -- rowwise envelope, with a loss of four for a disagreeing row
  have s2 : ∀ r, |3 * yZ d a r - 4 * a r| + 3 * (a r * yZ d a r) ≤
      max 4 (6 * |yZ d a r| - 4) - (if a r * yZ d a r ≤ -2 then 4 else 0) := by
    intro r
    rcases ha r with h | h <;> rw [h] <;> simp only [Int.abs_eq_natAbs] <;> split_ifs <;> omega
  -- `∑ a y = ‖p‖²`
  have s3 : ∑ r, a r * yZ d a r = ∑ k, pZ d a k ^ 2 := by
    have hr : ∀ r, a r * yZ d a r = ∑ k, pZ d a k * (a r * rootsZ d r k) := by
      intro r
      unfold yZ
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    simp_rw [hr]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.mul_sum, sq]
    rfl
  -- halved coordinates
  obtain ⟨z, hz⟩ : ∃ z : Fin d → ℤ, ∀ k, pZ d a k = 2 * z k :=
    ⟨fun k => pZ d a k / 2, fun k => (Int.mul_ediv_cancel' (pZ_even d a ha k)).symm⟩
  -- the envelope is `envW` of the halved magnitudes
  have s4 : ∑ r, max 4 (6 * |yZ d a r| - 4) - 3 * ∑ k, pZ d a k ^ 2 =
      envW (List.ofFn fun k => (z k).natAbs) := by
    unfold envW sqSum
    rw [← pairSum_ofFn pairW_comm d, sum_root, List.map_ofFn, List.sum_ofFn]
    simp only [yZ_pair, hz, ite_true, ite_false, Bool.false_eq_true, pair_envelope]
    congr 1
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Function.comp_apply, Int.natCast_natAbs, sq_abs]
    ring
  -- a disagreeing row in the two-zero case
  have s5 : (List.ofFn fun k => (z k).natAbs).count 0 = 2 → ∃ r, a r * yZ d a r ≤ -2 := by
    intro h2
    rw [count_ofFn, Finset.card_eq_two] at h2
    obtain ⟨k1, k2, hne, hset⟩ := h2
    have hmem : ∀ k, pZ d a k = 0 ↔ k = k1 ∨ k = k2 := by
      intro k
      have := Finset.ext_iff.mp hset k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton, Int.natAbs_eq_zero] at this
      rw [hz, ← this]
      omega
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact two_zero_disagree d a ha k1 k2 hlt ((hmem k1).2 (Or.inl rfl))
        ((hmem k2).2 (Or.inr rfl)) fun k hk => (hmem k).1 hk
    · exact two_zero_disagree d a ha k2 k1 hlt ((hmem k2).2 (Or.inr rfl))
        ((hmem k1).2 (Or.inl rfl)) fun k hk => ((hmem k).1 hk).symm
  -- assemble
  have henv := envW_le _ (List.ofFn fun k => (z k).natAbs) rfl
  rw [List.length_ofFn] at henv
  have hloss : (if (List.ofFn fun k => (z k).natAbs).count 0 = 2 then (4 : ℤ) else 0) ≤
      ∑ r, (if a r * yZ d a r ≤ -2 then (4 : ℤ) else 0) := by
    split_ifs with h
    · obtain ⟨r, hr⟩ := s5 h
      calc (4 : ℤ) = if a r * yZ d a r ≤ -2 then 4 else 0 := by simp [hr]
        _ ≤ ∑ r, (if a r * yZ d a r ≤ -2 then (4 : ℤ) else 0) :=
          Finset.single_le_sum (f := fun r => if a r * yZ d a r ≤ -2 then (4 : ℤ) else 0)
            (fun r _ => by split_ifs <;> norm_num) (Finset.mem_univ r)
    · exact Finset.sum_nonneg fun r _ => by split_ifs <;> norm_num
  have hsum2 := Finset.sum_le_sum fun r (_ : r ∈ Finset.univ) => s2 r
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, s3] at hsum2
  linarith [s1, s4, henv, hloss]

/-- The classical value against Bob's outputs, for any matrix. -/
theorem value_eq_sum {R K : Type*} [Fintype R] [Fintype K] (V : R → K → ℝ) (a b : R → ℝ) :
    value V a b = ∑ j, b j * (3 * ∑ k, V j k * coord V a k - 4 * a j) := by
  have h : gramScore V a b = ∑ j, b j * ∑ k, V j k * coord V a k := by
    unfold gramScore coord
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by ring
  have h2 : ∑ j, b j * (3 * ∑ k, V j k * coord V a k - 4 * a j) =
      3 * ∑ j, b j * ∑ k, V j k * coord V a k - 4 * ∑ j, a j * b j := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [h2, ← h]
  rfl

/-- **The missing matrix-level bridge**: the fixed-shift upper bound holds in every order. -/
theorem fixedUpper (d : ℕ) : FixedUpper d := by
  intro a b ha hb
  classical
  let aZ : Root d → ℤ := fun r => if a r = 1 then 1 else -1
  let bZ : Root d → ℤ := fun r => if b r = 1 then 1 else -1
  have haZ : ∀ r, a r = (aZ r : ℝ) := by
    intro r; rcases ha r with h | h <;> simp [aZ, h]
  have hbZ : ∀ r, b r = (bZ r : ℝ) := by
    intro r; rcases hb r with h | h <;> simp [bZ, h]
  have haZs : ∀ r, aZ r = 1 ∨ aZ r = -1 := by
    intro r; simp only [aZ]; split_ifs <;> simp
  have hbZs : ∀ r, bZ r = 1 ∨ bZ r = -1 := by
    intro r; simp only [bZ]; split_ifs <;> simp
  have hy : ∀ r, ∑ k, roots d r k * coord (roots d) a k = (yZ d aZ r : ℝ) := by
    intro r
    unfold yZ pZ coord
    push_cast
    simp only [roots_cast, haZ]
  have hval : value (roots d) a b =
      ((∑ r, bZ r * (3 * yZ d aZ r - 4 * aZ r) : ℤ) : ℝ) := by
    rw [value_eq_sum]
    push_cast
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [hy, hbZ, haZ]
  rw [hval]
  have h := upperZ d aZ bZ haZs hbZs
  unfold bound at h
  exact_mod_cast h

end Lemmata.FishburnReedsClassicalBound
