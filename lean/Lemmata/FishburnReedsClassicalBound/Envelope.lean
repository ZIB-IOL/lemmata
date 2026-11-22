module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Int
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-! # The envelope inequality for the halved coordinates

For the fixed shift, maximizing over Bob's signs first leaves the sum over the rows of
`max 4 (6 |v·p| - 4)` minus `3 ‖p‖²`, where `p = Vᵀ a` has even coordinates. This file proves
the purely combinatorial bound on that envelope, in terms of the magnitudes of the halved
coordinates: it is at most `2d(d-1)(2d-3)`, except for an excess of `4` when exactly two
coordinates vanish. -/

@[expose] public section

namespace Lemmata.FishburnReedsClassicalBound.Envelope

/-- The sum of `f x y` over the unordered pairs of positions of a list. -/
def pairSum (f : ℕ → ℕ → ℤ) : List ℕ → ℤ
  | [] => 0
  | x :: xs => (xs.map (f x)).sum + pairSum f xs

theorem pairSum_perm {f : ℕ → ℕ → ℤ} (hf : ∀ x y, f x y = f y x) {l₁ l₂ : List ℕ}
    (h : l₁.Perm l₂) : pairSum f l₁ = pairSum f l₂ := by
  induction h with
  | nil => rfl
  | cons x h ih => simp only [pairSum, ih, (h.map (f x)).sum_eq]
  | swap x y l =>
    simp only [pairSum, List.map_cons, List.sum_cons, hf x y]
    ring
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem pairSum_append (f : ℕ → ℕ → ℤ) (A B : List ℕ) :
    pairSum f (A ++ B) =
      pairSum f A + (A.map fun x => (B.map (f x)).sum).sum + pairSum f B := by
  induction A with
  | nil => simp [pairSum]
  | cons x A ih =>
    simp only [List.cons_append, pairSum, List.map_append, List.sum_append, ih,
      List.map_cons, List.sum_cons]
    ring

theorem pairSum_replicate (f : ℕ → ℕ → ℤ) (k m : ℕ) :
    2 * pairSum f (List.replicate k m) = (k : ℤ) * ((k : ℤ) - 1) * f m m := by
  induction k with
  | zero => simp [pairSum]
  | succ k ih =>
    rw [List.replicate_succ, pairSum, List.map_replicate, List.sum_replicate, mul_add, ih]
    push_cast
    ring

/-- The pair weight in halved coordinates `x = |p_i|/2`, `y = |p_j|/2`. -/
def pairW (x y : ℕ) : ℤ :=
  24 * (max x y : ℕ) - 8 + (if x = y then 8 else 0) + (if x = 0 ∧ y = 0 then 8 else 0)

theorem pairW_comm (x y : ℕ) : pairW x y = pairW y x := by
  have h1 : (if x = y then (8 : ℤ) else 0) = (if y = x then 8 else 0) := if_congr eq_comm rfl rfl
  have h2 : (if x = 0 ∧ y = 0 then (8 : ℤ) else 0) = (if y = 0 ∧ x = 0 then 8 else 0) :=
    if_congr and_comm rfl rfl
  unfold pairW
  rw [max_comm, h1, h2]

def sqSum (L : List ℕ) : ℤ := (L.map fun x : ℕ => ((x : ℤ) ^ 2 : ℤ)).sum

/-- The envelope in halved coordinates (a quarter of the real envelope). -/
def envW (L : List ℕ) : ℤ := pairSum pairW L - 12 * sqSum L

/-- The fixed-shift bound `2d(d-1)(2d-3)`. -/
def bound (n : ℕ) : ℤ := 2 * n * ((n : ℤ) - 1) * (2 * n - 3)

theorem sqSum_perm {l₁ l₂ : List ℕ} (h : l₁.Perm l₂) : sqSum l₁ = sqSum l₂ := by
  unfold sqSum
  exact (h.map (fun x : ℕ => ((x : ℤ) ^ 2 : ℤ))).sum_eq

theorem envW_perm {l₁ l₂ : List ℕ} (h : l₁.Perm l₂) : envW l₁ = envW l₂ := by
  unfold envW
  rw [pairSum_perm pairW_comm h, sqSum_perm h]

private theorem le_foldr_max (L : List ℕ) : ∀ y ∈ L, y ≤ L.foldr max 0 := by
  induction L with
  | nil => simp
  | cons x L ih =>
    intro y hy
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp hy with rfl | hy
    · exact le_max_left _ _
    · exact (ih y hy).trans (le_max_right _ _)

private theorem foldr_max_mem (L : List ℕ) (hL : L ≠ []) : L.foldr max 0 ∈ L := by
  induction L with
  | nil => exact absurd rfl hL
  | cons x L ih =>
    simp only [List.foldr_cons]
    by_cases hn : L = []
    · subst hn; simp
    · rcases le_total x (L.foldr max 0) with h | h
      · rw [max_eq_right h]; exact List.mem_cons_of_mem _ (ih hn)
      · rw [max_eq_left h]; exact List.mem_cons_self

/-- Adding a group of `k` copies of a new maximum `m > 0` on top of `ℓ` smaller values
increases the envelope by at most the increase of the bound. -/
private theorem group_step (k ℓ m : ℤ) (hk : 1 ≤ k) :
    12 * k * (k - 1) * m + k * ℓ * (24 * m - 8) - 12 * k * m ^ 2 ≤
      (2 * (k + ℓ) * (k + ℓ - 1) * (2 * (k + ℓ) - 3)) - 2 * ℓ * (ℓ - 1) * (2 * ℓ - 3) := by
  have key : (2 * (k + ℓ) * (k + ℓ - 1) * (2 * (k + ℓ) - 3)) - 2 * ℓ * (ℓ - 1) * (2 * ℓ - 3)
      - (12 * k * (k - 1) * m + k * ℓ * (24 * m - 8) - 12 * k * m ^ 2)
      = k * (3 * (2 * (m - ℓ) - k + 1) ^ 2 + (k - 1) * (k - 3)) := by ring
  have hpos : 0 ≤ 3 * (2 * (m - ℓ) - k + 1) ^ 2 + (k - 1) * (k - 3) := by
    rcases le_or_gt 3 k with h3 | h3
    · nlinarith [sq_nonneg (2 * (m - ℓ) - k + 1)]
    · have hk' : k = 1 ∨ k = 2 := by omega
      rcases hk' with rfl | rfl
      · nlinarith [sq_nonneg (2 * (m - ℓ))]
      · -- `2(m-ℓ) - 1` is odd, so its square is at least one
        have hodd : 1 ≤ (2 * (m - ℓ) - 2 + 1) ^ 2 := by
          rcases le_or_gt (m - ℓ) 0 with h | h <;> nlinarith
        nlinarith
  nlinarith

/-- The group of zeros: `k` zeros contribute `4k(k-1)`, which exceeds the bound only for `k = 2`. -/
private theorem zero_group (k : ℕ) (P : ℤ) (hP : 2 * P = (k : ℤ) * ((k : ℤ) - 1) * 8) :
    P ≤ 2 * (k : ℤ) * ((k : ℤ) - 1) * (2 * k - 3) + (if k = 2 then 4 else 0) := by
  by_cases h2 : k = 2
  · subst h2; norm_num at hP ⊢; linarith
  · simp only [h2, ite_false, add_zero]
    rcases Nat.lt_or_ge k 3 with h | h
    · interval_cases k
      · norm_num at hP ⊢; linarith
      · norm_num at hP ⊢; linarith
      · exact absurd rfl h2
    · have h3 : (3 : ℤ) ≤ k := by exact_mod_cast h
      have hprod : 0 ≤ (k : ℤ) * ((k : ℤ) - 1) * (2 * k - 5) :=
        mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
      nlinarith

/-- **The envelope inequality.** For every list of halved magnitudes, the envelope is at most
`2d(d-1)(2d-3)`, plus `4` when exactly two entries vanish. -/
theorem envW_le : ∀ (n : ℕ) (L : List ℕ), L.length = n →
    envW L ≤ bound L.length + (if L.count 0 = 2 then 4 else 0) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro L hn
  rcases eq_or_ne L [] with rfl | hL
  · simp [envW, pairSum, sqSum, bound]
  obtain ⟨m, hm⟩ : ∃ m, L.foldr max 0 = m := ⟨_, rfl⟩
  have hmem : m ∈ L := hm ▸ foldr_max_mem L hL
  have hle : ∀ y ∈ L, y ≤ m := hm ▸ le_foldr_max L
  obtain ⟨k, hk⟩ : ∃ k, L.count m = k := ⟨_, rfl⟩
  obtain ⟨L', hL'⟩ : ∃ L', L.filter (fun y => !(y = m : Bool)) = L' := ⟨_, rfl⟩
  have hperm : (List.replicate k m ++ L').Perm L := by
    have := List.filter_append_perm (fun y => (y = m : Bool)) L
    simpa [← hk, ← hL', List.filter_eq] using this
  have hk1 : 1 ≤ k := hk ▸ List.count_pos_iff.mpr hmem
  have hlen : L.length = k + L'.length := by
    rw [← hperm.length_eq, List.length_append, List.length_replicate]
  have hlt : ∀ y ∈ L', y < m := by
    intro y hy
    rw [← hL'] at hy
    simp only [List.mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true,
      decide_eq_false_iff_not] at hy
    exact lt_of_le_of_ne (hle y hy.1) hy.2
  have hIH := ih L'.length (by omega) L' rfl
  rw [← envW_perm hperm, ← hperm.length_eq, ← hperm.count_eq]
  have hcross : (List.replicate k m).map (fun x => (L'.map (pairW x)).sum) =
      List.replicate k ((L'.length : ℤ) * (24 * m - 8)) := by
    rw [List.map_replicate]
    congr 1
    have : L'.map (pairW m) = L'.map (fun _ => 24 * (m : ℤ) - 8) := by
      apply List.map_congr_left
      intro y hy
      have hy' := hlt y hy
      simp [pairW, max_eq_left hy'.le, Nat.ne_of_gt hy', show m ≠ 0 by omega]
    rw [this, List.map_const', List.sum_replicate, nsmul_eq_mul]
  have hsq : sqSum (List.replicate k m ++ L') = k * (m : ℤ) ^ 2 + sqSum L' := by
    simp only [sqSum, List.map_append, List.sum_append, List.map_replicate, List.sum_replicate,
      nsmul_eq_mul]
  have hps : pairSum pairW (List.replicate k m ++ L') = pairSum pairW (List.replicate k m) +
      k * ((L'.length : ℤ) * (24 * m - 8)) + pairSum pairW L' := by
    rw [pairSum_append, hcross, List.sum_replicate, nsmul_eq_mul]
  have hsplit : envW (List.replicate k m ++ L') =
      pairSum pairW (List.replicate k m) + k * ((L'.length : ℤ) * (24 * m - 8)) +
        envW L' - 12 * k * (m : ℤ) ^ 2 := by
    unfold envW
    rw [hps, hsq]
    ring
  have hrep := pairSum_replicate pairW k m
  rw [hsplit, List.length_append, List.length_replicate, List.count_append,
    List.count_replicate]
  rcases Nat.eq_zero_or_pos m with rfl | hmpos
  · -- the maximum is zero: every entry is zero and `L'` is empty
    have hL'nil : L' = [] := List.eq_nil_iff_forall_not_mem.mpr fun y hy => by
      have := hlt y hy; omega
    subst hL'nil
    have hw : pairW 0 0 = 8 := by simp [pairW]
    rw [hw] at hrep
    have hz := zero_group k _ hrep
    simpa [envW, pairSum, sqSum, bound] using hz
  · -- a positive maximum: the zero count is that of `L'`
    have hne : (m == 0) = false := by simp; omega
    rw [hne]
    simp only [Bool.false_eq_true, ite_false, zero_add]
    have hw : pairW m m = 24 * m := by simp [pairW]; omega
    rw [hw] at hrep
    have hstep := group_step k L'.length m (by exact_mod_cast hk1)
    unfold bound at hIH ⊢
    push_cast at hIH ⊢
    nlinarith

end Lemmata.FishburnReedsClassicalBound.Envelope
