module

public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Find
public import Lean.Elab.Tactic.Omega
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace Lemmata.Centroid

def generalBoundAt (n s : ℕ) : ℕ :=
  if s = 0 then n ^ 3 + 1
  else if s = 1 then n ^ 3 + 2
  else if s ≤ n then n ^ 3 + s * (s - 1) + 1
  else n ^ 3 + n * s + 1 + ((s - n - 1) ^ 2 - n)

def symmetricBase (n : ℕ) : ℕ := n * (n + 3) / 2

def symmetricBoundAt (n s : ℕ) : ℕ :=
  (n + 2).choose 3 + 1 + max s (s.choose 2)

def supportBoundAt (n s : ℕ) : ℕ :=
  if s ≤ n then n ^ 3 + s ^ 2 else generalBoundAt n s - 1

def triangleBoundAt (a b : ℕ) : ℕ := a.choose 3 + b.choose 2

def edgeIndex (E : ℕ) : ℕ := Nat.findGreatest (fun a => a.choose 2 ≤ E) (E + 2)

def triangleBound (E : ℕ) : ℕ :=
  triangleBoundAt (edgeIndex E) (E - (edgeIndex E).choose 2)

def generalIndex (N : ℕ) : ℕ :=
  Nat.findGreatest (fun n => n * (n + 1) ≤ N) N

def generalBound (N : ℕ) : ℕ :=
  if N ≤ 1 then N else generalBoundAt (generalIndex N) (N - generalIndex N * (generalIndex N + 1))

def supportBound (N : ℕ) : ℕ :=
  if N ≤ 1 then 0 else supportBoundAt (generalIndex N) (N - generalIndex N * (generalIndex N + 1))

def symmetricIndex (N : ℕ) : ℕ := Nat.findGreatest (fun n => symmetricBase n ≤ N) N

def symmetricBound (N : ℕ) : ℕ :=
  if N ≤ 1 then N else symmetricBoundAt (symmetricIndex N) (N - symmetricBase (symmetricIndex N))

@[simp] theorem generalBoundAt_zero (n : ℕ) : generalBoundAt n 0 = n ^ 3 + 1 := by
  simp [generalBoundAt]

@[simp] theorem generalBoundAt_one (n : ℕ) : generalBoundAt n 1 = n ^ 3 + 2 := by
  simp [generalBoundAt]

@[simp] theorem symmetricBoundAt_zero (n : ℕ) :
    symmetricBoundAt n 0 = (n + 2).choose 3 + 1 := by
  simp [symmetricBoundAt]

@[simp] theorem triangleBoundAt_zero (a : ℕ) : triangleBoundAt a 0 = a.choose 3 := by
  simp [triangleBoundAt]

theorem choose_two_add (a b : ℕ) :
    (a + b).choose 2 = a.choose 2 + b.choose 2 + a * b := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [show a + (b + 1) = (a + b) + 1 by omega,
      Nat.choose_succ_succ' _ 1, Nat.choose_succ_succ' _ 1, ih]
    simp only [Nat.choose_one_right]
    ring

theorem two_mul_choose_two_succ (n : ℕ) :
    2 * (n + 1).choose 2 = n * (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show n + 1 + 1 = (n + 1) + 1 by omega, Nat.choose_succ_succ' _ 1]
    simp only [Nat.choose_one_right]
    nlinarith

theorem lt_choose_add_two (E : ℕ) : E < (E + 2).choose 2 := by
  have h : (E + 2).choose 2 = (E + 1) + (E + 1).choose 2 := by
    simpa only [Nat.choose_one_right] using Nat.choose_succ_succ' (E + 1) 1
  omega

theorem edgeIndex_choose_le (E : ℕ) : (edgeIndex E).choose 2 ≤ E := by
  exact Nat.findGreatest_spec (P := fun a => a.choose 2 ≤ E)
    (m := 0) (n := E + 2) (by omega) (by simp [Nat.choose])

theorem edgeIndex_pos (E : ℕ) : 0 < edgeIndex E := by
  have h : 1 ≤ edgeIndex E := Nat.le_findGreatest (P := fun a => a.choose 2 ≤ E)
    (by omega) (by simp [Nat.choose])
  omega

theorem edgeIndex_lt (E : ℕ) : edgeIndex E < E + 2 := by
  have hle : edgeIndex E ≤ E + 2 := Nat.findGreatest_le _
  have hchoose := edgeIndex_choose_le E
  have hlarge := lt_choose_add_two E
  by_contra h
  have heq : edgeIndex E = E + 2 := by omega
  rw [heq] at hchoose
  omega

theorem lt_edgeIndex_succ_choose (E : ℕ) : E < (edgeIndex E + 1).choose 2 := by
  exact Nat.lt_of_not_ge (Nat.findGreatest_is_greatest
    (P := fun a => a.choose 2 ≤ E) (n := E + 2) (k := edgeIndex E + 1)
    (Nat.lt_succ_self _) (by have := edgeIndex_lt E; omega))

theorem edge_remainder_lt (E : ℕ) : E - (edgeIndex E).choose 2 < edgeIndex E := by
  have hle := edgeIndex_choose_le E
  have hlt := lt_edgeIndex_succ_choose E
  have hnext : (edgeIndex E + 1).choose 2 = edgeIndex E + (edgeIndex E).choose 2 := by
    simpa only [Nat.choose_one_right] using Nat.choose_succ_succ' (edgeIndex E) 1
  omega

theorem edge_decomposition (E : ℕ) :
    E = (edgeIndex E).choose 2 + (E - (edgeIndex E).choose 2) := by
  have := edgeIndex_choose_le E
  omega

theorem edgeIndex_eq {E a b : ℕ} (hb : b < a) (hE : E = a.choose 2 + b) :
    edgeIndex E = a := by
  have hle := edgeIndex_choose_le E
  have hlt := lt_edgeIndex_succ_choose E
  have hanext : (a + 1).choose 2 = a + a.choose 2 := by
    simpa only [Nat.choose_one_right] using Nat.choose_succ_succ' a 1
  apply Nat.le_antisymm
  · by_contra h
    have hmono := Nat.choose_le_choose 2 (by omega : a + 1 ≤ edgeIndex E)
    omega
  · by_contra h
    have hmono := Nat.choose_le_choose 2 (by omega : edgeIndex E + 1 ≤ a)
    omega

theorem triangleBound_eq {E a b : ℕ} (hb : b < a) (hE : E = a.choose 2 + b) :
    triangleBound E = triangleBoundAt a b := by
  rw [triangleBound, edgeIndex_eq hb hE, hE]
  simp

@[simp] theorem triangleBound_zero : triangleBound 0 = 0 := by
  have h := triangleBound_eq (E := 0) (a := 1) (b := 0) (by omega) (by simp)
  simpa [triangleBoundAt, Nat.choose] using h

theorem triangleBound_succ_le (E : ℕ) : triangleBound E ≤ triangleBound (E + 1) := by
  let a := edgeIndex E
  let b := E - a.choose 2
  have hb : b < a := edge_remainder_lt E
  have hE : E = a.choose 2 + b := edge_decomposition E
  have hcurrent : triangleBound E = triangleBoundAt a b := triangleBound_eq hb hE
  by_cases hnext : b + 1 < a
  · have hE' : E + 1 = a.choose 2 + (b + 1) := by omega
    rw [hcurrent, triangleBound_eq hnext hE', triangleBoundAt, triangleBoundAt]
    exact Nat.add_le_add_left (Nat.choose_le_choose 2 (Nat.le_succ b)) _
  · have hba : b + 1 = a := by omega
    have hstep : (a + 1).choose 2 = a + a.choose 2 := by
      simpa only [Nat.choose_one_right] using Nat.choose_succ_succ' a 1
    have hE' : E + 1 = (a + 1).choose 2 + 0 := by omega
    have hthree : (a + 1).choose 3 = a.choose 2 + a.choose 3 :=
      Nat.choose_succ_succ' a 2
    rw [hcurrent, triangleBound_eq (by omega : 0 < a + 1) hE', triangleBoundAt,
      triangleBoundAt, hthree]
    have hmono := Nat.choose_le_choose 2 (by omega : b ≤ a)
    simp only [Nat.choose_zero_succ, Nat.add_zero]
    omega

theorem triangleBound_mono : Monotone triangleBound :=
  monotone_nat_of_le_succ triangleBound_succ_le

theorem symmetricBase_eq_choose (n : ℕ) :
    symmetricBase n = (n + 2).choose 2 - 1 := by
  have hpos : 0 < (n + 2).choose 2 := Nat.choose_pos (by omega)
  have htwo : 2 * (n + 2).choose 2 = (n + 1) * (n + 2) := by
    simpa only [Nat.add_assoc] using two_mul_choose_two_succ (n + 1)
  have hsub : (n + 2).choose 2 - 1 + 1 = (n + 2).choose 2 := by omega
  have hpoly : n * (n + 3) = 2 * ((n + 2).choose 2 - 1) := by nlinarith
  rw [symmetricBase, hpoly]
  omega

@[simp] theorem symmetricBase_zero : symmetricBase 0 = 0 := rfl

theorem symmetricBase_succ (n : ℕ) :
    symmetricBase (n + 1) = symmetricBase n + n + 2 := by
  rw [symmetricBase_eq_choose, symmetricBase_eq_choose]
  have hpos : 0 < (n + 2).choose 2 := Nat.choose_pos (by omega)
  have hstep : (n + 1 + 2).choose 2 = n + 2 + (n + 2).choose 2 := by
    simpa only [Nat.choose_one_right] using Nat.choose_succ_succ' (n + 2) 1
  omega

theorem symmetricBoundAt_succ (n s : ℕ) :
    symmetricBoundAt n s + 1 ≤ symmetricBoundAt n (s + 1) := by
  have hstep : (s + 1).choose 2 = s + s.choose 2 := by
    simpa only [Nat.choose_one_right] using Nat.choose_succ_succ' s 1
  have hleft := Nat.le_max_left (s + 1) ((s + 1).choose 2)
  have hright := Nat.le_max_right (s + 1) ((s + 1).choose 2)
  unfold symmetricBoundAt
  by_cases hs : s ≤ s.choose 2
  · rw [max_eq_right hs]
    by_cases hz : s = 0
    · subst s
      simp [Nat.choose]
    · omega
  · rw [max_eq_left (by omega : s.choose 2 ≤ s)]
    omega

private theorem intervalIndex_eq (B : ℕ → ℕ) (hmono : Monotone B)
    {N n : ℕ} (hn : n ≤ N) (hlo : B n ≤ N) (hhi : N < B (n + 1)) :
    Nat.findGreatest (fun j => B j ≤ N) N = n := by
  apply Nat.le_antisymm
  · by_contra h
    have hspec : B (Nat.findGreatest (fun j => B j ≤ N) N) ≤ N :=
      Nat.findGreatest_spec (P := fun j => B j ≤ N) hn hlo
    have hbound := hmono (by omega : n + 1 ≤ Nat.findGreatest (fun j => B j ≤ N) N)
    omega
  · exact Nat.le_findGreatest hn hlo

theorem generalIndex_eq {N n s : ℕ} (hs : s ≤ 2 * n + 1) (hN : N = n * (n + 1) + s) :
    generalIndex N = n := by
  apply intervalIndex_eq (fun j => j * (j + 1))
  · intro i j hij
    exact Nat.mul_le_mul hij (Nat.add_le_add_right hij 1)
  · nlinarith
  · omega
  · nlinarith

theorem generalBound_eq {N n s : ℕ} (hN₂ : 2 ≤ N)
    (hs : s ≤ 2 * n + 1) (hN : N = n * (n + 1) + s) :
    generalBound N = generalBoundAt n s := by
  simp only [generalBound, show ¬ N ≤ 1 by omega, ite_false, generalIndex_eq hs hN]
  rw [hN]
  simp

theorem supportBound_eq {N n s : ℕ} (hN₂ : 2 ≤ N)
    (hs : s ≤ 2 * n + 1) (hN : N = n * (n + 1) + s) :
    supportBound N = supportBoundAt n s := by
  simp only [supportBound, show ¬ N ≤ 1 by omega, ite_false, generalIndex_eq hs hN]
  rw [hN]
  simp

theorem generalIndex_base_le (N : ℕ) : generalIndex N * (generalIndex N + 1) ≤ N := by
  exact Nat.findGreatest_spec (P := fun n => n * (n + 1) ≤ N) (m := 0) (by omega) (by simp)

theorem generalIndex_pos {N : ℕ} (hN : 2 ≤ N) : 0 < generalIndex N := by
  have h : 1 ≤ generalIndex N := Nat.le_findGreatest (P := fun n => n * (n + 1) ≤ N)
    (by omega) (by simpa using hN)
  omega

theorem general_remainder_le {N : ℕ} (hN : 2 ≤ N) :
    N - generalIndex N * (generalIndex N + 1) ≤ 2 * generalIndex N + 1 := by
  have hp := generalIndex_pos hN
  have hb := generalIndex_base_le N
  have hnext : generalIndex N + 1 ≤ N := by nlinarith
  have hlt := Nat.findGreatest_is_greatest (P := fun n => n * (n + 1) ≤ N)
    (n := N) (k := generalIndex N + 1) (Nat.lt_succ_self _) hnext
  dsimp only [generalIndex] at hb hp hnext hlt ⊢
  nlinarith [Nat.sub_add_cancel hb]

theorem general_decomposition (N : ℕ) :
    N = generalIndex N * (generalIndex N + 1) + (N - generalIndex N * (generalIndex N + 1)) := by
  have h := generalIndex_base_le N
  omega

theorem symmetricBase_mono : Monotone symmetricBase :=
  monotone_nat_of_le_succ fun n => by rw [symmetricBase_succ]; omega

theorem le_symmetricBase (n : ℕ) : n ≤ symmetricBase n := by
  induction n with
  | zero => simp
  | succ n ih => rw [symmetricBase_succ]; omega

theorem symmetricIndex_eq {N n s : ℕ} (hs : s ≤ n + 1) (hN : N = symmetricBase n + s) :
    symmetricIndex N = n := by
  apply intervalIndex_eq symmetricBase symmetricBase_mono
  · have := le_symmetricBase n; omega
  · omega
  · rw [symmetricBase_succ]; omega

theorem symmetricBound_eq {N n s : ℕ} (hN₂ : 2 ≤ N)
    (hs : s ≤ n + 1) (hN : N = symmetricBase n + s) :
    symmetricBound N = symmetricBoundAt n s := by
  simp only [symmetricBound, show ¬ N ≤ 1 by omega, ite_false, symmetricIndex_eq hs hN]
  rw [hN]
  simp

theorem symmetricIndex_base_le (N : ℕ) : symmetricBase (symmetricIndex N) ≤ N := by
  exact Nat.findGreatest_spec (P := fun n => symmetricBase n ≤ N)
    (m := 0) (n := N) (by omega) (by simp)

theorem symmetricIndex_next_lt (N : ℕ) : N < symmetricBase (symmetricIndex N + 1) := by
  by_cases h : symmetricIndex N + 1 ≤ N
  · exact Nat.lt_of_not_ge (Nat.findGreatest_is_greatest
      (P := fun n => symmetricBase n ≤ N) (n := N) (k := symmetricIndex N + 1)
      (Nat.lt_succ_self _) h)
  · have := le_symmetricBase (symmetricIndex N + 1)
    omega

theorem symmetric_remainder_le (N : ℕ) :
    N - symmetricBase (symmetricIndex N) ≤ symmetricIndex N + 1 := by
  have := symmetricIndex_base_le N
  have := symmetricIndex_next_lt N
  rw [symmetricBase_succ] at this
  omega

theorem symmetric_decomposition (N : ℕ) :
    N = symmetricBase (symmetricIndex N) + (N - symmetricBase (symmetricIndex N)) := by
  have := symmetricIndex_base_le N
  omega

theorem symmetricIndex_pos {N : ℕ} (hN : 2 ≤ N) : 0 < symmetricIndex N := by
  have h : 1 ≤ symmetricIndex N := Nat.le_findGreatest
    (P := fun n => symmetricBase n ≤ N) (by omega) (by change 2 ≤ N; exact hN)
  omega

theorem symmetricBoundAt_boundary {n : ℕ} (hn : 0 < n) :
    symmetricBoundAt n (n + 1) + 1 ≤ symmetricBoundAt (n + 1) 0 := by
  have htwo : (n + 2).choose 2 = (n + 1) + (n + 1).choose 2 := by
    simpa only [Nat.choose_one_right] using Nat.choose_succ_succ' (n + 1) 1
  have hthree : (n + 1 + 2).choose 3 = (n + 2).choose 2 + (n + 2).choose 3 := by
    simpa only [Nat.add_assoc] using Nat.choose_succ_succ' (n + 2) 2
  have hpos : 0 < (n + 1).choose 2 := Nat.choose_pos (by omega)
  rw [symmetricBoundAt_zero, hthree, symmetricBoundAt]
  have hmax := Nat.le_max_left (n + 1) ((n + 1).choose 2)
  by_cases h : n + 1 ≤ (n + 1).choose 2
  · rw [max_eq_right h]
    omega
  · rw [max_eq_left (by omega : (n + 1).choose 2 ≤ n + 1)]
    omega

theorem symmetricBound_succ (N : ℕ) : symmetricBound N + 1 ≤ symmetricBound (N + 1) := by
  by_cases hN : N ≤ 1
  · have h : N = 0 ∨ N = 1 := by omega
    rcases h with rfl | rfl <;> decide
  let n := symmetricIndex N
  let s := N - symmetricBase n
  have hn : 0 < n := symmetricIndex_pos (by omega)
  have hs : s ≤ n + 1 := symmetric_remainder_le N
  have hrepr : N = symmetricBase n + s := symmetric_decomposition N
  rw [symmetricBound_eq (by omega) hs hrepr]
  by_cases h : s + 1 ≤ n + 1
  · rw [symmetricBound_eq (by omega) h (by omega : N + 1 = symmetricBase n + (s + 1))]
    exact symmetricBoundAt_succ n s
  · have hs' : s = n + 1 := by omega
    have hrepr' : N + 1 = symmetricBase (n + 1) + 0 := by
      rw [symmetricBase_succ]
      omega
    rw [symmetricBound_eq (by omega) (by omega : 0 ≤ n + 1 + 1) hrepr', hs']
    exact symmetricBoundAt_boundary hn

theorem symmetricBound_add (N k : ℕ) : symmetricBound N + k ≤ symmetricBound (N + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h := symmetricBound_succ (N + k)
    simpa only [Nat.add_assoc] using (Nat.add_le_add_right ih 1).trans h

theorem symmetricBound_mono : Monotone symmetricBound :=
  monotone_nat_of_le_succ fun n => (Nat.le_add_right _ 1).trans (symmetricBound_succ n)

theorem le_symmetricBound (N : ℕ) : N ≤ symmetricBound N := by
  have h := symmetricBound_add 0 N
  simpa [symmetricBound] using h

theorem triangleBound_succ_le_symmetricBound {N : ℕ} (hN : 0 < N) :
    1 + triangleBound (N + 1) ≤ symmetricBound N := by
  by_cases hsmall : N = 1
  · subst N
    decide
  let n := symmetricIndex N
  let s := N - symmetricBase n
  have hs : s ≤ n + 1 := symmetric_remainder_le N
  have hrepr : N = symmetricBase n + s := symmetric_decomposition N
  have hpos : 0 < (n + 2).choose 2 := Nat.choose_pos (by omega)
  have hbase := symmetricBase_eq_choose n
  have hedge : N + 1 = (n + 2).choose 2 + s := by omega
  rw [triangleBound_eq (by omega : s < n + 2) hedge,
    symmetricBound_eq (by omega) hs hrepr, triangleBoundAt, symmetricBoundAt]
  have := Nat.le_max_right s (s.choose 2)
  omega

theorem symmetric_completion {m y ρ b N : ℕ} (hsupport : m + ρ ≤ N)
    (hcontraction : b + 1 ≤ m) (hgraph : y + b ≤ triangleBound (ρ + b + 2)) :
    m + y ≤ symmetricBound N := by
  let N₀ := ρ + b + 1
  have hN₀ : 0 < N₀ := by dsimp [N₀]; omega
  have hscalar := triangleBound_succ_le_symmetricBound hN₀
  have hgrowth := symmetricBound_add N₀ (m - b - 1)
  have hbalance : N₀ + (m - b - 1) = m + ρ := by dsimp [N₀]; omega
  rw [hbalance] at hgrowth
  have hmono := symmetricBound_mono hsupport
  have hindex : N₀ + 1 = ρ + b + 2 := by dsimp [N₀]
  rw [hindex] at hscalar
  omega

theorem generalBoundAt_second {n : ℕ} (hn : 0 < n) (t : ℕ) :
    generalBoundAt n (n + 1 + t) =
      n ^ 3 + n * (n + 1 + t) + 1 + (t ^ 2 - n) := by
  have h₁ : n + 1 + t ≠ 1 := by omega
  have h₂ : ¬ n + 1 + t ≤ n := by omega
  have hsub : n + 1 + t - n - 1 = t := by omega
  simp [generalBoundAt, h₁, h₂, hsub]

theorem triangleBoundAt_delete_small (a b d : ℕ) (hd : d ≤ b) :
    triangleBoundAt a (b - d) + d.choose 2 ≤ triangleBoundAt a b := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hd
  simp only [Nat.add_sub_cancel_left, triangleBoundAt]
  rw [choose_two_add]
  omega

theorem triangleBoundAt_delete_large (a b d : ℕ) (hb : b < d) (hd : d < a) :
    triangleBoundAt (a - 1) (a - 1 + b - d) + d.choose 2 ≤ triangleBoundAt a b := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hd)
  have h₁ : d + 1 + e - 1 = d + e := by omega
  have h₂ : d + e + b - d = e + b := by omega
  rw [triangleBoundAt, triangleBoundAt, h₁, h₂,
    show d + 1 + e = (d + e) + 1 by omega, Nat.choose_succ_succ' _ 2,
    choose_two_add e b, choose_two_add d e]
  nlinarith

end Lemmata.Centroid
