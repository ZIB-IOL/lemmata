module

public import Lemmata.Centroid.Def.Bounds
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace Lemmata.Centroid.General

def g (v : ℕ) : ℕ := (v + 1) ^ 2 / 4

@[simp] theorem g_zero : g 0 = 0 := rfl
@[simp] theorem g_one : g 1 = 1 := rfl

theorem g_even (v : ℕ) : g (2 * v) = v * (v + 1) := by
  unfold g
  rw [show (2 * v + 1) ^ 2 = 1 + 4 * (v * (v + 1)) by ring]
  omega

theorem g_odd (v : ℕ) : g (2 * v + 1) = (v + 1) ^ 2 := by
  unfold g
  rw [show (2 * v + 1 + 1) ^ 2 = 4 * (v + 1) ^ 2 by ring]
  omega

theorem g_succ (v : ℕ) : g (v + 1) = g v + (v + 2) / 2 := by
  have h : v = 2 * (v / 2) ∨ v = 2 * (v / 2) + 1 := by omega
  obtain h | h := h
  · rw [h, g_even, g_odd]
    have heq : (2 * (v / 2) + 2) / 2 = v / 2 + 1 := by omega
    rw [heq]
    ring
  · rw [h, g_odd, show 2 * (v / 2) + 1 + 1 = 2 * (v / 2 + 1) by omega, g_even]
    have heq : (2 * (v / 2) + 1 + 2) / 2 = v / 2 + 1 := by omega
    rw [heq]
    ring

theorem g_lipschitz {u v n : ℕ} (huv : u ≤ v) (hvn : v ≤ 2 * n) :
    g v ≤ g u + n * (v - u) := by
  induction v, huv using Nat.le_induction with
  | base => simp
  | succ v huv ih =>
    have hv : v ≤ 2 * n := by omega
    have hi := ih hv
    rw [g_succ]
    have hstep : (v + 2) / 2 ≤ n := by omega
    have hsub : v + 1 - u = v - u + 1 := by omega
    rw [hsub]
    nlinarith

theorem g_le_mul {v n : ℕ} (hvn : v ≤ 2 * n) : g v ≤ n * v := by
  simpa only [g_zero, Nat.sub_zero, Nat.zero_add] using g_lipschitz (u := 0) (by omega) hvn

theorem g_le_mul_pred {v : ℕ} (hv : 2 ≤ v) : g v ≤ v * (v - 1) := by
  have hp : v - 1 + 1 = v := by omega
  have hs : (v + 1) ^ 2 < 4 * (v * (v - 1) + 1) := by nlinarith
  unfold g
  omega

theorem g_mono : Monotone g := by
  apply monotone_nat_of_le_succ
  intro v
  rw [g_succ]
  omega

theorem g_le_square {v n : ℕ} (hn : 0 < n) (hv : v < 2 * n) : g v ≤ n ^ 2 := by
  have h := g_mono (show v ≤ 2 * (n - 1) + 1 by omega)
  rw [g_odd, show n - 1 + 1 = n by omega] at h
  exact h

theorem g_first_band {a s : ℕ} (ha : 1 ≤ a) (has : a ≤ s) (hs : 2 ≤ s) :
    g a + (s - a) ^ 2 ≤ s * (s - 1) := by
  have hsub : s - a + a = s := by omega
  have hs' : s - 1 + 1 = s := by omega
  by_cases ha1 : a = 1
  · subst a
    rw [g_one]
    nlinarith
  · have ha2 : 2 ≤ a := by omega
    have ha' : a - 1 + 1 = a := by omega
    have hg := g_le_mul_pred ha2
    have hp : 0 ≤ (s - a) * (2 * a - 1) := Nat.zero_le _
    have ha'' : 2 * a - 1 + 1 = 2 * a := by omega
    nlinarith

theorem supportBoundAt_second (n t : ℕ) (hn : 0 < n) :
    supportBoundAt n (n + 1 + t) = n * (n ^ 2 + n + t) + max n (t ^ 2) := by
  rw [supportBoundAt, ite_eq_right (by omega), generalBoundAt_second hn]
  have hp : n ^ 3 + n * (n + 1 + t) + 1 + (t ^ 2 - n) - 1 =
      n * (n ^ 2 + n + t) + (n + (t ^ 2 - n)) := by
    have hring : n ^ 3 + n * (n + 1 + t) = n * (n ^ 2 + n + t) + n := by ring
    omega
  rw [hp]
  congr 1
  by_cases h : n ≤ t ^ 2
  · rw [max_eq_right h]
    omega
  · rw [max_eq_left (by omega : t ^ 2 ≤ n)]
    omega

theorem generalBoundAt_second_pred (n t : ℕ) (hn : 0 < n) :
    generalBoundAt n (n + 1 + t) - 1 = n * (n ^ 2 + n + t) + max n (t ^ 2) := by
  rw [← supportBoundAt_second n t hn]
  simp only [supportBoundAt, show ¬ n + 1 + t ≤ n by omega, ite_false]

theorem generalBoundAt_extra {n s : ℕ} (_hn : 0 < n) (hs : s < 2 * n) :
    n ^ 3 + g s ≤ generalBoundAt n s - 1 := by
  by_cases hs0 : s = 0
  · subst s
    simp
  by_cases hs1 : s = 1
  · subst s
    simp
  by_cases hsn : s ≤ n
  · have hg := g_le_mul_pred (show 2 ≤ s by omega)
    simp only [generalBoundAt, hs0, hs1, hsn, ite_false, ite_true]
    omega
  · have hg := g_le_mul (n := n) (show s ≤ 2 * n by omega)
    simp only [generalBoundAt, hs0, hs1, hsn, ite_false]
    omega

theorem support_previous_loss {n b : ℕ} (hn : 2 ≤ n) (hb : 1 ≤ b) (hbn : b ≤ n) :
    supportBound (n * (n + 1) - b) + n * b ≤ n ^ 3 := by
  have hn' : n - 1 + 1 = n := by omega
  have hnb : n - b + b = n := by omega
  have hbig : b ≤ n * (n + 1) := by nlinarith
  have hbig' := Nat.sub_add_cancel hbig
  have hN : n * (n + 1) - b = (n - 1) * ((n - 1) + 1) + (n - 1 + 1 + (n - b)) := by
    nlinarith
  have hN₂ : 2 ≤ n * (n + 1) - b := by nlinarith
  rw [supportBound_eq hN₂ (by omega) hN,
    supportBoundAt_second (n - 1) (n - b) (by omega)]
  have hsq : (n - b) ^ 2 ≤ n ^ 2 - b := by
    have hmul : b ≤ n ^ 2 := by nlinarith
    have heq : n ^ 2 - b + b = n ^ 2 := by omega
    nlinarith
  have hlin : n - 1 ≤ n ^ 2 - b := by
    have hmul : b ≤ n ^ 2 := by nlinarith
    have heq : n ^ 2 - b + b = n ^ 2 := by omega
    nlinarith
  have hm := max_le hlin hsq
  have hq : (n - 1) ^ 2 + (n - 1) + (n - b) + b = n ^ 2 := by nlinarith
  have hbq : n ^ 2 - b + b = n ^ 2 := by
    have : b ≤ n ^ 2 := by nlinarith
    omega
  nlinarith [congrArg (fun z : ℕ => (n - 1) * z) hq,
    congrArg (fun z : ℕ => z * n ^ 2) hn']

theorem support_previous_far {n b : ℕ} (hn : 2 ≤ n) (hb : n < b) (hbn : b < 2 * n) :
    supportBound (n * (n + 1) - b) ≤ n * (n - 1) ^ 2 := by
  have hn' : n - 1 + 1 = n := by omega
  have hv : 2 * n - b ≤ n - 1 := by omega
  have hbig : b ≤ n * (n + 1) := by nlinarith
  have hbig' := Nat.sub_add_cancel hbig
  have hv' : 2 * n - b + b = 2 * n := by omega
  have hN : n * (n + 1) - b = (n - 1) * ((n - 1) + 1) + (2 * n - b) := by
    nlinarith
  have hN₂ : 2 ≤ n * (n + 1) - b := by nlinarith
  rw [supportBound_eq hN₂ (by omega) hN]
  simp only [supportBoundAt, hv, ite_true]
  calc
    _ ≤ (n - 1) ^ 3 + (n - 1) ^ 2 := by nlinarith
    _ = n * (n - 1) ^ 2 := by
      nlinarith [congrArg (fun z : ℕ => z * (n - 1) ^ 2) hn']

theorem small_loss_current {n s a : ℕ} (hn : 0 < n) (hs : s ≤ 2 * n + 1)
    (ha : 1 ≤ a) (has : a ≤ s) (han : a < 2 * n) :
    g a + supportBoundAt n (s - a) ≤ generalBoundAt n s - 1 := by
  by_cases hsn : s ≤ n
  · have hs0 : s ≠ 0 := by omega
    by_cases hs1 : s = 1
    · have ha1 : a = 1 := by omega
      subst s a
      simp [supportBoundAt, Nat.add_comm]
    · have hu : supportBoundAt n (s - a) = n ^ 3 + (s - a) ^ 2 := by
        simp [supportBoundAt, show s - a ≤ n by omega]
      have hm : generalBoundAt n s - 1 = n ^ 3 + s * (s - 1) := by
        simp [generalBoundAt, hs0, hs1, hsn]
      rw [hu, hm]
      have hg := g_first_band ha has (show 2 ≤ s by omega)
      omega
  · let t := s - n - 1
    have ht : t ≤ n := by dsimp [t]; omega
    have hst : s = n + 1 + t := by dsimp [t]; omega
    rw [hst, generalBoundAt_second_pred n t hn]
    by_cases hat : a ≤ t
    · have hsub : t - a + a = t := by omega
      have hu : n + 1 + t - a = n + 1 + (t - a) := by omega
      rw [hu, supportBoundAt_second n (t - a) hn]
      have hg := g_le_mul (n := n) (show a ≤ 2 * n by omega)
      have hsq : (t - a) ^ 2 ≤ t ^ 2 := by have := Nat.sub_le t a; nlinarith
      have hm := max_le_max (le_refl n) hsq
      nlinarith [congrArg (fun z : ℕ => n * z) hsub]
    · let v := a - t - 1
      have hv : v ≤ n := by dsimp [v]; omega
      have hav : a = t + 1 + v := by dsimp [v]; omega
      have hsub : a - (t + 1) = v := by omega
      have hv' : n - v + v = n := by omega
      have hu : n + 1 + t - a = n - v := by omega
      rw [hu, supportBoundAt, ite_eq_left (show n - v ≤ n by omega)]
      have hg := g_lipschitz (u := t + 1) (v := a) (n := n) (by omega) (by omega)
      rw [hsub] at hg
      have hg' := g_le_mul (v := t + 1) (n := n) (by omega)
      have hm := le_max_left n (t ^ 2)
      nlinarith [Nat.zero_le (v * (n - v))]

theorem small_loss {n s a : ℕ} (hn : 0 < n) (hs : s ≤ 2 * n + 1)
    (ha : 1 ≤ a) (han : a < 2 * n) :
    g a + supportBound (n * (n + 1) + s - a) ≤ generalBoundAt n s - 1 := by
  by_cases hn1 : n = 1
  · subst n
    have ha1 : a = 1 := by omega
    subst a
    interval_cases s <;>
      norm_num [g, supportBound, supportBoundAt, generalBoundAt, generalIndex, Nat.findGreatest]
  have hn2 : 2 ≤ n := by omega
  by_cases has : a ≤ s
  · have hN : n * (n + 1) + s - a = n * (n + 1) + (s - a) := by omega
    have hN₂ : 2 ≤ n * (n + 1) + s - a := by nlinarith
    rw [supportBound_eq hN₂ (by omega) hN]
    exact small_loss_current hn hs ha has han
  · let b := a - s
    have hb : 1 ≤ b := by dsimp [b]; omega
    have hbn : b < 2 * n := by dsimp [b]; omega
    have hbas : b + s = a := by dsimp [b]; omega
    have hbig : b ≤ n * (n + 1) := by nlinarith
    have habig : a ≤ n * (n + 1) + s := by nlinarith
    have hN : n * (n + 1) + s - a = n * (n + 1) - b := by omega
    rw [hN]
    have hextra := generalBoundAt_extra hn (show s < 2 * n by omega)
    by_cases hbn' : b ≤ n
    · have hU := support_previous_loss hn2 hb hbn'
      have hg := g_lipschitz (u := s) (v := a) (n := n) (by omega) (by omega)
      change g a ≤ g s + n * b at hg
      omega
    · have hU := support_previous_far hn2 (show n < b by omega) hbn
      have hg := g_le_square hn han
      have hp : n - 1 + 1 = n := by omega
      have hsmall : n * (n - 1) ^ 2 + n ^ 2 ≤ n ^ 3 := by
        nlinarith [congrArg (fun z : ℕ => n * z ^ 2) hp,
          congrArg (fun z : ℕ => n * z) hp]
      omega

theorem small_loss_at {N n s a : ℕ} (hn : 0 < n) (hs : s ≤ 2 * n + 1)
    (hN : N = n * (n + 1) + s) (ha : 1 ≤ a) (han : a < 2 * n) :
    g a + supportBound (N - a) ≤ generalBound N - 1 := by
  have hN₂ : 2 ≤ N := by nlinarith
  rw [generalBound_eq hN₂ hs hN, hN]
  exact small_loss hn hs ha han

end Lemmata.Centroid.General
