module

public import Lemmata.Centroid.Proof.General.Numeric
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity

@[expose] public section

noncomputable section

namespace Lemmata.Centroid.General

def phi (Q B : ℝ) : ℝ := (Q - B) * Real.sqrt (Q - 2) + B ^ (3 / 2 : ℝ)

theorem phi_eq {Q B : ℝ} (hB : 0 ≤ B) :
    phi Q B = (Q - B) * Real.sqrt (Q - 2) + B * Real.sqrt B := by
  unfold phi
  rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num,
    Real.rpow_add_one' hB (by norm_num), ← Real.sqrt_eq_rpow, mul_comm (Real.sqrt B)]

theorem phi_convex (Q : ℝ) : ConvexOn ℝ (Set.Ici 0) (phi Q) := by
  refine ⟨convex_Ici _, ?_⟩
  intro x hx y hy a b ha hb hab
  have hp := (convexOn_rpow (by norm_num : (1 : ℝ) ≤ 3 / 2)).2 hx hy ha hb hab
  have hlin : (Q - (a * x + b * y)) * Real.sqrt (Q - 2) =
      a * ((Q - x) * Real.sqrt (Q - 2)) + b * ((Q - y) * Real.sqrt (Q - 2)) := by
    nlinarith [congrArg (fun z : ℝ => z * Q * Real.sqrt (Q - 2)) hab]
  simp only [phi, smul_eq_mul] at hp ⊢
  nlinarith only [hp, hlin]

theorem phi_lt_of_endpoints {Q l u B μ : ℝ} (hl : 0 ≤ l) (hlB : l ≤ B) (hBu : B ≤ u)
    (hlμ : phi Q l < μ) (huμ : phi Q u < μ) : phi Q B < μ := by
  have h := (phi_convex Q).le_max_of_mem_Icc hl (by linarith : 0 ≤ u) ⟨hlB, hBu⟩
  exact lt_of_le_of_lt h (max_lt hlμ huμ)

theorem sqrt_tangent {z u : ℝ} (hz : 0 ≤ z) (hu : 0 < u) :
    Real.sqrt z ≤ u + (z - u ^ 2) / (2 * u) := by
  have hsq := Real.sq_sqrt hz
  have h := sq_nonneg (Real.sqrt z - u)
  have heq : 2 * u * (u + (z - u ^ 2) / (2 * u)) = z + u ^ 2 := by
    field_simp
    ring
  nlinarith

theorem phi_first_left {n s μ : ℝ} (hn : 3 ≤ n) (hs : 1 ≤ s)
    (hμ : n ^ 3 + s * (s - 1) + 1 ≤ μ) : phi (n ^ 2 + s) n < μ := by
  have hn0 : 0 < n := by linarith
  have hQ0 : 0 ≤ n ^ 2 + s - 2 := by nlinarith
  have hQ := sqrt_tangent hQ0 hn0
  have hN := sqrt_tangent (by linarith : 0 ≤ n) (by norm_num : (0 : ℝ) < 2)
  have hQ' : Real.sqrt (n ^ 2 + s - 2) ≤ n + (s - 2) / (2 * n) := by
    convert hQ using 1; ring
  have hN' : Real.sqrt n ≤ (n + 4) / 4 := by linarith
  let P := (n ^ 2 + s - n) * (n + (s - 2) / (2 * n)) + n * ((n + 4) / 4)
  have hP : phi (n ^ 2 + s) n ≤ P := by
    rw [phi_eq (by linarith : 0 ≤ n)]
    exact add_le_add (mul_le_mul_of_nonneg_left hQ' (by nlinarith))
      (mul_le_mul_of_nonneg_left hN' (by linarith))
  have hid : 4 * n * (n ^ 3 + s * (s - 1) + 1 - P) =
      (n - 1) * (s - 2) ^ 2 + (3 * n - 1) * (n - s) ^ 2 + (n - 2) ^ 2 := by
    dsimp [P]
    field_simp
    ring
  have h₁ : 0 ≤ (n - 1) * (s - 2) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have h₂ : 0 ≤ (3 * n - 1) * (n - s) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have h₃ : 0 < (n - 2) ^ 2 := sq_pos_of_pos (by linarith)
  have hpos : 0 < 4 * n * (n ^ 3 + s * (s - 1) + 1 - P) := by rw [hid]; linarith
  have hgap : P < n ^ 3 + s * (s - 1) + 1 := by nlinarith
  exact lt_of_le_of_lt hP (lt_of_lt_of_le hgap hμ)

theorem phi_first_right {n s μ : ℝ} (hn : 4 ≤ n) (hs : 1 ≤ s)
    (hμ : n ^ 3 + s * (s - 1) + 1 ≤ μ) :
    phi (n ^ 2 + s) (n ^ 2 + s - 2 * n) < μ := by
  have hn0 : 0 < n := by linarith
  have hn1 : 0 < n - 1 := by linarith
  have hQ0 : 0 ≤ n ^ 2 + s - 2 := by nlinarith
  have hE0 : 0 ≤ n ^ 2 + s - 2 * n := by nlinarith
  have hQ := sqrt_tangent hQ0 hn0
  have hE := sqrt_tangent hE0 hn1
  have hQ' : Real.sqrt (n ^ 2 + s - 2) ≤ n + (s - 2) / (2 * n) := by
    convert hQ using 1; ring
  have hE' : Real.sqrt (n ^ 2 + s - 2 * n) ≤ n - 1 + (s - 1) / (2 * (n - 1)) := by
    convert hE using 1; ring
  let P := 2 * n * (n + (s - 2) / (2 * n)) +
    (n ^ 2 + s - 2 * n) * (n - 1 + (s - 1) / (2 * (n - 1)))
  have hP : phi (n ^ 2 + s) (n ^ 2 + s - 2 * n) ≤ P := by
    rw [phi_eq hE0]
    have heq : n ^ 2 + s - (n ^ 2 + s - 2 * n) = 2 * n := by ring
    rw [heq]
    exact add_le_add (mul_le_mul_of_nonneg_left hQ' (by linarith))
      (mul_le_mul_of_nonneg_left hE' hE0)
  have hid : 4 * (n - 1) * (n ^ 3 + s * (s - 1) + 1 - P) =
      (n - 1) * (s - 3) ^ 2 + (3 * n - 5) * (n - s) ^ 2 + (n - 1) ^ 2 * (n - 3) := by
    dsimp [P]
    field_simp
    ring
  have h₁ : 0 ≤ (n - 1) * (s - 3) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have h₂ : 0 ≤ (3 * n - 5) * (n - s) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have h₃ : 0 < (n - 1) ^ 2 * (n - 3) := mul_pos (sq_pos_of_pos hn1) (by linarith)
  have hpos : 0 < 4 * (n - 1) * (n ^ 3 + s * (s - 1) + 1 - P) := by rw [hid]; linarith
  have hgap : P < n ^ 3 + s * (s - 1) + 1 := by nlinarith
  exact lt_of_le_of_lt hP (lt_of_lt_of_le hgap hμ)

theorem phi_six_two : phi 6 2 < 11 := by
  have h : Real.sqrt 2 < (3 : ℝ) / 2 := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  have h4 : Real.sqrt (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  rw [phi_eq (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num
  rw [h4]
  nlinarith

theorem phi_ten_four : phi 10 4 < 28 := by
  have h : Real.sqrt 8 < (3 : ℝ) := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  have h4 : Real.sqrt (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  rw [phi_eq (by norm_num : (0 : ℝ) ≤ 4)]
  norm_num
  rw [h4]
  nlinarith

theorem phi_eleven_five : phi 11 5 < 30 := by
  have h : Real.sqrt 5 < (12 : ℝ) / 5 := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  have h9 : Real.sqrt (9 : ℝ) = 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  rw [phi_eq (by norm_num : (0 : ℝ) ≤ 5)]
  norm_num
  rw [h9]
  nlinarith

theorem phi_twelve_six : phi 12 6 < 34 := by
  have h₁ : Real.sqrt 10 < (19 : ℝ) / 6 := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  have h₂ : Real.sqrt 6 < (5 : ℝ) / 2 := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  rw [phi_eq (by norm_num : (0 : ℝ) ≤ 6)]
  norm_num
  nlinarith

theorem phi_first_left_nat {n s : ℕ} {μ : ℝ} (hn : 2 ≤ n) (hs : 1 ≤ s) (hsn : s ≤ n)
    (hfeas : (n : ℝ) ≤ (n : ℝ) ^ 2 + s - 2 * n)
    (hμ : (n : ℝ) ^ 3 + s * ((s : ℝ) - 1) + 1 ≤ μ) :
    phi ((n : ℝ) ^ 2 + s) n < μ := by
  by_cases hn2 : n = 2
  · subst n
    have hs2 : s = 2 := by norm_num at hfeas; omega
    subst s
    norm_num at hμ ⊢
    exact lt_of_lt_of_le phi_six_two hμ
  · exact phi_first_left (by exact_mod_cast (show 3 ≤ n by omega))
      (by exact_mod_cast hs) hμ

theorem phi_first_right_nat {n s : ℕ} {μ : ℝ} (hn : 2 ≤ n) (hs : 1 ≤ s) (hsn : s ≤ n)
    (hfeas : (n : ℝ) ≤ (n : ℝ) ^ 2 + s - 2 * n)
    (hμ : (n : ℝ) ^ 3 + s * ((s : ℝ) - 1) + 1 ≤ μ) :
    phi ((n : ℝ) ^ 2 + s) ((n : ℝ) ^ 2 + s - 2 * n) < μ := by
  by_cases hn4 : 4 ≤ n
  · exact phi_first_right (by exact_mod_cast hn4) (by exact_mod_cast hs) hμ
  by_cases hn2 : n = 2
  · subst n
    have hs2 : s = 2 := by norm_num at hfeas; omega
    subst s
    norm_num at hμ ⊢
    exact lt_of_lt_of_le phi_six_two hμ
  have hn3 : n = 3 := by omega
  subst n
  interval_cases s
  · norm_num at hμ ⊢
    exact lt_of_lt_of_le phi_ten_four hμ
  · norm_num at hμ ⊢
    exact lt_of_lt_of_le phi_eleven_five hμ
  · norm_num at hμ ⊢
    exact lt_of_lt_of_le phi_twelve_six hμ

theorem common_tail_first {n s : ℕ} {B μ : ℝ} (hn : 2 ≤ n) (hs : 1 ≤ s) (hsn : s ≤ n)
    (hB : (n : ℝ) ≤ B) (hBQ : B ≤ (n : ℝ) ^ 2 + s - 2 * n)
    (hμ : (n : ℝ) ^ 3 + s * ((s : ℝ) - 1) + 1 ≤ μ) :
    phi ((n : ℝ) ^ 2 + s) B < μ :=
  phi_lt_of_endpoints (by positivity) hB hBQ
    (phi_first_left_nat hn hs hsn (hB.trans hBQ) hμ)
    (phi_first_right_nat hn hs hsn (hB.trans hBQ) hμ)

theorem phi_second_left {n t μ : ℝ} (hn : 2 ≤ n) (ht : 0 ≤ t)
    (hμ : n * (n ^ 2 + n + t) + t ^ 2 + 1 ≤ μ) :
    phi (n ^ 2 + n + t) n < μ := by
  have hn0 : 0 < n := by linarith
  have hQ0 : 0 ≤ n ^ 2 + n + t - 2 := by nlinarith
  have hQ := sqrt_tangent hQ0 hn0
  have hN := sqrt_tangent (by linarith : 0 ≤ n) (by norm_num : (0 : ℝ) < 2)
  have hQ' : Real.sqrt (n ^ 2 + n + t - 2) ≤ n + (n + t - 2) / (2 * n) := by
    convert hQ using 1; ring
  have hN' : Real.sqrt n ≤ (n + 4) / 4 := by linarith
  let P := (n ^ 2 + t) * (n + (n + t - 2) / (2 * n)) + n * ((n + 4) / 4)
  have hP : phi (n ^ 2 + n + t) n ≤ P := by
    rw [phi_eq (by linarith : 0 ≤ n)]
    have heq : n ^ 2 + n + t - n = n ^ 2 + t := by ring
    rw [heq]
    exact add_le_add (mul_le_mul_of_nonneg_left hQ' (by positivity))
      (mul_le_mul_of_nonneg_left hN' (by linarith))
  have hid : 4 * n * (n * (n ^ 2 + n + t) + t ^ 2 + 1 - P) =
      (n + 2) * (t - n + 1) ^ 2 + (3 * n - 4) * t ^ 2 + 7 * n - 2 := by
    dsimp [P]
    field_simp
    ring
  have h₁ : 0 ≤ (n + 2) * (t - n + 1) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have h₂ : 0 ≤ (3 * n - 4) * t ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have hpos : 0 < 4 * n * (n * (n ^ 2 + n + t) + t ^ 2 + 1 - P) := by rw [hid]; linarith
  have hgap : P < n * (n ^ 2 + n + t) + t ^ 2 + 1 := by nlinarith
  exact lt_of_le_of_lt hP (lt_of_lt_of_le hgap hμ)

theorem phi_second_right {n t μ : ℝ} (hn : 2 ≤ n) (ht : 0 ≤ t)
    (hμ : n * (n ^ 2 + n + t) + t ^ 2 + 1 ≤ μ) :
    phi (n ^ 2 + n + t) (n ^ 2 - n + t) < μ := by
  have hn0 : 0 < n := by linarith
  have hQ0 : 0 ≤ n ^ 2 + n + t - 2 := by nlinarith
  have hE0 : 0 ≤ n ^ 2 - n + t := by nlinarith
  have hQ := sqrt_tangent hQ0 hn0
  have hE := sqrt_tangent hE0 hn0
  have hQ' : Real.sqrt (n ^ 2 + n + t - 2) ≤ n + (n + t - 2) / (2 * n) := by
    convert hQ using 1; ring
  have hE' : Real.sqrt (n ^ 2 - n + t) ≤ n + (t - n) / (2 * n) := by
    convert hE using 1; ring
  let P := 2 * n * (n + (n + t - 2) / (2 * n)) +
    (n ^ 2 - n + t) * (n + (t - n) / (2 * n))
  have hP : phi (n ^ 2 + n + t) (n ^ 2 - n + t) ≤ P := by
    rw [phi_eq hE0]
    have heq : n ^ 2 + n + t - (n ^ 2 - n + t) = 2 * n := by ring
    rw [heq]
    exact add_le_add (mul_le_mul_of_nonneg_left hQ' (by linarith))
      (mul_le_mul_of_nonneg_left hE' hE0)
  have hid : 4 * n * (n * (n ^ 2 + n + t) + t ^ 2 + 1 - P) =
      n * (t - n) ^ 2 + (3 * n - 2) * t ^ 2 + n * ((n - 3) ^ 2 + 3) := by
    dsimp [P]
    field_simp
    ring
  have h₁ : 0 ≤ n * (t - n) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have h₂ : 0 ≤ (3 * n - 2) * t ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have h₃ : 0 < n * ((n - 3) ^ 2 + 3) := mul_pos hn0 (by positivity)
  have hpos : 0 < 4 * n * (n * (n ^ 2 + n + t) + t ^ 2 + 1 - P) := by rw [hid]; linarith
  have hgap : P < n * (n ^ 2 + n + t) + t ^ 2 + 1 := by nlinarith
  exact lt_of_le_of_lt hP (lt_of_lt_of_le hgap hμ)

theorem common_tail_second {n t : ℕ} {B μ : ℝ} (hn : 2 ≤ n)
    (hB : (n : ℝ) ≤ B) (hBQ : B ≤ (n : ℝ) ^ 2 - n + t)
    (hμ : (n : ℝ) * ((n : ℝ) ^ 2 + n + t) + (t : ℝ) ^ 2 + 1 ≤ μ) :
    phi ((n : ℝ) ^ 2 + n + t) B < μ :=
  phi_lt_of_endpoints (by positivity) hB hBQ
    (phi_second_left (by exact_mod_cast hn) (by positivity) hμ)
    (phi_second_right (by exact_mod_cast hn) (by positivity) hμ)

def radicalQ (n s : ℕ) : ℕ := if s ≤ n then n ^ 2 + s else n ^ 2 + s - 1

theorem common_tail_at {n s : ℕ} {B : ℝ} (hn : 2 ≤ n) (hs : 1 ≤ s) (hsn : s ≤ 2 * n + 1)
    (hB : (n : ℝ) ≤ B) (hBQ : B ≤ radicalQ n s - 2 * (n : ℝ)) :
    phi (radicalQ n s) B < (generalBoundAt n s : ℝ) := by
  by_cases hsn' : s ≤ n
  · have hQ : radicalQ n s = n ^ 2 + s := by simp [radicalQ, hsn']
    rw [hQ] at hBQ ⊢
    push_cast at hBQ ⊢
    have hμNat : n ^ 3 + s * (s - 1) + 1 ≤ generalBoundAt n s := by
      by_cases hs1 : s = 1
      · subst s
        simp
      · simp [generalBoundAt, show s ≠ 0 by omega, hs1, hsn']
    have hc : ((n ^ 3 + s * (s - 1) + 1 : ℕ) : ℝ) ≤ (generalBoundAt n s : ℝ) := by
      exact_mod_cast hμNat
    have hμ : (n : ℝ) ^ 3 + s * ((s : ℝ) - 1) + 1 ≤ (generalBoundAt n s : ℝ) := by
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_one, Nat.cast_sub hs] using hc
    exact common_tail_first hn hs hsn' hB hBQ hμ
  · let t := s - n - 1
    have ht : t ≤ n := by dsimp [t]; omega
    have hst : s = n + 1 + t := by dsimp [t]; omega
    rw [hst] at hBQ ⊢
    have hQ : radicalQ n (n + 1 + t) = n ^ 2 + n + t := by
      simp only [radicalQ, show ¬ n + 1 + t ≤ n by omega, ite_false]
      omega
    rw [hQ] at hBQ ⊢
    push_cast at hBQ ⊢
    have hpred := generalBoundAt_second_pred n t (show 0 < n by omega)
    have hmax := le_max_right n (t ^ 2)
    have hpos : 0 < generalBoundAt n (n + 1 + t) := by
      rw [generalBoundAt_second (show 0 < n by omega)]
      omega
    have hμNat : n * (n ^ 2 + n + t) + t ^ 2 + 1 ≤ generalBoundAt n (n + 1 + t) := by omega
    have hμ : (n : ℝ) * ((n : ℝ) ^ 2 + n + t) + (t : ℝ) ^ 2 + 1 ≤
        (generalBoundAt n (n + 1 + t) : ℝ) := by exact_mod_cast hμNat
    exact common_tail_second hn hB (by nlinarith) hμ

theorem common_tail {N n s : ℕ} {B : ℝ} (hn : 2 ≤ n) (hs : 1 ≤ s) (hsn : s ≤ 2 * n + 1)
    (hN : N = n * (n + 1) + s) (hB : (n : ℝ) ≤ B)
    (hBQ : B ≤ radicalQ n s - 2 * (n : ℝ)) : phi (radicalQ n s) B < (generalBound N : ℝ) := by
  have hN₂ : 2 ≤ N := by nlinarith
  rw [generalBound_eq hN₂ hsn hN]
  exact common_tail_at hn hs hsn hB hBQ

end Lemmata.Centroid.General
