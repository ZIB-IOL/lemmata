module

public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-! # A uniform cubic secondary-harmonic bound for reduced polygons of size at least 16 -/

@[expose] public section

namespace Lemmata.BellFollowup.Shift

noncomputable section

/-- Sum over the finite arithmetic progression `s, s+2, ..., s+2(n-1)`. -/
def oddSum (f : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0, _ => 0
  | n+1, s => f s + oddSum f n (s+2)

private theorem sum_le {f g : ℝ → ℝ} (n : ℕ) (s : ℝ)
    (h : ∀ k : ℕ, k < n → f (s+2*k) ≤ g (s+2*k)) :
    oddSum f n s ≤ oddSum g n s := by
  induction n generalizing s with
  | zero => simp [oddSum]
  | succ n ih =>
    apply add_le_add
    · simpa using h 0 (Nat.zero_lt_succ _)
    · apply ih
      intro k hk
      have h' := h (k+1) (Nat.succ_lt_succ hk)
      push_cast at h'
      convert h' using 1 <;> congr 1 <;> ring

private theorem sum_scale (f : ℝ → ℝ) (c : ℝ) (n : ℕ) (s : ℝ) :
    oddSum (fun i => c * f i) n s = c * oddSum f n s := by
  induction n generalizing s with
  | zero => simp [oddSum]
  | succ n ih => simp [oddSum, ih, mul_add]

private theorem cube_tail (n : ℕ) (s : ℝ) (hs : 0 < s) :
    oddSum (fun j => 1 / j^3) n (s+2) ≤ 1 / (4*s^2) := by
  induction n generalizing s with
  | zero => change 0 ≤ 1 / (4*s^2); positivity
  | succ n ih =>
    have hs' : 0 < s+2 := by linarith
    calc
      _ ≤ 1/(s+2)^3 + 1/(4*(s+2)^2) :=
        add_le_add le_rfl (ih (s+2) hs')
      _ ≤ _ := by
        field_simp
        nlinarith [sq_nonneg s, sq_nonneg (s*s)]

/-- Cubed Fourier-radius ratio at harmonic order `j`. -/
def secondaryCube (y j : ℝ) : ℝ := (Real.sin y / Real.sin (j*y))^3

private theorem far {y j : ℝ} (hy : 0 < y) (hj1 : 1 ≤ j)
    (hmax : j*y ≤ Real.pi/2) : secondaryCube y j ≤ (11/7 : ℝ)^3 * (1/j^3) := by
  have hj : 0 < j := by linarith
  have hz := mul_pos hj hy
  have chord := Real.mul_le_sin hz.le hmax
  have hpi : Real.pi < (22/7 : ℝ) := by linarith [Real.pi_lt_d4]
  have hpos : 0 < 2/Real.pi*j*y := by positivity
  have chord' : 2/Real.pi*j*y ≤ Real.sin (j*y) := by simpa only [mul_assoc] using chord
  have hs := hpos.trans_le chord'
  have hratio : Real.sin y / Real.sin (j*y) ≤ (11/7 : ℝ) / j := by
    apply (div_le_div_iff₀ hs hj).2
    have hscale : (7 / 11 : ℝ) ≤ 2 / Real.pi := by
      apply (le_div_iff₀ Real.pi_pos).2
      linarith
    nlinarith [mul_le_mul_of_nonneg_right hscale hz.le,
      mul_le_mul_of_nonneg_left (Real.sin_le hy.le) hj.le]
  have hyb : y ≤ j*y := by nlinarith [mul_nonneg (sub_nonneg.mpr hj1) hy.le]
  have hp1 := Real.sin_nonneg_of_nonneg_of_le_pi hy.le (by linarith [Real.pi_pos] : y ≤ Real.pi)
  have posRatio := div_nonneg hp1 hs.le
  unfold secondaryCube
  calc
    (Real.sin y / Real.sin (j*y))^3 ≤ ((11/7 : ℝ)/j)^3 := by gcongr
    _ = _ := by rw [div_pow]; ring

private theorem first {y j : ℝ} (hy : 0 < y) (hmax : y ≤ Real.pi/32)
    (hj : 1 ≤ j) (h7 : j ≤ 7) : secondaryCube y j ≤ (28/25 : ℝ)^3 * (1/j^3) := by
  have hz : 0 < j*y := mul_pos (by linarith) hy
  have hsmall : j*y ≤ 7/10 := by
    calc
      _ ≤ 7*(Real.pi/32) := mul_le_mul h7 hmax hy.le (by norm_num)
      _ ≤ _ := by linarith [Real.pi_lt_d4]
  have hsq : (j*y)^2 ≤ (7/10 : ℝ)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hsmall) (show 0 ≤ 7/10+j*y by linarith)]
  have hl : (9/10 : ℝ)*(j*y) ≤ Real.sin (j*y) := by
    nlinarith [Real.sin_ge_sub_cube hz.le, mul_nonneg hz.le (sub_nonneg.mpr hsq)]
  have hp : 0 < Real.sin (j*y) := by linarith
  have hjp : 0 < j := by linarith
  have hratio : Real.sin y / Real.sin (j*y) ≤ (28/25 : ℝ)/j := by
    apply (div_le_div_iff₀ hp hjp).2
    nlinarith [mul_le_mul_of_nonneg_right (Real.sin_le hy.le) hjp.le]
  have hp1 := Real.sin_nonneg_of_nonneg_of_le_pi hy.le (by linarith [Real.pi_pos] : y ≤ Real.pi)
  have hr := div_nonneg hp1 hp.le
  unfold secondaryCube
  calc
    (Real.sin y / Real.sin (j*y))^3 ≤ ((28/25 : ℝ)/j)^3 := by gcongr
    _ = _ := by rw [div_pow]; ring

/-- The sum of all cubic secondary radii is smaller than 0.086. Here
`2*n+1` is the largest secondary harmonic used (or 1 when the list is empty). -/
theorem secondary_mass (y : ℝ) (hy : 0 < y) (hsmall : y ≤ Real.pi/32)
    (n : ℕ) (hmax : (2*(n : ℝ)+1)*y ≤ Real.pi/2) :
    oddSum (secondaryCube y) n 3 < 86/1000 := by
  have h3 := first hy hsmall (j := 3) (by norm_num) (by norm_num)
  have h5 := first hy hsmall (j := 5) (by norm_num) (by norm_num)
  have h7 := first hy hsmall (j := 7) (by norm_num) (by norm_num)
  rcases n with _ | n
  · norm_num [oddSum]
  rcases n with _ | n
  · norm_num [oddSum] at *; linarith
  rcases n with _ | n
  · norm_num [oddSum] at *; linarith
  rcases n with _ | n
  · norm_num [oddSum] at *; linarith
  have htail : oddSum (secondaryCube y) n 11 ≤ (11/7 : ℝ)^3 * (1/(4*9^2)) := by
    calc
      _ ≤ oddSum (fun j => (11/7 : ℝ)^3 * (1/j^3)) n 11 := by
        apply sum_le
        intro k hk
        have kh : (k : ℝ)+1 ≤ n := by exact_mod_cast (show k+1 ≤ n by omega)
        have ang : (11+2*(k : ℝ))*y ≤ Real.pi/2 := by
          apply le_trans _ hmax
          apply mul_le_mul_of_nonneg_right _ hy.le
          push_cast
          linarith
        exact far hy (by linarith [Nat.cast_nonneg (α := ℝ) k]) ang
      _ = _ := sum_scale _ _ _ _
      _ ≤ _ := by gcongr; convert cube_tail n 9 (by norm_num) using 1; norm_num
  have h9 := far hy (j := 9) (by norm_num) (show 9*y ≤ Real.pi/2 by
    apply le_trans _ hmax
    apply mul_le_mul_of_nonneg_right _ hy.le
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) n])
  simp only [oddSum]
  norm_num
  norm_num at h3 h5 h7 h9 htail
  linarith

private theorem abs_sum (f : ℝ → ℝ) (n : ℕ) (s : ℝ) :
    |oddSum f n s| ≤ oddSum (fun j => |f j|) n s := by
  induction n generalizing s with
  | zero => simp [oddSum]
  | succ n ih =>
    exact (abs_add_le _ _).trans (add_le_add le_rfl (ih (s+2)))

/-- Rescaling the fundamental amplitude on a divisor of the setting count. -/
def polygonScale (x g : ℝ) : ℝ := (g*Real.sin x / Real.sin (g*x))^3

private theorem scale_cap {x g b : ℝ} (hx : 0 < x) (hg : 1 ≤ g)
    (hb : b ≤ 2/5) (hm : g*x ≤ b) :
    0 ≤ polygonScale x g ∧ polygonScale x g ≤ (1 / (1-b^2/6))^3 := by
  have hgp : 0 < g := by linarith
  have hz := mul_pos hgp hx
  have hle : x ≤ g*x := by nlinarith [mul_nonneg (sub_nonneg.mpr hg) hx.le]
  have hbp := hz.trans_le hm
  have hbs : b^2 ≤ (2/5 : ℝ)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hb) (show 0 ≤ 2/5+b by linarith)]
  have hsq : (g*x)^2 ≤ b^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hm) (show 0 ≤ b+g*x by linarith)]
  have hc : 0 < 1-b^2/6 := by linarith
  have hl : (1-b^2/6)*(g*x) ≤ Real.sin (g*x) := by
    nlinarith [Real.sin_ge_sub_cube hz.le, mul_nonneg hz.le (sub_nonneg.mpr hsq)]
  have hs := (mul_pos hc hz).trans_le hl
  have hsin := Real.sin_nonneg_of_nonneg_of_le_pi hx.le
    (by linarith [Real.pi_gt_three] : x ≤ Real.pi)
  have hleft : 0 ≤ g * Real.sin x / Real.sin (g*x) := by positivity
  have hright : g * Real.sin x / Real.sin (g*x) ≤ 1 / (1-b^2/6) := by
    apply (div_le_div_iff₀ hs hc).2
    have hn := mul_le_mul_of_nonneg_left (Real.sin_le hx.le) hgp.le
    nlinarith only [hl, mul_le_mul_of_nonneg_right hn hc.le]
  constructor
  · unfold polygonScale; positivity
  · unfold polygonScale; gcongr

/-- A test supported only at one order of a polygon of reduced length at least four
has absolute value less than one at amplitude coefficient at most 9/10. -/
theorem one_mode_bound {x g a : ℝ} (hx : 0 < x) (hg : 1 ≤ g)
    (hy : g*x ≤ Real.pi/8) (ha : |a| ≤ 9/10) :
    |polygonScale x g * a| < 1 := by
  have ⟨hp, hb⟩ := scale_cap hx hg (b := 393/1000) (by norm_num)
    (by linarith [Real.pi_lt_d4])
  rw [abs_mul, abs_of_nonneg hp]
  have h := mul_le_mul hb ha (abs_nonneg _) (by norm_num)
  linarith

private theorem small_secondary {y j : ℝ} (hy : 0 < y) (hmax : y ≤ Real.pi/24)
    (hj : 3 ≤ j) (ht : j*y ≤ Real.pi/2) : |secondaryCube y j| ≤ 41/1000 := by
  have hs : 0 < Real.sin y := Real.sin_pos_of_pos_of_lt_pi hy (by linarith [Real.pi_pos])
  have sy := Real.sin_le hy.le
  have hsy : Real.sin y ≤ 132/1000 := by linarith [Real.pi_lt_d4]
  have hpow : (Real.sin y)^2 ≤ (132/1000 : ℝ)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hsy)
      (show 0 ≤ 132/1000+Real.sin y by linarith)]
  have h3 : 3*y ≤ j*y := mul_le_mul_of_nonneg_right hj hy.le
  have mono := Real.sin_le_sin_of_le_of_le_pi_div_two
    (by linarith [Real.pi_pos] : -(Real.pi/2) ≤ 3*y) ht h3
  have triple : Real.sin (3*y) = 3*Real.sin y - 4*Real.sin y^3 := by
    rw [show 3*y=2*y+y by ring, Real.sin_add, Real.sin_two_mul, Real.cos_two_mul]
    linear_combination (4*Real.sin y) * Real.sin_sq_add_cos_sq y
  have hlow : (293/100 : ℝ)*Real.sin y ≤ Real.sin (j*y) := by
    nlinarith [mul_nonneg hs.le (sub_nonneg.mpr hpow)]
  have hp : 0 < Real.sin (j*y) := by linarith
  have hratio : Real.sin y / Real.sin (j*y) ≤ (100/293 : ℝ) := by
    apply (div_le_iff₀ hp).2
    linarith
  have hn := div_nonneg hs.le hp.le
  unfold secondaryCube
  rw [abs_of_nonneg (by positivity)]
  calc
    _ ≤ (100/293 : ℝ)^3 := by gcongr
    _ ≤ _ := by norm_num

/-- A test supported at at most two orders, at most one primary, is strictly
bounded on every reduced polygon of length at least twelve. -/
theorem two_mode_bound {x g a b j : ℝ} (hx : 0 < x) (hg : 1 ≤ g)
    (hy : g*x ≤ Real.pi/24) (hj : 3 ≤ j) (ht : j*(g*x) ≤ Real.pi/2)
    (ha : |a| ≤ 9/10) (hb : |b| ≤ 9/10) :
    |polygonScale x g * (a + b * secondaryCube (g*x) j)| < 1 := by
  have hypos := mul_pos (by linarith : 0 < g) hx
  have ⟨kp, kb⟩ := scale_cap hx hg (b := 132/1000) (by norm_num)
    (by linarith [Real.pi_lt_d4])
  have hsec := small_secondary hypos hy hj ht
  have hterm := mul_le_mul hb hsec (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 9/10)
  have hab := abs_add_le a (b * secondaryCube (g*x) j)
  rw [abs_mul] at hab
  rw [abs_mul, abs_of_nonneg kp]
  have hc : |a + b * secondaryCube (g*x) j| ≤ 9/10 + 9/10*(41/1000) := by linarith
  have h := mul_le_mul kb hc (abs_nonneg _) (by norm_num)
  linarith

/-- For a reduced polygon of length at least sixteen, any assignment of signed
coefficients to its distinct harmonic orders with the stated upper bounds scores
strictly below one in absolute value. The coefficients can include arbitrary
cosine phase factors. -/
theorem many_mode_bound (x g : ℝ) (hx : 0 < x) (hg : 1 ≤ g)
    (hy : g*x ≤ Real.pi/32) (n : ℕ) (hmax : (2*(n : ℝ)+1)*(g*x) ≤ Real.pi/2)
    (a : ℝ → ℝ) (hfirst : |a 1| ≤ 9/10)
    (hrest : ∀ k : ℕ, k < n → |a (3+2*k)| ≤ 1054/1000) :
    |polygonScale x g * (a 1 + oddSum (fun j => a j * secondaryCube (g*x) j) n 3)| < 1 := by
  let y := g*x
  have hypos : 0 < y := mul_pos (by linarith : 0 < g) hx
  have hcap := secondary_mass y hypos hy n hmax
  have ⟨kp, kb⟩ := scale_cap hx hg (b := 99/1000) (by norm_num)
    (by linarith [Real.pi_lt_d4])
  have hsum : |oddSum (fun j => a j * secondaryCube y j) n 3| ≤
      (1054/1000) * oddSum (secondaryCube y) n 3 := by
    apply (abs_sum _ _ _).trans
    rw [← sum_scale]
    apply sum_le
    intro k hk
    have hi : (3+2*(k : ℝ))*y ≤ Real.pi/2 := by
      apply le_trans _ hmax
      apply mul_le_mul_of_nonneg_right _ hypos.le
      have h : (k : ℝ)+1 ≤ n := by exact_mod_cast (show k+1 ≤ n by omega)
      linarith
    have hjpos : 0 < (3+2*(k : ℝ))*y := by positivity
    have hsn := Real.sin_nonneg_of_nonneg_of_le_pi hjpos.le (by linarith [Real.pi_pos])
    have hs := Real.sin_nonneg_of_nonneg_of_le_pi hypos.le (by linarith [Real.pi_pos] : y ≤ Real.pi)
    have sc : 0 ≤ secondaryCube y (3+2*(k : ℝ)) := by unfold secondaryCube; positivity
    rw [abs_mul, abs_of_nonneg sc]
    exact mul_le_mul_of_nonneg_right (hrest k hk) sc
  have hwhole : |a 1 + oddSum (fun j => a j * secondaryCube y j) n 3| ≤
      9/10 + 1054/1000 * (86/1000) := by
    linarith [abs_add_le (a 1) (oddSum (fun j => a j * secondaryCube y j) n 3)]
  rw [abs_mul, abs_of_nonneg kp]
  have h := mul_le_mul kb hwhole (abs_nonneg _) (by norm_num)
  change polygonScale x g * |a 1 + oddSum (fun j => a j * secondaryCube y j) n 3| < 1
  linarith

end
end Lemmata.BellFollowup.Shift
