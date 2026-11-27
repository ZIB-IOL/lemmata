module
public import Lemmata.FrankWolfePS.RandomHilbert.Weights
public import Mathlib.Data.Nat.Log
/-! Explicit all-budget conversion of the block estimate, including the small dyadic scales. -/
@[expose] public section
namespace Lemmata.FrankWolfePS.RandomHilbert
noncomputable def loglogT (T : ℕ) := Real.log (Real.log ((T:ℝ)+Real.exp (Real.exp 1)))
noncomputable def rate (T : ℕ) := (7/100000:ℝ)/(((T:ℝ)+2)*Real.log ((T:ℝ)+3)*loglogT T^2)
def scale (T : ℕ) := Nat.clog 2 (T+1)
theorem scale_fits (T : ℕ) : T≤budget (scale T) := by
  have h := Nat.le_pow_clog (by decide : 1<2) (T+1)
  change T≤2^Nat.clog 2 (T+1)-1; omega
private theorem ll_one (T : ℕ) : 1≤loglogT T := by
  have h := Real.log_le_log (Real.exp_pos (Real.exp 1))
    (show Real.exp (Real.exp 1) ≤ (T:ℝ)+Real.exp (Real.exp 1) by linarith [Nat.cast_nonneg (α:=ℝ) T])
  rw [Real.log_exp] at h
  simpa [loglogT] using Real.log_le_log (Real.exp_pos 1) h
private theorem tangent (x : ℝ) (h : 0<x) : Real.log x≤3*(694/1000)+(x-8)/8 := by
  have b := Real.log_le_sub_one_of_pos (div_pos h (by norm_num : (0:ℝ)<8))
  rw [Real.log_div h.ne' (by norm_num : (8:ℝ)≠0),
    show (8:ℝ)=2^3 by norm_num,Real.log_pow] at b
  norm_num only [Nat.cast_ofNat, Nat.cast_one] at b
  linarith [Real.log_two_lt_d9]
private theorem scale_product (T r : ℕ) (lo : 2^r≤T) :
    (7/100000:ℝ)*400*(2:ℝ)^(r+1)*((r:ℝ)+6)*Real.log ((r:ℝ)+6)^2 ≤
      ((T:ℝ)+2)*Real.log ((T:ℝ)+3)*loglogT T^2 := by
  let x := Real.log ((T:ℝ)+3)
  let b := loglogT T
  have lt : (2:ℝ)^r≤T := by exact_mod_cast lo
  have xp : 0<x := Real.log_pos (by linarith [Nat.cast_nonneg (α:=ℝ) T])
  have bp : 1≤b := ll_one T
  have lr : (r:ℝ)*Real.log 2≤x := by
    rw [← Real.log_pow]; apply Real.log_le_log (by positivity); linarith
  have low2 : (693/1000:ℝ)≤Real.log 2 := by linarith [Real.log_two_gt_d9]
  have logr : (r:ℝ)*(693/1000)≤x :=
    (mul_le_mul_of_nonneg_left low2 (Nat.cast_nonneg _)).trans lr
  have logpos : 0≤Real.log ((r:ℝ)+6) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α:=ℝ) r])
  by_cases big : 7≤r
  · have rr : (7:ℝ)≤r := by exact_mod_cast big
    have c : (r:ℝ)+6≤((r:ℝ)*(693/1000))^2 := by nlinarith [sq_nonneg ((r:ℝ)-7)]
    have lL : Real.log ((r:ℝ)+6)≤2*b := by
      have e : (3:ℝ)≤Real.exp (Real.exp 1) := by
        have z := Real.add_one_le_exp (Real.exp 1)
        linarith [Real.exp_one_gt_two]
      have xx := Real.log_le_log (show 0<(T:ℝ)+3 by positivity)
        (show (T:ℝ)+3≤(T:ℝ)+Real.exp (Real.exp 1) by linarith)
      change x≤_ at xx
      have a : 0<(r:ℝ)*(693/1000) := by positivity
      have u := Real.log_le_log (show 0<(r:ℝ)+6 by positivity) c
      rw [Real.log_pow] at u
      have v := Real.log_le_log a (logr.trans xx)
      change _≤b at v; linarith
    have a1 : (2:ℝ)^(r+1)≤2*((T:ℝ)+2) := by rw [pow_succ]; linarith
    have a2 : (r:ℝ)+6≤3*x := by linarith
    have a3 := pow_le_pow_left₀ logpos lL 2
    have calcB := mul_le_mul (mul_le_mul a1 a2 (by positivity) (by positivity)) a3
      (sq_nonneg _) (by positivity : 0≤2*((T:ℝ)+2)*(3*x))
    change _≤((T:ℝ)+2)*x*b^2
    nlinarith only [calcB,mul_nonneg (mul_nonneg (show 0≤(T:ℝ)+2 by positivity) xp.le) (sq_nonneg b)]
  · have sm : r≤6 := by omega
    let k := max 2 r
    have two : (2:ℝ)*Real.log 2≤x := by
      have z : 1≤T := (Nat.one_le_two_pow).trans lo
      have : (2:ℝ)^2≤(T:ℝ)+3 := by exact_mod_cast (show 2^2≤T+3 by omega)
      simpa [Real.log_pow] using Real.log_le_log (by positivity : 0<(2:ℝ)^2) this
    have l : (k:ℝ)*(693/1000)≤x := by
      dsimp [k]; rw [Nat.cast_max,max_mul_of_nonneg _ _ (by norm_num : (0:ℝ)≤693/1000)]
      exact max_le (by push_cast; linarith) logr
    let b0 : ℝ := if 5≤r then 1026/1000 else 1
    have bb : b0≤b := by
      dsimp [b0]; split_ifs with high
      · have large : (32:ℝ)≤T := by exact_mod_cast ((Nat.pow_le_pow_right (by decide : 0<2) high).trans lo)
        have exp3 : Real.exp 3≤27 := by
          rw [show (3:ℝ)=(3:ℕ)*1 by norm_num,Real.exp_nat_mul]
          exact le_trans (pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le 3) (by norm_num)
        have h3 : 3≤Real.log ((T:ℝ)+Real.exp (Real.exp 1)) := (Real.le_log_iff_exp_le (by positivity)).mpr
          (by linarith [Real.exp_pos (Real.exp 1)])
        have lx := Real.log_le_log (by norm_num : (0:ℝ)<3) h3
        have third := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2/3)
        rw [Real.log_div (by norm_num) (by norm_num)] at third
        change Real.log 3≤b at lx; linarith
      · exact bp
    let a : ℝ := 3*(694/1000)+((r:ℝ)-2)/8
    have tang : Real.log ((r:ℝ)+6)≤a := by
      have := tangent ((r:ℝ)+6) (by positivity); dsimp [a]; linarith
    have cert : (7/100000:ℝ)*400*(2:ℝ)^(r+1)*((r:ℝ)+6)*a^2 ≤
        ((2:ℝ)^r+2)*((k:ℝ)*(693/1000))*b0^2 := by
      dsimp [a,k,b0]; interval_cases r <;> norm_num
    apply le_trans _ (le_trans cert _)
    · gcongr
    · change _≤((T:ℝ)+2)*x*b^2
      have bb0 : 0≤b0 := by dsimp [b0]; split_ifs <;> norm_num
      gcongr
theorem rate_le_scale (T : ℕ) : rate T ≤ energy (scale T)/(400*(K (scale T):ℝ)) := by
  let j := scale T
  have jt : T+1≤2^j := Nat.le_pow_clog (by decide) _
  have h0 := ll_one T
  have lg : 0<Real.log ((T:ℝ)+3) := Real.log_pos (by linarith [Nat.cast_nonneg (α:=ℝ) T])
  have ll : 0<loglogT T := by linarith
  have q : 0<Real.log ((j:ℝ)+5) := Real.log_pos (by linarith [Nat.cast_nonneg (α:=ℝ) j])
  have den : (7/100000:ℝ)*400*(K j:ℝ)*((j:ℝ)+5)*Real.log ((j:ℝ)+5)^2 ≤
      ((T:ℝ)+2)*Real.log ((T:ℝ)+3)*loglogT T^2 := by
    cases eq : j with
    | zero =>
      have t : T=0 := by rw [eq] at jt; simp at jt; omega
      subst T; norm_num [K] at ⊢
      have z := tangent 5 (by norm_num)
      have lo : 1≤Real.log 3 := (Real.le_log_iff_exp_le (by norm_num)).mpr Real.exp_one_lt_three.le
      have a := pow_le_pow_left₀ (Real.log_nonneg (by norm_num : (1:ℝ)≤5)) z 2
      have l := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1) h0 2
      nlinarith [mul_le_mul lo l (by norm_num : (0:ℝ)≤1^2) (Real.log_nonneg (by norm_num : (1:ℝ)≤3))]
    | succ r =>
      have less : r<Nat.clog 2 (T+1) := by change r<j; omega
      have fit := (Nat.lt_clog_iff_pow_lt (by decide : 1<2)).mp less
      simpa only [K,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_succ,show (1:ℝ)+5=6 by norm_num,add_assoc]
        using scale_product T r (by omega)
  change rate T≤energy j/(400*(K j:ℝ))
  apply le_trans _ (div_le_div_of_nonneg_right (energy_lower j) (by positivity))
  unfold rate
  have kpos : 0<(K j:ℝ) := by exact_mod_cast K_pos j
  rw [le_div_iff₀ (by positivity),div_mul_eq_mul_div,div_le_div_iff₀ (by positivity) (by positivity)]
  linarith only [den]
end Lemmata.FrankWolfePS.RandomHilbert
