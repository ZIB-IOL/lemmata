module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Int
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.SplitIfs
public import Mathlib.Tactic.Zify

public section

namespace Lemmata.FishburnReedsClassicalBound.Block

def kernel : ℕ → ℤ
  | 0 => 8
  | 1 => 2
  | _ + 2 => 0

private theorem kernel_le (t : ℕ) : kernel t ≤ 8 := by
  cases t with
  | zero => decide
  | succ t => cases t <;> simp [kernel]

private theorem kernel_off {t : ℕ} (h : 2 ≤ t) : kernel t = 0 := by
  cases t with
  | zero => omega
  | succ t => cases t with
    | zero => omega
    | succ t => rfl

def pairTerm (x y : ℕ) : ℤ := kernel (x-y) + kernel (x+y)

private theorem pair_le (x y : ℕ) : pairTerm x y ≤ 16 := by
  unfold pairTerm
  linarith [kernel_le (x-y), kernel_le (x+y)]

private theorem pair_le_pos {x : ℕ} (hx : 0 < x) (y : ℕ) : pairTerm x y ≤ 8 := by
  by_cases h : 2 ≤ x+y
  · simpa [pairTerm, kernel_off h] using kernel_le (x-y)
  · have hx1 : x = 1 := by omega
    have hy0 : y = 0 := by omega
    subst x
    subst y
    decide

def cross (x : ℕ) : List ℕ → ℤ
  | [] => 0
  | y :: ys => pairTerm x y + cross x ys

private theorem cross_le (x : ℕ) (ys : List ℕ) (cap : ℤ)
    (hc : ∀ y, pairTerm x y ≤ cap) : cross x ys ≤ cap * (ys.length : ℤ) := by
  induction ys with
  | nil => simp [cross]
  | cons y ys ih =>
    simp only [cross, List.length_cons, Nat.cast_succ]
    nlinarith [hc y]

def penalty (x : ℕ) : ℤ := if x % 2 = 0 then 0 else 3

private theorem penalty_nn (x : ℕ) : 0 ≤ penalty x := by
  unfold penalty
  split <;> norm_num

/-- A zero block in decreasing order. The tail length is the ascending target index. -/
def score : List ℕ → ℤ
  | [] => 0
  | x :: xs => score xs + cross x xs
      - 3 * ((x : ℤ) - 2 * (xs.length : ℤ))^2 - penalty x

private theorem zero_peel (x : ℕ) (xs : List ℕ) (hx : x ≤ xs.length)
    (hn : 3 ≤ xs.length) : score (x :: xs) ≤ score xs := by
  have hn' : (3 : ℤ) ≤ (xs.length : ℤ) := by exact_mod_cast hn
  have hx' : (x : ℤ) ≤ (xs.length : ℤ) := by exact_mod_cast hx
  have hprod : 0 ≤ (xs.length : ℤ) * ((xs.length : ℤ) - 3) :=
    mul_nonneg (by positivity) (by linarith)
  by_cases h0 : x = 0
  · subst x
    have hc := cross_le 0 xs 16 (pair_le 0)
    change score xs + cross 0 xs - 3 * ((0 : ℤ) - 2 * (xs.length : ℤ))^2
      - penalty 0 ≤ score xs
    nlinarith [penalty_nn 0]
  · have hp : 0 < x := by omega
    have hc := cross_le x xs 8 (pair_le_pos hp)
    have hrs : 0 ≤ ((xs.length : ℤ) - (x : ℤ)) * (3 * (xs.length : ℤ) - (x : ℤ)) :=
      mul_nonneg (by linarith) (by linarith)
    change score xs + cross x xs - 3 * ((x : ℤ) - 2 * (xs.length : ℤ))^2
      - penalty x ≤ score xs
    nlinarith [penalty_nn x]

def top : List Bool → ℕ
  | [] => 0
  | b :: bs => top bs + (if b then 1 else 0)

def coords : List Bool → List ℕ
  | [] => [0]
  | b :: bs => top (b :: bs) :: coords bs

private theorem coords_length (bs : List Bool) : (coords bs).length = bs.length + 1 := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [coords, ih]

private theorem top_le (bs : List Bool) : top bs ≤ bs.length := by
  induction bs with
  | nil => decide
  | cons b bs ih => cases b <;> simp [top] <;> omega

/-- The only zero-block word allowed a positive upper bound is the two-zero word. -/
theorem zero_block (bs : List Bool) :
    score (coords bs) ≤ (if bs = [false] then 4 else 0) := by
  induction bs with
  | nil => decide
  | cons b bs ih =>
    cases bs with
    | nil => cases b <;> decide
    | cons b₁ tail =>
      cases tail with
      | nil => cases b <;> cases b₁ <;> decide
      | cons b₂ tail =>
        have htop : top (b :: b₁ :: b₂ :: tail) ≤ (coords (b₁ :: b₂ :: tail)).length := by
          simpa only [coords_length, List.length_cons] using top_le (b :: b₁ :: b₂ :: tail)
        have hlen : 3 ≤ (coords (b₁ :: b₂ :: tail)).length := by
          rw [coords_length]
          simp only [List.length_cons]
          omega
        have hold : score (coords (b₁ :: b₂ :: tail)) ≤ 0 := by simpa using ih
        have hnew : score (coords (b :: b₁ :: b₂ :: tail)) ≤ 0 :=
          (zero_peel _ _ htop hlen).trans hold
        simpa using hnew

private theorem positive_peel_raw {R f C : ℤ} (hr : 3 + f ≤ 2 * R)
    (hc : C ≤ 8 * f + 2) : C < 3 * R^2 := by
  nlinarith [sq_nonneg (3*R-8)]

def bit (b : Bool) : ℕ := if b then 1 else 0
def step (b : Bool) : ℤ := if b then 1 else 2
def flats : List Bool → ℤ
  | [] => 0
  | b :: bs => (if b then 0 else 1) + flats bs
def fall : List Bool → ℤ
  | [] => 0
  | b :: bs => step b + fall bs

private theorem fall_eq (gs : List Bool) : fall gs = (gs.length : ℤ) + flats gs := by
  induction gs with
  | nil => decide
  | cons b gs ih => cases b <;> simp [fall, step, flats, ih] <;> ring

def reach (h : ℕ) : List Bool → ℤ
  | [] => 0
  | b :: bs => kernel (h + bit b) + reach (h + bit b) bs

def fromRight : List Bool → ℤ
  | [] => 0
  | b :: bs => kernel (top (b :: bs)) + fromRight bs

private theorem reach_snoc (h : ℕ) (gs : List Bool) (c : Bool) :
    reach h (gs ++ [c]) = reach h gs + kernel (h + top (gs ++ [c])) := by
  induction gs generalizing h with
  | nil => simp [reach, top, bit]
  | cons b gs ih => simp [reach, top, bit, ih, add_assoc, add_comm, add_left_comm]

private theorem reach_bound (h : ℕ) (gs : List Bool) :
    reach h gs ≤ 8 * flats gs + (if h = 0 then 2 else 0) := by
  induction gs generalizing h with
  | nil => by_cases he : h = 0 <;> simp [reach, flats, he]
  | cons b gs ih =>
    cases b with
    | false =>
      change kernel h + reach h gs ≤ 8*(1+flats gs) + (if h=0 then 2 else 0)
      linarith [ih h, kernel_le h]
    | true =>
      cases h with
      | zero =>
        have hh : reach 1 gs ≤ 8*flats gs := by simpa using ih 1
        change (2 : ℤ) + reach 1 gs ≤ 8*(0+flats gs)+2
        linarith
      | succ h =>
        have hn : h+2 ≠ 0 := by omega
        have hh : reach (h+2) gs ≤ 8*flats gs := by simpa [hn] using ih (h+2)
        change (0 : ℤ) + reach (h+2) gs ≤ 8*(0+flats gs)+0
        linarith

private theorem right_bound (gs : List Bool) :
    fromRight gs ≤ 8 * flats gs + (if top gs = 0 then 0 else 2) := by
  induction gs with
  | nil => decide
  | cons b gs ih =>
    cases b with
    | false =>
      change kernel (top gs) + fromRight gs ≤ 8*(1+flats gs) + (if top gs=0 then 0 else 2)
      linarith [kernel_le (top gs)]
    | true =>
      by_cases h : top gs = 0
      · simp [h] at ih
        simpa [fromRight, flats, top, h, kernel, add_comm] using
          (show 2 + fromRight gs ≤ 2 + 8 * flats gs by linarith)
      · have ht : 2 ≤ top gs + 1 := by omega
        simp [h] at ih
        simpa [fromRight, top, flats, kernel_off ht] using ih

private theorem reach_length (h : ℕ) (gs : List Bool) :
    reach h gs ≤ 8 * (gs.length : ℤ) := by
  induction gs generalizing h with
  | nil => simp [reach]
  | cons b gs ih =>
    simp only [reach, List.length_cons, Nat.cast_succ]
    linarith [ih (h+bit b), kernel_le (h+bit b)]

def oddI (r : ℤ) : Bool := decide (r % 2 ≠ 0)
def loss (r : ℤ) : ℤ := 3*r^2 + (if oddI r then 3 else 0)
def cap (o : Bool) : ℤ := if o then -4 else 0

def hasOdd (r : ℤ) : List Bool → Bool
  | [] => oddI r
  | b :: gs => oddI r || hasOdd (r-step b) gs

/-- Positive-block score from the initial coordinate minus its target and its adjacent gaps. -/
def posScore (r : ℤ) : List Bool → ℤ
  | [] => -loss r
  | b :: gs => posScore (r-step b) gs + reach 0 (b :: gs) - loss r

private theorem loss_ge (r : ℤ) : 3*r^2 ≤ loss r := by
  unfold loss
  cases oddI r <;> simp <;> omega

private theorem cap_ge (o : Bool) : -4 ≤ cap o := by cases o <;> decide

private theorem rough (r : ℤ) (gs : List Bool) :
    posScore r gs ≤ 4*(gs.length : ℤ)*((gs.length : ℤ)+1) - 3*r^2 := by
  induction gs generalizing r with
  | nil =>
    simp only [posScore, List.length_nil, Nat.cast_zero, mul_zero, zero_mul, zero_sub]
    linarith [loss_ge r]
  | cons b gs ih =>
    have hr := reach_length 0 (b::gs)
    simp only [List.length_cons, Nat.cast_succ] at hr ⊢
    rw [posScore]
    nlinarith [ih (r-step b), sq_nonneg (r-step b), loss_ge r]

private theorem small (r : ℤ) (gs : List Bool) (hs : gs.length ≤ 2) :
    posScore r gs ≤ cap (hasOdd r gs) := by
  have hlen : (gs.length : ℤ) ≤ 2 := by exact_mod_cast hs
  have hp : 0 ≤ (2-(gs.length : ℤ))*((gs.length : ℤ)+3) :=
    mul_nonneg (by linarith) (by positivity)
  have hrough : posScore r gs ≤ 24-3*r^2 := by nlinarith [rough r gs]
  by_cases hlow : r < -3
  · have h4 : r ≤ -4 := by omega
    exact (show posScore r gs ≤ -4 by nlinarith [sq_nonneg (r+4)]).trans (cap_ge _)
  by_cases hhigh : 3 < r
  · have h4 : 4 ≤ r := by omega
    exact (show posScore r gs ≤ -4 by nlinarith [sq_nonneg (r-4)]).trans (cap_ge _)
  have h₁ : -3 ≤ r := by omega
  have h₂ : r ≤ 3 := by omega
  cases gs with
  | nil => interval_cases r <;> decide
  | cons b gs =>
    cases gs with
    | nil => cases b <;> interval_cases r <;> decide
    | cons c gs =>
      cases gs with
      | nil => cases b <;> cases c <;> interval_cases r <;> decide
      | cons e gs => simp only [List.length_cons] at hs; omega

private theorem score_snoc (r : ℤ) (gs : List Bool) (c : Bool) :
    posScore r (gs ++ [c]) = posScore r gs + fromRight (gs ++ [c])
       - loss (r - fall (gs ++ [c])) := by
  induction gs generalizing r with
  | nil => cases c <;> simp [posScore, reach, fromRight, top, bit, fall, step] <;> ring
  | cons b gs ih =>
    change posScore (r-step b) (gs++[c]) + reach 0 ((b::gs)++[c]) - loss r =
      (posScore (r-step b) gs + reach 0 (b::gs) - loss r) +
      (kernel (top ((b::gs)++[c])) + fromRight (gs++[c])) -
      loss (r-(step b + fall (gs++[c])))
    have hh : r-step b-fall (gs++[c]) = r-(step b+fall (gs++[c])) := by ring
    rw [ih, reach_snoc, hh]
    simp only [Nat.zero_add]
    ring

private theorem odd_snoc (r : ℤ) (gs : List Bool) (c : Bool) :
    hasOdd r (gs ++ [c]) = (hasOdd r gs || oddI (r - fall (gs ++ [c]))) := by
  induction gs generalizing r with
  | nil => simp [hasOdd, fall]
  | cons b gs ih =>
    change (oddI r || hasOdd (r-step b) (gs++[c])) =
      ((oddI r || hasOdd (r-step b) gs) || oddI (r-(step b+fall (gs++[c]))))
    have hh : r-step b-fall (gs++[c]) = r-(step b+fall (gs++[c])) := by ring
    rw [ih, hh, Bool.or_assoc]

private theorem splitLast (b : Bool) (gs : List Bool) :
    ∃ (p : List Bool) (c : Bool), b::gs = p++[c] := by
  induction gs generalizing b with
  | nil => exact ⟨[], b, rfl⟩
  | cons e gs ih =>
    obtain ⟨p, c, hp⟩ := ih e
    exact ⟨b::p, c, congrArg (List.cons b) hp⟩

private theorem oneEnd (old C r : ℤ) (o : Bool)
    (ho : old ≤ cap o) (hc : C < 3*r^2) :
    old + C - loss r ≤ cap (o || oddI r) := by
  simp only [loss, cap] at *
  cases e : oddI r <;> cases o <;> simp_all <;> omega

private theorem posInduction (n : ℕ) :
    ∀ gs : List Bool, gs.length = n → ∀ r : ℤ, posScore r gs ≤ cap (hasOdd r gs) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro gs hlen r
    cases gs with
    | nil => exact small r [] (by decide)
    | cons b gs =>
      by_cases hs : (b::gs).length ≤ 2
      · exact small r (b::gs) hs
      have h3 : 3 ≤ (b::gs).length := by omega
      have hi3 : (3 : ℤ) ≤ ((b::gs).length : ℤ) := by exact_mod_cast h3
      have hfall := fall_eq (b::gs)
      by_cases hl : 3 + flats (b::gs) ≤ 2*r
      · have hc : reach 0 (b::gs) ≤ 8*flats (b::gs)+2 :=
          (reach_bound 0 (b::gs)).trans_eq (by simp)
        have hp := positive_peel_raw hl hc
        have lt : gs.length < n := by simp only [List.length_cons] at hlen; omega
        have hold := ih gs.length lt gs rfl (r-step b)
        change posScore (r-step b) gs + reach 0 (b::gs) - loss r ≤
          cap (oddI r || hasOdd (r-step b) gs)
        rw [Bool.or_comm (oddI r) (hasOdd (r-step b) gs)]
        exact oneEnd _ _ _ _ hold hp
      · have hr : 3 + flats (b::gs) ≤ 2*(-(r-fall (b::gs))) := by omega
        have he := right_bound (b::gs)
        have hc : fromRight (b::gs) ≤ 8*flats (b::gs)+2 := by
          split_ifs at he <;> omega
        have hraw := positive_peel_raw hr hc
        have hright : fromRight (b::gs) < 3*(r-fall (b::gs))^2 := by nlinarith
        obtain ⟨p,c,hp⟩ := splitLast b gs
        have lt : p.length < n := by
          rw [hp] at hlen
          simp at hlen
          omega
        have hold := ih p.length lt p rfl r
        rw [hp] at hright ⊢
        rw [score_snoc, odd_snoc]
        exact oneEnd _ _ _ _ hold hright

/-- Positive blocks have nonpositive score, with a gap of four whenever an odd occurs. -/
theorem positive_block (r : ℤ) (gs : List Bool) :
    posScore r gs ≤ cap (hasOdd r gs) :=
  posInduction gs.length gs rfl r

end Lemmata.FishburnReedsClassicalBound.Block
