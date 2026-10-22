module

public import Lemmata.Centroid.Proof.General.CommonTail
public import Mathlib.Tactic.FinCases

@[expose] public section

open scoped BigOperators

noncomputable section

namespace Lemmata.Centroid.General

theorem quadratic_side_bound {k m N h : ℕ} (hkm : k ≤ m) (hm : m ≤ N)
    (hk : k ≤ h) (hh : 2 * h ≤ N) : k * (m - k) ≤ h * (N - h) := by
  have hN : h ≤ N := by omega
  have hp : (0 : ℤ) ≤ ((h : ℤ) - k) * ((N : ℤ) - h - k) :=
    mul_nonneg (by have : (k : ℤ) ≤ h := by exact_mod_cast hk
                   omega)
      (by have : (2 * h : ℤ) ≤ N := by exact_mod_cast hh
          have : (k : ℤ) ≤ h := by exact_mod_cast hk
          omega)
  have hq : (0 : ℤ) ≤ (k : ℤ) * ((N : ℤ) - m) :=
    mul_nonneg (by positivity) (by
      have hm' : (m : ℤ) ≤ N := by exact_mod_cast hm
      omega)
  have hz : (k : ℤ) * ((m : ℤ) - k) ≤ (h : ℤ) * ((N : ℤ) - h) := by nlinarith
  exact_mod_cast hz

theorem ordered_three (b : Fin 3 → ℕ) :
    ∃ i j k : Fin 3, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ b k ≤ b j ∧ b j ≤ b i := by
  by_cases h01 : b 0 ≤ b 1
  · by_cases h12 : b 1 ≤ b 2
    · exact ⟨2, 1, 0, by decide, by decide, by decide, h01, h12⟩
    · by_cases h02 : b 0 ≤ b 2
      · exact ⟨1, 2, 0, by decide, by decide, by decide, h02, by omega⟩
      · exact ⟨1, 0, 2, by decide, by decide, by decide, by omega, h01⟩
  · by_cases h02 : b 0 ≤ b 2
    · exact ⟨2, 0, 1, by decide, by decide, by decide, by omega, h02⟩
    · by_cases h12 : b 1 ≤ b 2
      · exact ⟨0, 2, 1, by decide, by decide, by decide, h12, by omega⟩
      · exact ⟨0, 1, 2, by decide, by decide, by decide, by omega, by omega⟩

theorem higher_tail_real {x y Q B C : ℝ} (_hx : 0 ≤ x) (_hy : 0 ≤ y)
    (hB : 0 < B) (hBC : B ≤ C) (hCQ : C ≤ Q - 2)
    (hxp : x ^ 2 ≤ (Q - 2) * (Q - B) * (Q - C))
    (hyp : y ^ 2 ≤ B ^ 2 * C) : x + y ≤ phi Q B := by
  let δ := C - B
  let u := Q - B - δ / 2
  have hδ : 0 ≤ δ := by dsimp [δ]; linarith
  have hQ : 0 ≤ Q - 2 := by linarith
  have hC : 0 ≤ C := by linarith
  have hu : 0 ≤ u := by dsimp [u, δ]; linarith
  have hu' : (Q - B) * (Q - C) ≤ u ^ 2 := by
    dsimp [u, δ]
    nlinarith [sq_nonneg (C - B)]
  have hxsq : x ^ 2 ≤ (u * Real.sqrt (Q - 2)) ^ 2 := by
    have hp := mul_le_mul_of_nonneg_left hu' hQ
    have hs := Real.sq_sqrt hQ
    nlinarith [congrArg (fun z : ℝ => u ^ 2 * z) hs]
  have hxc : x ≤ u * Real.sqrt (Q - 2) := by
    nlinarith [mul_nonneg hu (Real.sqrt_nonneg (Q - 2))]
  have hyc : y ≤ B * Real.sqrt C := by
    have hs := Real.sq_sqrt hC
    nlinarith [congrArg (fun z : ℝ => B ^ 2 * z) hs,
      mul_nonneg hB.le (Real.sqrt_nonneg C)]
  have hsB := Real.sq_sqrt hB.le
  have hrootB : 0 < Real.sqrt B := Real.sqrt_pos.2 hB
  have htan := sqrt_tangent hC hrootB
  rw [hsB] at htan
  have hmul := mul_le_mul_of_nonneg_left htan hB.le
  have heq : B * (Real.sqrt B + (C - B) / (2 * Real.sqrt B)) =
      B * Real.sqrt B + δ * Real.sqrt B / 2 := by
    dsimp [δ]
    field_simp
    nlinarith [hsB]
  rw [heq] at hmul
  have hroots : Real.sqrt B ≤ Real.sqrt (Q - 2) := Real.sqrt_le_sqrt (by linarith)
  have hdelta := mul_le_mul_of_nonneg_left hroots hδ
  rw [phi_eq hB.le]
  dsimp [u] at hxc
  nlinarith

theorem radicalQ_add_kernel {n s : ℕ} (hn : 0 < n) (_hs : s ≤ 2 * n + 1) :
    radicalQ n s + (if s ≤ n then n else n + 1) = n * (n + 1) + s := by
  unfold radicalQ
  split_ifs
  · ring
  · have hpos : 1 ≤ n ^ 2 + s := by nlinarith
    have heq := Nat.sub_add_cancel hpos
    nlinarith

theorem higher_radical_lower_factor {N n s r d m : ℕ} (hn : 0 < n)
    (hs : 1 ≤ s) (hsn : s ≤ 2 * n + 1) (hN : N = n * (n + 1) + s)
    (hr : generalBound N ≤ r) (hd : d ≤ m) (hm : m ≤ N) (hquad : r ≤ d * (m - d)) :
    (if s ≤ n then n else n + 1) ≤ d := by
  have hN₂ : 2 ≤ N := by nlinarith
  rw [generalBound_eq hN₂ hsn hN] at hr
  by_cases hsn' : s ≤ n
  · simp only [hsn', ite_true]
    by_contra h
    have hd' : d ≤ n - 1 := by omega
    have h2 : 2 * (n - 1) ≤ N := by have := Nat.sub_le n 1; nlinarith
    have hbound := quadratic_side_bound hd hm hd' h2
    have hpred : n - 1 + 1 = n := by omega
    have hsub : N - (n - 1) + (n - 1) = N := Nat.sub_add_cancel (by omega)
    have hμ : n ^ 3 + 1 ≤ generalBoundAt n s := by
      by_cases hs1 : s = 1
      · subst s; simp
      · simp [generalBoundAt, show s ≠ 0 by omega, hs1, hsn']
    have heq : (n - 1) * (N - (n - 1)) + (N - (n - 1)) = n * (N - (n - 1)) := by
      calc
        _ = (n - 1 + 1) * (N - (n - 1)) := by ring
        _ = _ := by rw [hpred]
    have hmono := Nat.mul_le_mul_left (n - 1) hsn'
    nlinarith [congrArg (fun z : ℕ => n * z) hsub,
      congrArg (fun z : ℕ => n * z) hN,
      congrArg (fun z : ℕ => n * z) hpred,
      congrArg (fun z : ℕ => s * z) hpred]
  · simp only [hsn', ite_false]
    by_contra h
    have hbound := quadratic_side_bound hd hm (show d ≤ n by omega)
      (show 2 * n ≤ N by nlinarith)
    let t := s - n - 1
    have ht : s = n + 1 + t := by dsimp [t]; omega
    have hμ := generalBoundAt_second_pred n t hn
    rw [ht] at hr
    have hpos : 0 < generalBoundAt n (n + 1 + t) := by
      rw [generalBoundAt_second hn]; omega
    have hmax := le_max_left n (t ^ 2)
    have hsub : N - n + n = N := Nat.sub_add_cancel (by omega)
    have heq : N - n = n ^ 2 + n + t + 1 := by nlinarith
    have hμ' : generalBoundAt n (n + 1 + t) =
        n * (n ^ 2 + n + t) + max n (t ^ 2) + 1 := by omega
    rw [heq] at hbound
    nlinarith

theorem higher_radical_gap {n s Q E : ℕ} (hn : 2 ≤ n) (hs : 1 ≤ s)
    (hsn : s ≤ 2 * n + 1) (hQ : Q = radicalQ n s) (hE : E + 2 * n = Q) :
    n * E + Q ≤ generalBoundAt n s := by
  by_cases hsn' : s ≤ n
  · have hQ' : Q = n ^ 2 + s := by simpa [radicalQ, hsn'] using hQ
    have hμ : n ^ 3 + s * (s - 1) + 1 ≤ generalBoundAt n s := by
      by_cases hs1 : s = 1
      · subst s; simp
      · simp [generalBoundAt, show s ≠ 0 by omega, hs1, hsn']
    have hs' : s - 1 + 1 = s := by omega
    have hprod : 0 ≤ (n - s) ^ 2 := Nat.zero_le _
    have hns : n - s + s = n := by omega
    have hnn : n - 2 + 2 = n := by omega
    have hnon : 0 ≤ (n - 2) * s := Nat.zero_le _
    nlinarith [congrArg (fun z : ℕ => n * z) hE,
      congrArg (fun z : ℕ => s * z) hs', congrArg (fun z : ℕ => s * z) hns,
      congrArg (fun z : ℕ => n * z) hns, congrArg (fun z : ℕ => s * z) hnn]
  · let t := s - n - 1
    have ht : s = n + 1 + t := by dsimp [t]; omega
    have htn : t ≤ n := by dsimp [t]; omega
    have hQ' : Q = n ^ 2 + n + t := by
      rw [hQ, radicalQ, ite_eq_right hsn', ht]; omega
    rw [ht]
    have hμ := generalBoundAt_second_pred n t (show 0 < n by omega)
    have hpos : 0 < generalBoundAt n (n + 1 + t) := by
      rw [generalBoundAt_second (show 0 < n by omega)]; omega
    have hmax := le_max_left n (t ^ 2)
    have hμ' : generalBoundAt n (n + 1 + t) =
        n * (n ^ 2 + n + t) + max n (t ^ 2) + 1 := by omega
    nlinarith [congrArg (fun z : ℕ => n * z) hE]

structure HigherRadicalProfile (N : ℕ) where
  r : ℕ
  x : ℕ
  y : ℕ
  m : Fin 3 → ℕ
  k : Fin 3 → ℕ
  a : Fin 3 → ℕ
  b : Fin 3 → ℕ
  split : x + y = r
  xpos : 0 < x
  format : ∀ i, m i ≤ N
  dimensions : ∀ i, k i + a i + b i = m i
  kernel : ∀ i, r ≤ k i * (a i + b i)
  separation : ∀ i, r ≤ b i * (k i + a i)
  difference : ∀ i, x ≤ g (a i)
  product : r ^ 2 ≤ ∏ i, (a i + b i)
  socleProduct : y ^ 2 ≤ ∏ i, b i
  socleBudget : ∀ d, (∀ i, d ≤ a i) → y ≤ supportBound (N - d)
  projected : ∀ Q i j k, i ≠ j → i ≠ k → j ≠ k → a i + b i ≤ Q → Q - 1 < x →
    x ^ 2 ≤ (Q - 2) * a j * a k

private theorem fin3_product (v : Fin 3 → ℕ) (i j k : Fin 3)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) : (∏ l, v l) = v i * v j * v k := by
  rw [Fin.prod_univ_three]
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    first | exact (hij rfl).elim | exact (hik rfl).elim | exact (hjk rfl).elim | ac_rfl

theorem higher_radical_profile_bound {N : ℕ} (p : HigherRadicalProfile N) :
    p.r ≤ generalBound N - 1 := by
  by_cases hNsmall : N ≤ 1
  · have hk := p.kernel 0
    have hd := p.dimensions 0
    have hm := p.format 0
    have hz : p.k 0 = 0 ∨ p.a 0 + p.b 0 = 0 := by omega
    rcases hz with hz | hz <;> rw [hz] at hk <;> simp only [zero_mul, mul_zero] at hk <;> omega
  have hN₂ : 2 ≤ N := by omega
  let n := generalIndex N
  let s := N - n * (n + 1)
  have hn : 0 < n := generalIndex_pos hN₂
  have hsn : s ≤ 2 * n + 1 := general_remainder_le hN₂
  have hN : N = n * (n + 1) + s := general_decomposition N
  by_contra h
  have hr : generalBound N ≤ p.r := by
    have hpos : 0 < generalBound N := by
      rw [generalBound_eq hN₂ hsn hN]
      unfold generalBoundAt
      split_ifs <;> omega
    omega
  have hμ := hr
  rw [generalBound_eq hN₂ hsn hN] at hμ
  by_cases hs0 : s = 0
  · have hN' : N = n * (n + 1) := by omega
    by_cases hsmall : ∃ i, p.k i ≤ n
    · obtain ⟨i, hi⟩ := hsmall
      have hd := p.dimensions i
      have hquad := p.kernel i
      have hbound := quadratic_side_bound (show p.k i ≤ p.m i by omega) (p.format i) hi
        (show 2 * n ≤ N by nlinarith)
      have heq : p.m i - p.k i = p.a i + p.b i := by omega
      have hNn : N - n = n ^ 2 := by nlinarith [Nat.sub_add_cancel (show n ≤ N by nlinarith)]
      rw [heq, hNn] at hbound
      rw [hs0, generalBoundAt_zero] at hμ
      nlinarith only [hquad, hbound, hμ]
    · have hq : ∀ i, p.a i + p.b i ≤ n ^ 2 := by
        intro i
        have hk : n < p.k i := lt_of_not_ge (fun hi => hsmall ⟨i, hi⟩)
        have hd := p.dimensions i
        have hm := p.format i
        nlinarith
      have hp := p.product.trans
        (show (∏ i, (p.a i + p.b i)) ≤ (n ^ 2) ^ 3 by
          rw [Fin.prod_univ_three]
          exact (Nat.mul_le_mul (Nat.mul_le_mul (hq 0) (hq 1)) (hq 2)).trans_eq (by ring))
      rw [hs0, generalBoundAt_zero] at hμ
      have hrle : p.r ≤ n ^ 3 := le_of_pow_le_pow_left₀ (by decide : 2 ≠ 0)
        (Nat.zero_le _) (hp.trans_eq (by ring))
      omega
  have hs : 1 ≤ s := by omega
  let Q := radicalQ n s
  let ℓ := if s ≤ n then n else n + 1
  have hQℓ : Q + ℓ = N := by rw [hN]; exact radicalQ_add_kernel hn hsn
  have hk : ∀ i, ℓ ≤ p.k i := by
    intro i
    have hd := p.dimensions i
    apply higher_radical_lower_factor hn hs hsn hN hr (show p.k i ≤ p.m i by omega)
      (p.format i)
    simpa only [show p.m i - p.k i = p.a i + p.b i by omega] using p.kernel i
  have hb : ∀ i, ℓ ≤ p.b i := by
    intro i
    have hd := p.dimensions i
    apply higher_radical_lower_factor hn hs hsn hN hr (show p.b i ≤ p.m i by omega)
      (p.format i)
    simpa only [show p.m i - p.b i = p.k i + p.a i by omega] using p.separation i
  have hq : ∀ i, p.a i + p.b i ≤ Q := by
    intro i
    have hd := p.dimensions i
    have hm := p.format i
    have hk' := hk i
    omega
  obtain ⟨i, _, hi⟩ := Finset.exists_min_image Finset.univ p.a Finset.univ_nonempty
  have hmin : ∀ j, p.a i ≤ p.a j := fun j => hi j (Finset.mem_univ j)
  have hapos : 1 ≤ p.a i := by
    by_contra hz
    have haz : p.a i = 0 := by omega
    have hx := p.difference i
    rw [haz, g_zero] at hx
    exact (Nat.not_le_of_lt p.xpos) hx
  by_cases ha : p.a i < 2 * n
  · have hy := p.socleBudget (p.a i) hmin
    have hloss := small_loss_at hn hsn hN hapos ha
    have hx := p.difference i
    have hsplit := p.split
    omega
  have hlarge : ∀ j, 2 * n ≤ p.a j := by intro j; have := hmin j; omega
  have hℓ : n ≤ ℓ := by dsimp [ℓ]; split_ifs <;> omega
  have hn2 : 2 ≤ n := by
    by_contra hn2
    have hn1 : n = 1 := by omega
    have hdim := hq 0
    have hla := hlarge 0
    have hbl := hb 0
    dsimp [Q, ℓ, radicalQ] at hdim hbl
    rw [hn1] at hdim hbl hla hsn
    split_ifs at hdim hbl <;> omega
  let E := Q - 2 * n
  have hE : E + 2 * n = Q := by
    have hdim := hq 0
    have hla := hlarge 0
    dsimp [E]
    omega
  have hbe : ∀ j, p.b j ≤ E := by
    intro j
    have hdim := hq j
    have hla := hlarge j
    omega
  have hEn : E ≤ n ^ 2 := by
    dsimp [Q, radicalQ] at hE
    split_ifs at hE <;> omega
  have hysq := p.socleProduct.trans
    (show (∏ j, p.b j) ≤ E ^ 3 by
      rw [Fin.prod_univ_three]
      exact (Nat.mul_le_mul (Nat.mul_le_mul (hbe 0) (hbe 1)) (hbe 2)).trans_eq (by ring))
  have hy : p.y ≤ n * E := by
    have hp := Nat.mul_le_mul_left (E ^ 2) hEn
    have hsq : p.y ^ 2 ≤ (n * E) ^ 2 := hysq.trans
      ((show E ^ 3 ≤ E ^ 2 * n ^ 2 from (by simpa only [pow_succ] using hp)).trans_eq (by ring))
    exact le_of_pow_le_pow_left₀ (by decide : 2 ≠ 0) (Nat.zero_le _) hsq
  have hgap := higher_radical_gap hn2 hs hsn (show Q = radicalQ n s from rfl) hE
  have hx : Q - 1 < p.x := by have := p.split; omega
  obtain ⟨i, j, k, hij, hik, hjk, hkj, hji⟩ := ordered_three p.b
  have hproj := p.projected Q k j i hjk.symm hik.symm hij.symm (hq k) hx
  have haQ : ∀ l, p.a l ≤ Q - p.b l := by intro l; have := hq l; omega
  have hxsq : p.x ^ 2 ≤ (Q - 2) * (Q - p.b j) * (Q - p.b i) :=
    hproj.trans (Nat.mul_le_mul (Nat.mul_le_mul_left _ (haQ j)) (haQ i))
  have hysq' : p.y ^ 2 ≤ p.b j ^ 2 * p.b i := by
    have hh := p.socleProduct
    rw [fin3_product p.b i j k hij hik hjk] at hh
    exact hh.trans ((Nat.mul_le_mul_left (p.b i * p.b j) hkj).trans_eq (by ring))
  have hbi : n ≤ p.b i := hℓ.trans (hb i)
  have hbj : n ≤ p.b j := hℓ.trans (hb j)
  have hbjE := hbe j
  have hbiE := hbe i
  have hQ2 : 2 ≤ Q := by omega
  have hbQ : ∀ l, p.b l ≤ Q := by intro l; have := hq l; omega
  have hrealx : (p.x : ℝ) ^ 2 ≤ ((Q : ℝ) - 2) * (Q - (p.b j : ℝ)) * (Q - (p.b i : ℝ)) := by
    have hc : ((p.x ^ 2 : ℕ) : ℝ) ≤ ((Q - 2) * (Q - p.b j) * (Q - p.b i) : ℕ) := by
      exact_mod_cast hxsq
    simpa only [Nat.cast_pow, Nat.cast_mul, Nat.cast_sub hQ2, Nat.cast_sub (hbQ j),
      Nat.cast_sub (hbQ i), Nat.cast_ofNat] using hc
  have hrealy : (p.y : ℝ) ^ 2 ≤ (p.b j : ℝ) ^ 2 * p.b i := by exact_mod_cast hysq'
  have htail := higher_tail_real (by positivity : (0 : ℝ) ≤ p.x)
    (by positivity : (0 : ℝ) ≤ p.y) (by exact_mod_cast (show 0 < p.b j by omega))
    (by exact_mod_cast hji) (show (p.b i : ℝ) ≤ Q - 2 by
      have hc : (p.b i : ℝ) + 2 ≤ Q := by exact_mod_cast (show p.b i + 2 ≤ Q by omega)
      linarith)
    hrealx hrealy
  have hcommon := common_tail hn2 hs hsn hN
    (B := (p.b j : ℝ)) (by exact_mod_cast hbj)
    (by
      have hc : (p.b j : ℝ) + 2 * (n : ℝ) ≤ radicalQ n s := by
        exact_mod_cast (show p.b j + 2 * n ≤ radicalQ n s by omega)
      linarith)
  have hsplit : (p.x : ℝ) + p.y = p.r := by exact_mod_cast p.split
  have hrreal : (generalBound N : ℝ) ≤ p.r := by exact_mod_cast hr
  linarith

end Lemmata.Centroid.General
