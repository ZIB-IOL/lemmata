module

public import Lemmata.TensorRank.Def.Separation
public import Lemmata.TensorRank.Proof.Interpolation
public import Lemmata.TensorRank.Proof.DirectSum
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

set_option autoImplicit false

open scoped BigOperators
open Classical

namespace Lemmata.TensorRank.Separation

theorem frequency_bound {r M : ℕ} (g : Fin r → Fin M) (h u v : Fin M) :
    |frequency g h u v| < (period r M : ℤ) := by
  have bounds (a : Fin M) : 0 ≤ (a : ℤ) ∧ (a : ℤ) ≤ (M : ℤ) - 1 := by
    have := a.isLt
    constructor <;> omega
  have hs0 : 0 ≤ ∑ i, (g i : ℤ) := Finset.sum_nonneg (fun i _ => (bounds (g i)).1)
  have hs1 : (∑ i, (g i : ℤ)) ≤ (r : ℤ) * ((M : ℤ) - 1) := by
    calc
      _ ≤ ∑ _i : Fin r, ((M : ℤ) - 1) := Finset.sum_le_sum (fun i _ => (bounds (g i)).2)
      _ = _ := by simp; ring
  have hrh0 : 0 ≤ (r : ℤ) * h := mul_nonneg (by positivity) (bounds h).1
  have hrh1 := mul_le_mul_of_nonneg_left (bounds h).2 (show 0 ≤ (r : ℤ) by positivity)
  have hu := bounds u
  have hv := bounds v
  rw [abs_lt]
  dsimp [frequency, period]
  constructor <;> nlinarith

theorem squares_identity {r M : ℕ} (g : Fin r → Fin M) (h u v : Fin M) :
    (∑ i, ((g i : ℤ) - h) ^ 2) + 2 * (h : ℤ) * frequency g h u v =
      (∑ i, (g i : ℤ) ^ 2) + 2 * (h : ℤ) * (u - v) - (r : ℤ) * (h : ℤ) ^ 2 := by
  have hs : (∑ i, ((g i : ℤ) - h) ^ 2) =
      ∑ i, ((g i : ℤ) ^ 2 - 2 * (h : ℤ) * g i + (h : ℤ) ^ 2) := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hs]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, frequency]
  ring

theorem squares_zero_iff {r M : ℕ} (g : Fin r → Fin M) (h : Fin M) :
    (∑ i, ((g i : ℤ) - h) ^ 2) = 0 ↔ ∀ i, g i = h := by
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg ((g i : ℤ) - h))]
  simp only [Finset.mem_univ, forall_true_left, sq_eq_zero_iff, sub_eq_zero]
  constructor
  · intro hg i
    exact Fin.ext (by exact_mod_cast hg i)
  · intro hg i
    rw [hg i]

theorem frequency_zero_of_aligned {r M : ℕ} (g : Fin r → Fin M) (h u v : Fin M)
    (hg : ∀ i, g i = h) : frequency g h u v = 0 ↔ u = v := by
  simp only [frequency, hg, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, sub_self, zero_add, sub_eq_zero]
  constructor
  · intro h
    exact Fin.ext (by exact_mod_cast h)
  · rintro rfl
    rfl

private theorem product_bound {M : ℕ} (a b : Fin M) :
    a.val * b.val ≤ (M - 1) ^ 2 := by
  have ha : a.val ≤ M - 1 := by have := a.isLt; omega
  have hb : b.val ≤ M - 1 := by have := b.isLt; omega
  simpa only [pow_two] using Nat.mul_le_mul ha hb

theorem degree_identity {r M : ℕ} (g : Fin r → Fin M) (h u v : Fin M) :
    (totalDegree g h u v : ℤ) = (shift r M : ℤ) +
      (∑ i, ((g i : ℤ) - h) ^ 2) + 2 * (h : ℤ) * frequency g h u v := by
  have hh : h.val ^ 2 ≤ (M - 1) ^ 2 := by simpa only [pow_two] using product_bound h h
  have hv := product_bound h v
  simp only [totalDegree, shift, Nat.cast_add, Nat.cast_mul, Nat.cast_sum, Nat.cast_pow,
    Nat.cast_ofNat, Nat.cast_sub hh, Nat.cast_sub hv]
  nlinarith [squares_identity g h u v]

theorem shift_le_degree {r M : ℕ} (g : Fin r → Fin M) (h u v : Fin M)
    (hf : frequency g h u v = 0) : shift r M ≤ totalDegree g h u v := by
  have hi := degree_identity g h u v
  rw [hf, mul_zero, add_zero] at hi
  have hz : (shift r M : ℤ) ≤ (totalDegree g h u v : ℤ) := by
    rw [hi]
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => sq_nonneg ((g i : ℤ) - h)))
  exact_mod_cast hz

theorem degree_eq_shift_iff {r M : ℕ} (g : Fin r → Fin M) (h u v : Fin M)
    (hf : frequency g h u v = 0) :
    totalDegree g h u v = shift r M ↔ (∀ i, g i = h) ∧ u = v := by
  have hi := degree_identity g h u v
  rw [hf, mul_zero, add_zero] at hi
  constructor
  · intro hd
    have hc : (totalDegree g h u v : ℤ) = shift r M := by exact_mod_cast hd
    have hs : (∑ i, ((g i : ℤ) - h) ^ 2) = 0 := by omega
    have hg := (squares_zero_iff g h).mp hs
    exact ⟨hg, (frequency_zero_of_aligned g h u v hg).mp hf⟩
  · rintro ⟨hg, _⟩
    have hs := (squares_zero_iff g h).mpr hg
    rw [hs, add_zero] at hi
    exact_mod_cast hi

theorem fourier_average {L : ℕ} (hL : L ≠ 0) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ L)
    (e : ℤ) :
    (L : ℂ)⁻¹ * (∑ t : Fin L, ζ ^ ((t : ℤ) * e)) =
      if (L : ℤ) ∣ e then 1 else 0 := by
  have hterm (t : ℕ) : ζ ^ ((t : ℤ) * e) = (ζ ^ e) ^ t := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm]
  have hperiod : (ζ ^ e) ^ L = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, hζ.zpow_eq_one, one_zpow]
  simp_rw [hterm]
  rw [Fin.sum_univ_eq_sum_range]
  by_cases he : ζ ^ e = 1
  · have hd := (hζ.zpow_eq_one_iff_dvd e).mp he
    simp [he, hd, hL]
  · have hd : ¬ (L : ℤ) ∣ e := by simpa only [← hζ.zpow_eq_one_iff_dvd] using he
    have hs : (∑ t ∈ Finset.range L, (ζ ^ e) ^ t) = 0 := by
      apply (mul_eq_zero.mp (show (∑ t ∈ Finset.range L, (ζ ^ e) ^ t) * (ζ ^ e - 1) = 0 by
        rw [geom_sum_mul, hperiod, sub_self])).resolve_right
      exact sub_ne_zero.mpr he
    simp [hs, hd]

theorem fourier_frequency {r M : ℕ} (hM : 0 < M) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (period r M)) (g : Fin r → Fin M) (h u v : Fin M) :
    (period r M : ℂ)⁻¹ *
      (∑ t : Fin (period r M), ζ ^ ((t : ℤ) * frequency g h u v)) =
      if frequency g h u v = 0 then 1 else 0 := by
  rw [fourier_average (by simp [period, hM.ne']) hζ]
  have hd : (period r M : ℤ) ∣ frequency g h u v ↔ frequency g h u v = 0 := by
    constructor
    · intro hd
      have hz := Int.eq_zero_of_dvd_of_nonneg_of_lt (abs_nonneg (frequency g h u v))
        (frequency_bound g h u v) ((dvd_abs _ _).mpr hd)
      exact abs_eq_zero.mp hz
    · intro hz
      rw [hz]
      exact dvd_zero _
  simp only [hd]

private theorem product_zpow {J : Type*} [Fintype J] {ζ : ℂ} (hz : ζ ≠ 0)
    (f : J → ℤ) : (∏ j, ζ ^ f j) = ζ ^ ∑ j, f j := by
  have hs (s : Finset J) : (∏ j ∈ s, ζ ^ f j) = ζ ^ ∑ j ∈ s, f j := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert j s hj ih => rw [Finset.prod_insert hj, Finset.sum_insert hj, ih, zpow_add₀ hz]
  exact hs Finset.univ

private theorem selected_map {R P : Type*} [CommSemiring R] [Fintype P]
    {V W : P → Type*} [∀ p, Fintype (V p)] (T : Tensor R P V)
    (f : ∀ p, W p → V p) (a : ∀ p, W p → R) (y : ∀ p, W p) :
    Tensor.localMap (fun p y x => a p y * if x = f p y then 1 else 0) T y =
      (∏ p, a p (y p)) * T (fun p => f p (y p)) := by
  have hs := congrFun (Tensor.localMap_select f T) y
  simp only [Tensor.localMap, Tensor.reindex] at hs
  simp only [Tensor.localMap, Finset.prod_mul_distrib]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, hs]

universe u

variable {r M : ℕ} {V : Party r → Type u}

theorem labels_iff (x : ∀ p, SeparatedCoordinate V M p) :
    (∀ p, label p (x p) = (x (.inl false)).1.1) ↔
      (x (.inl true)).1.1 = (x (.inl false)).1.1 ∧
        ∀ i, (x (.inr i)).1 = (x (.inl false)).1.1 := by
  constructor
  · intro hx
    exact ⟨hx (.inl true), fun i => hx (.inr i)⟩
  · rintro ⟨hb, hg⟩ p
    cases p with
    | inl b => cases b <;> simp_all [label]
    | inr i => exact hg i

theorem sum_weights (x : ∀ p, SeparatedCoordinate V M p)
    (hh : (x (.inl false)).1.1 = (x (.inl true)).1.1) :
    (∑ p, weight p (x p)) = totalDegree (fun i => (x (.inr i)).1)
      (x (.inl false)).1.1 (x (.inl false)).1.2 (x (.inl true)).1.2 := by
  simp only [Fintype.sum_sum_type, Fintype.sum_bool, weight, totalDegree]
  rw [← hh]
  omega

theorem product_amplitudes {ζ : ℂ} (hz : ζ ≠ 0) (t : Fin (period r M))
    (x : ∀ p, SeparatedCoordinate V M p) :
    (∏ p, amplitude ζ p t (x p)) = (period r M : ℂ)⁻¹ * ζ ^ ((t : ℤ) *
      frequency (fun i => (x (.inr i)).1) (x (.inl false)).1.1
        (x (.inl false)).1.2 (x (.inl true)).1.2) := by
  let g := fun i => (x (.inr i)).1
  let h := (x (.inl false)).1.1
  let u := (x (.inl false)).1.2
  let v := (x (.inl true)).1.2
  simp only [Fintype.prod_sum_type, Fintype.prod_bool, amplitude]
  rw [product_zpow hz]
  change (((period r M : ℂ)⁻¹ * ζ ^ (-((t : ℤ) * v))) *
      ζ ^ ((t : ℤ) * ((u : ℤ) - (r : ℤ) * h))) *
      ζ ^ (∑ i, (t : ℤ) * (g i : ℤ)) = _
  calc
    _ = (period r M : ℂ)⁻¹ * ((ζ ^ (-((t : ℤ) * v)) *
        ζ ^ ((t : ℤ) * ((u : ℤ) - (r : ℤ) * h))) *
        ζ ^ (∑ i, (t : ℤ) * (g i : ℤ))) := by ring
    _ = (period r M : ℂ)⁻¹ * ζ ^ (-((t : ℤ) * v) +
        (t : ℤ) * ((u : ℤ) - (r : ℤ) * h) + ∑ i, (t : ℤ) * (g i : ℤ)) := by
      rw [← zpow_add₀ hz, ← zpow_add₀ hz]
    _ = _ := by
      congr 1
      congr 1
      dsimp [frequency, g, h, u, v]
      rw [← Finset.mul_sum]
      ring

theorem shared_input (Z : Fin M → Tensor ℂ (Party r) V)
    (x : ∀ p, SeparatedCoordinate V M p) :
    sharedSum Z (fun p => input p (x p)) =
      if (x (.inl false)).1.1 = (x (.inl true)).1.1 then
        Z (x (.inl false)).1.1 (fun p => (x p).2) else 0 := by
  have hb : sharedBase (fun p => input p (x p)) = fun p => (x p).2 := by
    funext p
    cases p <;> rfl
  change (if (x (.inl false)).1.1 = (x (.inl true)).1.1 then
    Z (x (.inl false)).1.1 (sharedBase (fun p => input p (x p))) else 0) = _
  rw [hb]

private theorem constants_copies (L : ℕ) (T : Tensor ℂ (Party r) (SharedCoordinate V M)) :
    (fun x => Polynomial.C (Tensor.copies L T x)) =
      Tensor.copies L (fun x => Polynomial.C (T x)) := by
  funext x
  simp only [Tensor.copies, Tensor.product, Tensor.diagonal]
  split_ifs <;> simp

theorem family_formula [∀ p, Fintype (V p)] {ζ : ℂ} (hz : ζ ≠ 0)
    (Z : Fin M → Tensor ℂ (Party r) V) (x : ∀ p, SeparatedCoordinate V M p) :
    family ζ Z x = Polynomial.C (((period r M : ℂ)⁻¹ *
      ∑ t : Fin (period r M), ζ ^ ((t : ℤ) * frequency (fun i => (x (.inr i)).1)
        (x (.inl false)).1.1 (x (.inl false)).1.2 (x (.inl true)).1.2)) *
      sharedSum Z (fun p => input p (x p))) * Polynomial.X ^ (∑ p, weight p (x p)) := by
  change Tensor.localMap (kernel ζ)
    (fun a => Polynomial.C (Tensor.copies (period r M) (sharedSum Z) a)) x = _
  rw [constants_copies, Tensor.localMap_copies]
  simp only [Finset.sum_apply]
  have ht (t : Fin (period r M)) :
      (∏ p, Polynomial.C (amplitude ζ p t (x p)) * Polynomial.X ^ weight p (x p)) =
        Polynomial.C ((period r M : ℂ)⁻¹ * ζ ^ ((t : ℤ) *
          frequency (fun i => (x (.inr i)).1) (x (.inl false)).1.1
            (x (.inl false)).1.2 (x (.inl true)).1.2)) *
          Polynomial.X ^ (∑ p, weight p (x p)) := by
    rw [Finset.prod_mul_distrib, ← map_prod (Polynomial.C : ℂ →+* Polynomial ℂ),
      Finset.prod_pow_eq_pow_sum, product_amplitudes hz]
  calc
    _ = ∑ t : Fin (period r M),
        (∏ p, Polynomial.C (amplitude ζ p t (x p)) * Polynomial.X ^ weight p (x p)) *
          Polynomial.C (sharedSum Z (fun p => input p (x p))) := by
      apply Finset.sum_congr rfl
      intro t _
      exact selected_map (fun a => Polynomial.C (sharedSum Z a)) input
        (fun p y => Polynomial.C (amplitude ζ p t y) * Polynomial.X ^ weight p y) x
    _ = (∑ t : Fin (period r M), Polynomial.C ((period r M : ℂ)⁻¹ *
        ζ ^ ((t : ℤ) * frequency (fun i => (x (.inr i)).1) (x (.inl false)).1.1
          (x (.inl false)).1.2 (x (.inl true)).1.2))) *
        Polynomial.X ^ (∑ p, weight p (x p)) *
        Polynomial.C (sharedSum Z (fun p => input p (x p))) := by
      simp_rw [ht]
      rw [Finset.sum_mul, Finset.sum_mul]
    _ = Polynomial.C ((period r M : ℂ)⁻¹ *
        ∑ t : Fin (period r M), ζ ^ ((t : ℤ) * frequency (fun i => (x (.inr i)).1)
          (x (.inl false)).1.1 (x (.inl false)).1.2 (x (.inl true)).1.2)) *
        Polynomial.X ^ (∑ p, weight p (x p)) *
        Polynomial.C (sharedSum Z (fun p => input p (x p))) := by
      rw [Finset.mul_sum, map_sum]
    _ = _ := by simp only [map_mul]; ring

theorem family_filtered [∀ p, Fintype (V p)] (hM : 0 < M) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (period r M)) (Z : Fin M → Tensor ℂ (Party r) V)
    (x : ∀ p, SeparatedCoordinate V M p) :
    family ζ Z x =
      if (x (.inl false)).1.1 = (x (.inl true)).1.1 ∧
          frequency (fun i => (x (.inr i)).1) (x (.inl false)).1.1
            (x (.inl false)).1.2 (x (.inl true)).1.2 = 0 then
        Polynomial.C (Z (x (.inl false)).1.1 (fun p => (x p).2)) *
          Polynomial.X ^ totalDegree (fun i => (x (.inr i)).1)
            (x (.inl false)).1.1 (x (.inl false)).1.2 (x (.inl true)).1.2
      else 0 := by
  rw [family_formula (hζ.ne_zero (by simp [period, hM.ne'])),
    fourier_frequency hM hζ, shared_input]
  by_cases hh : (x (.inl false)).1.1 = (x (.inl true)).1.1
  · rw [sum_weights x hh]
    by_cases hf : frequency (fun i => (x (.inr i)).1) (x (.inl false)).1.1
        (x (.inl false)).1.2 (x (.inl true)).1.2 = 0
    · rw [ite_eq_left hh, ite_eq_left hf, ite_eq_left ⟨hh, hf⟩]
      simp
    · rw [ite_eq_left hh, ite_eq_right hf, ite_eq_right (fun h => hf h.2)]
      simp
  · simp [hh]

theorem family_coefficient [∀ p, Fintype (V p)] (hM : 0 < M) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (period r M)) (Z : Fin M → Tensor ℂ (Party r) V)
    (j : ℕ) (x : ∀ p, SeparatedCoordinate V M p) :
    Tensor.coefficient (family ζ Z) j x =
      if (x (.inl false)).1.1 = (x (.inl true)).1.1 ∧
          frequency (fun i => (x (.inr i)).1) (x (.inl false)).1.1
            (x (.inl false)).1.2 (x (.inl true)).1.2 = 0 ∧
          j = totalDegree (fun i => (x (.inr i)).1)
            (x (.inl false)).1.1 (x (.inl false)).1.2 (x (.inl true)).1.2 then
        Z (x (.inl false)).1.1 (fun p => (x p).2) else 0 := by
  change (family ζ Z x).coeff j = _
  rw [family_filtered hM hζ]
  by_cases h : (x (.inl false)).1.1 = (x (.inl true)).1.1 ∧
      frequency (fun i => (x (.inr i)).1) (x (.inl false)).1.1
        (x (.inl false)).1.2 (x (.inl true)).1.2 = 0
  · rw [ite_eq_left h, Polynomial.coeff_C_mul_X_pow]
    have hc : ((x (.inl false)).1.1 = (x (.inl true)).1.1 ∧
        frequency (fun i => (x (.inr i)).1) (x (.inl false)).1.1
          (x (.inl false)).1.2 (x (.inl true)).1.2 = 0 ∧
        j = totalDegree (fun i => (x (.inr i)).1)
          (x (.inl false)).1.1 (x (.inl false)).1.2 (x (.inl true)).1.2) ↔
        j = totalDegree (fun i => (x (.inr i)).1)
          (x (.inl false)).1.1 (x (.inl false)).1.2 (x (.inl true)).1.2 :=
      ⟨fun hc => hc.2.2, fun hd => ⟨h.1, h.2, hd⟩⟩
    simp only [hc]
  · have hn : ¬ ((x (.inl false)).1.1 = (x (.inl true)).1.1 ∧
        frequency (fun i => (x (.inr i)).1) (x (.inl false)).1.1
          (x (.inl false)).1.2 (x (.inl true)).1.2 = 0 ∧
        j = totalDegree (fun i => (x (.inr i)).1)
          (x (.inl false)).1.1 (x (.inl false)).1.2 (x (.inl true)).1.2) :=
      fun hc => h ⟨hc.1, hc.2.1⟩
    rw [ite_eq_right h, ite_eq_right hn]
    rfl

theorem family_leading [∀ p, Fintype (V p)] (hM : 0 < M) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (period r M)) (Z : Fin M → Tensor ℂ (Party r) V) :
    Tensor.Leading (family ζ Z) (shift r M) (separatedSum Z) := by
  constructor
  · funext x
    rw [family_coefficient hM hζ]
    have hc : ((x (.inl false)).1.1 = (x (.inl true)).1.1 ∧
        frequency (fun i => (x (.inr i)).1) (x (.inl false)).1.1
          (x (.inl false)).1.2 (x (.inl true)).1.2 = 0 ∧
        shift r M = totalDegree (fun i => (x (.inr i)).1)
          (x (.inl false)).1.1 (x (.inl false)).1.2 (x (.inl true)).1.2) ↔
        (∀ p, label p (x p) = (x (.inl false)).1.1) ∧
          (x (.inl false)).1.2 = (x (.inl true)).1.2 := by
      constructor
      · rintro ⟨hh, hf, hd⟩
        obtain ⟨hg, huv⟩ := (degree_eq_shift_iff _ _ _ _ hf).mp hd.symm
        exact ⟨(labels_iff x).mpr ⟨hh.symm, hg⟩, huv⟩
      · rintro ⟨hl, huv⟩
        obtain ⟨hh, hg⟩ := (labels_iff x).mp hl
        have hf := (frequency_zero_of_aligned _ _ _ _ hg).mpr huv
        exact ⟨hh.symm, hf, ((degree_eq_shift_iff _ _ _ _ hf).mpr ⟨hg, huv⟩).symm⟩
    simpa only [hc] using (show
      (if (∀ p, label p (x p) = (x (.inl false)).1.1) ∧
          (x (.inl false)).1.2 = (x (.inl true)).1.2 then
        Z (x (.inl false)).1.1 (fun p => (x p).2) else 0) = separatedSum Z x from rfl)
  · intro j hj
    funext x
    rw [family_coefficient hM hζ]
    have hn : ¬ ((x (.inl false)).1.1 = (x (.inl true)).1.1 ∧
        frequency (fun i => (x (.inr i)).1) (x (.inl false)).1.1
          (x (.inl false)).1.2 (x (.inl true)).1.2 = 0 ∧
        j = totalDegree (fun i => (x (.inr i)).1)
          (x (.inl false)).1.1 (x (.inl false)).1.2 (x (.inl true)).1.2) := by
      rintro ⟨_, hf, hd⟩
      have := shift_le_degree _ _ _ _ hf
      omega
    simp only [hn, ite_false]
    rfl

theorem separated_degenerates [∀ p, Fintype (V p)] (hM : 0 < M)
    (Z : Fin M → Tensor ℂ (Party r) V) :
    Tensor.Degenerates (separatedSum Z) (Tensor.copies (period r M) (sharedSum Z)) := by
  have hL : period r M ≠ 0 := by simp [period, hM.ne']
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / period r M)
  have hζ : IsPrimitiveRoot ζ (period r M) := Complex.isPrimitiveRoot_exp _ hL
  exact ⟨kernel ζ, shift r M, family_leading hM hζ Z⟩

theorem separated_asymptoticRank_le [∀ p, Fintype (V p)] (hM : 0 < M)
    (Z : Fin M → Tensor ℂ (Party r) V) :
    Tensor.asymptoticRank (separatedSum Z) ≤
      Tensor.asymptoticRank (Tensor.copies (period r M) (sharedSum Z)) :=
  (separated_degenerates hM Z).asymptoticRank_le

end Lemmata.TensorRank.Separation
