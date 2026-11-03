module

/-
Copyright (c) 2026 Kirill Khoruzhii. Licensed under Apache-2.0.
Modified for the arbitrary-field tensor-rank formalization; namespace and imports
adapted for Lemmata. See docs/tensor-rank/NOTICE.txt for upstream attribution
and modification notices, and docs/tensor-rank/LICENSE.txt for the license.
-/

public import Lemmata.TensorRank.Def.Separation
public import Lemmata.TensorRank.Proof.PolynomialInterpolation
public import Lemmata.TensorRank.Proof.Interpolation
public import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

set_option autoImplicit false

open scoped BigOperators
open Classical

noncomputable section

namespace Lemmata.TensorRank.Separation

variable {𝕜 : Type*} [Field 𝕜]

def outputIndex {r M : ℕ} (h v : Fin M) : Fin (sourceCopies r M) :=
  ⟨r * h.val + v.val, by
    have hh : h.val ≤ M - 1 := by have := h.isLt; omega
    have hm := Nat.mul_le_mul_left r hh
    have hv := v.isLt
    unfold sourceCopies
    omega⟩

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

theorem sourceCopies_pos {r M : ℕ} (hM : 0 < M) : 0 < sourceCopies r M := by
  unfold sourceCopies
  omega

theorem sourceCopies_upper_sharp (r M : ℕ) : sourceCopies r M ≤ (r + 1) * M := by
  have h := Nat.mul_le_mul_left r (Nat.sub_le M 1)
  unfold sourceCopies
  nlinarith

theorem input_sum_lt {r M : ℕ} (g : Fin r → Fin M) (u : Fin M) :
    u.val + (∑ i, (g i).val) < sourceCopies r M := by
  have hs : (∑ i, (g i).val) ≤ r * (M - 1) := by
    calc
      _ ≤ ∑ _i : Fin r, (M - 1) := Finset.sum_le_sum (fun i _ => by have := (g i).isLt; omega)
      _ = _ := by simp
  have hu := u.isLt
  unfold sourceCopies
  omega

theorem frequency_eq_zero_iff {r M : ℕ} (g : Fin r → Fin M) (h u v : Fin M) :
    frequency g h u v = 0 ↔ u.val + (∑ i, (g i).val) = r * h.val + v.val := by
  constructor
  · intro he
    have he' : (u : ℤ) + (∑ i, (g i : ℤ)) = (r : ℤ) * h + v := by
      unfold frequency at he
      omega
    exact_mod_cast he'
  · intro he
    have he' : (u : ℤ) + (∑ i, (g i : ℤ)) = (r : ℤ) * h + v := by exact_mod_cast he
    unfold frequency
    omega

theorem sourceCopies_upper (r M : ℕ) : sourceCopies r M ≤ (r + 2) * M := by
  have h := sourceCopies_upper_sharp r M
  nlinarith

universe u

variable {r M : ℕ} {V : Party r → Type u}

def amplitude (c : 𝕜) (p : Party r) (t : Fin (sourceCopies r M))
    (x : SeparatedCoordinate V M p) : Polynomial 𝕜 :=
  match p with
  | .inl false => Polynomial.C c * PolynomialInterpolation.node (sourceCopies r M) t ^ x.1.2.val
  | .inl true => PolynomialInterpolation.dual (sourceCopies r M) (outputIndex x.1.1 x.1.2) t
  | .inr _ => PolynomialInterpolation.node (sourceCopies r M) t ^ x.1.val

def kernel (c : 𝕜) (p : Party r) (x : SeparatedCoordinate V M p)
    (a : Fin (sourceCopies r M) × SharedCoordinate V M p) : Polynomial 𝕜 :=
  amplitude c p a.1 x * Polynomial.X ^ weight p x *
    if a.2 = input p x then 1 else 0

def family [∀ p, Fintype (V p)] (c : 𝕜) (Z : Fin M → Tensor 𝕜 (Party r) V) :
    Tensor (Polynomial 𝕜) (Party r) (SeparatedCoordinate V M) :=
  Tensor.polynomialMap (kernel c) (Tensor.copies (sourceCopies r M) (sharedSum Z))

def filtered (Z : Fin M → Tensor 𝕜 (Party r) V) :
    Tensor (Polynomial 𝕜) (Party r) (SeparatedCoordinate V M) := fun x =>
  if (x (.inl false)).1.1 = (x (.inl true)).1.1 ∧
      frequency (fun i => (x (.inr i)).1) (x (.inl false)).1.1
        (x (.inl false)).1.2 (x (.inl true)).1.2 = 0 then
    Polynomial.C (Z (x (.inl false)).1.1 (fun p => (x p).2)) *
      Polynomial.X ^ totalDegree (fun i => (x (.inr i)).1)
        (x (.inl false)).1.1 (x (.inl false)).1.2 (x (.inl true)).1.2
  else 0

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

theorem shared_input (Z : Fin M → Tensor 𝕜 (Party r) V)
    (x : ∀ p, SeparatedCoordinate V M p) :
    sharedSum (𝕜 := 𝕜) Z (fun p => input p (x p)) =
      if (x (.inl false)).1.1 = (x (.inl true)).1.1 then
        Z (x (.inl false)).1.1 (fun p => (x p).2) else 0 := by
  have hb : sharedBase (fun p => input p (x p)) = fun p => (x p).2 := by
    funext p
    cases p <;> rfl
  change (if (x (.inl false)).1.1 = (x (.inl true)).1.1 then
    Z (x (.inl false)).1.1 (sharedBase (fun p => input p (x p))) else 0) = _
  rw [hb]

theorem product_amplitudes (c : 𝕜) (t : Fin (sourceCopies r M))
    (x : ∀ p, SeparatedCoordinate V M p) :
    (∏ p, amplitude c p t (x p)) = Polynomial.C c *
      (PolynomialInterpolation.dual (sourceCopies r M)
          (outputIndex (x (.inl true)).1.1 (x (.inl true)).1.2) t *
        PolynomialInterpolation.node (sourceCopies r M) t ^
          ((x (.inl false)).1.2.val + ∑ i, (x (.inr i)).1.val)) := by
  simp only [Fintype.prod_sum_type, Fintype.prod_bool, amplitude,
    Finset.prod_pow_eq_pow_sum, pow_add]
  ring

theorem sum_amplitudes (c : 𝕜) (x : ∀ p, SeparatedCoordinate V M p)
    (hh : (x (.inl false)).1.1 = (x (.inl true)).1.1) :
    (∑ t : Fin (sourceCopies r M), ∏ p, amplitude c p t (x p)) =
      Polynomial.C c * PolynomialInterpolation.determinant (sourceCopies r M) *
        if frequency (fun i => (x (.inr i)).1) (x (.inl false)).1.1
          (x (.inl false)).1.2 (x (.inl true)).1.2 = 0 then 1 else 0 := by
  simp_rw [product_amplitudes]
  rw [← Finset.mul_sum, PolynomialInterpolation.filter]
  · simp only [outputIndex, frequency_eq_zero_iff, ← hh]
    split_ifs <;> ring
  · exact input_sum_lt _ _

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

private theorem constants_copies (L : ℕ) (T : Tensor 𝕜 (Party r) (SharedCoordinate V M)) :
    (fun x => Polynomial.C (Tensor.copies L T x)) =
      Tensor.copies L (fun x => Polynomial.C (T x)) := by
  funext x
  simp only [Tensor.copies, Tensor.product, Tensor.diagonal]
  split_ifs <;> simp

theorem family_formula [∀ p, Fintype (V p)] (c : 𝕜)
    (Z : Fin M → Tensor 𝕜 (Party r) V) (x : ∀ p, SeparatedCoordinate V M p) :
    family c Z x =
      (∑ t : Fin (sourceCopies r M), ∏ p, amplitude c p t (x p)) *
        Polynomial.C (sharedSum Z (fun p => input p (x p))) *
          Polynomial.X ^ (∑ p, weight p (x p)) := by
  change Tensor.localMap (kernel c)
    (fun a => Polynomial.C (Tensor.copies (sourceCopies r M) (sharedSum Z) a)) x = _
  rw [constants_copies, Tensor.localMap_copies]
  simp only [Finset.sum_apply]
  have ht (t : Fin (sourceCopies r M)) :
      (∏ p, amplitude c p t (x p) * Polynomial.X ^ weight p (x p)) =
        (∏ p, amplitude c p t (x p)) * Polynomial.X ^ (∑ p, weight p (x p)) := by
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  calc
    _ = ∑ t : Fin (sourceCopies r M),
        (∏ p, amplitude c p t (x p) * Polynomial.X ^ weight p (x p)) *
          Polynomial.C (sharedSum Z (fun p => input p (x p))) := by
      apply Finset.sum_congr rfl
      intro t _
      exact selected_map (fun a => Polynomial.C (sharedSum Z a)) input
        (fun p y => amplitude c p t y * Polynomial.X ^ weight p y) x
    _ = (∑ t : Fin (sourceCopies r M), ∏ p, amplitude c p t (x p)) *
        Polynomial.X ^ (∑ p, weight p (x p)) *
        Polynomial.C (sharedSum Z (fun p => input p (x p))) := by
      simp_rw [ht]
      rw [Finset.sum_mul, Finset.sum_mul]
    _ = _ := by ring

theorem family_filtered [∀ p, Fintype (V p)] (c : 𝕜)
    (Z : Fin M → Tensor 𝕜 (Party r) V) (x : ∀ p, SeparatedCoordinate V M p) :
    family c Z x = Polynomial.C c * PolynomialInterpolation.determinant (sourceCopies r M) * filtered Z x := by
  rw [family_formula, shared_input]
  by_cases hh : (x (.inl false)).1.1 = (x (.inl true)).1.1
  · rw [sum_amplitudes c x hh, sum_weights x hh]
    unfold filtered
    by_cases hf : frequency (fun i => (x (.inr i)).1) (x (.inl false)).1.1
        (x (.inl false)).1.2 (x (.inl true)).1.2 = 0 <;> simp [hh, hf, mul_assoc]
  · simp [filtered, hh]

theorem filtered_coefficient (Z : Fin M → Tensor 𝕜 (Party r) V)
    (j : ℕ) (x : ∀ p, SeparatedCoordinate V M p) :
    Tensor.coefficient (filtered Z) j x =
      if (x (.inl false)).1.1 = (x (.inl true)).1.1 ∧
          frequency (fun i => (x (.inr i)).1) (x (.inl false)).1.1
            (x (.inl false)).1.2 (x (.inl true)).1.2 = 0 ∧
          j = totalDegree (fun i => (x (.inr i)).1)
            (x (.inl false)).1.1 (x (.inl false)).1.2 (x (.inl true)).1.2 then
        Z (x (.inl false)).1.1 (fun p => (x p).2) else 0 := by
  change (filtered Z x).coeff j = _
  unfold filtered
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

theorem filtered_leading (Z : Fin M → Tensor 𝕜 (Party r) V) :
    Tensor.Leading (filtered Z) (shift r M) (separatedSum Z) := by
  constructor
  · funext x
    rw [filtered_coefficient]
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
    simp only [hc]
    rfl
  · intro j hj
    funext x
    rw [filtered_coefficient]
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

theorem separated_degenerates [∀ p, Fintype (V p)] (_hM : 0 < M)
    (Z : Fin M → Tensor 𝕜 (Party r) V) :
    Tensor.Degenerates (separatedSum Z) (Tensor.copies (sourceCopies r M) (sharedSum Z)) := by
  let D : Polynomial 𝕜 := PolynomialInterpolation.determinant (sourceCopies r M)
  let d := D.natTrailingDegree
  let c := (D.coeff d)⁻¹
  let q : Polynomial 𝕜 := Polynomial.C c * D
  have hD : D ≠ 0 := PolynomialInterpolation.determinant_ne_zero _
  have hc : D.coeff d ≠ 0 := Polynomial.coeff_natTrailingDegree_ne_zero.mpr hD
  have hq : ∀ j < d, q.coeff j = 0 := by
    intro j hj
    simp only [q, Polynomial.coeff_C_mul,
      Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hj, mul_zero]
  have hq1 : q.coeff d = 1 := by
    simpa only [q, Polynomial.coeff_C_mul, c] using inv_mul_cancel₀ hc
  have hlead := (filtered_leading Z).polynomial_mul q d hq
  rw [hq1, one_smul] at hlead
  have heq : (fun x => q * filtered Z x) = family c Z := by
    funext x
    exact (family_filtered c Z x).symm
  rw [heq] at hlead
  exact ⟨kernel c, d + shift r M, hlead⟩

theorem separated_asymptoticRank_le [∀ p, Fintype (V p)] (hM : 0 < M)
    (Z : Fin M → Tensor 𝕜 (Party r) V) :
    Tensor.asymptoticRank (separatedSum Z) ≤
      Tensor.asymptoticRank (Tensor.copies (sourceCopies r M) (sharedSum Z)) :=
  (separated_degenerates hM Z).asymptoticRank_le

end Lemmata.TensorRank.Separation
