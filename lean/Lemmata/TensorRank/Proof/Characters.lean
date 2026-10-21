module

public import Lemmata.TensorRank.Proof.TensorSpectrum
public import Lemmata.TensorRank.Proof.SpectrumDuality
public import Lemmata.TensorRank.Proof.MultiplicativeGrowth
public import Lemmata.TensorRank.Proof.InterpolationRestriction

@[expose] public section

set_option autoImplicit false

open scoped BigOperators
open Classical

noncomputable section

namespace Lemmata.TensorRank.TensorSemiring

def Character (k : ℕ) :=
  {f : Value k →+* ℝ // ∀ {a b}, Rel a b → f a ≤ f b}

instance {k : ℕ} : CoeFun (Character k) (fun _ => Value k → ℝ) := ⟨fun f => f.val⟩

namespace Character

variable {k : ℕ} [Nonempty (Fin k)] (f : Character k)
variable {V W : Fin k → Type} [∀ i, Fintype (V i)] [∀ i, Fintype (W i)]

def eval (T : Tensor ℂ (Fin k) V) : ℝ := f (ofTensor T)

theorem nonneg (a : Value k) : 0 ≤ f a := by
  simpa only [map_zero] using f.prop (zero_rel a)

omit [Nonempty (Fin k)] in
@[simp] theorem eval_zero : f.eval (0 : Tensor ℂ (Fin k) V) = 0 := by
  simp only [eval, ofTensor_zero, map_zero]

omit [Nonempty (Fin k)] in
@[simp] theorem eval_product (S : Tensor ℂ (Fin k) V) (T : Tensor ℂ (Fin k) W) :
    f.eval (Tensor.product S T) = f.eval S * f.eval T := by
  simp only [eval, ofTensor_product, map_mul]

omit [Nonempty (Fin k)] in
@[simp] theorem eval_reindex (e : ∀ i, W i ≃ V i) (T : Tensor ℂ (Fin k) V) :
    f.eval (Tensor.reindex (fun i => e i) T) = f.eval T := by
  simp only [eval, ofTensor_reindex]

@[simp] theorem eval_diagonal (l : ℕ) : f.eval (Tensor.diagonal (R := ℂ) (I := Fin k) l) = l := by
  change f.val (ofObject (Object.nat k l)) = l
  rw [ofObject_nat, map_natCast]

theorem eval_nonneg (T : Tensor ℂ (Fin k) V) : 0 ≤ f.eval T := f.nonneg (ofTensor T)

omit [Nonempty (Fin k)] in
theorem monotone {S : Tensor ℂ (Fin k) W} {T : Tensor ℂ (Fin k) V} (h : Tensor.Restricts S T) :
    f.eval S ≤ f.eval T := f.prop h

theorem one_le_eval {T : Tensor ℂ (Fin k) V} (hT : T ≠ 0) : 1 ≤ f.eval T := by
  simpa only [eval_diagonal, Nat.cast_one] using f.monotone (Tensor.diagonal_one_restricts hT)

theorem eval_pos {T : Tensor ℂ (Fin k) V} (hT : T ≠ 0) : 0 < f.eval T :=
  zero_lt_one.trans_le (f.one_le_eval hT)

theorem eval_eq_zero_iff (T : Tensor ℂ (Fin k) V) : f.eval T = 0 ↔ T = 0 := by
  constructor
  · intro h
    by_contra hT
    exact (f.eval_pos hT).ne' h
  · rintro rfl
    exact f.eval_zero

theorem eval_le_rank (T : Tensor ℂ (Fin k) V) : f.eval T ≤ Tensor.rank T := by
  simpa only [eval_diagonal] using f.monotone (Tensor.restricts_diagonal_rank T)

@[simp] theorem eval_copies (l : ℕ) (T : Tensor ℂ (Fin k) V) :
    f.eval (Tensor.copies l T) = l * f.eval T := by
  change f.eval (Tensor.product (Tensor.diagonal l) T) = _
  rw [eval_product, eval_diagonal]

omit [Nonempty (Fin k)] in
@[simp] theorem eval_power (T : Tensor ℂ (Fin k) V) (n : ℕ) :
    f.eval (Tensor.power T n) = f.eval T ^ n := by
  simp only [eval, ofTensor_power, map_pow]

theorem eval_degenerates {S : Tensor ℂ (Fin k) W} {T : Tensor ℂ (Fin k) V}
    (h : Tensor.Degenerates S T) : f.eval S ≤ f.eval T := by
  obtain ⟨D, hD⟩ := h.exists_power_copies
  apply le_of_polynomial_power_bound (f.eval_nonneg S) (f.eval_nonneg T)
    ((D : ℝ) + 1) (by positivity) 1
  intro n _
  have hh := f.monotone (hD n)
  rw [eval_power, eval_copies, eval_power] at hh
  apply hh.trans
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg (f.eval_nonneg T) n)
  push_cast
  nlinarith [Nat.cast_nonneg (α := ℝ) D, Nat.cast_nonneg (α := ℝ) n]

def asPoint (hk : 2 ≤ k) : Spectrum.Point (preorder hk) := ⟨f.val, f.prop⟩

omit [Nonempty (Fin k)] in
theorem eval_le_asymptoticRank (hk : 2 ≤ k) (T : Tensor ℂ (Fin k) V) :
    f.eval T ≤ Tensor.asymptoticRank T := by
  have h := (f.asPoint hk).le_asymptoticRank (ofTensor T)
  simpa only [asPoint, eval, preorder_asymptoticRank_ofTensor] using h

end Character

def characterOfPoint {k : ℕ} {hk : 2 ≤ k} (f : Spectrum.Point (preorder hk)) : Character k :=
  ⟨f.val, f.prop⟩

theorem exists_character_eq_asymptoticRank {k : ℕ} (hk : 2 ≤ k)
    {V : Fin k → Type} [∀ i, Fintype (V i)] (T : Tensor ℂ (Fin k) V) :
    ∃ f : Character k, f.eval T = Tensor.asymptoticRank T := by
  obtain ⟨f, hf⟩ := (preorder hk).exists_point_eq_asymptoticRank
    (preorder_oneLeNonzero hk) (ofTensor T)
  exact ⟨characterOfPoint f, by
    simpa only [characterOfPoint, Character.eval, preorder_asymptoticRank_ofTensor] using hf⟩

theorem asymptoticRank_le_iff_characters {k : ℕ} (hk : 2 ≤ k)
    {V : Fin k → Type} [∀ i, Fintype (V i)] (T : Tensor ℂ (Fin k) V) (x : ℝ) :
    Tensor.asymptoticRank T ≤ x ↔ ∀ f : Character k, f.eval T ≤ x := by
  constructor
  · exact fun h f => (f.eval_le_asymptoticRank hk T).trans h
  · intro h
    obtain ⟨f, hf⟩ := exists_character_eq_asymptoticRank hk T
    simpa only [hf] using h f

end Lemmata.TensorRank.TensorSemiring
