module

public import Lemmata.TensorRank.Proof.Characters
public import Lemmata.TensorRank.Proof.TensorPermutation

@[expose] public section

set_option autoImplicit false

open scoped BigOperators
open Classical

noncomputable section

namespace Lemmata.TensorRank.TensorSemiring

namespace Character

variable {k : ℕ} (f : Character k)

def permute (σ : Equiv.Perm (Fin k)) : Character k :=
  ⟨f.val.comp (relabelHom σ), fun h => f.prop (rel_relabel σ h)⟩

@[simp] theorem permute_apply (σ : Equiv.Perm (Fin k)) (a : Value k) :
    f.permute σ a = f (relabel σ a) := rfl

theorem le_rank [Nonempty (Fin k)] (a : Value k) : f a ≤ rank a := by
  refine Quot.inductionOn a (fun A => ?_)
  exact f.eval_le_rank A.tensor

end Character

def symmetricProduct {k : ℕ} (f : Character k) (a : Value k) : ℝ :=
  ∏ σ : Equiv.Perm (Fin k), f (relabel σ a)

def symmetricValue {k : ℕ} (f : Character k) (p : ℝ) (a : Value k) : ℝ :=
  symmetricProduct f a ^ (1 / ((Fintype.card (Equiv.Perm (Fin k)) : ℝ) * p))

def symmetricEval {k : ℕ} (f : Character k) (p : ℝ)
    {V : Fin k → Type} [∀ i, Fintype (V i)] (T : Tensor ℂ (Fin k) V) : ℝ :=
  symmetricValue f p (ofTensor T)

variable {k : ℕ} [Nonempty (Fin k)] (f : Character k)

omit [Nonempty (Fin k)] in
theorem permutationCount_pos : 0 < (Fintype.card (Equiv.Perm (Fin k)) : ℝ) := by
  exact_mod_cast Fintype.card_pos_iff.mpr (show Nonempty (Equiv.Perm (Fin k)) from ⟨1⟩)

theorem symmetricProduct_nonneg (a : Value k) : 0 ≤ symmetricProduct f a :=
  Finset.prod_nonneg (fun _ _ => f.nonneg _)

theorem symmetricProduct_mono {a b : Value k} (h : Rel a b) :
    symmetricProduct f a ≤ symmetricProduct f b :=
  Finset.prod_le_prod₀ (fun _ _ => f.nonneg _) (fun σ _ => f.prop (rel_relabel σ h))

omit [Nonempty (Fin k)] in
@[simp] theorem symmetricProduct_one : symmetricProduct f 1 = 1 := by
  change (∏ σ : Equiv.Perm (Fin k), f.val (relabelHom σ 1)) = 1
  simp only [map_one, Finset.prod_const_one]

omit [Nonempty (Fin k)] in
@[simp] theorem symmetricProduct_zero : symmetricProduct f 0 = 0 := by
  change (∏ σ : Equiv.Perm (Fin k), f.val (relabelHom σ 0)) = 0
  simp only [map_zero]
  simp

omit [Nonempty (Fin k)] in
theorem symmetricProduct_mul (a b : Value k) :
    symmetricProduct f (a * b) = symmetricProduct f a * symmetricProduct f b := by
  change (∏ σ : Equiv.Perm (Fin k), f.val (relabelHom σ (a * b))) = _
  simp only [map_mul, Finset.prod_mul_distrib]
  rfl

omit [Nonempty (Fin k)] in
theorem symmetricProduct_relabel (τ : Equiv.Perm (Fin k)) (a : Value k) :
    symmetricProduct f (relabel τ a) = symmetricProduct f a := by
  apply Fintype.prod_equiv (Equiv.mulLeft τ)
  intro σ
  change f (relabel σ (relabel τ a)) = f (relabel (τ * σ) a)
  rw [relabel_mul]

theorem symmetricProduct_le_rank (a : Value k) :
    symmetricProduct f a ≤ (rank a : ℝ) ^ Fintype.card (Equiv.Perm (Fin k)) := by
  calc
    _ ≤ ∏ σ : Equiv.Perm (Fin k), (rank a : ℝ) :=
      Finset.prod_le_prod₀ (fun _ _ => f.nonneg _) (fun σ _ => by
        simpa only [rank_relabel] using f.le_rank (relabel σ a))
    _ = _ := by simp

theorem symmetricValue_nonneg (p : ℝ) (a : Value k) : 0 ≤ symmetricValue f p a :=
  Real.rpow_nonneg (symmetricProduct_nonneg f a) _

omit [Nonempty (Fin k)] in
@[simp] theorem symmetricValue_one (p : ℝ) : symmetricValue f p 1 = 1 := by
  rw [symmetricValue, symmetricProduct_one, Real.one_rpow]

omit [Nonempty (Fin k)] in
theorem symmetricValue_zero (p : ℝ) (hp : 0 < p) : symmetricValue f p 0 = 0 := by
  rw [symmetricValue, symmetricProduct_zero, Real.zero_rpow]
  exact (one_div_pos.mpr (mul_pos permutationCount_pos hp)).ne'

theorem symmetricValue_mul (p : ℝ) (a b : Value k) :
    symmetricValue f p (a * b) = symmetricValue f p a * symmetricValue f p b := by
  rw [symmetricValue, symmetricProduct_mul,
    Real.mul_rpow (symmetricProduct_nonneg f a) (symmetricProduct_nonneg f b)]
  rfl

theorem symmetricValue_pow (p : ℝ) (a : Value k) (n : ℕ) :
    symmetricValue f p (a ^ n) = symmetricValue f p a ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, symmetricValue_mul, ih, pow_succ]

theorem symmetricValue_mono (p : ℝ) (hp : 0 < p) {a b : Value k} (h : Rel a b) :
    symmetricValue f p a ≤ symmetricValue f p b :=
  Real.rpow_le_rpow (symmetricProduct_nonneg f a) (symmetricProduct_mono f h) (by positivity)

omit [Nonempty (Fin k)] in
theorem symmetricValue_relabel (p : ℝ) (σ : Equiv.Perm (Fin k)) (a : Value k) :
    symmetricValue f p (relabel σ a) = symmetricValue f p a := by
  rw [symmetricValue, symmetricProduct_relabel]
  rfl

theorem symmetricValue_le_rank (p : ℝ) (hp : 0 < p) (a : Value k) :
    symmetricValue f p a ≤ (rank a : ℝ) ^ (1 / p) := by
  apply (Real.rpow_le_rpow (symmetricProduct_nonneg f a) (symmetricProduct_le_rank f a)
    (show 0 ≤ 1 / ((Fintype.card (Equiv.Perm (Fin k)) : ℝ) * p) by positivity)).trans_eq
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
  congr 1
  field_simp [(permutationCount_pos (k := k)).ne']

variable {V W : Fin k → Type} [∀ i, Fintype (V i)] [∀ i, Fintype (W i)]

theorem symmetricEval_product (p : ℝ) (S : Tensor ℂ (Fin k) V) (T : Tensor ℂ (Fin k) W) :
    symmetricEval f p (Tensor.product S T) = symmetricEval f p S * symmetricEval f p T := by
  simp only [symmetricEval, ofTensor_product, symmetricValue_mul]

theorem symmetricEval_power (p : ℝ) (T : Tensor ℂ (Fin k) V) (n : ℕ) :
    symmetricEval f p (Tensor.power T n) = symmetricEval f p T ^ n := by
  simp only [symmetricEval, ofTensor_power, symmetricValue_pow]

omit [Nonempty (Fin k)] in
theorem symmetricEval_reindex (p : ℝ) (e : ∀ i, W i ≃ V i) (T : Tensor ℂ (Fin k) V) :
    symmetricEval f p (Tensor.reindex (fun i => e i) T) = symmetricEval f p T := by
  simp only [symmetricEval, ofTensor_reindex]

omit [Nonempty (Fin k)] in
theorem symmetricEval_relabel (p : ℝ) (σ : Equiv.Perm (Fin k)) (T : Tensor ℂ (Fin k) V) :
    symmetricEval f p (Tensor.relabel σ T) = symmetricEval f p T := by
  simp only [symmetricEval, ofTensor_relabel, symmetricValue_relabel]

theorem symmetricEval_mono (p : ℝ) (hp : 0 < p)
    {S : Tensor ℂ (Fin k) W} {T : Tensor ℂ (Fin k) V} (h : Tensor.Restricts S T) :
    symmetricEval f p S ≤ symmetricEval f p T := symmetricValue_mono f p hp h

theorem symmetricEval_degenerates (p : ℝ) (hp : 0 < p)
    {S : Tensor ℂ (Fin k) W} {T : Tensor ℂ (Fin k) V} (h : Tensor.Degenerates S T) :
    symmetricEval f p S ≤ symmetricEval f p T := by
  apply Real.rpow_le_rpow (symmetricProduct_nonneg f (ofTensor S)) _ (by positivity)
  apply Finset.prod_le_prod₀ (fun _ _ => f.nonneg _)
  intro σ _
  exact (f.permute σ).eval_degenerates h

theorem symmetricEval_le_rank (p : ℝ) (hp : 0 < p) (T : Tensor ℂ (Fin k) V) :
    symmetricEval f p T ≤ (Tensor.rank T : ℝ) ^ (1 / p) :=
  symmetricValue_le_rank f p hp (ofTensor T)

end Lemmata.TensorRank.TensorSemiring
