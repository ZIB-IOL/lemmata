module

public import Lemmata.TensorRank.Proof.Interpolation
public import Lemmata.TensorRank.Proof.DirectSum

@[expose] public section

set_option autoImplicit false

open scoped BigOperators
open Classical

namespace Lemmata.TensorRank.Tensor

universe u v w z

variable {R : Type u} [CommSemiring R] {I : Type v} [Fintype I] [Nonempty I]
variable {V : I → Type w} [∀ i, Fintype (V i)] {W : I → Type z}

omit [Nonempty I] in
theorem localMap_scale_party (A : ∀ i, W i → V i → R) (T : Tensor R I V) (i₀ : I) (c : R) :
    localMap (fun i y x => (if i = i₀ then c else 1) * A i y x) T = c • localMap A T := by
  funext y
  simp only [localMap, Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib]
  have hc : (∏ i : I, if i = i₀ then c else 1) = c := by simp
  simp only [hc, Finset.mul_sum, mul_assoc]

theorem linear_combination_restricts_copies (T : Tensor R I V) (l : ℕ)
    (A : Fin l → ∀ i, W i → V i → R) (c : Fin l → R) :
    Restricts (∑ q, c q • localMap (A q) T) (copies l T) := by
  let i₀ : I := Classical.arbitrary I
  refine ⟨fun i y x => (if i = i₀ then c x.1 else 1) * A x.1 i y x.2, ?_⟩
  rw [localMap_copies]
  exact Finset.sum_congr rfl (fun q _ => (localMap_scale_party (A q) T i₀ (c q)).symm)

variable {F : Type u} [Field F] [Infinite F]

theorem coefficient_restricts_copies (P : Tensor (Polynomial F) I W) (D e : ℕ)
    (hD : DegreeLE P D) (T : Tensor F I V) (A : F → ∀ i, W i → V i → F)
    (hA : ∀ t, evaluate P t = localMap (A t) T) :
    Restricts (coefficient P e) (copies (D + 1) T) := by
  let nodes : Fin (D + 1) → F := fun j => Infinite.natEmbedding F j.val
  have hn : Function.Injective nodes := fun i j h => Fin.ext ((Infinite.natEmbedding F).injective h)
  rw [coefficient_eq_interpolation P nodes hn hD e]
  simp_rw [hA]
  exact linear_combination_restricts_copies T (D + 1) (fun q => A (nodes q)) _

theorem power_restricts_copies_of_leading
    (A : ∀ i, W i → V i → Polynomial F) (T : Tensor F I V) (S : Tensor F I W)
    (e D n : ℕ) (h : Leading (polynomialMap A T) e S)
    (hD : DegreeLE (polynomialMap A T) D) :
    Restricts (power S n) (copies (D * n + 1) (power T n)) := by
  rw [← h.power_coefficient n]
  apply coefficient_restricts_copies _ (D * n) (e * n) (hD.power n) (power T n)
    (fun t => powerKernel (fun i y x => (A i y x).eval t) n)
  intro t
  rw [evaluate_power, evaluate_polynomialMap, localMap_power]

variable [∀ i, Fintype (W i)]

theorem Degenerates.exists_power_copies {S : Tensor F I W} {T : Tensor F I V}
    (h : Degenerates S T) : ∃ D, ∀ n,
      Restricts (power S n) (copies (D * n + 1) (power T n)) := by
  obtain ⟨A, e, h⟩ := h
  obtain ⟨D, hD⟩ := exists_degree_bound (polynomialMap A T)
  exact ⟨D, fun n => power_restricts_copies_of_leading A T S e D n h hD⟩

end Lemmata.TensorRank.Tensor
