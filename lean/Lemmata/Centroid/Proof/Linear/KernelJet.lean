module

public import Lemmata.Centroid.Proof.Linear.KernelLift

@[expose] public section

namespace Lemmata.Centroid.Linear

open Polynomial
open scoped Matrix

noncomputable section

variable {F U W : Type*} [Field F] [Infinite F]
  [AddCommGroup U] [Module F U] [Module.Finite F U]
  [AddCommGroup W] [Module F W] [Module.Finite F W]

theorem maximal_rank_kernel_jet (f g : U →ₗ[F] W)
    (hmax : ∀ t : F, Module.finrank F (f + t • g).range ≤ Module.finrank F f.range)
    {x : U} (hx : f x = 0) :
    ∃ r : ℕ → U, r 0 = x ∧ ∀ n, f (r (n + 1)) = -g (r n) := by
  classical
  let b := Module.finBasis F U
  let c := Module.finBasis F W
  let A := LinearMap.toMatrix b c f
  let B := LinearMap.toMatrix b c g
  have hrank (h : U →ₗ[F] W) :
      (LinearMap.toMatrix b c h).rank = Module.finrank F h.range := by
    rw [Matrix.rank_eq_finrank_range_toLin _ c b, Matrix.toLin_toMatrix]
  have hmax' (t : F) : (A + t • B).rank ≤ A.rank := by
    have h : A + t • B = LinearMap.toMatrix b c (f + t • g) := by
      simp only [map_add, map_smul, A, B]
    rw [h, hrank, hrank]
    exact hmax t
  have hx' : A *ᵥ b.equivFun x = 0 := by
    rw [Module.Basis.equivFun_apply, LinearMap.toMatrix_mulVec_repr, hx, map_zero]
    rfl
  obtain ⟨p, hp0, hp⟩ := maximal_rank_kernel_lift A B hmax' (b.equivFun x) hx'
  let r : ℕ → U := fun n => b.equivFun.symm (fun i => (p i).coeff n)
  have hr (n : ℕ) : b.equivFun (r n) = fun i => (p i).coeff n :=
    b.equivFun.apply_symm_apply _
  have hcoeff (M : Matrix (Fin (Module.finrank F W)) (Fin (Module.finrank F U)) F) (n : ℕ) :
      (fun j => ((M.map C *ᵥ p) j).coeff n) = M *ᵥ (fun i => (p i).coeff n) := by
    funext j
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, finsetSum_coeff, coeff_C_mul]
  have hrec (n : ℕ) : A *ᵥ (fun i => (p i).coeff (n + 1)) +
      B *ᵥ (fun i => (p i).coeff n) = 0 := by
    have hp' : A.map C *ᵥ p + (X : F[X]) • (B.map C *ᵥ p) = 0 := by
      simpa only [pencil, Matrix.add_mulVec, Matrix.smul_mulVec] using hp
    have h := congrArg (fun q : Fin (Module.finrank F W) → F[X] =>
      fun j => (q j).coeff (n + 1)) hp'
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, coeff_add,
      coeff_X_mul, Pi.zero_apply, coeff_zero] at h
    change (fun j => ((A.map C *ᵥ p) j).coeff (n + 1)) +
      (fun j => ((B.map C *ᵥ p) j).coeff n) = 0 at h
    rwa [hcoeff, hcoeff] at h
  have hfm (n : ℕ) : c.equivFun (f (r n)) = A *ᵥ (fun i => (p i).coeff n) := by
    rw [Module.Basis.equivFun_apply, ← LinearMap.toMatrix_mulVec_repr b c,
      ← Module.Basis.equivFun_apply b, hr]
  have hgm (n : ℕ) : c.equivFun (g (r n)) = B *ᵥ (fun i => (p i).coeff n) := by
    rw [Module.Basis.equivFun_apply, ← LinearMap.toMatrix_mulVec_repr b c,
      ← Module.Basis.equivFun_apply b, hr]
  refine ⟨r, ?_, ?_⟩
  · apply b.equivFun.injective
    rw [hr]
    funext i
    rw [coeff_zero_eq_eval_zero, hp0]
  · intro n
    apply eq_neg_of_add_eq_zero_left
    apply c.equivFun.injective
    rw [map_add, map_zero, hfm, hgm]
    exact hrec n

end

end Lemmata.Centroid.Linear
