module

public import Lemmata.CocubicCovering.Proof.Model
public meta import Lemmata.CocubicCovering.Proof.Model
public import Mathlib.LinearAlgebra.BilinearForm.Basic

@[expose] public section

set_option Elab.async false

namespace Lemmata.CocubicCovering.Covering

open scoped BigOperators

def homogeneousQuadratics (m : ℕ) : Submodule Field (BooleanFunction m) :=
  Submodule.span Field (Set.range fun s : {s : Finset (Fin m) // s.card = 2} =>
    monomial s.val)

def quadraticMultipliers {m : ℕ} (f : BooleanFunction m) :
    Submodule Field (BooleanFunction m) :=
  homogeneousQuadratics m ⊓
    (reedMuller m (m - 2)).comap (LinearMap.mulRight Field f)

def pairing {m : ℕ} (f h : BooleanFunction m) :
    LinearMap.BilinForm Field (quadraticMultipliers f) :=
  LinearMap.mk₂ Field (fun q q' => ∑ x : Vector m, q.val x * q'.val x * (f + h) x)
    (by intro q₁ q₂ q'; simp [add_mul, Finset.sum_add_distrib])
    (by intro a q q'; simp [Finset.mul_sum, mul_assoc])
    (by
      intro q q₁ q₂
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x hx
      change q.val x * (q₁.val x + q₂.val x) * (f + h) x =
        q.val x * q₁.val x * (f + h) x + q.val x * q₂.val x * (f + h) x
      rw [mul_add, add_mul])
    (by intro a q q'; simp [Finset.mul_sum, mul_assoc, mul_left_comm])

noncomputable abbrev rank {E : Type*} [AddCommGroup E] [Module Field E]
    (B : LinearMap.BilinForm Field E) : ℕ :=
  Module.finrank Field (LinearMap.range B)

end Lemmata.CocubicCovering.Covering
