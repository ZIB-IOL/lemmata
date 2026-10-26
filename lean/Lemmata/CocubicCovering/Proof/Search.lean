module

public import Lemmata.CocubicCovering.Proof.Branching
public meta import Lemmata.CocubicCovering.Proof.Branching
public import Lemmata.CocubicCovering.Proof.Witness
public meta import Lemmata.CocubicCovering.Proof.Witness

@[expose] public section

set_option Elab.async false

namespace Lemmata.CocubicCovering.CoveringSearch

open Module CoveringBranching CoveringWitness

variable {P : Type*}

/-- A search state specifies a parameter condition and vectors in its kernel. -/
def Feasible {c : ℕ} (allowed : P → Prop)
    (kernel : P → Submodule Field LocalVector) (core : Fin c → LocalVector) : Prop :=
  ∃ p, allowed p ∧ familySpan core ≤ kernel p

theorem branch {c d k : ℕ} (allowed : P → Prop)
    (kernel : P → Submodule Field LocalVector) (ambient : Submodule Field LocalVector)
    (core : Fin c → LocalVector) (fresh : Fin d → LocalVector)
    (hkernel : ∀ p, allowed p → kernel p ≤ ambient)
    (hdimension : ∀ p, allowed p → k ≤ finrank Field (kernel p))
    (hfresh : familySpace fresh ≤ ambient)
    (hdisjoint : familySpace fresh ⊓ familySpan core = ⊥)
    (hfreshdim : finrank Field (familySpace fresh) = d)
    (hamb : finrank Field ambient < d + k)
    (impossible : ∀ b ∈ branches d,
      ¬∃ p, allowed p ∧ familySpan core ⊔
        Submodule.span Field {combine fresh b} ≤ kernel p) :
    ¬Feasible allowed kernel core := by
  rintro ⟨p, hp, hcore⟩
  obtain ⟨b, hb, _, _, hnext⟩ := exists_kernel_branch fresh ambient (kernel p)
    (familySpan core) hfresh (hkernel p hp) hcore hdisjoint hfreshdim
      (hdimension p hp) hamb
  exact impossible b hb ⟨p, hp, hnext⟩

theorem weaken {c d : ℕ} (allowed : P → Prop)
    (kernel : P → Submodule Field LocalVector)
    (core : Fin c → LocalVector) (target : Fin d → LocalVector)
    (hspan : familySpan target ≤ familySpan core) :
    Feasible allowed kernel core → Feasible allowed kernel target := by
  rintro ⟨p, hp, hcore⟩
  exact ⟨p, hp, hspan.trans hcore⟩

theorem transport {Q : Type*} {c d : ℕ}
    (allowed : P → Prop) (nextAllowed : Q → Prop)
    (kernel : P → Submodule Field LocalVector)
    (nextKernel : Q → Submodule Field LocalVector)
    (core : Fin c → LocalVector) (target : Fin d → LocalVector)
    (transform : P → Q) (action : LocalVector →ₗ[Field] LocalVector)
    (hallowed : ∀ p, allowed p → nextAllowed (transform p))
    (hkernel : ∀ p, allowed p →
      (kernel p).map action ≤ nextKernel (transform p))
    (hspan : familySpan target ≤ (familySpan core).map action) :
    Feasible allowed kernel core → Feasible nextAllowed nextKernel target := by
  rintro ⟨p, hp, hcore⟩
  refine ⟨transform p, hallowed p hp, hspan.trans ?_⟩
  exact (Submodule.map_mono hcore).trans (hkernel p hp)

end Lemmata.CocubicCovering.CoveringSearch
