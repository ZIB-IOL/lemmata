module

public import Lemmata.FockCircuits.Main

@[expose] public section

set_option autoImplicit false

open scoped BigOperators

namespace Lemmata.EnergyShellCrossings

open Lemmata.FockCircuits

noncomputable section

namespace BalancedCrossing

/-- A transversal cut selects exactly one endpoint of each paired index. -/
def select {S A : Type*} (mask : S → Bool) (x y : S → A) : S → A :=
  fun s => if mask s then x s else y s

/-- A grouped decomposition of independent identity wires. Each layout has a
single shared rank index; its two factors see complementary transversal cuts. -/
structure Decomposition (S A C K : Type*) [Fintype S] [Fintype C] [Fintype K]
    [DecidableEq A] where
  mask : C → S → Bool
  left : C → K → (S → A) → ℤ
  right : C → K → (S → A) → ℤ
  identity : ∀ (x y : S → A),
    (∑ c, ∑ k, left c k (select (mask c) x y) * right c k (select (mask c) y x)) =
      ∏ s, if x s = y s then (1 : ℤ) else 0

/-- Leaves of a complete binary fusion tree. -/
def Leaves : ℕ → Type
  | 0 => Unit
  | r + 1 => Leaves r ⊕ Leaves r

instance leavesFintype : (r : ℕ) → Fintype (Leaves r)
  | 0 => inferInstanceAs (Fintype Unit)
  | r + 1 => by
    letI := leavesFintype r
    exact inferInstanceAs (Fintype (Leaves r ⊕ Leaves r))

/-- Relative orientations at the internal nodes of a complete binary tree. -/
def Layouts : ℕ → Type
  | 0 => Unit
  | r + 1 => (Layouts r × Layouts r) × Bool

instance layoutsFintype : (r : ℕ) → Fintype (Layouts r)
  | 0 => inferInstanceAs (Fintype Unit)
  | r + 1 => by
    letI := layoutsFintype r
    exact inferInstanceAs (Fintype ((Layouts r × Layouts r) × Bool))

def firstLeaf : (r : ℕ) → Leaves r
  | 0 => ()
  | r + 1 => Sum.inl (firstLeaf r)

/-- Per-cut rank after each level; no mode or child-rank coordinate is retained. -/
def rankSequence (n : ℕ) (h : ℕ → ℕ) : ℕ → ℕ
  | 0 => n
  | r + 1 => stateCount (2 * h r)

end BalancedCrossing

/-- An integral crossing with one intermediate-state coordinate per cut. -/
def IntegralShellCrossing (H E n m : ℕ) : Prop :=
  ∃ a b c d : Fin (stateCount (H + E)) → Fin n → Fin m → ℤ,
    ∀ (i k : Fin n) (j l : Fin m),
      (∑ s, a s i j * b s k l) + (∑ s, c s i l * d s k j) =
        if i = k then (if j = l then 1 else 0) else 0

/-- A rectangular complex sum-of-squares identity with a finite energy bound. -/
def ShellSumOfSquares (H E n m : ℕ) : Prop :=
  ∃ (s : ℕ) (forms : Fin s → Fin n → Fin m → ℂ),
    s ≤ 4 * stateCount (H + E) ∧
    ∀ (x : Fin n → ℂ) (y : Fin m → ℂ),
      (∑ r, Hurwitz.bilinear (forms r) x y ^ 2) =
        (∑ i, x i ^ 2) * (∑ j, y j ^ 2)

/-- A grouped decomposition with distinct cuts and the balanced rank recurrence. -/
def BalancedFusion (n : ℕ) (h : ℕ → ℕ) (r : ℕ) : Prop :=
  ∃ p : BalancedCrossing.Decomposition (BalancedCrossing.Leaves r) (Fin n)
      (BalancedCrossing.Layouts r) (Fin (BalancedCrossing.rankSequence n h r)),
    Function.Injective p.mask ∧
    (∀ c, p.mask c (BalancedCrossing.firstLeaf r) = true) ∧
    Fintype.card (BalancedCrossing.Leaves r) = 2 ^ r ∧
    Fintype.card (BalancedCrossing.Layouts r) = 2 ^ (2 ^ r - 1)

end

end Lemmata.EnergyShellCrossings
