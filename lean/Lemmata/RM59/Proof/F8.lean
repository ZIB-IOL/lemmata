module

public import Mathlib.Algebra.Field.MinimalAxioms
public import Mathlib.Algebra.CharP.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Tactic.DeriveFintype
public meta import Mathlib.Data.Fintype.Defs
public meta import Mathlib.Data.Fintype.Card
public meta import Mathlib.Algebra.Ring.Defs
public meta import Mathlib.Algebra.Field.Defs
public meta import Lean.Elab.Tactic.Decide

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace Lemmata.RM59

/-- Polynomial-basis encoding modulo X^3 + X + 1. -/
structure F8Scalar where
  code : Fin 8
  deriving DecidableEq, Fintype, Inhabited, Repr

namespace F8Scalar

def ofNat (n : Nat) : F8Scalar := ⟨⟨n % 8, Nat.mod_lt _ (by decide)⟩⟩

def timesAlpha (a : Nat) : Nat :=
  if a.testBit 2 then Nat.xor (a * 2) 11 else a * 2

def multiplyCode (a b : Nat) : Nat :=
  Nat.xor (Nat.xor (if b.testBit 0 then a else 0)
    (if b.testBit 1 then timesAlpha a else 0))
    (if b.testBit 2 then timesAlpha (timesAlpha a) else 0)

instance : Zero F8Scalar := ⟨ofNat 0⟩
instance : One F8Scalar := ⟨ofNat 1⟩
instance : Add F8Scalar := ⟨fun a b => ofNat (Nat.xor a.code.val b.code.val)⟩
instance : Neg F8Scalar := ⟨id⟩
instance : Mul F8Scalar := ⟨fun a b => ofNat (multiplyCode a.code.val b.code.val)⟩
instance : Inv F8Scalar := ⟨fun a =>
  let a2 := a * a
  a2 * (a2 * a2)⟩

instance : Field F8Scalar :=
  Field.ofMinimalAxioms F8Scalar
    (by decide)
    (by decide)
    (by decide)
    (by decide)
    (by decide)
    (by decide)
    (by decide)
    (by decide)
    (by decide)
    ⟨0, 1, by decide⟩

instance : CharP F8Scalar 2 :=
  (CharP.charP_iff_prime_eq_zero (R := F8Scalar) (by decide : Nat.Prime 2)).2
    (by decide)

theorem card_eq : Fintype.card F8Scalar = 8 := by decide

theorem add_self_eq_zero : ∀ a : F8Scalar, a + a = 0 := by decide

def alpha : F8Scalar := ofNat 2

theorem alpha_sq : alpha ^ 2 = ofNat 4 := by decide

theorem alpha_cubed : alpha ^ 3 = alpha + 1 := by decide

theorem pow_eight : ∀ a : F8Scalar, a ^ 8 = a := by decide

def trace (a : F8Scalar) : F8Scalar := a + a ^ 2 + a ^ 4

def traceBit (a : F8Scalar) : Bool := trace a == 1

def bit (a : F8Scalar) (i : Fin 3) : Bool := a.code.val.testBit i.val

def binaryDot (a x : F8Scalar) : Bool :=
  Bool.xor (Bool.xor (a.bit 0 && x.bit 0) (a.bit 1 && x.bit 1))
    (a.bit 2 && x.bit 2)

/-- The trace-dual basis is (1, alpha^2, alpha). -/
def traceDual (a : F8Scalar) : F8Scalar :=
  ofNat ((if a.bit 0 then 1 else 0) +
    (if a.bit 1 then 4 else 0) + (if a.bit 2 then 2 else 0))

theorem trace_zero_or_one : ∀ a : F8Scalar, trace a = 0 ∨ trace a = 1 := by
  decide

theorem trace_low_bit : ∀ a : F8Scalar, traceBit a = a.bit 0 := by decide

theorem trace_add : ∀ a b : F8Scalar, trace (a + b) = trace a + trace b := by
  decide

theorem trace_square : ∀ a : F8Scalar, trace (a ^ 2) = trace a := by decide

theorem trace_duality : ∀ a x : F8Scalar,
    traceBit (traceDual a * x) = binaryDot a x := by decide

theorem frobenius_duality : ∀ a x : F8Scalar,
    traceBit (a * x ^ 2) = traceBit (a ^ 4 * x) := by decide

end F8Scalar

end Lemmata.RM59
