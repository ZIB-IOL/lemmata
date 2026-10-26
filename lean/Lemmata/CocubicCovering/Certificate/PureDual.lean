module

public import Init.Data.Nat.Bitwise.Basic
public import Init.Data.Fin.Lemmas

@[expose] public section

set_option Elab.async false

namespace Lemmata.CocubicCovering.Certificate.PureDual

def parity : Nat → Nat → Bool
  | 0, _ => false
  | n + 1, mask => Bool.xor (parity n mask) (mask.testBit n)

def checkDual (n : Nat) {k : Nat} (columns rows : Fin k → Nat) : Bool :=
  decide (∀ i j : Fin k, parity n (rows j &&& columns i) = decide (i = j))

def listCheckDual (n : Nat) (columns rows : List Nat) : Bool :=
  checkDual n columns.get fun i => rows[i.val]?.getD 0

def appendColumns {c d : Nat} (core : Fin c → Nat) (fresh : Fin d → Nat) :
    Fin (c + d) → Nat :=
  Fin.addCases core fresh

def listCheckCombinedDual (n : Nat) (core fresh rows : List Nat) : Bool :=
  checkDual n (appendColumns core.get fresh.get) fun i => rows[i.val]?.getD 0

end Lemmata.CocubicCovering.Certificate.PureDual
