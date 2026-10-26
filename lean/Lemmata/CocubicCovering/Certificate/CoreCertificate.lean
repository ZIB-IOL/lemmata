module

public import Init
public import Lemmata.CocubicCovering.Certificate.PureDual
public meta import Lemmata.CocubicCovering.Certificate.PureDual

@[expose] public section

set_option Elab.async false

namespace Lemmata.CocubicCovering.Certificate.CoreCertificate

def xorRows : List Nat → Nat
  | [] => 0
  | row :: rest => row ^^^ xorRows rest

def composeRow {m : Nat} (mask : Nat) (columns : Fin m → Nat) : Nat :=
  xorRows ((List.finRange m).map fun i => if mask.testBit i.val then columns i else 0)

def checkSpan {c d : Nat} (source : Fin c → Nat) (target : Fin d → Nat)
    (coefficients : Fin c → Nat) : Bool :=
  (List.finRange c).all fun i => decide (composeRow (coefficients i) target = source i)

def listCheckSpan (source target coefficients : List Nat) : Bool :=
  checkSpan source.get target.get fun i => coefficients[i.val]?.getD 0

structure Root where
  assignment : Nat
  radical : List Nat
  required : Nat

structure State (r : Nat) where
  root : Fin r
  core : List Nat

structure Obstruction where
  core : List Nat
  selected : List Nat

structure Row where
  mask : Nat
  column : Nat
  value : Nat

def obstructionCheck (rows : Nat → Row) (obstruction : Obstruction) : Bool :=
  obstruction.selected.all (fun i => obstruction.core.contains (rows i).mask) &&
    decide (xorRows (obstruction.selected.map fun i => (rows i).value) = 2 ^ 126)

structure Edge (n l w : Nat) where
  target : Sum (Fin n) (Fin l)
  word : Option (Fin w)
  coefficients : List Nat

structure Branch (n l w : Nat) where
  fresh : List Nat
  inRadical : List Nat
  dual : List Nat
  children : Fin (2 ^ fresh.length - 1) → Edge n l w

inductive Rule (n l w t : Nat) where
  | branch (data : Branch n l w)
  | terminal (reference : Fin t) (word : Fin w) (coefficients : List Nat)

def targetCore {r n l : Nat} (states : Fin n → State r)
    (obstructions : Fin l → Obstruction) : Sum (Fin n) (Fin l) → List Nat
  | .inl i => (states i).core
  | .inr i => (obstructions i).core

def targetRoot {r n l : Nat} (states : Fin n → State r) (source : Fin r) :
    Sum (Fin n) (Fin l) → Fin r
  | .inl i => (states i).root
  | .inr _ => source

def edgeColumns {w c : Nat} (columns : Fin w → Fin 12 → Nat)
    (word : Option (Fin w)) (core : Fin c → Nat) : Fin c → Nat :=
  match word with
  | none => core
  | some word => fun i => composeRow (core i) (columns word)

def edgeCheck {r n l w : Nat} (states : Fin n → State r)
    (obstructions : Fin l → Obstruction) (columns : Fin w → Fin 12 → Nat)
    (guard : Fin w → Fin r → Fin r → Bool) (i : Fin n)
    {c : Nat} (core : Fin c → Nat) (edge : Edge n l w) : Bool :=
  (match edge.word with
    | none => decide ((states i).root = targetRoot states (states i).root edge.target)
    | some word => guard word (states i).root (targetRoot states (states i).root edge.target)) &&
  checkSpan (targetCore states obstructions edge.target).get
    (edgeColumns columns edge.word core) (fun j => edge.coefficients[j.val]?.getD 0) &&
  match edge.target with
  | .inl j => decide (j.val < i.val)
  | .inr _ => true

def nodeCheck {r n l w t : Nat} (roots : Fin r → Root) (states : Fin n → State r)
    (obstructions : Fin l → Obstruction) (terminals : Fin t → State r)
    (columns : Fin w → Fin 12 → Nat) (guard : Fin w → Fin r → Fin r → Bool)
    (i : Fin n) : Rule n l w t → Bool
  | .terminal reference word coefficients =>
      guard word (states i).root (terminals reference).root &&
        checkSpan (terminals reference).core.get
          (edgeColumns columns (some word) (states i).core.get)
          (fun j => coefficients[j.val]?.getD 0)
  | .branch data =>
      ((listCheckSpan data.fresh (roots (states i).root).radical data.inRadical &&
        PureDual.listCheckCombinedDual 12 (states i).core data.fresh data.dual) &&
        decide ((roots (states i).root).radical.length <
          data.fresh.length + (roots (states i).root).required)) &&
      (List.finRange (2 ^ data.fresh.length - 1)).all fun j =>
        edgeCheck states obstructions columns guard i
          (PureDual.appendColumns (states i).core.get
            (fun _ : Fin 1 => composeRow (j.val + 1) data.fresh.get)) (data.children j)

end Lemmata.CocubicCovering.Certificate.CoreCertificate
