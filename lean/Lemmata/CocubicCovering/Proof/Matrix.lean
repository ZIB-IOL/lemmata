module

public import Lemmata.CocubicCovering.Proof.Certificate
public meta import Lemmata.CocubicCovering.Proof.Certificate
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Finset.SDiff

@[expose] public section

set_option Elab.async false

namespace Lemmata.CocubicCovering.CoveringMatrix

open CoveringCertificate

def cubic : List Monomial :=
  [{0, 3, 6}, {0, 4, 7}, {0, 5, 8}, {1, 3, 7}, {1, 4, 6}, {1, 4, 8},
   {1, 5, 6}, {2, 3, 8}, {2, 4, 6}, {2, 5, 7}, {2, 5, 8}]

def ambient : Monomial := Finset.range 9

/-- A parameter is indexed by the binary support mask of its degree-five monomial. -/
def parameterIndex (support : Monomial) : ℕ := support.sum fun v => 2 ^ v

def pairEquation (left right : Monomial) : Polynomial :=
  let support := left ∪ right
  let constant := cubic.foldr (fun term rest =>
    if term ⊆ support then toggle ∅ rest else rest) []
  let parameter := if support.card = 4 then [{parameterIndex (ambient \ support)}] else []
  add constant parameter

def equation (left right : Polynomial) : Polynomial :=
  left.foldr (fun first rest => add
    (right.foldr (fun second tail => add (pairEquation first second) tail) []) rest) []

def contraction (quadratic : Polynomial) : Polynomial :=
  quadratic.foldr (fun pair rest =>
    cubic.foldr (fun term tail => if pair ⊆ term then toggle (term \ pair) tail else tail) rest) []

def multiplierBasis : List Polynomial :=
  [
    [{0, 1}],
    [{0, 2}],
    [{1, 2}],
    [{0, 4}, {1, 3}],
    [{0, 3}, {0, 5}, {1, 4}],
    [{0, 3}, {1, 5}],
    [{0, 7}, {0, 8}, {1, 6}],
    [{0, 6}, {1, 7}],
    [{0, 7}, {1, 8}],
    [{0, 5}, {2, 3}],
    [{0, 3}, {2, 4}],
    [{0, 4}, {0, 5}, {2, 5}],
    [{0, 7}, {2, 6}],
    [{0, 8}, {2, 7}],
    [{0, 6}, {0, 8}, {2, 8}],
    [{3, 4}],
    [{3, 5}],
    [{4, 5}],
    [{3, 7}, {3, 8}, {4, 6}],
    [{3, 6}, {4, 7}],
    [{3, 7}, {4, 8}],
    [{3, 7}, {5, 6}],
    [{3, 8}, {5, 7}],
    [{3, 6}, {3, 8}, {5, 8}]
  ]

def localIndices : List ℕ := [0, 1, 2, 3, 4, 5, 9, 10, 11, 15, 16, 17]

def localBasis : List Polynomial :=
  localIndices.map fun i => multiplierBasis[i]?.getD []

def coordinatePairs : List Monomial :=
  [{0, 1}, {0, 2}, {1, 2}, {1, 3}, {1, 4}, {1, 5}, {1, 6}, {1, 7}, {1, 8}, {2, 3}, {2, 4}, {2, 5}, {2, 6}, {2, 7}, {2, 8}, {3, 4}, {3, 5}, {4, 5}, {4, 6}, {4, 7}, {4, 8}, {5, 6}, {5, 7}, {5, 8}]

def multiplier (i : Fin 24) : Polynomial := multiplierBasis[i.val]?.getD []

def localMultiplier (i : Fin 12) : Polynomial := localBasis[i.val]?.getD []

def localInclusion (i : Fin 12) : Fin 24 := Fin.ofNat 24 (localIndices[i.val]?.getD 0)

def matrix (assignment : ℕ → Bool) (i j : Fin 24) : Bool :=
  eval assignment (equation (multiplier i) (multiplier j))

theorem multiplierBasis_length : multiplierBasis.length = 24 := by decide

theorem localBasis_length : localBasis.length = 12 := by decide

theorem multiplier_contractions :
    multiplierBasis.all (fun q => decide (contraction q = [])) = true := by decide

theorem multiplier_supports :
    multiplierBasis.all (fun q => q.all (fun pair =>
      decide (pair.card = 2 ∧ pair ⊆ ambient ∧ ¬Disjoint pair (Finset.range 6)))) = true := by decide

theorem multiplier_nodup :
    multiplierBasis.all (fun q => decide q.Nodup) = true := by decide

theorem local_contractions :
    localBasis.all (fun q => decide (contraction q = [])) = true := by decide

/-- Each multiplier has a coordinate occurring in no other basis vector. -/
theorem multiplier_coordinates :
    ∀ i j : Fin 24,
      ((coordinatePairs[j.val]?.getD ∅) ∈ multiplier i) ↔ i = j := by decide

theorem local_span :
    ∀ i : Fin 12, localMultiplier i = multiplier (localInclusion i) := by decide

end Lemmata.CocubicCovering.CoveringMatrix
