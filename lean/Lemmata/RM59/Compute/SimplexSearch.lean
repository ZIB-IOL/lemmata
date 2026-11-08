module

public import Std
public import Init.Data.Vector.Lemmas
public import Init.Data.Vector.OfFn

@[expose] public section

namespace Lemmata.RM59

def packedXor (x y : Fin 512) : Fin 512 :=
  ⟨(Nat.xor x.val y.val) % 512, Nat.mod_lt _ (by decide)⟩

end Lemmata.RM59

namespace Lemmata.RM59.BinarySpan9

structure State where
  rows : Vector (Fin 512) 9

def empty : State := ⟨Vector.replicate 9 0⟩

def indices : List (Fin 9) := [8, 7, 6, 5, 4, 3, 2, 1, 0]

def step (state : State) (value : (Fin 512)) (i : Fin 9) : (Fin 512) :=
  if value.val.testBit i.val then packedXor value (state.rows.get i) else value

def reduce (state : State) (value : (Fin 512)) : (Fin 512) :=
  indices.foldl (step state) value

def pivot (value : (Fin 512)) : Fin 9 :=
  ⟨value.val.log2 % 9, Nat.mod_lt _ (by decide)⟩

def insert (state : State) (value : (Fin 512)) : State :=
  let residual := reduce state value
  if residual = 0 then state else
    ⟨state.rows.set (pivot residual).val residual (pivot residual).isLt⟩

end Lemmata.RM59.BinarySpan9

namespace Lemmata.RM59.SimplexSearch

def choices : List (Fin 512) → List ((Fin 512) × List (Fin 512))
  | [] => []
  | x :: xs => (x, xs) :: choices xs

def nextCandidates (allowed : (Fin 512 -> Fin 512 -> Bool)) (chosen : List (Fin 512))
    (basis : BinarySpan9.State) (x : (Fin 512)) (rest : List (Fin 512)) : List (Fin 512) :=
  rest.filter fun y => (BinarySpan9.reduce basis y != 0) &&
    chosen.all (fun z => allowed (packedXor z x) (packedXor z y))

def existsExtension (allowed : (Fin 512 -> Fin 512 -> Bool)) :
    Nat → List (Fin 512) → List (Fin 512) → BinarySpan9.State → Bool
  | 0, _, _, _ => true
  | remaining + 1, chosen, candidates, basis =>
    if candidates.length < remaining + 1 then false else
      (choices candidates).any fun branch =>
        let x := branch.1
        if BinarySpan9.reduce basis x = 0 then false else
          let next := BinarySpan9.insert basis x
          existsExtension allowed remaining (chosen ++ [x])
            (nextCandidates allowed chosen next x branch.2) next

def rootCandidates (allowed : (Fin 512 -> Fin 512 -> Bool)) : List (Fin 512) :=
  (List.finRange 512).filter fun v => (v != 0) && (List.finRange 512).any (allowed v)

def noSimplex (allowed : (Fin 512 -> Fin 512 -> Bool)) (dimension : Nat) : Bool :=
  !existsExtension allowed dimension [0] (rootCandidates allowed) BinarySpan9.empty

end Lemmata.RM59.SimplexSearch

namespace Lemmata.RM59.PlaneFinder

def lookup (table : Array Bool) (a b : Fin 512) : Bool :=
  table[512 * a.val + b.val]?.getD false

end Lemmata.RM59.PlaneFinder
