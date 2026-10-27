module

public import Lemmata.CocubicCovering.Proof.Orbit
public meta import Lemmata.CocubicCovering.Proof.Orbit
public import Lemmata.CocubicCovering.Proof.Affine
public meta import Lemmata.CocubicCovering.Proof.Affine

@[expose] public section

namespace Lemmata.CocubicCovering.CoveringLocalForest

open CoveringOrbit CoveringAffine

def columnData : Array (Array Nat) := #[
  #[5,1,2,16,40,8,128,320,64,512,2048,5120,1024,8192,16384],
  #[512,8192,16384,8,64,1024,16,128,2048,1,32,256,4096,2,4],
  #[1,2,4,8,17,34,65,128,260,593,1026,2052,4096,9250,18692],
  #[4,5,3,128,384,448,2176,6528,7616,16384,2192,6576,7672,16896,8704]
]

def columns (g : Fin 4) (i : Fin 15) : Nat :=
  (columnData[g.val]?.getD #[])[i.val]?.getD 0

def step (g : Fin 4) (i : Fin 32768) : Fin 32768 :=
  Fin.ofNat 32768 (composeRow i.val (columns g))

def roots : List (Fin 32768) :=
  [0,1,8,12,80,81,88,89,104,522,1184,1188,1192,1193,1400,1550,1573,1580]

structure SearchResult where
  parent : Array Nat
  generator : Array Nat
  distance : Array Nat

def generate : SearchResult := Id.run do
  let mut incoming : Array (List (Nat × Nat)) := Array.replicate 32768 []
  for source in [:32768] do
    for generator in [:4] do
      let target := (step (Fin.ofNat 4 generator) (Fin.ofNat 32768 source)).val
      incoming := incoming.set! target ((source, generator) :: (incoming[target]?.getD []))
  let mut result : SearchResult :=
    ⟨Array.replicate 32768 0, Array.replicate 32768 0, Array.replicate 32768 32768⟩
  let mut queue : Array Nat := #[]
  for root in roots do
    result := { result with distance := result.distance.set! root.val 0 }
    queue := queue.push root.val
  for cursor in [:32768] do
    if let some target := queue[cursor]? then
      for edge in incoming[target]?.getD [] do
        let (source, generator) := edge
        if result.distance[source]?.getD 32768 == 32768 then
          result := {
            parent := result.parent.set! source target
            generator := result.generator.set! source generator
            distance := result.distance.set! source (result.distance[target]?.getD 32768 + 1)
          }
          queue := queue.push source
  return result

def forest : Forest 32768 4 where
  roots := roots
  parent i := Fin.ofNat 32768 (generate.parent[i.val]?.getD 0)
  generator i := Fin.ofNat 4 (generate.generator[i.val]?.getD 0)
  distance i := generate.distance[i.val]?.getD 32768

theorem all_checked :
    (List.finRange 32768).all (checkAt forest step) = true := by
  native_decide

theorem checked (i : Fin 32768) : checkAt forest step i = true :=
  (List.all_eq_true.mp all_checked) i (List.mem_finRange _)

end Lemmata.CocubicCovering.CoveringLocalForest
