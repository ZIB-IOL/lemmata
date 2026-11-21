module

public import Mathlib.Data.List.Sort
public import Std.Data.HashSet.Basic

@[expose] public section

namespace Lemmata.SteinerSixSpectrum

abbrev Rows := List (List ℕ)

/-- A point permutation is stored as a sequence of differences of its images. -/
inductive Difference where
  | value (difference : ℤ)
  | repeat (distance count : ℕ)

/-- A small collection of six-point blocks and generators for their orbits. -/
structure OrbitRecord where
  order : ℕ
  maps : List (List Difference)
  starters : Rows

def expandPermutation (tokens : List Difference) : Array ℕ := Id.run do
  let mut diffs : Array ℤ := #[]
  for token in tokens do
    match token with
    | .value d => diffs := diffs.push d
    | .repeat distance count =>
      for _ in [0:count] do
        diffs := diffs.push (diffs[diffs.size - distance]?.getD 0)
  let mut images := #[]
  let mut value : ℤ := 0
  for d in diffs do
    value := value + d
    images := images.push value.toNat
  return images

/-- Breadth-first development of the starter blocks under the recorded permutations. -/
def expandOrbit (record : OrbitRecord) : Rows := Id.run do
  let maps := record.maps.map expandPermutation
  let mut blocks := record.starters.toArray
  let mut seen : Std.HashSet (List ℕ) := {}
  for row in record.starters do
    seen := seen.insert row
  for i in [0:record.order * (record.order - 1) / 30 + 1] do
    let some row := blocks[i]? | break
    for perm in maps do
      let image := (row.map (fun x => perm[x]?.getD 0)).mergeSort
      if !seen.contains image then
        seen := seen.insert image
        blocks := blocks.push image
  return blocks.toList

end Lemmata.SteinerSixSpectrum
