module

public import Lemmata.SteinerSixSpectrum.RecipeTable
public import Lemmata.SteinerSixSpectrum.Certificates
public import Lemmata.SteinerSixSpectrum.UpperOrders
public meta import Lemmata.SteinerSixSpectrum.RecipeTable

@[expose] public section

namespace Lemmata.SteinerSixSpectrum

def runRecipe (design : BlockSource) (n : ℕ) : Recipe → Rows
  | .product d m e delete => productRows design d m e delete
  | .groups g u m e =>
    let (rows, groups) := groupRows (List.replicate u g)
    inflateRows design rows groups m e
  | .hole h =>
    partialRows design n h ++ (design h).map (List.map (n-h + ·))
  | .six v h => sixGroups design v h
  | .fibres s t h => fibreRows design s t h
  | .sharedIncomplete v h a mode t m tail =>
    sharedIncomplete design v h a mode t m tail

/-- Develop the seed and fill its hole recursively, if it has one. -/
def completeOrbit (fill : BlockSource) (n : ℕ) : Option Rows :=
  (completeOrbits.find? (fun item => item.1.1 == n)).map fun ((_, h), record) =>
    expandOrbit record ++ if h = 0 then [] else
      (fill h).map (List.map (fun x => n - h + x))

/-- Try the three uniform masters of the atlas: a complete design, a design
with a point deleted, or a group-divisible seed with equal group sizes. -/
def findInflation (n : ℕ) : Option Recipe := Id.run do
  for e in [1,6,0] do
    for m in [1:(n-e)/6+1] do
      if (n-e) % m != 0 then continue
      let d := (n-e)/m
      if 5 ≤ m && decide (constructible d ∧ constructible (m+e)) && !(td6 m).isEmpty then
        return some (.product d m e false)
      if 5 ≤ m && d % 5 == 0 && decide (constructible (d+1) ∧ constructible (5*m+e)) &&
          !(td6 m).isEmpty then
        return some (.product (d+1) m e true)
      for (sizes, _) in groupOrbits do
        let g := sizes.headD 0
        if g*sizes.length == d && decide (constructible (g*m+e)) && !(td6 m).isEmpty then
          return some (.groups g sizes.length m e)
  return none

def finiteDesign : ℕ → BlockSource
  | 0, _ => []
  | fuel+1, n =>
    let prev := finiteDesign fuel
    match completeOrbit prev n with
    | some rows => rows
    | none =>
      let recipe := ((recipes.find? (fun entry => entry.1 == n)).map Prod.snd).orElse
        (fun _ => findInflation n)
      recipe.elim [] (runRecipe prev n)

def verifyOrder (n : ℕ) : Bool :=
  checkComplete n ((finiteDesign n n).map (fun row => row.mergeSort))

end Lemmata.SteinerSixSpectrum
