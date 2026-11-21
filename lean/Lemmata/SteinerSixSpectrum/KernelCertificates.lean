module

public import Lemmata.SteinerSixSpectrum.TaggedIncidence
public import Lemmata.SteinerSixSpectrum.FiniteOrders
public meta import Lemmata.SteinerSixSpectrum.TaggedIncidence
public meta import Lemmata.SteinerSixSpectrum.FiniteOrders
public import Mathlib.Tactic.Eval
public meta import Lean

public section

namespace Lemmata.SteinerSixSpectrum

def Supplies (orders : List Nat) : Prop :=
  ∀ n ∈ orders, Nonempty (SteinerSystem (Fin n))

theorem suppliesNil : Supplies [] := by simp [Supplies]

theorem suppliesCons {n : Nat} {ns : List Nat} (h : Nonempty (SteinerSystem (Fin n)))
    (rest : Supplies ns) : Supplies (n::ns) := by
  intro m hm
  rcases List.mem_cons.mp hm with rfl | hm
  · exact h
  · exact rest m hm

theorem suppliesAppend {a b : List Nat} (ha : Supplies a) (hb : Supplies b) :
    Supplies (a++b) := by
  intro n hn
  exact (List.mem_append.mp hn).elim (ha n) (hb n)

open Lean in
/-- Elaborate the orbit and filling recipes to literal incidence masks, then
prove their column sizes and intersections in the kernel. Separate proofs for
successive rows bound the memory of both the build and independent replay. -/
macro "certify_orders " group:ident " [" ns:num,* "]" : command => do
  let mut commands := #[]
  let mut witnesses := #[]
  let groupOrders := mkIdent (group.getId.appendAfter "Orders")
  let orders := ns.getElems
  for n in orders do
    let value := n.getNat
    let masks := mkIdent (group.getId.appendAfter s!"Masks{value}")
    let proof := mkIdent (group.getId.appendAfter s!"Design{value}")
    let k := max 1 (min value (12000/value))
    let step := Syntax.mkNumLit (toString k)
    let mut pairProof ← `(term| BitIncidence.suffixEnd (by decide +kernel))
    for j in (List.range ((value+k-1)/k)).reverse do
      let start := Syntax.mkNumLit (toString (j*k))
      pairProof ← `(term| BitIncidence.suffixStep (xs := $masks) (i := $start) (k := $step)
        (by decide +kernel) $pairProof)
    commands := commands.push (← `(command|
      private noncomputable def $masks : List Nat :=
        eval% BitIncidence.taggedMasks $n (finiteDesign $n $n)))
    commands := commands.push (← `(command|
      private theorem $proof : Nonempty (SteinerSystem (Fin $n)) :=
        ⟨BitIncidence.completeTagged $masks (by decide +kernel) (by decide +kernel) $pairProof⟩))
    witnesses := witnesses.push proof
  let mut supplied ← `(term| suppliesNil)
  for proof in witnesses.reverse do
    supplied ← `(term| suppliesCons $proof $supplied)
  commands := commands.push (← `(command| @[expose] def $groupOrders : List Nat := [$orders,*]))
  commands := commands.push (← `(command| theorem $group : Supplies $groupOrders := $supplied))
  return ⟨mkNullNode (commands.map TSyntax.raw)⟩

end Lemmata.SteinerSixSpectrum
