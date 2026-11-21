module

public import Lemmata.SteinerSixSpectrum.TemplateSeeds
public import Lemmata.SteinerSixSpectrum.BitIncidence
public import Lemmata.SteinerSixSpectrum.Wilson
public meta import Lemmata.SteinerSixSpectrum.TemplateSeeds
public meta import Lemmata.SteinerSixSpectrum.BitIncidence
import Mathlib.Tactic.Eval

public section

namespace Lemmata.SteinerSixSpectrum

private def unitProduct (X : Type*) : Unit × X ≃ X where
  toFun := Prod.snd
  invFun x := ((),x)
  left_inv := by rintro ⟨⟨⟩,x⟩; rfl
  right_inv _ := rfl

private def rowEquiv (k d : ℕ) : (Σ i : Columns k, RowCell d i) ≃ Fin (k*5+d) :=
  (Equiv.sumSigmaDistrib (RowCell d)).trans
    ((Equiv.sumCongr ((Equiv.sigmaEquivProd (Fin k) (Fin 5)).trans finProdFinEquiv)
      ((Equiv.sigmaEquivProd Unit (Fin d)).trans (unitProduct _))).trans finSumFinEquiv)

private def columnNumber {k : ℕ} : Columns k → ℕ
  | .inl i => i.val
  | .inr _ => k

private theorem columnNumber_injective (k : ℕ) : Function.Injective (columnNumber (k := k)) := by
  rintro (i | ⟨⟩) (j | ⟨⟩) h
  · exact congrArg Sum.inl (Fin.ext h)
  · exact (Nat.ne_of_lt i.isLt h).elim
  · exact (Nat.ne_of_lt j.isLt h.symm).elim
  · rfl

private theorem rowEquiv_column {k d : ℕ} (x : Σ i : Columns k, RowCell d i) :
    min ((rowEquiv k d x).val / 5) k = columnNumber x.1 := by
  rcases x with ⟨i | ⟨⟩, x⟩
  · change min ((x.val + 5*i.val) / 5) k = i.val
    have a := i.isLt
    have b := x.isLt
    omega
  · change min ((k*5+x.val) / 5) k = k
    omega

/-- Blocks through the deleted point give consecutive groups of five. In an
incomplete design the rest of the hole is the final group. -/
@[expose] def templateCertificate (seed : OrbitRecord) (hole : ℕ) : Rows :=
  let pivot := if hole = 0 then 0 else seed.order - 1
  let (through, off) := (expandOrbit seed).partition (·.contains pivot)
  let tail := (List.range pivot).drop (seed.order - hole)
  let labels := (through.flatMap (List.filter (· != pivot))) ++ tail
  off.map fun b => (b.map labels.idxOf).mergeSort

@[expose] def interGroup (k x y : ℕ) : Bool :=
  decide (min (x/5) k ≠ min (y/5) k)

private def rowTemplateOfMasks {k d : ℕ} (xs : List Nat) (size : xs.length = k*5+d)
    (six : BitIncidence.atLeast xs 0 = BitIncidence.atLeast xs 5)
    (seven : BitIncidence.atLeast xs 6 = 0)
    (cert : BitIncidence.pairs (interGroup k) 0 xs = true) :
    RowTemplate k d := by
  have sym : ∀ x y, interGroup k x y = interGroup k y x := by
    intro x y
    simp [interGroup, ne_comm]
  let design : PairDesign (Fin (k*5+d)) (fun x y => interGroup k x.val y.val = true) :=
    size ▸ BitIncidence.ofMasks xs (interGroup k) sym six seven cert
  refine (design.relabel (rowEquiv k d).symm).congr ?_
  intro x y
  change interGroup k (rowEquiv k d x).val (rowEquiv k d y).val = true ↔ x.1 ≠ y.1
  rw [interGroup, rowEquiv_column, rowEquiv_column]
  simpa using (columnNumber_injective k).ne_iff (x := x.1) (y := y.1)

private def mask13light : List Nat := eval% BitIncidence.masksOfRows 65 (templateCertificate design66 0)
private def mask13heavy : List Nat := eval% BitIncidence.masksOfRows 80 (templateCertificate incomplete81 16)
private def mask17light : List Nat := eval% BitIncidence.masksOfRows 90 (templateCertificate design91 0)
private def mask17heavy : List Nat := eval% BitIncidence.masksOfRows 105 (templateCertificate incomplete106 21)

set_option maxHeartbeats 0
set_option maxRecDepth 100000 in
def template13light : RowTemplate 13 0 :=
  rowTemplateOfMasks mask13light rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)

def template13heavy : RowTemplate 13 15 :=
  rowTemplateOfMasks mask13heavy rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)

def template17light : RowTemplate 17 5 :=
  rowTemplateOfMasks mask17light rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)

def template17heavy : RowTemplate 17 20 :=
  rowTemplateOfMasks mask17heavy rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Lemmata.SteinerSixSpectrum
