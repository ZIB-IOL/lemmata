module

public import Lemmata.Centroid.Proof.Symmetric.Coordinates
public import Lemmata.Centroid.Proof.Linear.Leading
public import Lemmata.Centroid.Proof.Combinatorics.Triangles
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Data.Finsupp.MonomialOrder

@[expose] public section

namespace Lemmata.Centroid.Symmetric

open Classical

noncomputable section

variable {F I : Type*} [Field F] [Fintype I] [DecidableEq I]

def monomialIndex (m : MonomialOrder I) {d : ℕ} (s : Sym I d) : m.syn :=
  m.toSyn s.val.toFinsupp

omit [Fintype I] in theorem monomialIndex_injective (m : MonomialOrder I) (d : ℕ) :
    Function.Injective (@monomialIndex I _ m d) := by
  intro s t h
  apply Sym.ext
  exact Multiset.toFinsupp.injective (m.toSyn.injective h)

abbrev coefficientOrder (m : MonomialOrder I) (d : ℕ) : LinearOrder (Sym I d) :=
  LinearOrder.lift' (monomialIndex m) (monomialIndex_injective m d)

omit [Fintype I] in theorem monomialIndex_cons (m : MonomialOrder I) {d : ℕ} (i : I) (s : Sym I d) :
    monomialIndex m (Sym.cons i s) = m.toSyn (Finsupp.single i 1) + monomialIndex m s := by
  change m.toSyn ((i ::ₘ s.val).toFinsupp) = _
  change m.toSyn (({i} : Multiset I) + s.val).toFinsupp = _
  rw [map_add, Multiset.toFinsupp_singleton, map_add]
  rfl

omit [Fintype I] in theorem cons_strictMono (m : MonomialOrder I) (d : ℕ) (i : I) :
    @StrictMono (Sym I d) (Sym I (d + 1)) (coefficientOrder m d).toPreorder
      (coefficientOrder m (d + 1)).toPreorder (Sym.cons i) := by
  intro s t h
  change monomialIndex m s < monomialIndex m t at h
  change monomialIndex m (Sym.cons i s) < monomialIndex m (Sym.cons i t)
  rw [monomialIndex_cons, monomialIndex_cons]
  simpa only [add_comm] using add_lt_add_left h (m.toSyn (Finsupp.single i 1))

def leadingCubics (m : MonomialOrder I) (S : Submodule F (Coefficients F I 3)) : Finset (Sym I 3) :=
  let _ := coefficientOrder m 3
  Linear.leadingPositions S

def leadingQuadrics (m : MonomialOrder I) (S : Submodule F (Coefficients F I 3)) : Finset (Sym I 2) :=
  let _ := coefficientOrder m 2
  Linear.leadingPositions (quadraticShadow S)

theorem card_leadingCubics (m : MonomialOrder I) (S : Submodule F (Coefficients F I 3)) :
    (leadingCubics m S).card = Module.finrank F S := by
  let _ := coefficientOrder m 3
  exact Linear.card_leadingPositions S

theorem card_leadingQuadrics (m : MonomialOrder I) (S : Submodule F (Coefficients F I 3)) :
    (leadingQuadrics m S).card = Module.finrank F (quadraticShadow S) := by
  let _ := coefficientOrder m 2
  exact Linear.card_leadingPositions (quadraticShadow S)

theorem leading_divisor (m : MonomialOrder I) (S : Submodule F (Coefficients F I 3))
    (i : I) (q : Sym I 2) (h : Sym.cons i q ∈ leadingCubics m S) :
    q ∈ leadingQuadrics m S := by
  let _ := coefficientOrder m 2
  let _ := coefficientOrder m 3
  have hlead : Linear.IsLeading S (Sym.cons i q) := (Linear.mem_leadingPositions _ _).1 h
  have hmap := hlead.pullback (cons_strictMono m 2 i)
  apply (Linear.mem_leadingPositions _ _).2
  apply hmap.mono
  rintro v ⟨c, hc, rfl⟩
  exact contractCoordinate_mem_quadraticShadow S i hc

end

end Lemmata.Centroid.Symmetric
