module

public import Lemmata.BellFollowup.Positive.Finite

@[expose] public section

namespace Lemmata.BellFollowup.Positive

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Ordered witnesses of the positive and negative coordinate axes. -/
def witnesses5 : List (List Int × List Int × List Int) :=
  [([1,1,1,1,1], [1,1,1,1,1], [-1,-1,-1,-1,1]),
    ([-1,-1,-1,-1,-1], [1,1,1,1,1], [-1,-1,-1,-1,1]),
    ([1,1,-1,1,1], [1,1,-1,1,1], [1,-1,1,1,-1]),
    ([-1,-1,1,-1,-1], [1,1,-1,1,1], [1,-1,1,1,-1]),
    ([1,-1,1,-1,1], [1,-1,1,-1,1], [1,-1,1,-1,1]),
    ([-1,1,-1,1,-1], [1,-1,1,-1,1], [1,-1,1,-1,1])]

-- Separating the table into independent kernel reductions keeps memory bounded.
set_option Elab.async false
private def pairTable : List (List Int) := [[-5,-3,-1,1,3],
  [-5,1,-1,1,-1],
  [-5,1,3,-3,-1],
  [-5,5,-5,5,-5],
  [-3,-5,-3,-1,1],
  [-3,-1,-3,-1,1],
  [-3,-1,1,-1,-3],
  [-3,-1,1,-1,1],
  [-3,-1,1,3,1],
  [-3,-1,1,3,5],
  [-3,-1,5,-1,-3],
  [-3,3,-3,3,-3],
  [-3,3,1,-5,1],
  [-3,3,1,-1,1],
  [-1,-3,-5,-3,-1],
  [-1,-3,-1,-3,-1],
  [-1,-3,-1,1,-1],
  [-1,-3,-1,1,3],
  [-1,-3,3,1,-5],
  [-1,-3,3,1,-1],
  [-1,1,-5,1,-1],
  [-1,1,-1,-3,-1],
  [-1,1,-1,-3,3],
  [-1,1,-1,1,-5],
  [-1,1,-1,1,-1],
  [-1,1,-1,1,3],
  [-1,1,-1,5,-1],
  [-1,1,3,-3,-1],
  [-1,1,3,1,-1],
  [-1,1,3,1,3],
  [-1,1,3,5,3],
  [-1,5,-1,-3,3],
  [-1,5,-1,1,-1],
  [1,-5,1,-1,1],
  [1,-5,1,3,-3],
  [1,-1,-3,-5,-3],
  [1,-1,-3,-1,-3],
  [1,-1,-3,-1,1],
  [1,-1,-3,3,1],
  [1,-1,1,-5,1],
  [1,-1,1,-1,-3],
  [1,-1,1,-1,1],
  [1,-1,1,-1,5],
  [1,-1,1,3,-3],
  [1,-1,1,3,1],
  [1,-1,5,-1,1],
  [1,3,-3,-1,1],
  [1,3,-3,-1,5],
  [1,3,1,-1,-3],
  [1,3,1,-1,1],
  [1,3,1,3,1],
  [1,3,5,3,1],
  [3,-3,-1,1,-1],
  [3,-3,-1,5,-1],
  [3,-3,3,-3,3],
  [3,1,-5,1,3],
  [3,1,-1,-3,-5],
  [3,1,-1,-3,-1],
  [3,1,-1,1,-1],
  [3,1,-1,1,3],
  [3,1,3,1,-1],
  [3,5,3,1,-1],
  [5,-5,5,-5,5],
  [5,-1,-3,3,1],
  [5,-1,1,-1,1],
  [5,3,1,-1,-3]]
private def legalPairRow (a : List Int) : Bool :=
  (signRows 5).all fun b => pairTable.contains (ncMul 5 a b)
private def goodPair (p : List Int) : Bool :=
  (signRows 5).all fun c => decide (gauge inv5 (evenCoords 5 (ncMul 5 p c)) ≤ 3200)
private theorem legalPairRow0 : legalPairRow [1,1,1,1,1] = true := by rfl
private theorem legalPairRow1 : legalPairRow [1,1,1,1,-1] = true := by rfl
private theorem legalPairRow2 : legalPairRow [1,1,1,-1,1] = true := by rfl
private theorem legalPairRow3 : legalPairRow [1,1,1,-1,-1] = true := by rfl
private theorem legalPairRow4 : legalPairRow [1,1,-1,1,1] = true := by rfl
private theorem legalPairRow5 : legalPairRow [1,1,-1,1,-1] = true := by rfl
private theorem legalPairRow6 : legalPairRow [1,1,-1,-1,1] = true := by rfl
private theorem legalPairRow7 : legalPairRow [1,1,-1,-1,-1] = true := by rfl
private theorem legalPairRow8 : legalPairRow [1,-1,1,1,1] = true := by rfl
private theorem legalPairRow9 : legalPairRow [1,-1,1,1,-1] = true := by rfl
private theorem legalPairRow10 : legalPairRow [1,-1,1,-1,1] = true := by rfl
private theorem legalPairRow11 : legalPairRow [1,-1,1,-1,-1] = true := by rfl
private theorem legalPairRow12 : legalPairRow [1,-1,-1,1,1] = true := by rfl
private theorem legalPairRow13 : legalPairRow [1,-1,-1,1,-1] = true := by rfl
private theorem legalPairRow14 : legalPairRow [1,-1,-1,-1,1] = true := by rfl
private theorem legalPairRow15 : legalPairRow [1,-1,-1,-1,-1] = true := by rfl
private theorem legalPairRow16 : legalPairRow [-1,1,1,1,1] = true := by rfl
private theorem legalPairRow17 : legalPairRow [-1,1,1,1,-1] = true := by rfl
private theorem legalPairRow18 : legalPairRow [-1,1,1,-1,1] = true := by rfl
private theorem legalPairRow19 : legalPairRow [-1,1,1,-1,-1] = true := by rfl
private theorem legalPairRow20 : legalPairRow [-1,1,-1,1,1] = true := by rfl
private theorem legalPairRow21 : legalPairRow [-1,1,-1,1,-1] = true := by rfl
private theorem legalPairRow22 : legalPairRow [-1,1,-1,-1,1] = true := by rfl
private theorem legalPairRow23 : legalPairRow [-1,1,-1,-1,-1] = true := by rfl
private theorem legalPairRow24 : legalPairRow [-1,-1,1,1,1] = true := by rfl
private theorem legalPairRow25 : legalPairRow [-1,-1,1,1,-1] = true := by rfl
private theorem legalPairRow26 : legalPairRow [-1,-1,1,-1,1] = true := by rfl
private theorem legalPairRow27 : legalPairRow [-1,-1,1,-1,-1] = true := by rfl
private theorem legalPairRow28 : legalPairRow [-1,-1,-1,1,1] = true := by rfl
private theorem legalPairRow29 : legalPairRow [-1,-1,-1,1,-1] = true := by rfl
private theorem legalPairRow30 : legalPairRow [-1,-1,-1,-1,1] = true := by rfl
private theorem legalPairRow31 : legalPairRow [-1,-1,-1,-1,-1] = true := by rfl
private theorem pairCoverage : (signRows 5).all legalPairRow = true := by
  change (List.all [[1,1,1,1,1], [1,1,1,1,-1], [1,1,1,-1,1], [1,1,1,-1,-1], [1,1,-1,1,1], [1,1,-1,1,-1], [1,1,-1,-1,1], [1,1,-1,-1,-1], [1,-1,1,1,1], [1,-1,1,1,-1], [1,-1,1,-1,1], [1,-1,1,-1,-1], [1,-1,-1,1,1], [1,-1,-1,1,-1], [1,-1,-1,-1,1], [1,-1,-1,-1,-1], [-1,1,1,1,1], [-1,1,1,1,-1], [-1,1,1,-1,1], [-1,1,1,-1,-1], [-1,1,-1,1,1], [-1,1,-1,1,-1], [-1,1,-1,-1,1], [-1,1,-1,-1,-1], [-1,-1,1,1,1], [-1,-1,1,1,-1], [-1,-1,1,-1,1], [-1,-1,1,-1,-1], [-1,-1,-1,1,1], [-1,-1,-1,1,-1], [-1,-1,-1,-1,1], [-1,-1,-1,-1,-1]] legalPairRow) = true
  simp only [List.all_cons, List.all_nil, legalPairRow0, legalPairRow1, legalPairRow2, legalPairRow3, legalPairRow4, legalPairRow5, legalPairRow6, legalPairRow7, legalPairRow8, legalPairRow9, legalPairRow10, legalPairRow11, legalPairRow12, legalPairRow13, legalPairRow14, legalPairRow15, legalPairRow16, legalPairRow17, legalPairRow18, legalPairRow19, legalPairRow20, legalPairRow21, legalPairRow22, legalPairRow23, legalPairRow24, legalPairRow25, legalPairRow26, legalPairRow27, legalPairRow28, legalPairRow29, legalPairRow30, legalPairRow31, Bool.and_self]
private theorem goodPair0 : goodPair [-5,-3,-1,1,3] = true := by rfl
private theorem goodPair1 : goodPair [-5,1,-1,1,-1] = true := by rfl
private theorem goodPair2 : goodPair [-5,1,3,-3,-1] = true := by rfl
private theorem goodPair3 : goodPair [-5,5,-5,5,-5] = true := by rfl
private theorem goodPair4 : goodPair [-3,-5,-3,-1,1] = true := by rfl
private theorem goodPair5 : goodPair [-3,-1,-3,-1,1] = true := by rfl
private theorem goodPair6 : goodPair [-3,-1,1,-1,-3] = true := by rfl
private theorem goodPair7 : goodPair [-3,-1,1,-1,1] = true := by rfl
private theorem goodPair8 : goodPair [-3,-1,1,3,1] = true := by rfl
private theorem goodPair9 : goodPair [-3,-1,1,3,5] = true := by rfl
private theorem goodPair10 : goodPair [-3,-1,5,-1,-3] = true := by rfl
private theorem goodPair11 : goodPair [-3,3,-3,3,-3] = true := by rfl
private theorem goodPair12 : goodPair [-3,3,1,-5,1] = true := by rfl
private theorem goodPair13 : goodPair [-3,3,1,-1,1] = true := by rfl
private theorem goodPair14 : goodPair [-1,-3,-5,-3,-1] = true := by rfl
private theorem goodPair15 : goodPair [-1,-3,-1,-3,-1] = true := by rfl
private theorem goodPair16 : goodPair [-1,-3,-1,1,-1] = true := by rfl
private theorem goodPair17 : goodPair [-1,-3,-1,1,3] = true := by rfl
private theorem goodPair18 : goodPair [-1,-3,3,1,-5] = true := by rfl
private theorem goodPair19 : goodPair [-1,-3,3,1,-1] = true := by rfl
private theorem goodPair20 : goodPair [-1,1,-5,1,-1] = true := by rfl
private theorem goodPair21 : goodPair [-1,1,-1,-3,-1] = true := by rfl
private theorem goodPair22 : goodPair [-1,1,-1,-3,3] = true := by rfl
private theorem goodPair23 : goodPair [-1,1,-1,1,-5] = true := by rfl
private theorem goodPair24 : goodPair [-1,1,-1,1,-1] = true := by rfl
private theorem goodPair25 : goodPair [-1,1,-1,1,3] = true := by rfl
private theorem goodPair26 : goodPair [-1,1,-1,5,-1] = true := by rfl
private theorem goodPair27 : goodPair [-1,1,3,-3,-1] = true := by rfl
private theorem goodPair28 : goodPair [-1,1,3,1,-1] = true := by rfl
private theorem goodPair29 : goodPair [-1,1,3,1,3] = true := by rfl
private theorem goodPair30 : goodPair [-1,1,3,5,3] = true := by rfl
private theorem goodPair31 : goodPair [-1,5,-1,-3,3] = true := by rfl
private theorem goodPair32 : goodPair [-1,5,-1,1,-1] = true := by rfl
private theorem goodPair33 : goodPair [1,-5,1,-1,1] = true := by rfl
private theorem goodPair34 : goodPair [1,-5,1,3,-3] = true := by rfl
private theorem goodPair35 : goodPair [1,-1,-3,-5,-3] = true := by rfl
private theorem goodPair36 : goodPair [1,-1,-3,-1,-3] = true := by rfl
private theorem goodPair37 : goodPair [1,-1,-3,-1,1] = true := by rfl
private theorem goodPair38 : goodPair [1,-1,-3,3,1] = true := by rfl
private theorem goodPair39 : goodPair [1,-1,1,-5,1] = true := by rfl
private theorem goodPair40 : goodPair [1,-1,1,-1,-3] = true := by rfl
private theorem goodPair41 : goodPair [1,-1,1,-1,1] = true := by rfl
private theorem goodPair42 : goodPair [1,-1,1,-1,5] = true := by rfl
private theorem goodPair43 : goodPair [1,-1,1,3,-3] = true := by rfl
private theorem goodPair44 : goodPair [1,-1,1,3,1] = true := by rfl
private theorem goodPair45 : goodPair [1,-1,5,-1,1] = true := by rfl
private theorem goodPair46 : goodPair [1,3,-3,-1,1] = true := by rfl
private theorem goodPair47 : goodPair [1,3,-3,-1,5] = true := by rfl
private theorem goodPair48 : goodPair [1,3,1,-1,-3] = true := by rfl
private theorem goodPair49 : goodPair [1,3,1,-1,1] = true := by rfl
private theorem goodPair50 : goodPair [1,3,1,3,1] = true := by rfl
private theorem goodPair51 : goodPair [1,3,5,3,1] = true := by rfl
private theorem goodPair52 : goodPair [3,-3,-1,1,-1] = true := by rfl
private theorem goodPair53 : goodPair [3,-3,-1,5,-1] = true := by rfl
private theorem goodPair54 : goodPair [3,-3,3,-3,3] = true := by rfl
private theorem goodPair55 : goodPair [3,1,-5,1,3] = true := by rfl
private theorem goodPair56 : goodPair [3,1,-1,-3,-5] = true := by rfl
private theorem goodPair57 : goodPair [3,1,-1,-3,-1] = true := by rfl
private theorem goodPair58 : goodPair [3,1,-1,1,-1] = true := by rfl
private theorem goodPair59 : goodPair [3,1,-1,1,3] = true := by rfl
private theorem goodPair60 : goodPair [3,1,3,1,-1] = true := by rfl
private theorem goodPair61 : goodPair [3,5,3,1,-1] = true := by rfl
private theorem goodPair62 : goodPair [5,-5,5,-5,5] = true := by rfl
private theorem goodPair63 : goodPair [5,-1,-3,3,1] = true := by rfl
private theorem goodPair64 : goodPair [5,-1,1,-1,1] = true := by rfl
private theorem goodPair65 : goodPair [5,3,1,-1,-3] = true := by rfl
private theorem pairBounds : pairTable.all goodPair = true := by
  change (List.all [[-5,-3,-1,1,3], [-5,1,-1,1,-1], [-5,1,3,-3,-1], [-5,5,-5,5,-5], [-3,-5,-3,-1,1], [-3,-1,-3,-1,1], [-3,-1,1,-1,-3], [-3,-1,1,-1,1], [-3,-1,1,3,1], [-3,-1,1,3,5], [-3,-1,5,-1,-3], [-3,3,-3,3,-3], [-3,3,1,-5,1], [-3,3,1,-1,1], [-1,-3,-5,-3,-1], [-1,-3,-1,-3,-1], [-1,-3,-1,1,-1], [-1,-3,-1,1,3], [-1,-3,3,1,-5], [-1,-3,3,1,-1], [-1,1,-5,1,-1], [-1,1,-1,-3,-1], [-1,1,-1,-3,3], [-1,1,-1,1,-5], [-1,1,-1,1,-1], [-1,1,-1,1,3], [-1,1,-1,5,-1], [-1,1,3,-3,-1], [-1,1,3,1,-1], [-1,1,3,1,3], [-1,1,3,5,3], [-1,5,-1,-3,3], [-1,5,-1,1,-1], [1,-5,1,-1,1], [1,-5,1,3,-3], [1,-1,-3,-5,-3], [1,-1,-3,-1,-3], [1,-1,-3,-1,1], [1,-1,-3,3,1], [1,-1,1,-5,1], [1,-1,1,-1,-3], [1,-1,1,-1,1], [1,-1,1,-1,5], [1,-1,1,3,-3], [1,-1,1,3,1], [1,-1,5,-1,1], [1,3,-3,-1,1], [1,3,-3,-1,5], [1,3,1,-1,-3], [1,3,1,-1,1], [1,3,1,3,1], [1,3,5,3,1], [3,-3,-1,1,-1], [3,-3,-1,5,-1], [3,-3,3,-3,3], [3,1,-5,1,3], [3,1,-1,-3,-5], [3,1,-1,-3,-1], [3,1,-1,1,-1], [3,1,-1,1,3], [3,1,3,1,-1], [3,5,3,1,-1], [5,-5,5,-5,5], [5,-1,-3,3,1], [5,-1,1,-1,1], [5,3,1,-1,-3]] goodPair) = true
  simp only [List.all_cons, List.all_nil, goodPair0, goodPair1, goodPair2, goodPair3, goodPair4, goodPair5, goodPair6, goodPair7, goodPair8, goodPair9, goodPair10, goodPair11, goodPair12, goodPair13, goodPair14, goodPair15, goodPair16, goodPair17, goodPair18, goodPair19, goodPair20, goodPair21, goodPair22, goodPair23, goodPair24, goodPair25, goodPair26, goodPair27, goodPair28, goodPair29, goodPair30, goodPair31, goodPair32, goodPair33, goodPair34, goodPair35, goodPair36, goodPair37, goodPair38, goodPair39, goodPair40, goodPair41, goodPair42, goodPair43, goodPair44, goodPair45, goodPair46, goodPair47, goodPair48, goodPair49, goodPair50, goodPair51, goodPair52, goodPair53, goodPair54, goodPair55, goodPair56, goodPair57, goodPair58, goodPair59, goodPair60, goodPair61, goodPair62, goodPair63, goodPair64, goodPair65, Bool.and_self]

private theorem bound5 (a b c : List Int)
    (ha : a ∈ signRows 5) (hb : b ∈ signRows 5) (hc : c ∈ signRows 5) :
    gauge inv5 (threeCoords 5 a b c) ≤ 3200 := by
  have hp : ncMul 5 a b ∈ pairTable := by
    have hh := List.all_eq_true.mp (List.all_eq_true.mp pairCoverage a ha) b hb
    simpa using hh
  exact of_decide_eq_true
    (List.all_eq_true.mp (List.all_eq_true.mp pairBounds _ hp) c hc)


/-- Exact one-norm bound for every triple of length-5 sign rows. -/
theorem all_rows_5 {a b c : List Int} (ha : a ∈ signRows 5)
    (hb : b ∈ signRows 5) (hc : c ∈ signRows 5) :
    gauge inv5 (threeCoords 5 a b c) ≤ 3200 :=
  bound5 a b c ha hb hc

/-- Every signed vertex at radius 3200 is attained. -/
theorem signed_axes_5 {v : List Int} (h : v ∈ axes 3 3200) :
    ∃ a ∈ signRows 5, ∃ b ∈ signRows 5, ∃ c ∈ signRows 5,
      integerImage inv5 (threeCoords 5 a b c) = v :=
  realizes_axes (W := witnesses5) (by rfl) (by rfl) h

end Lemmata.BellFollowup.Positive
