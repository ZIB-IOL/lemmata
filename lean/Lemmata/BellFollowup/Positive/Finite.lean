module

public import Std

/-! Exact three-party certificates in even negacyclic coordinates.
The rows are actual sign lists, with no frequency, rotation, or phase constraints.
The component vector is 2 m² times the reduced Reynolds vector. -/

@[expose] public section

namespace Lemmata.BellFollowup.Positive

/-- All possible single-party rows in prefix order. -/
def signRows : Nat → List (List Int)
  | 0 => [[]]
  | m + 1 => (signRows m).map (1 :: ·) ++ (signRows m).map ((-1) :: ·)

/-- The enumeration contains exactly the rows of the stated length with sign entries. -/
theorem mem_signRows {m : Nat} {a : List Int} :
    a ∈ signRows m ↔ a.length = m ∧ ∀ x ∈ a, x = 1 ∨ x = -1 := by
  induction m generalizing a with
  | zero =>
    cases a <;> simp [signRows]
  | succ m ih =>
    cases a with
    | nil => simp [signRows]
    | cons x xs =>
      simp only [signRows, List.mem_append, List.mem_map, List.cons.injEq,
        List.length_cons, Nat.succ.injEq, List.forall_mem_cons, ih]
      grind

/-- Negacyclic polynomial multiplication in Z[t]/(t^m + 1), in coefficient order. -/
def ncMul (m : Nat) (a b : List Int) : List Int :=
  (List.range m).map fun r =>
    ((List.range m).map fun i =>
      let j := if i ≤ r then r - i else m + r - i
      let value := a[i]! * b[j]!
      if i ≤ r then value else -value).sum

/-- Add the reflected coefficient vector and retain the independent coordinates. -/
def evenCoords (m : Nat) (h : List Int) : List Int :=
  (List.range ((m+1)/2)).map fun r =>
    if r = 0 then 2 * h[0]! else h[r]! - h[m-r]!

def threeCoords (m : Nat) (a b c : List Int) : List Int :=
  evenCoords m (ncMul m (ncMul m a b) c)

/-- A signed-column inverse, with its common denominator kept separate. -/
def integerImage (M : List (List Int)) (q : List Int) : List Int :=
  M.map fun row => (List.zipWith (· * ·) row q).sum

def gauge (M : List (List Int)) (q : List Int) : Nat :=
  ((integerImage M q).map Int.natAbs).sum

def inv2 : List (List Int) := [[1]]
def inv3 : List (List Int) := [[9,9],[3,-5]]
def inv4 : List (List Int) := [[3,4],[3,-4]]
def inv5 : List (List Int) := [[50,75,25],[50,-25,-75],[12,-26,26]]

def pairs (m : Nat) : List (List Int) :=
  ((signRows m).flatMap fun a => (signRows m).map (ncMul m a)).eraseDups

/-- A finite Boolean check of the scaled l1 ball bound. Distinct pair products
are deduplicated. No third-party strategies are discarded. -/
def checkBound (m : Nat) (M : List (List Int)) (D : Nat) : Bool :=
  (pairs m).all fun ab =>
    (signRows m).all fun c => decide (gauge M (evenCoords m (ncMul m ab c)) ≤ D)

/-- Soundness of the Boolean certificate, for every sign strategy. -/
theorem gauge_le_of_check {m D : Nat} {M : List (List Int)}
    (ok : checkBound m M D = true) {a b c : List Int}
    (ha : a ∈ signRows m) (hb : b ∈ signRows m) (hc : c ∈ signRows m) :
    gauge M (threeCoords m a b c) ≤ D := by
  have hp : ncMul m a b ∈ pairs m := by
    apply List.mem_eraseDups.mpr
    exact List.mem_flatMap.mpr ⟨a, ha, List.mem_map.mpr ⟨b,hb,rfl⟩⟩
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp ok _ hp) _ hc)

/-- Every vector in this list is a realized image, with actual three-party signs. -/
def checkAxes (m : Nat)
    (witnesses : List (List Int × List Int × List Int)) : Bool :=
  witnesses.all fun (a,b,c) => (signRows m).contains a &&
    (signRows m).contains b && (signRows m).contains c

def witnessImages (m : Nat) (M : List (List Int))
    (witnesses : List (List Int × List Int × List Int)) : List (List Int) :=
  witnesses.map fun (a,b,c) => integerImage M (threeCoords m a b c)

def axes (d : Nat) (D : Int) : List (List Int) :=
  (List.range d).flatMap fun i =>
    let v := (List.range d).map fun j => if i = j then D else 0
    [v,v.map Neg.neg]

/-- A finite check including all signed column witnesses entails their realizability. -/
theorem realizes_axes {m d : Nat} {D : Int} {M : List (List Int)}
    {W : List (List Int × List Int × List Int)}
    (legal : checkAxes m W = true) (data : witnessImages m M W = axes d D)
    {v : List Int} (hv : v ∈ axes d D) :
    ∃ a ∈ signRows m, ∃ b ∈ signRows m, ∃ c ∈ signRows m,
      integerImage M (threeCoords m a b c) = v := by
  rw [← data] at hv
  obtain ⟨⟨a,b,c⟩,hw,he⟩ := List.mem_map.mp hv
  have hh := List.all_eq_true.mp legal (a,b,c) hw
  simp at hh
  exact ⟨a,hh.1.1,b,hh.1.2,c,hh.2,he⟩

end Lemmata.BellFollowup.Positive
