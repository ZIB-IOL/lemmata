module

public import Lemmata.SteinerSixSpectrum.OrbitTable

@[expose] public section

namespace Lemmata.SteinerSixSpectrum

def rangeGroups (count size : ℕ) : Rows :=
  (List.range count).map fun i => (List.range size).map (i*size + ·)

/-- For the small local tables, recover groups from the complement of the pair graph. -/
def freeNeighbours (n : ℕ) (rows : Rows) : Array (List ℕ) := Id.run do
  let mut covered := Array.replicate (n*n) false
  for row in rows do
    for x in row do
      for y in row do
        if x != y then
          covered := covered.set! (x*n+y) true
  return ((List.range n).map fun x =>
    (List.range n).filter fun y => !covered[x*n+y]!).toArray

def sortRows (rows : Rows) : Rows :=
  rows.mergeSort (fun a b => compare a b != .gt)

def groupRows (sizes : List ℕ) : Rows × Rows :=
  match groupOrbits.find? (fun item => item.1 == sizes) with
  | none => ([], [])
  | some (_, record) =>
    let rows := expandOrbit record
    let groups := (freeNeighbours record.order rows).toList.eraseDups
    (rows, groups.mergeSort (fun a b =>
      a.length < b.length || (a.length == b.length && compare a b != .gt)))

def rowCoordinates (rows groups : Rows) : List (List (ℕ × ℕ)) := Id.run do
  let mut coords := Array.replicate (groups.flatten.foldl max 0 + 1) (0, 0)
  for (group, i) in groups.zipIdx do
    for (x, j) in group.zipIdx do
      coords := coords.set! x (i, j)
  return rows.map fun row => (row.map (fun x => coords[x]!)).mergeSort
    (fun a b => a.1 < b.1 || (a.1 == b.1 && a.2 ≤ b.2))

def transversalRows (rows groups : Rows) : Rows :=
  (rowCoordinates rows groups).map (List.map Prod.snd)

def incompleteArray (m h : ℕ) : Rows :=
  match arrayOrbits.find? (fun item => item.1 == (m,h)) with
  | none => []
  | some (_, record) =>
    let rows := expandOrbit record
    let free := (freeNeighbours (6*m) rows).toList
    let hole := free.zipIdx.filterMap (fun (g,i) => if g.length != m then some i else none)
    let groups := sortRows ((free.filter (fun g => g.length == m)).eraseDups)
    let reordered := groups.map fun g =>
      g.filter (fun x => !hole.contains x) ++ g.filter hole.contains
    transversalRows rows reordered

/-- Arithmetic in a small polynomial presentation. The empty modulus is used for
a prime field. -/
structure FieldArithmetic where
  p : ℕ
  modulus : List ℕ

def arithmetic (q : ℕ) : FieldArithmetic :=
  match q with
  | 8 => ⟨2,[1,0,1]⟩
  | 9 => ⟨3,[2,1]⟩
  | 16 => ⟨2,[1,0,0,1]⟩
  | 25 => ⟨5,[2,1]⟩
  | 27 => ⟨3,[1,0,2]⟩
  | 49 => ⟨7,[3,1]⟩
  | 81 => ⟨3,[2,0,0,1]⟩
  | _ => ⟨q,[]⟩

def pack (p : ℕ) (digits : List ℕ) : ℕ :=
  digits.foldr (fun digit acc => p*acc+digit % p) 0

def fieldAdd (f : FieldArithmetic) (x y : ℕ) : ℕ :=
  if f.modulus.isEmpty then
    (x+y) % f.p
  else
    pack f.p ((List.range f.modulus.length).map fun i =>
      x / f.p ^ i % f.p + y / f.p ^ i % f.p)

def fieldMul (f : FieldArithmetic) (x y : ℕ) : ℕ := Id.run do
  if f.modulus.isEmpty then return x*y % f.p
  let degree := f.modulus.length
  let idx := List.range degree
  let digits (z : ℕ) := idx.map (fun i => z / f.p ^ i % f.p)
  let mut coeff := Array.replicate (2*degree-1) (0 : ℕ)
  for (a,i) in (digits x).zipIdx do
    for (b,j) in (digits y).zipIdx do
      coeff := coeff.set! (i+j) ((coeff[i+j]! + a*b) % f.p)
  for i in (List.range (2*degree-1)).reverse do
    if degree ≤ i then
      let c := coeff[i]!
      for (m,j) in f.modulus.zipIdx do
        let h := i-degree+j
        coeff := coeff.set! h ((coeff[h]! + f.p - (c*m % f.p)) % f.p)
  return pack f.p (idx.map fun i => coeff[i]!)

def affineRows (q columns : ℕ) : Rows :=
  let f := arithmetic q
  let range := List.range q
  range.flatMap fun x => range.map fun y =>
    (List.range (columns-1)).map (fun i => fieldAdd f x (fieldMul f i y)) ++ [y]

def pairwiseRows (m : ℕ) : Rows :=
  if m = 66 then
    let f := arithmetic 8
    let values := List.range 8
    let points := (values.flatMap fun a => values.map fun b => (1,a,b)) ++
      (values.map fun b => (0,1,b)) ++ [(0,0,1)]
    let removed := (List.range 7).map fun x => (1,x,fieldMul f x x)
    let kept := (points.filter fun p => !removed.contains p).zipIdx
    points.map fun (a,b,c) => kept.filterMap fun ((x,y,z),i) =>
      if fieldAdd f (fieldAdd f (fieldMul f x a) (fieldMul f y b)) (fieldMul f z c) = 0
        then some i else none
  else
    let (q, sizes) :=
      match m with
      | 70 => (8, List.replicate 7 8 ++ [7,7])
      | 96 => (11, List.replicate 8 11 ++ [8])
      | 111 => (13, List.replicate 8 13 ++ [7])
      | 150 => (19, List.replicate 7 19 ++ [17])
      | 156 => (19, List.replicate 7 19 ++ [16,7])
      | _ => (0, [])
    let groups := (sizes.zipIdx).map fun (size,i) =>
      (List.range size).map ((sizes.take i).sum + ·)
    groups ++ (affineRows q groups.length).map fun row =>
      (groups.zip row).filterMap fun (g,x) => g[x]?

def arrayFromPairwise (m : ℕ) : Rows :=
  let diagonal := (List.range m).map (List.replicate 6)
  diagonal ++ (pairwiseRows m).flatMap fun group =>
    let q := group.length
    let f := arithmetic q
    (List.range q).flatMap fun x =>
      ((List.range q).drop 1).map fun y =>
        (List.range 6).map fun i => group[fieldAdd f x (fieldMul f i y)]!

def sixColumnArray : ℕ → ℕ → Option Rows
  | 0, _ => none
  | fuel+1, m => Id.run do
    if m = 1 then return some [List.replicate 6 0]
    if [14,15,18,20].contains m then
      let (blocks, groups) := groupRows (List.replicate 6 m)
      return some (transversalRows blocks groups)
    if m ≥ 5 && (!(arithmetic m).modulus.isEmpty ||
        ((List.range m).drop 2).all (fun i => m % i != 0)) then
      return some (affineRows m 6)
    if [66,70,96,111,150,156].contains m then
      return some (arrayFromPairwise m)
    for d in [5:Nat.sqrt m+1] do
      if m % d = 0 then
        let some a := sixColumnArray fuel d | continue
        let some b := sixColumnArray fuel (m/d) | continue
        return some (a.flatMap fun x => b.map fun y => x.zipWith (fun u v => u*(m/d)+v) y)
    return none

def td6 (m : ℕ) : Rows := (sixColumnArray 8 m).getD []

end Lemmata.SteinerSixSpectrum
