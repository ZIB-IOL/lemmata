module

public import Lemmata.SteinerSixSpectrum.FiniteArrays

@[expose] public section

namespace Lemmata.SteinerSixSpectrum

abbrev BlockSource := ℕ → Rows

def relabelRows (labels : Array ℕ) (rows : Rows) : Rows :=
  rows.map (List.map fun x => labels[x]!)

def orderLabels (first all : List ℕ) : Array ℕ := Id.run do
  let mut labels := Array.replicate all.length 0
  for (label,i) in (first ++ all.filter (fun x => !first.contains x)).zipIdx do
    labels := labels.set! label i
  return labels

def fillOne (design : BlockSource) (group shared : List ℕ) : Rows := Id.run do
  let n := group.length+shared.length
  let rows := design n
  let anchor := match shared.length with
    | 6 => rows.headD [] | 1 => [0] | _ => []
  let rest := (List.range n).filter (fun x => !anchor.contains x)
  let mut labels := Array.replicate n 0
  for (x,y) in (anchor.zip shared ++ rest.zip group) do
    labels := labels.set! x y
  return relabelRows labels (rows.filter (fun row => row != anchor))

def fillAll (design : BlockSource) (groups : Rows) (e : ℕ) : Rows :=
  let start := groups.flatten.foldl max 0 + 1
  let shared := (List.range e).map (start + ·)
  let sizes := (groups.map (fun g => g.length + e)).eraseDups
  let fillings := sizes.map (fun n => (n, design n))
  let cached n := ((fillings.find? (fun f => f.1 == n)).map Prod.snd).getD []
  (if e = 6 then [shared] else []) ++ groups.flatMap (fun g => fillOne cached g shared)

def inflateRows (design : BlockSource) (blocks groups : Rows) (m e : ℕ) : Rows :=
  let inflated := groups.map fun group =>
    group.flatMap fun x => (List.range m).map (x*m + ·)
  let rows := td6 m
  blocks.flatMap (fun b => rows.map fun row => b.zipWith (fun x y => x*m+y) row) ++
    fillAll design inflated e

def productRows (design : BlockSource) (d m e : ℕ) (delete : Bool) : Rows :=
  let rows := design d
  if delete then
    let (through, off) := rows.partition (fun row => row.contains (d-1))
    let groups := through.map (fun row => row.filter (· != d-1))
    inflateRows design off groups m e
  else
    inflateRows design rows ((List.range d).map fun x => [x]) m e

def directPartial (v h : ℕ) : Rows :=
  match incompleteOrbits.find? (fun item => item.1 == (v,h)) with
  | none => []
  | some (_, record) => expandOrbit record

def partialRows (design : BlockSource) (v h : ℕ) : Rows :=
  if h = 31 && [156,186,211].contains v then
    let (out, groups) :=
      if v = 211 then groupRows (List.replicate 7 30) else
        let m := if v = 156 then 25 else 31
        ((td6 m).map (fun b => b.zipIdx.map fun (x,i) => i*m+x), rangeGroups 6 m)
    let start := groups.flatten.length
    let shared := ((List.range v).drop start)
    let rows := out ++ (groups.take (groups.length-1)).flatMap (fun g => fillOne design g shared)
    let hole := groups.getLastD [] ++ shared
    let ordinary := (List.range v).filter (fun x => !hole.contains x)
    relabelRows (orderLabels ordinary (List.range v)) rows
  else
    directPartial v h

def sixGroups (design : BlockSource) (v h : ℕ) : Rows :=
  let g := v-h
  let outer := (td6 g).map (fun row => row.zipIdx.map fun (x,i) => i*g+x)
  let part := partialRows design v h
  let full := design v
  outer ++ (List.range 6).flatMap fun i =>
    let labels := (((List.range g).map (i*g + ·)) ++ ((List.range h).map (6*g + ·))).toArray
    relabelRows labels (if i < 5 then part else full)

/-- Remove selected disjoint rows after assigning them constant symbol labels. -/
def puncturedArray (m extra : ℕ) (axis : Bool) : Rows := Id.run do
  let n := m+extra
  let rows := td6 n
  let diagonal := (List.range n).drop m ++ if axis then [0] else []
  let mut selected := List.replicate 6 []
  for row in rows do
    if (selected.headD []).length = diagonal.length then break
    if (row.zip selected).all (fun (x, col) => !col.contains x) then
      selected := selected.zipWith (fun col x => col ++ [x]) row
  let target := diagonal ++ (List.range n).filter (fun x => !diagonal.contains x)
  let maps := selected.map fun col =>
    (orderLabels col (List.range n)).map (fun i => target[i]!)
  let mapped := rows.map (fun row => row.zipWith (fun x p => p[x]!) maps)
  return mapped.filter fun row => !diagonal.any (fun x => row == List.replicate 6 x)

inductive Puncture where
  | row | axis | tail | array | three
  deriving BEq

def wilsonArray (size h : ℕ) (mode : Puncture) (t m : ℕ) (tail : List ℕ) : Rows := Id.run do
  let offsets := tail.zipIdx.map fun (_,i) => m*t + (tail.take i).sum
  let skipped := if mode == .tail then tail.idxOf h else tail.length
  let mut hole :=
    if mode == .tail then List.replicate 6 ((List.range h).map (offsets[skipped]! + ·))
    else if mode == .axis then List.replicate 6 ((List.range t).map (· * m))
    else List.replicate 6 []
  let active := if mode == .row then
    ((tail.zipIdx.mergeSort fun a b => a.1 ≥ b.1).take (h-m)).map Prod.snd
    else List.range tail.length
  let localRows := ((List.range (tail.length+1)).map
    (fun j => puncturedArray m j (mode == .axis))).toArray
  let mut result := []
  for row in affineRows t (6+tail.length) do
    let extra := (((row.drop 6).zip tail).zip offsets).zipIdx.filterMap
      fun (((x,w),start),i) =>
        let y := if active.contains i then x else (x+w) % t
        if y < w then some (start+y) else none
    if mode == .row && (hole.headD []).isEmpty && m+extra.length = h then
      hole := (row.take 6).map (fun x => (List.range m).map (x*m + ·) ++ extra)
    else
      let part := localRows[extra.length]!
      result := (part.map fun b => (row.take 6).zipWith
        (fun a x => if x < m then a*m+x else extra[x-m]!) b) ++ result
  for ((start,w),i) in (offsets.zip tail).zipIdx do
    if i != skipped then
      let part := td6 w
      let removed := ((hole.headD []).filter fun x => start ≤ x && x < start+w)
      let rows := match removed with
        | [] => part.map (List.map (start + ·))
        | cut :: _ => (part.drop 1).map fun row => row.zipWith
            (fun x z => start+(x+w-z+cut-start)%w) (part.headD [])
      result := rows ++ result
  let maps := hole.map fun col =>
    orderLabels ((List.range size).filter (fun x => !col.contains x)) (List.range size)
  return result.map (fun row => row.zipWith (fun x p => p[x]!) maps)

def threeColumns (weights : List ℕ) : Rows :=
  let range := List.range 8
  let f := arithmetic 8
  let pieces := (weights.map (fun h => (h, if h = 0 then td6 15 else incompleteArray (15+h) h)))
  let ordinary := td6 15
  range.flatMap fun a => range.flatMap fun b =>
    if a = 0 && b = 0 then [] else
      let pt := range.map (fun i => fieldAdd f a (fieldMul f i b)) ++ [b]
      let chosen := ((pt.drop 6).zipIdx).find? (fun (x,_) => x = 0)
      let (weight,offset) := match chosen with
        | none => (0,0)
        | some (_,i) => (weights[i]!, 120+(weights.take i).sum)
      let part := if weight = 0 then ordinary else
        ((pieces.find? (fun p => p.1 == weight)).map Prod.snd).getD []
      part.map fun row => (pt.take 6).zipWith (fun x y =>
        if y ≥ 15 then offset+y-15 else 15*((x+7)%8)+y) row

def sharedIncomplete (design : BlockSource) (v h a : ℕ) (mode : Puncture)
    (t m : ℕ) (tail : List ℕ) : Rows :=
  let g := v-h
  let master := match mode with
    | .array => incompleteArray (g+a) a
    | .three => threeColumns tail
    | _ => wilsonArray (g+a) a mode t m tail
  let outer := master.map (fun row => row.zipIdx.map fun (x,i) =>
    if x < g then i*g+x else 6*g+i*a+x-g)
  let part := partialRows design v h
  let body := (List.range 6).flatMap fun i =>
    let labels := ((List.range g).map (i*g + ·)) ++
      ((List.range a).map (6*g+i*a + ·)) ++ ((List.range (h-a)).map (6*g+6*a + ·))
    relabelRows labels.toArray part
  outer ++ body ++ (design (h+5*a)).map (List.map (6*g + ·))

def fibreRows (design : BlockSource) (s t h : ℕ) : Rows := Id.run do
  let some (_, record) := fibreOrbits.find? (fun item => item.1 == (s,t,h)) | return []
  let part := expandOrbit record
  let n := s*t
  let free := freeNeighbours (n+h) part
  let missing := (List.range n).map (fun x => free[x]!.filter (· != x))
  let classes := missing.eraseDups
  let members := classes.map (fun c => (List.range n).filter (fun x => missing[x]! == c))
  let master := td6 s
  let diagonal := sortRows (master.filter (fun row => row.getLastD 1 == 0))
  let names := (List.range 5).map fun i =>
    orderLabels (diagonal.map (fun row => row[i]!)) (List.range s)
  let start := 5*n+(s-1)*t
  let short := td6 t
  let outside := master.flatMap fun row =>
    let indices := (row.take 5).zipWith (fun x p => p[x]!) names
    let c := row.getLastD 0
    short.map fun b =>
      let y := b.getLastD 0
      let extra := if c = 0 then start + (classes[indices.headD 0]!)[y]! - n
        else 5*n+(c-1)*t+y
      (((indices.zip (b.take 5)).zipIdx).map fun ((i,x),j) => j*n+(members[i]!)[x]!) ++ [extra]
  let copies := (List.range 5).flatMap (fun i => part.map
    (List.map fun x => if x < n then i*n+x else start+x-n))
  return outside ++ copies ++ (design ((s-1)*t+h)).map (List.map (5*n + ·))

end Lemmata.SteinerSixSpectrum
