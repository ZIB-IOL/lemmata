module

public import Lemmata.ModifiedE8Bell.Compute.Raw

@[expose] public section
namespace Lemmata.ModifiedE8Bell

def weights : List Nat := [2,5,7,10,8,6,4,2]

def cost : List Nat → List Nat → Nat
  | w :: ws, k :: ks => w*k + cost ws ks
  | _, _ => 0

def tuples : List Nat → Nat → List (List Nat)
  | [], _ => [[]]
  | w :: ws, budget =>
    (List.range (budget+1)).flatMap fun k =>
      if w*k ≤ budget then (tuples ws (budget-w*k)).map (k :: ·) else []

def rawDot (u v : Fin 8 → Int) : Int :=
  u 0*v 0 + u 1*v 1 + u 2*v 2 + u 3*v 3 + u 4*v 4 + u 5*v 5 + u 6*v 6 + u 7*v 7

def rawEnvelope (q : Fin 8 → Int) : Int :=
  (rootRows.toList.map fun r => max 52 (6 * ((rawDot (fun j => r[j.val]?.getD 0) q).natAbs : Int) - 52)).sum - 3*rawDot q q

def rawPoint : List Nat → Fin 8 → Int
  | [d,s,t,a,b,c,e,f] =>
    let p1 : Int := (s:Int)-(t:Int)
    let p2 : Int := (s:Int)+(t:Int)
    let p3 := p2+2*a
    let p4 := p3+2*b
    let p5 := p4+2*c
    let p6 := p5+2*e
    let p7 := p6+2*f
    let p8 : Int := 2*d+5*s+7*t+10*a+8*b+6*c+4*e+2*f
    let p := #[2*p1,2*p2,2*p3,2*p4,2*p5,2*p6,2*p7,2*p8]
    fun j => p[j.val]?.getD 0
  | _ => fun _ => 0

def passes (ks : List Nat) : Bool := decide (rawEnvelope (rawPoint ks) ≤ 24416)

end Lemmata.ModifiedE8Bell
