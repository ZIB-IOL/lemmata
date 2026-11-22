module

public import Lemmata.ModifiedE8Bell.Envelope
public import Lemmata.ModifiedE8Bell.Compute
public meta import Lemmata.ModifiedE8Bell.Compute

@[expose] public section
namespace Lemmata.ModifiedE8Bell
open scoped BigOperators

/-- Completeness of the weighted enumeration, including all boundary cases. -/
theorem mem_tuples (ws ks : List ℕ) (budget : ℕ)
    (pos : ∀ w ∈ ws, 0 < w) (len : ks.length = ws.length)
    (fit : cost ws ks ≤ budget) : ks ∈ tuples ws budget := by
  induction ws generalizing ks budget with
  | nil =>
    cases ks with
    | nil => simp [tuples]
    | cons k ks => simp at len
  | cons w ws ih =>
    cases ks with
    | nil => simp at len
    | cons k ks =>
      have hw : 1 ≤ w := pos w (by simp)
      have hk : w*k ≤ budget := by change w*k + cost ws ks ≤ budget at fit; omega
      have hk' : k ≤ budget := le_trans (by simpa using Nat.mul_le_mul_right k hw) hk
      have tail : ks ∈ tuples ws (budget-w*k) := by
        apply ih
        · intro a ha; exact pos a (by simp [ha])
        · simpa using len
        · change w*k + cost ws ks ≤ budget at fit; omega
      rw [tuples]
      apply List.mem_flatMap.mpr
      refine ⟨k, List.mem_range.mpr (by omega), ?_⟩
      simp only [if_pos hk]
      exact List.mem_map.mpr ⟨ks,tail,rfl⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- All 38,549 tuples of weighted cost at most 46 satisfy the upper bound. -/
theorem all_tuples_pass : (tuples weights 46).all passes = true := by
  native_decide

lemma rawDot_eq (u v : IntVector) : rawDot u v = dot u v := by
  simp [rawDot, dot, Fin.sum_univ_succ, add_assoc]

set_option maxHeartbeats 0 in
lemma rootRows_list : rootRows.toList = List.ofFn (fun i : Setting => rootRows[i.val]?.getD #[]) := by
  decide +kernel

lemma rawEnvelope_eq (q : IntVector) : rawEnvelope q = envelope q := by
  rw [rawEnvelope, rootRows_list, List.map_ofFn, List.sum_ofFn]
  simp only [rawDot_eq, Int.natCast_natAbs, envelope, Function.comp_apply]
  rfl

lemma rawPoint_ofFn (g : Coordinate → ℕ) :
    rawPoint (List.ofFn g) = fun j => 2 * coordinates (fun k => (g k : ℤ)) j := by
  funext j
  fin_cases j <;> simp [rawPoint, List.ofFn_succ, coordinates, basis, Fin.sum_univ_succ] <;> ring

lemma cost_ofFn (g : Coordinate → ℕ) :
    (cost weights (List.ofFn g) : ℤ) = coordinates (fun k => (g k : ℤ)) 7 := by
  simp [weights, cost, List.ofFn_succ, coordinates, basis, Fin.sum_univ_succ]

/-- The finite calculation applies to every nonnegative gap vector within the budget. -/
theorem chamber_envelope (g : IntVector) (hg : ∀ k, 0 ≤ g k)
    (hb : coordinates g 7 ≤ 46) : envelope (fun j => 2 * coordinates g j) ≤ 24416 := by
  let n : Coordinate → ℕ := fun k => (g k).toNat
  have hn : (fun k => (n k : ℤ)) = g := by funext k; exact Int.toNat_of_nonneg (hg k)
  have hcost : cost weights (List.ofFn n) ≤ 46 := by
    have hc := cost_ofFn n
    rw [hn] at hc
    omega
  have hm := mem_tuples weights (List.ofFn n) 46
    (by intro w hw; simp [weights] at hw; omega) (by simp [weights]) hcost
  have hp := List.all_eq_true.mp all_tuples_pass (List.ofFn n) hm
  have hv : rawEnvelope (rawPoint (List.ofFn n)) ≤ 24416 := of_decide_eq_true hp
  simpa only [rawEnvelope_eq, rawPoint_ofFn, hn] using hv

end Lemmata.ModifiedE8Bell
