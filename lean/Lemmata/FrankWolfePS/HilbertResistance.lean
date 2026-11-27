module
public import Lemmata.FrankWolfePS.HilbertFrame
public import Lemmata.FrankWolfePS.HilbertSeed

/-! The deterministic resisting construction. Finite histories include all past replies.
Each step chooses only one perpendicular direction and computes an exact finite response. -/
@[expose] public section
namespace Lemmata.FrankWolfePS.Hilbert.Anytime
open Lemmata.FrankWolfePS.Hilbert Finset Filter
open scoped Topology RealInnerProductSpace BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A deterministic anytime strategy has one query and one output for each finite reply history.
It may return any ambient vector, including at budget zero. -/
structure Strategy (E : Type*) where
  ask : (t : ℕ) → (Fin t → World E) → World E
  output : (t : ℕ) → (Fin t → World E) → World E

def queryAt (M : Strategy E) (r : ℕ → World E) (t : ℕ) := M.ask t (fun i => r i)
def outputAt (M : Strategy E) (r : ℕ → World E) (t : ℕ) := M.output t (fun i => r i)

/-- The public start depends only on a public unit vector, even before the frame is chosen. -/
noncomputable def start (v : E) : World E := WithLp.toLp 2 (0,(2*coef 0) • v)

noncomputable def select (a : ℕ → ℝ) (Q : ℝ) : ℕ → ℝ :=
  open Classical in
  if e : ∃ u, u∈simplex ∧ IsMaxOn (score (lin a Q) (pen Q)) simplex u then e.choose else 0

theorem select_spec {a : ℕ → ℝ} {k : ℕ} (h : ∀ i,k ≤ i → a i=0) {Q : ℝ} (qp : 0 < Q) :
    select a Q∈simplex ∧ IsMaxOn (score (lin a Q) (pen Q)) simplex (select a Q) := by
  have la : Tendsto a atTop (𝓝 0) := tendsto_const_nhds.congr' (by
    filter_upwards [eventually_ge_atTop k] with i hi using (h i hi).symm)
  have e := (unique_reply_parameter la qp).exists
  simpa [select,dite_eq_left e] using e.choose_spec

noncomputable def tests (M : Strategy E) (d : ℕ → E) (r : ℕ → World E) (t : ℕ) : Finset E :=
  open Classical in
  (range (t+1)).image d ∪ (range (t+1)).image (fun i => (queryAt M r i).snd) ∪
    (range (t+1)).image (fun i => (outputAt M r i).snd)

noncomputable def finiteCoeff (d : ℕ → E) (k : ℕ) (q : World E) (i : ℕ) : ℝ :=
  if i<k then ⟪q.snd,atom d i-mean d k⟫ else 0

noncomputable def partialReply (v : E) (d : ℕ → E) (k : ℕ) (q : World E) : World E :=
  open Classical in
  if q=0 then start v else
    let u := select (finiteCoeff d k q) ‖q‖
    let c := WithLp.toLp 2 ((1:ℝ), ∑ i ∈ range (k+1),u i • atom d i)
    tip c (rad u) q

structure State (E : Type*) where
  dirs : ℕ → E
  replies : ℕ → World E

noncomputable def advance (inf : ¬FiniteDimensional ℝ E) (M : Strategy E) (v : E) (t : ℕ)
    (s : State E) : State E :=
  let w := (fresh_exists inf (tests M s.dirs s.replies t)).choose
  let d := Function.update s.dirs (t+1) w
  let r := partialReply v d (t+1) (-(queryAt M s.replies t))
  ⟨d,Function.update s.replies t r⟩

noncomputable def history (inf : ¬FiniteDimensional ℝ E) (M : Strategy E) (v : E) : ℕ → State E
  | 0 => ⟨fun _ => v, fun _ => start v⟩
  | t+1 => advance inf M v t (history inf M v t)

noncomputable def directions (inf : ¬FiniteDimensional ℝ E) (M : Strategy E) (v : E) (i : ℕ) :=
  (history inf M v i).dirs i
noncomputable def answers (inf : ¬FiniteDimensional ℝ E) (M : Strategy E) (v : E) (i : ℕ) :=
  (history inf M v (i+1)).replies i

variable (inf : ¬FiniteDimensional ℝ E) (M : Strategy E) (v : E)

theorem dirs_stable {i n : ℕ} (le : i≤n) :
    (history inf M v n).dirs i=directions inf M v i := by
  induction n,le using Nat.le_induction with
  | base => rfl
  | succ n hn ih => simpa [history,advance,Function.update_of_ne (show i≠n+1 by omega)] using ih

theorem answers_stable {i n : ℕ} (lt : i<n) :
    (history inf M v n).replies i=answers inf M v i := by
  induction n,lt using Nat.le_induction with
  | base => rfl
  | succ n hn ih => simpa [history,advance,Function.update_of_ne (show i≠n by omega)] using ih

private theorem ask_stable {i n : ℕ} (hi : i≤n) :
    queryAt M (history inf M v n).replies i=queryAt M (answers inf M v) i := by
  apply congrArg (M.ask i)
  funext j
  exact answers_stable inf M v (lt_of_lt_of_le j.isLt hi)

private theorem out_stable {i n : ℕ} (hi : i≤n) :
    outputAt M (history inf M v n).replies i=outputAt M (answers inf M v) i := by
  apply congrArg (M.output i)
  funext j
  exact answers_stable inf M v (lt_of_lt_of_le j.isLt hi)

theorem next_direction (t : ℕ) : directions inf M v (t+1)=
    (fresh_exists inf (tests M (history inf M v t).dirs (history inf M v t).replies t)).choose := by
  simp [directions,history,advance]

private theorem fresh_at (t : ℕ) : ‖directions inf M v (t+1)‖=1 ∧
    ∀ w∈tests M (history inf M v t).dirs (history inf M v t).replies t,
      ⟪w,directions inf M v (t+1)⟫=0 := by
  rw [next_direction]
  exact (fresh_exists inf _).choose_spec

theorem directions_on (hv : ‖v‖=1) : Orthonormal ℝ (directions inf M v) := by
  classical
  constructor
  · intro j; cases j with
    | zero => exact hv
    | succ k => exact (fresh_at inf M v k).1
  · have orth (i j : ℕ) (lt : i<j) : ⟪directions inf M v i,directions inf M v j⟫=0 := by
      obtain ⟨t,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt lt)
      rw [←dirs_stable inf M v (Nat.lt_succ_iff.mp lt)]
      apply (fresh_at inf M v t).2
      exact mem_union_left _ (mem_union_left _ (mem_image_of_mem _ (mem_range.mpr lt)))
    intro i j ne
    rcases lt_or_gt_of_ne ne with h|h
    · exact orth i j h
    · rw [real_inner_comm (directions inf M v j)]; exact orth j i h

theorem captured_input {t j : ℕ} (lt : t<j) :
    ⟪(queryAt M (answers inf M v) t).snd,directions inf M v j⟫=0 ∧
    ⟪(outputAt M (answers inf M v) t).snd,directions inf M v j⟫=0 := by
  classical
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt lt)
  rw [←ask_stable inf M v (Nat.lt_succ_iff.mp lt),←out_stable inf M v (Nat.lt_succ_iff.mp lt)]
  constructor
  · exact (fresh_at inf M v n).2 _ (mem_union_left _ (mem_union_right _ (mem_image_of_mem _ (mem_range.mpr lt))))
  · exact (fresh_at inf M v n).2 _ (mem_union_right _ (mem_image_of_mem _ (mem_range.mpr lt)))

private theorem mean_eq {d e : ℕ → E} {k : ℕ} (h : ∀ i,i<k → d i=e i) : mean d k=mean e k :=
  sum_congr rfl (fun i hi => by rw [h i (mem_range.mp hi)])

private theorem atom_eq {d e : ℕ → E} {k : ℕ} (h : ∀ i,i ≤ k → d i=e i) : atom d k=atom e k := by
  rw [atom,atom,mean_eq (fun i hi => h i hi.le),h k le_rfl]

private theorem partial_eq {d e : ℕ → E} (k : ℕ) (h : ∀ i,i ≤ k → d i=e i) (q : World E) :
    partialReply v d k q=partialReply v e k q := by
  have a : finiteCoeff d k q=finiteCoeff e k q := by
    funext i; by_cases hi : i<k
    · simp [finiteCoeff,hi,atom_eq (fun j hj => h j (hj.trans hi.le)),mean_eq (fun i hi => h i hi.le)]
    · simp [finiteCoeff,hi]
  have c (u : ℕ → ℝ) : (∑ i ∈ range (k+1),u i • atom d i)=∑ i ∈ range (k+1),u i • atom e i :=
    sum_congr rfl (fun i hi => by rw [atom_eq (fun j hj => h j (hj.trans (Nat.lt_succ_iff.mp (mem_range.mp hi))))])
  simp only [partialReply,a,c]

theorem answers_rule (t : ℕ) : answers inf M v t =
    partialReply v (directions inf M v) (t+1) (-(queryAt M (answers inf M v) t)) := by
  have rule : answers inf M v t =
      partialReply v (history inf M v (t+1)).dirs (t+1) (-(queryAt M (history inf M v t).replies t)) := by
    simp [answers,history,advance]
  rw [rule,ask_stable inf M v (le_refl t)]
  exact partial_eq v _ (fun _ hi => dirs_stable inf M v hi) _

end Lemmata.FrankWolfePS.Hilbert.Anytime
