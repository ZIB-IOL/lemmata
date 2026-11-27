module
public import Lemmata.FrankWolfePS.Unique.Tests
public import Lemmata.FrankWolfePS.Unique.Local
@[expose] public section
namespace Lemmata.FrankWolfePS.Unique
open Finset
open scoped BigOperators RealInnerProductSpace
variable {ι : Type*} [Fintype ι] [LinearOrder ι] {Q : ℕ}
abbrev Hist (ι : Type*) [Fintype ι] := List (Ambient ι)
def extendR (R : Finset ι) : Option ι → Finset ι
  | none => R
  | some i => insert i R
omit [Fintype ι] in
theorem extend_subset (R : Finset ι) (i : Option ι) : R ⊆ extendR R i := by
  cases i <;> simp [extendR]

noncomputable def scanOrder (v : ι → Ambient ι) (q : Ambient ι) : List ι :=
  if q = 0 then [] else listing (rankOrder inferInstance (fun j => ⟪unit q, v j⟫))

noncomputable def child (A : ℝ) (a : ι) (b s : ℝ) (start : Ambient ι) (ask : Hist ι → Ambient ι)
    (R : Finset ι) (h : Table ι Q → Hist ι) (i : Option ι) (D : Table ι Q) : Hist ι :=
  reply (Body (vertices A a b D) s (extendR R i)) start (ask (h D)) :: h D

theorem child_local (A : ℝ) (a : ι) (b s : ℝ) (start : Ambient ι) (ask : Hist ι → Ambient ι)
    {R : Finset ι} {h : Table ι Q → Hist ι} (loc : Local R h) (i : Option ι) :
    Local (extendR R i) (child A a b s start ask R h i) := by
  intro D F agree
  have ee := loc D F (fun j hj => agree j (extend_subset R i hj))
  have eb := body_congr s (fun j hj => vertex_same A a b (agree j hj))
  simp [child, ee, eb]

noncomputable def trouble (A : ℝ) (a : ι) (b s : ℝ) (start : Ambient ι) (ask : Hist ι → Ambient ι) :
    ℕ → Finset ι → (Table ι Q → Hist ι) → Table ι Q → Prop
  | 0, _, _, _ => False
  | t + 1, R, h, D => (∃ k, Test A a b s R (fun F => ask (h F)) k D) ∨
      ∃ i, trouble A a b s start ask t (extendR R i) (child A a b s start ask R h i) D

def nodes (ι : Type*) [Fintype ι] : ℕ → ℕ
  | 0 => 0
  | t + 1 => 1 + Fintype.card (Option ι) * nodes ι t

theorem trouble_count (A : ℝ) (a : ι) {b s : ℝ} (hb : 0 ≤ b) (small : (dim ι : ℝ) * (4 * s) < b)
    (start : Ambient ι) (ask : Hist ι → Ambient ι) (t : ℕ) {R : Finset ι} (ha : a ∈ R)
    {h : Table ι Q → Hist ι} (loc : Local R h) :
    countP (trouble A a b s start ask t R h) * (Q : ℝ) ≤
        (nodes ι t : ℝ) * (tests ι : ℝ) * Fintype.card (Table ι Q) := by
  induction t generalizing R h with
  | zero => simp [trouble, nodes, count_false]
  | succ t ih =>
    let N := fun D => ∃ k, Test A a b s R (fun F => ask (h F)) k D
    let B := fun i => trouble A a b s start ask t (extendR R i) (child A a b s start ask R h i)
    have hU := mul_le_mul_of_nonneg_right (count_union N (fun D => ∃ i, B i D)) (Nat.cast_nonneg Q)
    have E := mul_le_mul_of_nonneg_right (count_exists B) (Nat.cast_nonneg Q)
    rw [add_mul] at hU; rw [sum_mul] at E
    have root := node_count A a hb small ha (q := fun F => ask (h F)) (fun D F e =>
        congrArg ask (loc D F e))
    have branches := sum_le_sum (s := (univ : Finset (Option ι))) (fun i _ =>
        ih (extend_subset R i ha) (child_local A a b s start ask loc i))
    change (∑ i, countP (B i) * (Q : ℝ)) ≤ _ at branches
    simp only [sum_const, card_univ, nsmul_eq_mul] at branches
    change countP N * (Q : ℝ) ≤ _ at root
    change countP (fun D => N D ∨ ∃ i, B i D) * (Q : ℝ) ≤ _
    simp only [nodes, Nat.cast_add, Nat.cast_one, Nat.cast_mul]
    linarith only [hU, E, branches, root]

noncomputable def simulate (A : ℝ) (a : ι) (b s : ℝ) (start : Ambient ι) (ask : Hist ι → Ambient ι)
    (out : Hist ι → Pt ι) (D : Table ι Q) : (t : ℕ) → Finset ι → Hist ι → Orders ι (Pt ι) t
    | 0, _, h => .ret (out h)
    | t + 1, R, h => .ask (scanOrder (vertices A a b D) (ask h)) (fun i =>
      simulate A a b s start ask out D t (extendR R i)
        (child A a b s start ask R (fun _ => h) i D))

noncomputable def play {E : Type*} (oracle : E → E) (ask : List E → E) : ℕ → List E → List E
  | 0, h => h
  | t + 1, h => play oracle ask t (oracle (ask h)::h)

theorem replay (A : ℝ) (a : ι) {b s : ℝ} (hs : 0 < s) (start : Ambient ι) (ask : Hist ι → Ambient ι)
    (out : Hist ι → Pt ι) (I : Finset ι) (D : Table ι Q)
    (anchor : ∀ R : Finset ι, a ∈ R → start ∈ Body (vertices A a b D) s R)
    (t : ℕ) {R : Finset ι} (ha : a ∈ R) (sub : R ⊆ I) {h : Table ι Q → Hist ι}
    (ok : ¬trouble A a b s start ask t R h D) :
    (simulate A a b s start ask out D t R (h D)).run I =
    out (play (reply (Body (vertices A a b D) s I) start) ask t (h D)) := by
  induction t generalizing R h with
  | zero => rfl
  | succ t ih =>
    let v := vertices A a b D
    let q := ask (h D)
    let i := first I (scanOrder v q)
    have clear : ¬∃ k, Test A a b s R (fun F => ask (h F)) k D := fun e => ok (Or.inl e)
    have tail : ¬trouble A a b s start ask t (extendR R i) (child A a b s start ask R h i) D :=
      fun e => ok (Or.inr ⟨i, e⟩)
    have branch : extendR R i ⊆ I ∧ reply (Body v s I) start q =
        reply (Body v s (extendR R i)) start q := by
      by_cases z : q = 0
      · have ei : i = none := by simp [i, scanOrder, z, first]
        simp [ei, extendR, z, reply, sub]
      · obtain ⟨win, winI, ef, hm⟩ := first_rank_spec (fun j => ⟪unit q, v j⟫) ⟨a, sub ha⟩
        have ei : i = some win := by simpa [i, scanOrder, z] using ef
        rw [ei]; change insert win R ⊆ I ∧ _
        have sub' := insert_subset winI sub
        refine ⟨sub',
            reply_local hs sub' (anchor _ (mem_insert_of_mem ha)) z (mem_insert_self win R) ?_⟩
        intro j hj hjR
        have ne : win ≠ j := by rintro rfl; exact hjR (mem_insert_self _ _)
        have jr : j ∉ R := fun e => hjR (mem_insert_of_mem e)
        have le := (hm j hj).1
        by_contra! near
        obtain ⟨c, hc⟩ := large_coordinate (unit q) (norm_unit z)
        apply clear
        refine ⟨(win, j, c), jr, ne, z, hc, ?_⟩
        change |⟪unit q, v win⟫ - ⟪unit q, v j⟫| ≤ 2 * s
        rw [abs_of_nonpos (sub_nonpos.mpr le)]; linarith
    have H := ih (extend_subset R i ha) branch.1 tail
    change (simulate A a b s start ask out D t (extendR R i)
        (child A a b s start ask R h i D)).run I =
      out (play (reply (Body v s I) start) ask t (reply (Body v s I) start q::h D))
    rw [H]; unfold child; rw [branch.2]

end Lemmata.FrankWolfePS.Unique
