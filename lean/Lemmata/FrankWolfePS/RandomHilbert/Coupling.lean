module
public import Lemmata.FrankWolfePS.RandomHilbert.Estimation
/-! Finite jitter, cylinder counting and exact adaptive transcript coupling. -/
@[expose] public section
namespace Lemmata.FrankWolfePS.RandomHilbert
open Finset _root_.Lemmata.FrankWolfePS.Unique
open scoped BigOperators
variable {ι X : Type*} [Fintype ι] [LinearOrder ι] {Q : ℕ}

abbrev Grid (ι : Type*) (Q : ℕ) := ι → Fin Q
def levels (ι : Type*) [Fintype ι] (T : ℕ) := 1+100*(nodes ι T)*(Fintype.card ι)^2
instance (ι : Type*) [Fintype ι] (T : ℕ) : NeZero (levels ι T) := ⟨by unfold levels; omega⟩
noncomputable def noise (a : ι) (b : ℝ) (D : Grid ι Q) (i : ι) : ℝ :=
  if i=a then 0 else b*(D i).val

def depends (R : Finset ι) (f : Grid ι Q → X) := ∀ D F,(∀ i∈R,D i=F i) → f D=f F

/-- Each fiber of a near tie contains at most one grid value of the unrevealed label. -/
theorem pair_count (a : ι) {b s : ℝ} (sep : 4*s<b) (bp : 0≤b)
    {R : Finset ι} (ha : a∈R) {f : Grid ι Q → ι → ℝ} (loc : depends R f) (i j : ι) :
    countP (fun D => j∉R ∧ i≠j ∧ |(f D i-noise a b D i)-(f D j-noise a b D j)|≤2*s) *
        (Q:ℝ) ≤ Fintype.card (Grid ι Q) := by
  classical
  have H := fiber_count j (fun D : Grid ι Q =>
    j∉R ∧ i≠j ∧ |(f D i-noise a b D i)-(f D j-noise a b D j)|≤2*s) (by
    intro D F hd hf eq
    have same := loc D F (fun l hl => eq l (by rintro rfl; exact hd.1 hl))
    have hj : j≠a := by rintro rfl; exact hd.1 ha
    have hi : noise a b D i=noise a b F i := by simp only [noise,eq i hd.2.1]
    have h1 := abs_le.mp hd.2.2
    have h2 := abs_le.mp hf.2.2
    rw [← same,← hi] at h2
    simp only [noise,ite_eq_right hj] at h1 h2
    apply Fin.ext; by_contra ne
    rcases lt_or_gt_of_ne ne with lt | gt
    · have one : ((D j).val:ℝ)+1 ≤ (F j).val := by exact_mod_cast lt
      nlinarith only [mul_le_mul_of_nonneg_left one bp,h1.1,h2.2,sep,h1.2,h2.1]
    · have one : ((F j).val:ℝ)+1 ≤ (D j).val := by exact_mod_cast gt
      nlinarith only [mul_le_mul_of_nonneg_left one bp,h1.1,h2.2,sep,h1.2,h2.1])
  simpa using H

structure Scanner (ι X : Type*) [Fintype ι] [LinearOrder ι] (Q : ℕ) where
  anchor : ι
  step : ℝ
  bulge : ℝ
  score : X → ι → ℝ
  reply : Finset ι → Grid ι Q → X → X
  localReply : ∀ R : Finset ι, ∀ q, depends R (fun D => reply R D q)
  restrictReply : ∀ {R I : Finset ι} {D : Grid ι Q} {q : X} {i : ι}, anchor∈R → R⊆I → i∈R →
    (∀ j∈I,j∉R → score q i-noise anchor step D i+2*bulge < score q j-noise anchor step D j) →
    reply I D q=reply R D q

namespace Scanner
variable (S : Scanner ι X Q) (ask : List X → X)

private noncomputable def scoreAt (D : Grid ι Q) (q : X) (i : ι) := S.score q i-noise S.anchor S.step D i

private def child (R : Finset ι) (h : Grid ι Q → List X) (i : Option ι) (D : Grid ι Q) :=
  S.reply (extendR R i) D (ask (h D))::h D

private theorem child_dep {R : Finset ι} {h : Grid ι Q → List X} (loc : depends R h) (i : Option ι) :
    depends (extendR R i) (S.child ask R h i) := by
  intro D F agree
  have e := loc D F (fun j hj => agree j (extend_subset R i hj))
  simp only [child,e,S.localReply _ _ D F agree]

private def hit (R : Finset ι) (h : Grid ι Q → List X) (j : ι × ι) (D : Grid ι Q) :=
  j.2∉R ∧ j.1≠j.2 ∧ |S.scoreAt D (ask (h D)) j.1-S.scoreAt D (ask (h D)) j.2|≤2*S.bulge

private def trouble : ℕ → Finset ι → (Grid ι Q → List X) → Grid ι Q → Prop
  | 0,_,_,_ => False
  | t+1,R,h,D => (∃ j,S.hit ask R h j D) ∨ ∃ i,trouble t (extendR R i) (S.child ask R h i) D

private theorem count_trouble (bp : 0≤S.step) (gap : 4*S.bulge<S.step) (t : ℕ)
    {R : Finset ι} (ha : S.anchor∈R) {h : Grid ι Q → List X} (loc : depends R h) :
    countP (S.trouble ask t R h)*(Q:ℝ) ≤
      (nodes ι t:ℝ)*(Fintype.card ι:ℝ)^2 * Fintype.card (Grid ι Q) := by
  induction t generalizing R h with
  | zero => simp [trouble,nodes,count_false]
  | succ t ih =>
    let N := fun D => ∃ j,S.hit ask R h j D
    let B := fun i => S.trouble ask t (extendR R i) (S.child ask R h i)
    have root := mul_le_mul_of_nonneg_right (count_exists (S.hit ask R h)) (Nat.cast_nonneg Q)
    rw [sum_mul] at root
    have pair (j : ι × ι) : countP (S.hit ask R h j)*(Q:ℝ) ≤ Fintype.card (Grid ι Q) :=
      pair_count S.anchor gap bp ha (f:=fun D => S.score (ask (h D)))
        (fun D F e => congrArg (fun l => S.score (ask l)) (loc D F e)) j.1 j.2
    have root' := sum_le_sum (s:=(univ:Finset (ι×ι))) (fun j _ => pair j)
    have comb := mul_le_mul_of_nonneg_right (count_union N (fun D => ∃ i,B i D)) (Nat.cast_nonneg Q)
    rw [add_mul] at comb
    have ex := mul_le_mul_of_nonneg_right (count_exists B) (Nat.cast_nonneg Q)
    rw [sum_mul] at ex
    have tails := sum_le_sum (s:=(univ:Finset (Option ι))) (fun i _ =>
      ih (extend_subset R i ha) (S.child_dep ask loc i))
    change ∑ i,countP (B i)*(Q:ℝ) ≤ _ at tails
    simp only [sum_const,card_univ,Fintype.card_prod,Nat.cast_mul,nsmul_eq_mul] at root' tails
    change countP N*(Q:ℝ)≤_ at root
    change countP (fun D => N D ∨ ∃ i,B i D)*(Q:ℝ)≤_
    simp only [nodes,Nat.cast_add,Nat.cast_one,Nat.cast_mul]
    nlinarith only [comb,ex,tails,root,root']

private noncomputable def tree (out : List X → Pt ι) (D : Grid ι Q) :
    (t : ℕ) → Finset ι → List X → Orders ι (Pt ι) t
  | 0,_,h => .ret (out h)
  | t+1,R,h => .ask (listing (rankOrder inferInstance (S.scoreAt D (ask h)))) (fun i =>
    tree out D t (extendR R i) (S.child ask R (fun _ => h) i D))

private theorem replay (out : List X → Pt ι) (D : Grid ι Q) (I : Finset ι) (t : ℕ)
    {R : Finset ι} (ha : S.anchor∈R) (sub : R⊆I) {h : Grid ι Q → List X}
    (ok : ¬S.trouble ask t R h D) :
    (S.tree ask out D t R (h D)).run I=out (play (S.reply I D) ask t (h D)) := by
  induction t generalizing R h with
  | zero => rfl
  | succ t ih =>
    let q := ask (h D)
    obtain ⟨i,hi,win,hm⟩ := first_rank_spec (S.scoreAt D q) ⟨S.anchor,sub ha⟩
    let R' := insert i R
    have me : S.reply I D q=S.reply R' D q := by
      apply S.restrictReply (mem_insert_of_mem ha) (insert_subset hi sub) (mem_insert_self _ _)
      intro j hj hno
      have hlt := (hm j hj).1
      change S.scoreAt D q i+2*S.bulge < S.scoreAt D q j
      by_contra! near
      apply ok (Or.inl ⟨(i,j), ?_,?_,?_⟩)
      · exact fun h => hno (mem_insert_of_mem h)
      · change i≠j; rintro rfl; exact hno (mem_insert_self _ _)
      · change |S.scoreAt D q i-S.scoreAt D q j| ≤ _
        rw [abs_of_nonpos (sub_nonpos.mpr hlt)]; linarith
    have tail := ih (extend_subset R (some i) ha) (show extendR R (some i)⊆I from insert_subset hi sub)
      (h:=S.child ask R h (some i)) (fun bad => ok (Or.inr ⟨some i,bad⟩))
    simp only [tree,Orders.run,play]; change _ = out (play _ ask t (S.reply I D q :: h D))
    rw [show first I (listing (rankOrder inferInstance (S.scoreAt D (ask (h D)))))=some i from win, me]
    exact tail

/-- On a uniform hidden set and an independent finite jitter table, even an arbitrary
transcript estimator misses the hidden barycenter on at least six twenty-fifths of the pairs. -/
theorem estimation {T : ℕ} (S : Scanner ι X (levels ι T)) (ask : List X → X) (out : List X → Pt ι)
    (bp : 0≤S.step) (gap : 4*S.bulge<S.step) (size : Fintype.card ι=256*(T+1)) :
    let H := instanceSets T S.anchor
    let E := fun (D : Grid ι (levels ι T)) (J : Finset ι) =>
      let I := insert S.anchor J
      1/(128*((T+1:ℕ):ℝ)) ≤ sq (fun i =>
        (out (play (S.reply I D) ask T [])).1 i-simplexBarycenter I i)
    (Fintype.card (Grid ι (levels ι T)):ℝ)*(H.card:ℝ)*6/25 ≤ ∑ D,∑ J∈H,flag (E D J) := by
  classical
  dsimp only
  let H := instanceSets T S.anchor
  let B := S.trouble ask T {S.anchor} (fun _ => [])
  let E := fun (D : Grid ι (levels ι T)) (J : Finset ι) =>
    let I := insert S.anchor J
    1/(128*((T+1:ℕ):ℝ)) ≤ sq (fun i => (out (play (S.reply I D) ask T [])).1 i-simplexBarycenter I i)
  let M : ℝ := Fintype.card (Grid ι (levels ι T))
  have one (D) : (H.card:ℝ)/4 ≤ ∑ J∈H,flag (E D J)+(H.card:ℝ)/4*flag (B D) := by
    by_cases no : B D
    · simp [flag,no]
    · simp only [flag,ite_eq_right no,mul_zero,add_zero]
      have e := finite_estimation T S.anchor size (S.tree ask out D T {S.anchor} [])
      apply e.trans; apply sum_le_sum; intro J _
      have eq := S.replay ask out D (insert S.anchor J) T (R:={S.anchor}) (mem_singleton_self _)
        (singleton_subset_iff.mpr (mem_insert_self _ _)) (h:=fun _ => []) no
      simp [eq,E,flag]
  have all := sum_le_sum (s:=(univ:Finset (Grid ι (levels ι T)))) (fun D _ => one D)
  rw [sum_add_distrib,← mul_sum] at all
  simp only [sum_const,card_univ,nsmul_eq_mul] at all
  change M*((H.card:ℝ)/4) ≤ _ + (H.card:ℝ)/4*countP B at all
  have bar := S.count_trouble ask bp gap T (mem_singleton_self S.anchor) (h:=fun _=>[]) (fun _ _ _ => rfl)
  let W : ℝ := (nodes ι T:ℝ)*(Fintype.card ι:ℝ)^2
  have eq : (levels ι T:ℝ)=1+100*W := by simp [levels,W]; ring
  change countP B*(levels ι T:ℝ) ≤ W*M at bar
  rw [eq] at bar
  have cb : 0≤countP B := sum_nonneg (fun _ _ => flag_nonneg _)
  have bar' : countP B ≤ M/100 := by
    by_cases z : W=0
    · rw [z] at bar; simp at bar; exact bar.trans (by dsimp [M]; positivity)
    · have wp : 0<W := lt_of_le_of_ne (by dsimp [W]; positivity) (Ne.symm z)
      by_contra! no; nlinarith only [bar,cb,mul_pos wp (sub_pos.mpr no)]
  change M*(H.card:ℝ)*6/25 ≤ ∑ D,∑ J∈H,flag (E D J)
  nlinarith only [all,mul_le_mul_of_nonneg_left bar' (by positivity : 0≤(H.card:ℝ)/4),
    mul_nonneg (by dsimp [M]; positivity : 0≤M) (Nat.cast_nonneg H.card)]
end Scanner
end Lemmata.FrankWolfePS.RandomHilbert
