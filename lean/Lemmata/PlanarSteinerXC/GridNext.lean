module

public import Lemmata.PlanarSteinerXC.GridSlots

/-!
# The planar cyclic order of literal occurrences

For the product formula of the grid, the occurrences of a vertex variable `x_p` are the slots at
`p`: the gadget of the edge in direction `d` contributes the occurrences in clause `B` (or `C`)
and in clause `A`, in the slots `(d, false)` and `(d, true)`. The occurrences of an edge variable
`z_e` are cyclically ordered `C, A, B`. The permutation `next` runs through all of them.
-/

@[expose] public section

set_option autoImplicit false

namespace Lemmata.PlanarSteinerXC

namespace Grid

variable {h : ℕ}

/-- The oriented edge at a point in a present direction. -/
def edgeIn (p : Pt h) : (d : Dir) → present p d → OE h
  | .E, hp => ⟨(p, false), by simpa [present] using hp⟩
  | .N, hp => ⟨(p, true), by simpa [present] using hp⟩
  | .W, hp => ⟨((⟨p.1.val - 1, by have := p.1.isLt; lia⟩, p.2), false), by
      have h1 : 0 < p.1.val := hp
      have := p.1.isLt
      simp; lia⟩
  | .S, hp => ⟨((p.1, ⟨p.2.val - 1, by have := p.2.isLt; lia⟩), true), by
      have h1 : 0 < p.2.val := hp
      have := p.2.isLt
      simp; lia⟩

/-- The clause slot of the occurrence in slot `(d, b)`. -/
def kOf : Dir → Bool → Fin 7
  | .E, false => 3 | .E, true => 0
  | .N, false => 3 | .N, true => 0
  | .W, false => 1 | .W, true => 5
  | .S, false => 1 | .S, true => 5

/-- The occurrence in slot `(d, b)` at a point. -/
def occAt (p : Pt h) (d : Dir) (b : Bool) (hp : present p d) : OE h × Fin 7 :=
  (edgeIn p d hp, kOf d b)

/-- Occurrences of a vertex variable: `k ∈ {0, 1, 3, 5}`. -/
def IsX (o : OE h × Fin 7) : Prop := o.2 = 0 ∨ o.2 = 1 ∨ o.2 = 3 ∨ o.2 = 5

instance (o : OE h × Fin 7) : Decidable (IsX o) := by unfold IsX; infer_instance

/-- The point of a vertex-variable occurrence. -/
def ptOf (o : OE h × Fin 7) : Pt h := if o.2 = 0 ∨ o.2 = 3 then src o.1 else tgt o.1

/-- The direction of a vertex-variable occurrence. -/
def dirOf (o : OE h × Fin 7) : Dir :=
  if o.2 = 0 ∨ o.2 = 3 then (if o.1.1.2 then .N else .E) else (if o.1.1.2 then .S else .W)

/-- The position in the pair of a vertex-variable occurrence. -/
def bOf (o : OE h × Fin 7) : Bool := decide (o.2 = 0 ∨ o.2 = 5)

theorem present_of_isX {o : OE h × Fin 7} (ho : IsX o) : present (ptOf o) (dirOf o) := by
  obtain ⟨⟨⟨p, v⟩, hv⟩, k⟩ := o
  simp only [IsX] at ho
  cases v
  · have hh : p.1.val + 1 < h := by simpa using hv
    rcases ho with rfl | rfl | rfl | rfl
    · simpa [ptOf, dirOf, src, present] using hh
    · simp [ptOf, dirOf, tgt, present]
    · simpa [ptOf, dirOf, src, present] using hh
    · simp [ptOf, dirOf, tgt, present]
  · have hh : p.2.val + 1 < h := by simpa using hv
    rcases ho with rfl | rfl | rfl | rfl
    · simpa [ptOf, dirOf, src, present] using hh
    · simp [ptOf, dirOf, tgt, present]
    · simpa [ptOf, dirOf, src, present] using hh
    · simp [ptOf, dirOf, tgt, present]

theorem occAt_ptOf {o : OE h × Fin 7} (ho : IsX o) :
    occAt (ptOf o) (dirOf o) (bOf o) (present_of_isX ho) = o := by
  obtain ⟨⟨⟨p, v⟩, hv⟩, k⟩ := o
  simp only [IsX] at ho
  cases v <;> rcases ho with rfl | rfl | rfl | rfl <;>
    simp [occAt, ptOf, dirOf, bOf, edgeIn, kOf, src, tgt] <;>
    first
    | rfl
    | (ext <;> simp)

theorem isX_occAt (p : Pt h) (d : Dir) (b : Bool) (hp : present p d) : IsX (occAt p d b hp) := by
  cases d <;> cases b <;> simp [occAt, kOf, IsX]

theorem ptOf_occAt (p : Pt h) (d : Dir) (b : Bool) (hp : present p d) :
    ptOf (occAt p d b hp) = p := by
  cases d <;> cases b <;> simp [occAt, kOf, ptOf, edgeIn, src, tgt] <;>
    first
    | rfl
    | (ext <;> simp <;> (have : 0 < p.1.val := hp; lia))
    | (ext <;> simp <;> (have : 0 < p.2.val := hp; lia))

theorem dirOf_occAt (p : Pt h) (d : Dir) (b : Bool) (hp : present p d) :
    dirOf (occAt p d b hp) = d := by
  cases d <;> cases b <;> simp [occAt, kOf, dirOf, edgeIn]

theorem bOf_occAt (p : Pt h) (d : Dir) (b : Bool) (hp : present p d) :
    bOf (occAt p d b hp) = b := by
  cases d <;> cases b <;> simp [occAt, kOf, bOf]

theorem occAt_inj {p p' : Pt h} {d d' : Dir} {b b' : Bool} (hp : present p d)
    (hp' : present p' d') (heq : occAt p d b hp = occAt p' d' b' hp') : p = p' ∧ d = d' ∧ b = b' := by
  have h1 := ptOf_occAt p d b hp
  have h2 := dirOf_occAt p d b hp
  have h3 := bOf_occAt p d b hp
  rw [heq] at h1 h2 h3
  rw [ptOf_occAt] at h1; rw [dirOf_occAt] at h2; rw [bOf_occAt] at h3
  exact ⟨h1.symm, h2.symm, h3.symm⟩

/-! ### The permutation `next` -/

/-- The cyclic order `C → A → B → C` of the occurrences of an edge variable (`6 → 2 → 4`). -/
def zNext (k : Fin 7) : Fin 7 := if k = 2 then 4 else if k = 4 then 6 else if k = 6 then 2 else k
def zPrev (k : Fin 7) : Fin 7 := if k = 4 then 2 else if k = 6 then 4 else if k = 2 then 6 else k

variable (hh : 2 ≤ h)

/-- The next occurrence of the same variable. -/
def nextOcc (o : OE h × Fin 7) : OE h × Fin 7 :=
  if hx : IsX o then
    if bOf o = false then occAt (ptOf o) (dirOf o) true (present_of_isX hx)
    else occAt (ptOf o) (Dir.nextIn (pat (ptOf o)) (dirOf o)) false
      (pat_eq_true.mp (Dir.nextIn_present _ _ (pat_good hh _)))
  else (o.1, zNext o.2)

/-- The previous occurrence of the same variable. -/
def prevOcc (o : OE h × Fin 7) : OE h × Fin 7 :=
  if hx : IsX o then
    if bOf o = true then occAt (ptOf o) (dirOf o) false (present_of_isX hx)
    else occAt (ptOf o) (Dir.prevIn (pat (ptOf o)) (dirOf o)) true
      (pat_eq_true.mp (Dir.prevIn_present _ _ (pat_good hh _)))
  else (o.1, zPrev o.2)

theorem occAt_congr {p : Pt h} {d d' : Dir} (b : Bool) (hd : d = d') (hp : present p d)
    (hp' : present p d') : occAt p d b hp = occAt p d' b hp' := by
  subst hd; rfl

theorem not_isX_iff (o : OE h × Fin 7) : ¬ IsX o ↔ o.2 = 2 ∨ o.2 = 4 ∨ o.2 = 6 := by
  obtain ⟨e, k⟩ := o
  simp only [IsX]
  fin_cases k <;> simp

theorem occAt_eq_of {p p' : Pt h} {d d' : Dir} (b : Bool) (h1 : p = p') (h2 : d = d')
    (hp : present p d) (hp' : present p' d') : occAt p d b hp = occAt p' d' b hp' := by
  subst h1; subst h2; rfl

theorem nextOcc_occAt_false (p : Pt h) (d : Dir) (hp : present p d) :
    nextOcc hh (occAt p d false hp) = occAt p d true hp := by
  rw [nextOcc, dif_pos (isX_occAt p d false hp), if_pos (bOf_occAt p d false hp)]
  exact occAt_eq_of _ (ptOf_occAt p d false hp) (dirOf_occAt p d false hp) _ _

theorem nextOcc_occAt_true (p : Pt h) (d : Dir) (hp : present p d) :
    nextOcc hh (occAt p d true hp) = occAt p (Dir.nextIn (pat p) d) false
      (pat_eq_true.mp (Dir.nextIn_present _ _ (pat_good hh p))) := by
  rw [nextOcc, dif_pos (isX_occAt p d true hp), if_neg (by rw [bOf_occAt]; simp)]
  exact occAt_eq_of _ (ptOf_occAt p d true hp)
    (by rw [ptOf_occAt, dirOf_occAt]) _ _

theorem prevOcc_occAt_true (p : Pt h) (d : Dir) (hp : present p d) :
    prevOcc hh (occAt p d true hp) = occAt p d false hp := by
  rw [prevOcc, dif_pos (isX_occAt p d true hp), if_pos (bOf_occAt p d true hp)]
  exact occAt_eq_of _ (ptOf_occAt p d true hp) (dirOf_occAt p d true hp) _ _

theorem prevOcc_occAt_false (p : Pt h) (d : Dir) (hp : present p d) :
    prevOcc hh (occAt p d false hp) = occAt p (Dir.prevIn (pat p) d) true
      (pat_eq_true.mp (Dir.prevIn_present _ _ (pat_good hh p))) := by
  rw [prevOcc, dif_pos (isX_occAt p d false hp), if_neg (by rw [bOf_occAt]; simp)]
  exact occAt_eq_of _ (ptOf_occAt p d false hp)
    (by rw [ptOf_occAt, dirOf_occAt]) _ _

theorem zPrev_zNext {k : Fin 7} (hk : k = 2 ∨ k = 4 ∨ k = 6) : zPrev (zNext k) = k := by
  rcases hk with rfl | rfl | rfl <;> decide

theorem zNext_zPrev {k : Fin 7} (hk : k = 2 ∨ k = 4 ∨ k = 6) : zNext (zPrev k) = k := by
  rcases hk with rfl | rfl | rfl <;> decide

theorem zNext_mem {k : Fin 7} (hk : k = 2 ∨ k = 4 ∨ k = 6) :
    zNext k = 2 ∨ zNext k = 4 ∨ zNext k = 6 := by
  rcases hk with rfl | rfl | rfl <;> decide

theorem zPrev_mem {k : Fin 7} (hk : k = 2 ∨ k = 4 ∨ k = 6) :
    zPrev k = 2 ∨ zPrev k = 4 ∨ zPrev k = 6 := by
  rcases hk with rfl | rfl | rfl <;> decide

/-- Every vertex-variable occurrence is in some slot. -/
theorem exists_occAt {o : OE h × Fin 7} (ho : IsX o) :
    ∃ p d b hp, o = occAt p d b hp :=
  ⟨_, _, _, _, (occAt_ptOf ho).symm⟩

theorem prev_next (o : OE h × Fin 7) : prevOcc hh (nextOcc hh o) = o := by
  by_cases ho : IsX o
  · obtain ⟨p, d, b, hp, rfl⟩ := exists_occAt ho
    cases b
    · rw [nextOcc_occAt_false, prevOcc_occAt_true]
    · rw [nextOcc_occAt_true, prevOcc_occAt_false]
      exact occAt_eq_of _ rfl (Dir.prevIn_nextIn _ _ (pat_good hh p) (pat_eq_true.mpr hp)) _ _
  · have hz := (not_isX_iff o).mp ho
    have hnext : nextOcc hh o = (o.1, zNext o.2) := by rw [nextOcc, dif_neg ho]
    have hz' : ¬ IsX (o.1, zNext o.2) := (not_isX_iff _).mpr (zNext_mem hz)
    rw [hnext, prevOcc, dif_neg hz']
    simp [zPrev_zNext hz]

theorem next_prev (o : OE h × Fin 7) : nextOcc hh (prevOcc hh o) = o := by
  by_cases ho : IsX o
  · obtain ⟨p, d, b, hp, rfl⟩ := exists_occAt ho
    cases b
    · rw [prevOcc_occAt_false, nextOcc_occAt_true]
      exact occAt_eq_of _ rfl (Dir.nextIn_prevIn _ _ (pat_good hh p) (pat_eq_true.mpr hp)) _ _
    · rw [prevOcc_occAt_true, nextOcc_occAt_false]
  · have hz := (not_isX_iff o).mp ho
    have hprev : prevOcc hh o = (o.1, zPrev o.2) := by rw [prevOcc, dif_neg ho]
    have hz' : ¬ IsX (o.1, zPrev o.2) := (not_isX_iff _).mpr (zPrev_mem hz)
    rw [hprev, nextOcc, dif_neg hz']
    simp [zNext_zPrev hz]

/-- The cyclic order of occurrences as a permutation. -/
def nextPerm : Equiv.Perm (OE h × Fin 7) where
  toFun := nextOcc hh
  invFun := prevOcc hh
  left_inv := prev_next hh
  right_inv := next_prev hh

theorem nextPerm_apply (o : OE h × Fin 7) : nextPerm hh o = nextOcc hh o := rfl

/-- The variable of an occurrence. -/
theorem prodVar_eq_inl_iff (o : OE h × Fin 7) (p : Pt h) :
    prodVar src tgt o = .inl p ↔ IsX o ∧ ptOf o = p := by
  obtain ⟨e, k⟩ := o
  fin_cases k <;> simp [prodVar, IsX, ptOf]

theorem prodVar_eq_inr_iff (o : OE h × Fin 7) (e : OE h) :
    prodVar src tgt o = .inr e ↔ ¬ IsX o ∧ o.1 = e := by
  obtain ⟨e', k⟩ := o
  fin_cases k <;> simp [prodVar, IsX]

theorem var_nextPerm (o : OE h × Fin 7) :
    prodVar src tgt (nextPerm hh o) = prodVar src tgt o := by
  rw [nextPerm_apply]
  by_cases ho : IsX o
  · obtain ⟨p, d, b, hp, rfl⟩ := exists_occAt ho
    have h1 : prodVar src tgt (occAt p d b hp) = .inl p :=
      (prodVar_eq_inl_iff _ _).mpr ⟨isX_occAt p d b hp, ptOf_occAt p d b hp⟩
    cases b
    · rw [nextOcc_occAt_false, h1, (prodVar_eq_inl_iff _ _).mpr ⟨isX_occAt _ _ _ _, ptOf_occAt _ _ _ _⟩]
    · rw [nextOcc_occAt_true, h1, (prodVar_eq_inl_iff _ _).mpr ⟨isX_occAt _ _ _ _, ptOf_occAt _ _ _ _⟩]
  · have hz := (not_isX_iff o).mp ho
    have hnext : nextOcc hh o = (o.1, zNext o.2) := by rw [nextOcc, dif_neg ho]
    rw [hnext]
    have h1 : prodVar src tgt o = .inr o.1 := (prodVar_eq_inr_iff _ _).mpr ⟨ho, rfl⟩
    rw [h1, (prodVar_eq_inr_iff _ _).mpr ⟨(not_isX_iff _).mpr (zNext_mem hz), rfl⟩]

theorem nextPerm_pow_two_occAt_false (p : Pt h) (d : Dir) (hp : present p d) :
    (nextPerm hh ^ 2) (occAt p d false hp) = occAt p (Dir.nextIn (pat p) d) false
      (pat_eq_true.mp (Dir.nextIn_present _ _ (pat_good hh p))) := by
  rw [pow_two, Equiv.Perm.mul_apply, nextPerm_apply, nextPerm_apply, nextOcc_occAt_false,
    nextOcc_occAt_true]

/-- The cyclic order is cyclic on the occurrences of every variable. -/
theorem nextPerm_cyclic (o o' : OE h × Fin 7) (heq : prodVar src tgt o = prodVar src tgt o') :
    ∃ k : ℕ, (nextPerm hh ^ k) o = o' := by
  by_cases ho : IsX o
  · obtain ⟨p, d, b, hp, rfl⟩ := exists_occAt ho
    have h1 : prodVar src tgt (occAt p d b hp) = .inl p :=
      (prodVar_eq_inl_iff _ _).mpr ⟨isX_occAt p d b hp, ptOf_occAt p d b hp⟩
    rw [h1, eq_comm, prodVar_eq_inl_iff] at heq
    obtain ⟨ho', hpt⟩ := heq
    obtain ⟨p', d', b', hp', rfl⟩ := exists_occAt ho'
    rw [ptOf_occAt] at hpt
    have hpt' : p = p' := hpt.symm
    subst hpt'
    -- reduce to the case `b = false`
    have key : ∀ (d₀ : Dir) (hp₀ : present p d₀), ∃ k : ℕ,
        (nextPerm hh ^ k) (occAt p d₀ false hp₀) = occAt p d' b' hp' := by
      intro d₀ hp₀
      have hg := pat_good hh p
      have hstep : ∀ (m : ℕ) (d₁ : Dir) (hp₁ : present p d₁),
          (nextPerm hh ^ (2 * m)) (occAt p d₁ false hp₁) = occAt p ((Dir.nextIn (pat p))^[m] d₁) false
            (by
              induction m generalizing d₁ with
              | zero => simpa using hp₁
              | succ m ih =>
                rw [Function.iterate_succ_apply']
                exact pat_eq_true.mp (Dir.nextIn_present _ _ hg)) := by
        intro m
        induction m with
        | zero => intro d₁ hp₁; rfl
        | succ m ih =>
          intro d₁ hp₁
          rw [show 2 * (m + 1) = 2 + 2 * m by ring, pow_add, Equiv.Perm.mul_apply, ih,
            nextPerm_pow_two_occAt_false]
          exact occAt_eq_of _ rfl (by rw [Function.iterate_succ_apply']) _ _
      have hcases : ∃ m, d' = (Dir.nextIn (pat p))^[m] d₀ := by
        rcases Dir.nextIn_cyclic (pat p) d₀ d' hg (pat_eq_true.mpr hp₀) (pat_eq_true.mpr hp') with
          hm | hm | hm | hm
        · exact ⟨0, hm⟩
        · exact ⟨1, hm⟩
        · exact ⟨2, hm⟩
        · exact ⟨3, hm⟩
      obtain ⟨m, hm'⟩ := hcases
      cases b'
      · exact ⟨2 * m, (hstep m d₀ hp₀).trans (occAt_eq_of _ rfl hm'.symm _ _)⟩
      · refine ⟨2 * m + 1, ?_⟩
        rw [pow_succ', Equiv.Perm.mul_apply, hstep m d₀ hp₀, nextPerm_apply, nextOcc_occAt_false]
        exact occAt_eq_of _ rfl hm'.symm _ _
    cases b
    · exact key d hp
    · obtain ⟨k, hk⟩ := key (Dir.nextIn (pat p) d) (pat_eq_true.mp (Dir.nextIn_present _ _
        (pat_good hh p)))
      refine ⟨k + 1, ?_⟩
      rw [pow_succ, Equiv.Perm.mul_apply, nextPerm_apply, nextOcc_occAt_true]
      exact hk
  · have hz := (not_isX_iff o).mp ho
    have h1 : prodVar src tgt o = .inr o.1 := (prodVar_eq_inr_iff _ _).mpr ⟨ho, rfl⟩
    rw [h1, eq_comm, prodVar_eq_inr_iff] at heq
    obtain ⟨ho', he⟩ := heq
    have hz' := (not_isX_iff o').mp ho'
    obtain ⟨e, k⟩ := o
    obtain ⟨e', k'⟩ := o'
    simp only at he hz hz'
    have he' := he.symm
    subst he'
    have hn : ∀ k₀ : Fin 7, ¬ IsX (e, k₀) → nextPerm hh (e, k₀) = (e, zNext k₀) := by
      intro k₀ hk₀; rw [nextPerm_apply, nextOcc, dif_neg hk₀]
    rcases hz with rfl | rfl | rfl <;> rcases hz' with rfl | rfl | rfl
    all_goals first
      | exact ⟨0, rfl⟩
      | exact ⟨1, by rw [pow_one, hn _ (by simp [IsX])]; rfl⟩
      | exact ⟨2, by rw [pow_two, Equiv.Perm.mul_apply, hn _ (by simp [IsX]), hn _ (by simp [IsX, zNext])]; rfl⟩

end Grid

end Lemmata.PlanarSteinerXC
