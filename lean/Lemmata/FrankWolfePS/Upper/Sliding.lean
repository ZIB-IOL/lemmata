module

public import Lemmata.FrankWolfePS.Upper.Product
public import Lemmata.FrankWolfePS.Upper.Outer
public import Lemmata.FrankWolfePS.Upper.Main
@[expose] public section

namespace Lemmata.FrankWolfePS.Upper
open scoped RealInnerProductSpace Classical
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

structure SlideState (E : Type*) where
  x : Pair E
  y : Pair E
  slots : ℕ
  gradients : ℕ

noncomputable def advance (oracle grad : E → E) (ℓ A δ r : ℝ) (j : ℕ)
    (s : SlideState E) : SlideState E :=
  let z := blend (gamma j) s.y s.x
  let a := productInner oracle (grad (total z)) s.x (tau ℓ j) δ (eta ℓ A j) r
  ⟨a.1, blend (gamma j) s.y a.1, s.slots + a.2, s.gradients + 1⟩

noncomputable def slideRun (oracle grad : E → E) (ℓ A δ r : ℝ) (p : E) : ℕ → SlideState E
  | 0 => ⟨pair p 0, pair p 0, 0, 0⟩
  | j + 1 => advance oracle grad ℓ A δ r (j + 1) (slideRun oracle grad ℓ A δ r p j)

theorem advance_spec {K : Set E} (hK : Convex ℝ K) (O : LMO K)
    {r L δ A : ℝ} (hr : 0 ≤ r) (hL : 0 < L) (hA : 0 < A)
    (width : ∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ ≤ δ) {f : E → ℝ} {g : E → E}
    (mdl : Models (Rounded K r) f g L) (s : SlideState E) (hx : s.x ∈ domain K r)
    (hy : s.y ∈ domain K r) {j : ℕ} (hj : 0 < j) :
    let ℓ := 2 * L
    let v := advance O.query g ℓ A δ r j s
    v.x ∈ domain K r ∧ v.y ∈ domain K r ∧
    (v.slots : ℝ) ≤ s.slots + 1 + 18 * (j : ℝ) * δ ^ 2 / A ∧ v.gradients = s.gradients + 1 ∧
    ∀ w ∈ domain K r, f (total v.y) - f (total w) ≤
      (1 - gamma j) * (f (total s.y) - f (total w)) + gamma j * eta ℓ A j +
      gamma j * tau ℓ j / 2 * (‖s.x - w‖ ^ 2 - ‖v.x - w‖ ^ 2) := by
  let ℓ := 2 * L
  have hl : 0 < ℓ := by dsimp [ℓ]; positivity
  obtain ⟨hg, hg', hmajor, ht, he⟩ := sliding_parameters hl hA hj
  let z := blend (gamma j) s.y s.x
  let inn := productInner O.query (g (total z)) s.x (tau ℓ j) δ (eta ℓ A j) r
  obtain ⟨hm, hgap, hcost⟩ := productInner_spec hK O hr ht he width (g (total z)) s.x hx
  change inn.1 ∈ domain K r at hm
  have cc := domain_convex hK r
  refine ⟨hm, blend_mem cc hg.le hg' hy hm, ?_, rfl, ?_⟩
  · change ((s.slots + inn.2 : ℕ) : ℝ) ≤ _
    rw [Nat.cast_add]
    have id : 6 * tau ℓ j * δ ^ 2 / eta ℓ A j = 18 * (j : ℝ) * δ ^ 2 / A := by
      have hp : 0 < (j : ℝ) := by exact_mod_cast hj
      unfold tau eta; field_simp; ring
    rw [id] at hcost
    change (inn.2 : ℝ) ≤ _ at hcost
    linarith
  · intro w hw
    exact sliding_step cc (product_models hL.le mdl) hx hy hm hw hg.le hg' hmajor (hgap w hw)

theorem slideRun_bounds {K : Set E} (hK : Convex ℝ K) (O : LMO K)
    {r L δ : ℝ} (hr : 0 < r) (hL : 0 < L) (width : ∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ ≤ δ)
    {f : E → ℝ} {g : E → E} (mdl : Models (Rounded K r) f g L) {p : E} (hp : p ∈ K)
    {n : ℕ} (hn : 0 < n) :
    let A := δ ^ 2 + 4 * r ^ 2
    let S := slideRun O.query g (2 * L) A δ r p
    (S n).y ∈ domain K r ∧ (S n).gradients = n ∧
    ((S n).slots : ℝ) ≤ n + 9 * δ ^ 2 * (n : ℝ) * ((n : ℝ) + 1) / A ∧
    (∀ j, total (blend (gamma (j + 1)) (S j).y (S j).x) ∈ Rounded K r) ∧
    ∀ w ∈ domain K r, f (total (S n).y) - f (total w) ≤
      15 * (2 * L) * A / (2 * ((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
  let A := δ ^ 2 + 4 * r ^ 2
  let S := slideRun O.query g (2 * L) A δ r p
  have hA : 0 < A := by dsimp [A]; positivity
  have init : pair p 0 ∈ domain K r := ⟨hp, by simpa [pair] using hr.le⟩
  have mem (i : ℕ) : (S i).x ∈ domain K r ∧ (S i).y ∈ domain K r := by
    induction i with
    | zero => exact ⟨init, init⟩
    | succ j ih =>
      have h := advance_spec hK O hr.le hL hA width mdl (S j) ih.1 ih.2 (Nat.zero_lt_succ j)
      exact ⟨h.1, h.2.1⟩
  have st (j : ℕ) :=
      advance_spec hK O hr.le hL hA width mdl (S j) (mem j).1 (mem j).2 (Nat.zero_lt_succ j)
  have grads (i : ℕ) : (S i).gradients = i := by
    induction i with
    | zero => rfl
    | succ j ih => exact (st j).2.2.2.1.trans (congrArg (fun k => k + 1) ih)
  refine ⟨(mem n).2, grads n, sliding_count (fun j => (S j).slots) rfl ?_ n, ?_, ?_⟩
  · intro j
    have h := (st j).2.2.1
    rw [Nat.cast_succ] at h
    exact h
  · intro j
    have par := sliding_parameters (show 0 < 2 * L by positivity) hA (Nat.zero_lt_succ j)
    exact total_mem (blend_mem (domain_convex hK r) par.1.le par.2.1 (mem j).2 (mem j).1)
  · intro w hw
    exact sliding_rate (show 0 ≤ 2 * L by positivity) (fun j => f (total (S j).y) - f (total w))
      (fun j => ‖(S j).x - w‖ ^ 2) (fun _ => _root_.sq_nonneg _)
      (fun j => product_width width _ (mem j).1 _ hw) (fun j => (st j).2.2.2.2 w hw) hn

/-- **Conditional gradient sliding on `K × B_r`.** It uses only the LMO `O`, the gradient `g` and
the parameters. It returns the final point, the number of LMO calls (including one initial
call) and the number of gradient evaluations. -/
noncomputable def slidingRun {C : Set E} (O : LMO C) (g : E → E) (L r D : ℝ)
    (e : E) (n : ℕ) : E × ℕ × ℕ :=
  let p := unwrap O r e
  let δ := D - 2 * r
  let inner := fun q => if q = 0 then p else unwrap O r q
  let s := slideRun inner g (2 * L) (δ ^ 2 + 4 * r ^ 2) δ r p n
  (total s.y, 1 + s.slots, s.gradients)

theorem sliding_parallel_upper {K : Set E} (hK : Convex ℝ K)
    {r L D : ℝ} (hr : 0 < r) (hL : 0 < L) (hD : 2 * r ≤ D)
    (width : ∀ x ∈ Rounded K r, ∀ y ∈ Rounded K r, ‖x - y‖ ≤ D)
    (O : LMO (Rounded K r)) {f : E → ℝ} {g : E → E} (mdl : Models (Rounded K r) f g L)
    (e : E) (he : e ≠ 0) {n : ℕ} (hn : 0 < n) :
    let δ := D - 2 * r
    let A := δ ^ 2 + 4 * r ^ 2
    let ans := slidingRun O g L r D e n
    ans.1 ∈ Rounded K r ∧ ans.2.2 = n ∧
    (ans.2.1 : ℝ) ≤ 1 + n + 9 * δ ^ 2 * (n : ℝ) * ((n : ℝ) + 1) / A ∧
    ∀ w ∈ Rounded K r, f ans.1 - f w ≤ 15 * (2 * L) * A / (2 * ((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
  let p := unwrap O r e
  have hp := (unwrap_spec hr O he).1
  let V := coreLMO hr O p hp
  let δ := D - 2 * r
  let A := δ ^ 2 + 4 * r ^ 2
  let S := slideRun V.query g (2 * L) A δ r p n
  obtain ⟨hm, hg, hc, _, rate⟩ := slideRun_bounds hK V hr hL (fun _ hx _ hy =>
      core_width hr hD width hx hy) mdl hp hn
  change S.y ∈ domain K r at hm
  change (S.slots : ℝ) ≤ _ at hc
  refine ⟨total_mem hm, hg, ?_, ?_⟩
  · change ((1 + S.slots : ℕ) : ℝ) ≤ _
    push_cast; linarith only [hc]
  · rintro w ⟨a, ha, hw⟩
    have hv : pair a (w - a) ∈ domain K r := ⟨ha, hw⟩
    have h := rate (pair a (w - a)) hv
    change f (total S.y) - f (a + (w - a)) ≤ _ at h
    rw [add_sub_cancel] at h
    exact h

end Lemmata.FrankWolfePS.Upper
