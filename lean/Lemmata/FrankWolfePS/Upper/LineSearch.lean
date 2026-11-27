module

public import Lemmata.FrankWolfePS.Upper.Inner
@[expose] public section

namespace Lemmata.FrankWolfePS.Upper
open scoped RealInnerProductSpace Classical
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def lineFraction (G H : ℝ) : ℝ := if H ≤ G then 1 else G / H
theorem lineFraction_spec {G H : ℝ} (hG : 0 ≤ G) (hH : 0 ≤ H) :
    let u := lineFraction G H
    0 ≤ u ∧ u ≤ 1 ∧ ∀ t : ℝ, 0 ≤ t → t ≤ 1 → -u * G + H / 2 * u ^ 2 ≤ -t * G + H / 2 * t ^ 2 := by
  unfold lineFraction
  split
  · next h =>
      refine ⟨by norm_num, le_rfl, fun t _ ht => ?_⟩
      have m := mul_nonneg (sub_nonneg.mpr ht) (sub_nonneg.mpr h)
      nlinarith [mul_nonneg hH (_root_.sq_nonneg (1 - t))]
  · next h =>
      have hp : 0 < H := hG.trans_lt (lt_of_not_ge h)
      refine ⟨div_nonneg hG hH, (div_le_one hp).mpr (le_of_lt (lt_of_not_ge h)), fun t _ _ => ?_⟩
      have eq : (-t * G + H / 2 * t ^ 2) - (-(G / H) * G + H / 2 * (G / H) ^ 2) =
          H / 2 * (t - G / H) ^ 2 := by field_simp; ring
      linarith only [eq, mul_nonneg (show 0 ≤ H / 2 by positivity) (_root_.sq_nonneg (t - G / H))]

noncomputable def lineMove (g : E → E) (τ : ℝ) (x v : E) :=
  blend (lineFraction ⟪g x, x - v⟫ (τ * ‖v - x‖ ^ 2)) x v

theorem lineMove_spec {K : Set E} (hK : Convex ℝ K) (O : LMO K) {τ : ℝ} (hτ : 0 ≤ τ)
    (q c x : E) (hx : x ∈ K) :
    let g := proxGrad q c τ
    let v := O.query (g x)
    let y := lineMove g τ x v
    y ∈ K ∧ ∀ t : ℝ, 0 ≤ t → t ≤ 1 → prox q c τ y ≤ prox q c τ (blend t x v) := by
  let g := proxGrad q c τ
  let v := O.query (g x)
  let G := ⟪g x, x - v⟫
  let H := τ * ‖v - x‖ ^ 2
  have hg : 0 ≤ G := by
    dsimp only [G]; rw [inner_sub_right]; exact sub_nonneg.mpr (O.least (g x) x hx)
  have hH : 0 ≤ H := by dsimp [H]; positivity
  obtain ⟨h0, h1, hmin⟩ := lineFraction_spec hg hH
  refine ⟨blend_mem hK h0 h1 hx (O.mem _), ?_⟩
  have eq (t : ℝ) (ht : 0 ≤ t) : prox q c τ (blend t x v) = prox q c τ x +
      (-t * G + H / 2 * t ^ 2) := by
    rw [prox_taylor q c τ x, blend_sub, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg ht]
    have e : ⟪g x, v - x⟫ = -G := by dsimp only [G]; simp only [inner_sub_right]; ring
    change _ + t * ⟪g x, v - x⟫ + _ = _
    rw [e]; dsimp [H]; ring
  intro t ht ht'
  change prox q c τ (blend (lineFraction G H) x v) ≤ _
  rw [eq _ h0, eq _ ht]
  exact add_le_add (le_refl _) (hmin t ht ht')

noncomputable def lineIter (step : E → E) (x : E) : ℕ → E
  | 0 => x
  | j + 1 => step (lineIter step x j)

omit [NormedAddCommGroup E] in
theorem lineIter_shift (step : E → E) (x : E) (j : ℕ) :
    lineIter step x (j + 1) = lineIter step (step x) j := by
  induction j with
  | zero => rfl
  | succ j ih => exact congrArg step ih

/-- Actual stopped CndG recursion; v is used for the stopping test and the
line search. The analysis-only infinite path lineIter is never evaluated. -/
noncomputable def lineLoop (g oracle : E → E) (τ η : ℝ) : ℕ → E → E × ℕ
  | 0, x => (x, 0)
  | n + 1, x => let v := oracle (g x)
              if ⟪g x, x - v⟫ ≤ η then (x, 1)
              else let r := lineLoop g oracle τ η n (lineMove g τ x v)
                   (r.1, 1 + r.2)

theorem lineLoop_spec {K : Set E} (hK : Convex ℝ K) (O : LMO K) {τ η : ℝ} (hτ : 0 ≤ τ)
    (q c x : E) (hx : x ∈ K) (n : ℕ) :
    let g := proxGrad q c τ
    let move := fun v => lineMove g τ v (O.query (g v))
    let out := lineLoop g O.query τ η n x
    (∃ j < n, let v := lineIter move x j; ⟪g v, v - O.query (g v)⟫ ≤ η) →
      out.1 ∈ K ∧ (∀ w ∈ K, ⟪g out.1, out.1 - w⟫ ≤ η) ∧ out.2 ≤ n := by
  dsimp only
  let g := proxGrad q c τ
  let move := fun v => lineMove g τ v (O.query (g v))
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    intro success
    by_cases h : ⟪g x, x - O.query (g x)⟫ ≤ η
    · simp only [lineLoop, show ⟪proxGrad q c τ x, x - O.query (proxGrad q c τ x)⟫ ≤ η from h,
        ite_true]
      refine ⟨hx, fun w hw => ?_, by omega⟩
      rw [inner_sub_right] at h ⊢; linarith [O.least (g x) w hw]
    · obtain ⟨j, hj, hit⟩ := success
      cases j with
      | zero => exact (h hit).elim
      | succ j =>
        have hit' : let v := lineIter move (move x) j; ⟪g v, v - O.query (g v)⟫ ≤ η := by
          change ⟪g (lineIter move x (j + 1)),
            lineIter move x (j + 1) - O.query (g (lineIter move x (j + 1)))⟫ ≤ η at hit
          rwa [lineIter_shift] at hit
        obtain ⟨hm, hg, hc⟩ := ih (move x) (lineMove_spec hK O hτ q c x hx).1 ⟨j, by omega, hit'⟩
        simp only [lineLoop, show ¬⟪proxGrad q c τ x, x - O.query (proxGrad q c τ x)⟫ ≤ η from h,
            ite_false]
        exact ⟨hm, hg, Nat.add_le_add_left hc 1 |>.trans_eq (Nat.add_comm 1 n)⟩

theorem lineIter_hit {K : Set E} (hK : Convex ℝ K) (O : LMO K) {τ δ η : ℝ}
    (hτ : 0 ≤ τ) (hη : 0 < η) (hbig : η < τ * δ ^ 2)
    (width : ∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ ≤ δ) (q c : E) (hc : c ∈ K) :
    let C := τ * δ ^ 2
    let m := ⌈2 * C / η⌉₊
    let g := proxGrad q c τ
    let X := lineIter (fun x => lineMove g τ x (O.query (g x))) c
    ∃ j < 2 * m, ⟪g (X j), X j - O.query (g (X j))⟫ ≤ η := by
  let C := τ * δ ^ 2
  let m := ⌈2 * C / η⌉₊
  let g := proxGrad q c τ
  let f := prox q c τ
  let X := lineIter (fun x => lineMove g τ x (O.query (g x))) c
  have hC : 0 < C := hη.trans hbig
  have hm : 2 * C / η ≤ (m : ℝ) := Nat.le_ceil _
  have hmp : 0 < (m : ℝ) := (show 0 < 2 * C / η by positivity).trans_le hm
  have mpos : 0 < m := by exact_mod_cast hmp
  have mem (j) : X j ∈ K := by induction j with
                              | zero => exact hc
                              | succ j ih => exact (lineMove_spec hK O hτ q c (X j) ih).1
  have next (j) := (lineMove_spec hK O hτ q c (X j) (mem j)).2
  have mdl := prox_models q c hτ K
  have recurrence (w : E) (hw : w ∈ K) (j) :
      f (X (j + 1)) - f w ≤ (1 - fwStepSize j) * (f (X j) - f w) + C / 2 * (fwStepSize j) ^ 2 := by
    have H := next j (fwStepSize j) (stepSize_bounds j).1 (stepSize_bounds j).2
    have B := fw_one_step hK mdl hτ width O (mem j) hw (stepSize_bounds j).1 (stepSize_bounds j).2
    change f (X (j + 1)) ≤ f _ at H
    change f _ - f w ≤ _ at B
    linarith only [H, B]
  let w := X (2 * m)
  obtain ⟨i, hi⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt mpos)
  have warm := fw_rate_scalar (fun j => f (X j) - f w) hC.le (recurrence w (mem (2 * m))) i
  have mi : i + 1 = m := hi.symm
  change f (X (i + 1)) - f w ≤ 2 * C / ((i : ℝ) + 3) at warm
  rw [mi] at warm
  have realmi : (m : ℝ) = (i : ℝ) + 1 := by exact_mod_cast hi
  have hg : 2 * C / ((i : ℝ) + 3) < η :=
      (div_lt_iff₀ (by positivity)).mpr (by nlinarith [(div_le_iff₀ hη).mp hm])
  change ∃ j < 2 * m, ⟪g (X j), X j - O.query (g (X j))⟫ ≤ η
  by_contra! bad
  let t := η / C
  have ht : 0 < t := div_pos hη hC
  have ht' : t ≤ 1 := (div_le_one hC).mpr hbig.le
  have dec (j : ℕ) (hj : j < 2 * m) : f (X (j + 1)) ≤ f (X j) - η ^ 2 / (2 * C) := by
    let x := X j
    let v := O.query (g x)
    have lin := next j t ht.le ht'
    have model := mdl.upper x (mem j) (blend t x v) (blend_mem hK ht.le ht' (mem j) (O.mem _))
    rw [blend_sub, real_inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_pos ht] at model
    have N := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (width v (O.mem _) x (mem j)) 2)
      (by positivity : 0 ≤ (τ / 2) * t ^ 2)
    have gap := mul_le_mul_of_nonneg_left (le_of_lt (bad j hj)) ht.le
    have id : t * η - C / 2 * t ^ 2 = η ^ 2 / (2 * C) := by dsimp [t]; field_simp; ring
    change f (X (j + 1)) ≤ f (blend t x v) at lin
    change f (blend t x v) ≤ f x + t * ⟪g x, v - x⟫ + τ / 2 * (t * ‖v - x‖) ^ 2 at model
    change t * η ≤ t * ⟪g x, x - v⟫ at gap
    have neg : ⟪g x, v - x⟫ = -⟪g x, x - v⟫ := by simp only [inner_sub_right]; ring
    rw [neg] at model
    change f (X (j + 1)) ≤ f x - _
    dsimp only [C] at id
    linarith only [lin, model, gap, N, id]
  have sum (j : ℕ) (hj : j ≤ m) : f (X (m + j)) ≤ f (X m) - (j : ℝ) * (η ^ 2 / (2 * C)) := by
    induction j with
    | zero => simp
    | succ j ih =>
      have H := dec (m + j) (by omega)
      have B := ih (by omega)
      rw [Nat.cast_succ, ← Nat.add_assoc]
      linarith only [H, B]
  have enough : η ≤ (m : ℝ) * (η ^ 2 / (2 * C)) := by
    calc
      η = (2 * C / η) * (η ^ 2 / (2 * C)) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hm (by positivity)
  have B := sum m (le_refl _)
  rw [← two_mul] at B
  change f w ≤ _ at B
  linarith only [B, enough, warm, hg]

noncomputable def innerLineRun (oracle : E → E) (q c : E) (τ δ η : ℝ) : E × ℕ :=
  let C := τ * δ ^ 2
  if C ≤ η then (oracle (proxGrad q c τ c), 1)
  else lineLoop (proxGrad q c τ) oracle τ η (2 * ⌈2 * C / η⌉₊) c

theorem innerLineRun_spec {K : Set E} (hK : Convex ℝ K) (O : LMO K)
    {τ δ η : ℝ} (hτ : 0 ≤ τ) (hη : 0 < η) (width : ∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ ≤ δ)
    (q c : E) (hc : c ∈ K) :
    let a := innerLineRun O.query q c τ δ η
    a.1 ∈ K ∧ (∀ w ∈ K, ⟪proxGrad q c τ a.1, a.1 - w⟫ ≤ η) ∧ (a.2 : ℝ) ≤ 1 + 6 * τ * δ ^ 2 / η := by
  let C := τ * δ ^ 2
  by_cases h : C ≤ η
  · simp only [innerLineRun, show τ * δ ^ 2 ≤ η from h, ite_true, Nat.cast_one]
    exact ⟨O.mem _, fun w hw => (prox_atom_gap O hτ width q c c hc hw).trans h,
        by linarith [show 0 ≤ 6 * τ * δ ^ 2 / η by positivity]⟩
  · let m := ⌈2 * C / η⌉₊
    have hbig : η < C := lt_of_not_ge h
    have hC : 0 < C := hη.trans hbig
    obtain ⟨hm, hgap, hcnt⟩ := lineLoop_spec hK O hτ q c c hc (2 * m)
      (lineIter_hit hK O hτ hη hbig width q c hc)
    simp only [innerLineRun, show ¬τ * δ ^ 2 ≤ η from h, ite_false]
    refine ⟨hm, hgap, ?_⟩
    have n := (show (m : ℝ) < 2 * C / η + 1 from Nat.ceil_lt_add_one (by positivity))
    have big := (one_lt_div₀ hη).mpr hbig
    have co := (show ((lineLoop (proxGrad q c τ) O.query τ η (2 * m) c).2 : ℝ) ≤
        2 * (m : ℝ) by exact_mod_cast hcnt)
    change ((lineLoop (proxGrad q c τ) O.query τ η (2 * m) c).2 : ℝ) ≤ _
    dsimp only [C] at n big
    simp only [div_eq_mul_inv] at n big ⊢
    linarith only [co, n, big]

end Lemmata.FrankWolfePS.Upper
