module

public import Lemmata.FrankWolfePS.Unique.Parameters
public import Lemmata.FrankWolfePS.Unique.Borel
public import Lemmata.FrankWolfePS.Lower.Faces
public import Lemmata.FrankWolfePS.Model
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace

@[expose] public section

/-!
# The lower bound with unique linear minimizers, at simplex scale `A`

For a method requiring no more than `T` calls, a random instance of the jittered family (a grid
table `D` and a hidden set `I`) makes the method fail with probability at least `1/5`, for every
tape (`unique_fixed_tape`). Averaging over the tape selects one fixed instance
(`unique_lmo_lower_bound`). Every nonzero direction has exactly one minimizing point, so the
oracle has no choice to make; the zero direction returns the public start point.
-/

namespace Lemmata.FrankWolfePS

open Lemmata.FrankWolfePS.Unique in
/-- `play` only prepends: running from a longer history shifts the rule. -/
theorem play_shift {E : Type*} (O : E → E) (ask : List E → E) (n : ℕ) (h₀ h : List E) :
    play O ask n (h ++ h₀) = play O (fun h' => ask (h' ++ h₀)) n h ++ h₀ := by
  induction n generalizing h with
  | zero => rfl
  | succ n ih =>
    simp only [play]
    rw [← List.cons_append, ih]

/-- The direction a method asks after the replies `rs` (oldest first), `0` once it has
returned. -/
def Method.queryAfter {E : Type*} [Zero E] : {t : ℕ} → Method E t → List E → E
  | _, .ret _, _ => 0
  | _, .ask q _, [] => q
  | _, .ask _ next, r :: rs => (next r).queryAfter rs

/-- The point a method returns after the replies `rs` (oldest first). -/
def Method.outAfter {E : Type*} [Zero E] : {t : ℕ} → Method E t → List E → E
  | _, .ret x, _ => x
  | _, .ask _ _, [] => 0
  | _, .ask _ next, r :: rs => (next r).outAfter rs

open Lemmata.FrankWolfePS.Unique in
/-- A method requiring no more than `t ≤ n` calls is the rule-based method given by its
queries and outputs: running the rules for `n` rounds returns the same point. -/
theorem Method.outAfter_play {E : Type*} [Zero E] {t : ℕ} (s : Method E t) (O : E → E) {n : ℕ}
    (hn : t ≤ n) :
    s.outAfter (play O (fun h => s.queryAfter h.reverse) n []).reverse = s.run O := by
  induction s generalizing n with
  | ret x => simp [outAfter, run]
  | @ask t q next ih =>
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have shift := play_shift O (fun h => (Method.ask q next).queryAfter h.reverse) n [O q] []
    have rule : (fun h' => (Method.ask q next).queryAfter (h' ++ [O q]).reverse) =
        fun h' => (next (O q)).queryAfter h'.reverse := by
      funext h'; simp [queryAfter]
    simp only [List.nil_append, rule] at shift
    simp only [play, queryAfter, List.reverse_nil]
    rw [shift, List.reverse_append]
    simpa [outAfter, run] using ih (O q) (by omega)

/-- The method given by query and output rules (histories most recent reply first). -/
def Method.ofRules {E : Type*} (ask : List E → E) (out : List E → E) :
    (t : ℕ) → List E → Method E t
  | 0, h => .ret (out h)
  | t + 1, h => .ask (ask h) fun r => Method.ofRules ask out t (r :: h)

open Lemmata.FrankWolfePS.Unique in
theorem Method.ofRules_run {E : Type*} (ask out : List E → E) (t : ℕ) (h : List E) (O : E → E) :
    (Method.ofRules ask out t h).run O = out (play O ask t h) := by
  induction t generalizing h with
  | zero => rfl
  | succ t ih => simp [ofRules, run, play, ih]

open Lemmata.FrankWolfePS.Unique in
/-- Methods given by query and output rules that are jointly measurable in the tape and the
replies are measurable. -/
theorem Method.isMeasurable_ofRules {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] (ask out : Ω → List E → E)
    (hq : BorelRule ask) (ho : BorelRule out) (T : ℕ) :
    Method.IsMeasurable fun ω => Method.ofRules (ask ω) (out ω) T [] := by
  intro O hO
  have z : Measurable (fun _ : Ω => (fun i : Fin 0 => Fin.elim0 i : Fin 0 → E)) :=
    measurable_const
  simpa [ofRules_run] using measurable_run O hO ask hq out ho T z

end Lemmata.FrankWolfePS

namespace Lemmata.FrankWolfePS.Unique
open Finset MeasureTheory
open scoped BigOperators RealInnerProductSpace
variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- The output of query and output rules against the oracle of the instance `(D, I)`. -/
noncomputable def outcome (A : ℝ) (a : ι) (T : ℕ) (D : Draw ι T) (I : Finset ι)
    (ask : Hist ι → Ambient ι) (out : Hist ι → Ambient ι) : Ambient ι :=
  out (play (reply (instanceBody A a T D I) (start A a)) ask T [])

/-- The properties of each instance of the jittered family. -/
theorem fixed_instance_spec {A : ℝ} (hA : 0 < A) (a : ι) (T : ℕ) (D : Draw ι T)
    {I : Finset ι} (ha : a ∈ I) (size : 1 < I.card) :
    let C := instanceBody A a T D I
    IsCompact C ∧ Convex ℝ C ∧ (interior C).Nonempty ∧ Upper.LipschitzNormals C 1 ∧
    Metric.diam C ≤ 2 + Real.sqrt 2 * A + 2 * (2 * jitter A T) ∧ start A a ∈ C ∧
    reply C (start A a) 0 = start A a ∧ (∀ q, q ≠ 0 → ∃! x, MinAt C q x) ∧
    Measurable (reply C (start A a)) ∧ ∃ x ∈ C, cost x = valC C := by
  let C := instanceBody A a T D I
  have S := settings hA ι T
  have G := geometry (vtx A a T D) S.2.2.1.le I
  have hst := vtx_anchor hA a T D ha
  have U (q : Ambient ι) (ne : q ≠ 0) (x y : Ambient ι) (hx : MinAt C q x)
      (hy : MinAt C q y) : x = y :=
    min_unique S.2.2.1 (norm_unit ne) ((normalize_min ne).mpr hx) ((normalize_min ne).mpr hy)
  refine ⟨G.1, G.2.1, rounded_interior_nonempty (by norm_num : (0 : ℝ) < 1)
    ⟨_, vertex_mem (vtx A a T D) ha S.2.2.1.le⟩, G.2.2,
    smooth_diameter hA size S.2.2.1.le S.2.2.2.2.1 (vtx_near hA a T D), hst,
    by simp [reply],
    fun q h => ⟨_, reply_min G.1 hst q, fun y hy => U q h y _ hy (reply_min G.1 hst q)⟩,
    measurable_reply G.1 hst U, ?_⟩
  have c : Continuous (cost (ι := ι)) := by unfold cost quadratic; fun_prop
  obtain ⟨x, hx, m⟩ := G.1.exists_isMinOn ⟨_, hst⟩ c.continuousOn
  refine ⟨x, hx, Eq.symm (IsLeast.csInf_eq ⟨⟨_, hx, rfl⟩, ?_⟩)⟩
  rintro _ ⟨y, hy, rfl⟩; exact m hy

theorem shell_info {T : ℕ} {a : ι} {S : Finset ι} (hs : S ∈ instanceSets T a) :
    a ∈ insert a S ∧ (insert a S).card = 8 * (T + 1) := by
  obtain ⟨sub, sz⟩ := mem_powersetCard.mp hs
  have na : a ∉ S := fun h => (notMem_erase a _) (sub h)
  exact ⟨mem_insert_self _ _, by rw [card_insert_of_notMem na, sz]; omega⟩

/-- The instances: a grid table and a hidden set. -/
noncomputable def ensemble (ι : Type*) [Fintype ι] [DecidableEq ι] (a : ι) (T : ℕ) :
    Finset (Draw ι T × Finset ι) :=
  univ ×ˢ instanceSets T a

/-- For every deterministic method (rules), at least a fifth of the instances fail. -/
theorem unique_fixed_tape {A θ : ℝ} (hA : 0 < A) (a : ι) (T : ℕ)
    (hN : Fintype.card ι = 256 * (T + 1))
    (hθ : θ + (A + 35) * (2 * A + 5) * (2 * jitter A T) ≤ A ^ 2 / (16 * ((T + 1 : ℕ) : ℝ)))
    (ask : Hist ι → Ambient ι) (out : Hist ι → Ambient ι) :
    ((ensemble ι a T).card : ℝ) / 5 ≤ ∑ d ∈ ensemble ι a T,
      flag (Bad (instanceBody A a T d.1 (insert a d.2)) θ
        (outcome A a T d.1 (insert a d.2) ask out)) := by
  classical
  let η := jitter A T
  let b := step A ι T
  let s := smooth A ι T
  let H := instanceSets T a
  let M := (Fintype.card (Draw ι T) : ℝ)
  let B := trouble (Q := alphabet ι T) A a b s (start A a) ask T {a} (fun _ => [])
  let E := fun (D : Draw ι T) (J : Finset ι) =>
    Bad (instanceBody A a T D (insert a J)) θ (outcome A a T D (insert a J) ask out)
  have P := settings hA ι T
  have each (D : Draw ι T) :
      (H.card : ℝ) / 4 ≤ (∑ J ∈ H, flag (E D J)) + (H.card : ℝ) / 4 * flag (B D) := by
    by_cases trouble' : B D
    · simp [flag, trouble']
    · simp only [flag, ite_eq_right trouble', mul_zero, add_zero]
      let o : Hist ι → Pt ι := fun x => scalePt A⁻¹ (coords (repaired A a (2 * η) (out x)))
      let tree := simulate A a b s (start A a) ask o D T {a} []
      have H1 := fixed_tape_lower_bound T a hN (1 / A) (by positivity) tree
      apply H1.trans
      apply sum_le_sum; intro J hJ
      have hi := shell_info hJ
      have rep := replay A a P.2.2.1 (start A a) ask o (insert a J) D
        (fun R h => vtx_anchor hA a T D h) T (R := {a}) (mem_singleton_self a)
        (singleton_subset_iff.mpr hi.1) (h := fun _ => []) trouble'
      have impl : failure (1 / A) (T + 1) (insert a J) (tree.run (insert a J)) → E D J := by
        intro f
        change failure (1 / A) (T + 1) (insert a J)
          ((simulate A a b s (start A a) ask o D T {a} []).run (insert a J)) at f
        rw [rep] at f
        have f' := (failure_scale one_pos hA one_pos (T + 1) (insert_nonempty a J) _).mpr f
        exact loss_transfer hA hi.1 P.2.2.1.le (mul_pos two_pos P.1) P.2.2.2.2.2.1
          P.2.2.2.2.1 hθ (vtx_near hA a T D) f'
      by_cases f : failure (1 / A) (T + 1) (insert a J) (tree.run (insert a J))
      · simp only [flag, ite_eq_left f, ite_eq_left (impl f), le_refl]
      · simp only [flag, ite_eq_right f]; split <;> norm_num
  have all := sum_le_sum (s := (univ : Finset (Draw ι T))) (fun D _ => each D)
  rw [sum_add_distrib, ← mul_sum] at all
  simp only [sum_const, card_univ, nsmul_eq_mul] at all
  change M * (_ / 4) ≤ (∑ D, ∑ J ∈ H, flag (E D J)) + (H.card : ℝ) / 4 * countP B at all
  have bar : countP B ≤ M / 100 := bad_table_count hA a T ask
  have hbar := mul_le_mul_of_nonneg_left bar (by positivity : 0 ≤ (H.card : ℝ) / 4)
  simp only [ensemble, card_product, card_univ, Nat.cast_mul, sum_product]
  change M * (H.card : ℝ) / 5 ≤ ∑ D, ∑ J ∈ H, flag (E D J)
  nlinarith only [all, hbar, mul_nonneg (by dsimp [M]; positivity : 0 ≤ M) (Nat.cast_nonneg H.card)]

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The normalized lower bound with unique linear minimizers.** For every measurable
randomized method requiring no more than `T` calls, some instance of the jittered family,
chosen before the tape, makes the method fail at threshold `θ` with probability at least
`1/5`. -/
theorem unique_lmo_lower_bound {A θ : ℝ} (hA : 0 < A) (a : ι) (T : ℕ)
    (hN : Fintype.card ι = 256 * (T + 1))
    (hθ : θ + (A + 35) * (2 * A + 5) * (2 * jitter A T) ≤ A ^ 2 / (16 * ((T + 1 : ℕ) : ℝ)))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (s : Ω → Method (Ambient ι) T)
    (hs : Method.IsMeasurable s) :
    ∃ D : Draw ι T, ∃ J ∈ instanceSets T a, let C := instanceBody A a T D (insert a J)
      IsCompact C ∧ Convex ℝ C ∧ (interior C).Nonempty ∧ Upper.LipschitzNormals C 1 ∧
      Metric.diam C ≤ 2 + Real.sqrt 2 * A + 2 * (2 * jitter A T) ∧ start A a ∈ C ∧
      reply C (start A a) 0 = start A a ∧ (∀ q, q ≠ 0 → ∃! x, MinAt C q x) ∧
      (∀ q, MinAt C q (reply C (start A a) q)) ∧
      1 / 5 ≤ μ.real {ω | Bad C θ ((s ω).run (reply C (start A a)))} := by
  classical
  let H := ensemble ι a T
  let C := fun d : Draw ι T × Finset ι => instanceBody A a T d.1 (insert a d.2)
  let e := fun d : Draw ι T × Finset ι => {ω | Bad (C d) θ ((s ω).run (reply (C d) (start A a)))}
  have sh : (instanceSets T a).Nonempty := by
    apply powersetCard_nonempty.mpr; simp [hN]; omega
  let : NeZero (alphabet ι T) := ⟨by unfold alphabet; omega⟩
  have ne : H.Nonempty := Finset.univ_nonempty.product sh
  have m (d) (hd : d ∈ H) : MeasurableSet (e d) := by
    have si := shell_info (mem_product.mp hd).2
    have size : 1 < (insert a d.2).card := by rw [si.2]; omega
    have spec := fixed_instance_spec hA a T d.1 si.1 size
    have outM := hs _ spec.2.2.2.2.2.2.2.2.1
    have cont : Continuous (cost (ι := ι)) := by unfold cost quadratic; fun_prop
    exact ((spec.1.isClosed.measurableSet.preimage outM).compl).union (measurableSet_le
      measurable_const ((cont.measurable.comp outM).sub measurable_const))
  have fixed (ω : Ω) : (H.card : ℝ) * (1 / 5) ≤ ∑ d ∈ H, flag (ω ∈ e d) := by
    have h := unique_fixed_tape hA a T hN hθ (fun h => (s ω).queryAfter h.reverse)
      (fun h => (s ω).outAfter h.reverse)
    simp only [outcome, Method.outAfter_play _ _ (le_refl T)] at h
    simpa [e, C, div_eq_mul_inv] using h
  obtain ⟨⟨D, J⟩, hj, hp⟩ := select_tape H ne μ (1 / 5) e m fixed
  have si := shell_info (mem_product.mp hj).2
  have size : 1 < (insert a J).card := by rw [si.2]; omega
  obtain ⟨hc, hv, inter, reg, diam, st, zero, uniq, _, _⟩ := fixed_instance_spec hA a T D si.1 size
  exact ⟨D, J, (mem_product.mp hj).2, hc, hv, inter, reg, diam, st, zero, uniq,
    fun q => reply_min hc st q, hp⟩

omit [LinearOrder ι] in
/-- The disclosed objective has the exact unit-curvature Taylor model and identity Hessian. -/
theorem disclosed_objective (x : Ambient ι) :
    HasFDerivAt cost (innerSL ℝ (grad 1 tilt x)) x ∧
    HasFDerivAt (grad 1 tilt) (ContinuousLinearMap.id ℝ (Ambient ι)) x ∧
    ∀ y : Ambient ι, cost y = cost x + ⟪grad 1 tilt x, y - x⟫ + (1 / 2 : ℝ) * ‖y - x‖ ^ 2 :=
  ⟨quadratic_derivative 1 tilt x, by simpa using quadratic_hessian 1 tilt x,
    fun y => quadratic_taylor 1 tilt x y⟩

end Lemmata.FrankWolfePS.Unique
