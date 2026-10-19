module

public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
A four-variable Lagrangian duality gap, adapted from the Geoffrion theorem
experiment's `formalizations/theorem14-multirow/Theorem14Counterexample.lean`
at commit e6c64b90ba8b15f4939e9650a13742c39c893efa.
-/

public section

set_option autoImplicit false

namespace Lemmata.LagrangianDualityGap

noncomputable section

open Set
open scoped Topology

/-- Ambient real space with coordinates `(u,v,r,z)`. -/
abbrev Point : Type := Fin 4 → ℝ

/-- Multiplier space for the two rational rows `-u ≥ 0`, `-v ≥ 0`. -/
abbrev Multiplier : Type := Fin 2 → ℝ

abbrev uIdx : Fin 4 := ⟨0, by decide⟩
abbrev vIdx : Fin 4 := ⟨1, by decide⟩
abbrev rIdx : Fin 4 := ⟨2, by decide⟩
abbrev zIdx : Fin 4 := ⟨3, by decide⟩
abbrev lamUIdx : Fin 2 := ⟨0, by decide⟩
abbrev lamVIdx : Fin 2 := ⟨1, by decide⟩

/-- Build a point from coordinates `(u,v,r,z)`. -/
def mkPoint (u v r z : ℝ) : Point := ![u, v, r, z]

/-- Build a multiplier vector for the two rows. -/
def mkMultiplier (a b : ℝ) : Multiplier := ![a, b]

/-- The `u` coordinate. -/
def U (x : Point) : ℝ := x uIdx

/-- The `v` coordinate. -/
def V (x : Point) : ℝ := x vIdx

/-- The `r` coordinate. -/
def R (x : Point) : ℝ := x rIdx

/-- The objective coordinate `z`. -/
def Z (x : Point) : ℝ := x zIdx

/-- Multiplier for row `-u ≥ 0`. -/
def LamU (lam : Multiplier) : ℝ := lam lamUIdx

/-- Multiplier for row `-v ≥ 0`. -/
def LamV (lam : Multiplier) : ℝ := lam lamVIdx

/-- The irrational normal form `sqrt(2) u + v`. -/
def ell (x : Point) : ℝ := Real.sqrt 2 * U x + V x

/-- The closed convex conic set `K`. -/
def InK (x : Point) : Prop :=
    0 ≤ Z x ∧ Z x ≤ 1 ∧ 0 ≤ R x ∧ 0 ≤ ell x ∧ (1 - Z x) ^ 2 ≤ R x * ell x

/-- The real conic set `K`. -/
def Kset : Set Point := {x | InK x}

/-- Real point all of whose coordinates are integers. -/
def IsIntegerPoint (x : Point) : Prop := ∀ i : Fin 4, ∃ m : ℤ, x i = (m : ℝ)

/-- The integer feasible set `X = K ∩ Z^4`, represented in real coordinates. -/
def Xset : Set Point := {x | InK x ∧ IsIntegerPoint x}

/-- The two-row rational system `-u ≥ 0`, `-v ≥ 0`, i.e. `u ≤ 0`, `v ≤ 0`. -/
def Pset : Set Point := {x | U x ≤ 0 ∧ V x ≤ 0}

/-- The primal feasible ray forced by the rational system. -/
def PrimalRay : Set Point := {x | U x = 0 ∧ V x = 0 ∧ 0 ≤ R x ∧ Z x = 1}

/-- Feasible set of the original integer primal problem. -/
def IntegerPrimalFeasible : Set Point := Xset ∩ Pset

/-- Feasible set of the convexified primal problem using `conv X`. -/
def ConvexifiedPrimalFeasible : Set Point := convexHull ℝ Xset ∩ Pset

/-- Feasible set of the closed-convexified primal problem using `closure (conv X)`. -/
def ClosedConvexifiedPrimalFeasible : Set Point := closure (convexHull ℝ Xset) ∩ Pset

/-- `f` has minimum value `a` on a set `s`, with attainment. -/
def HasMinimumValue (s : Set Point) (f : Point → ℝ) (a : ℝ) : Prop :=
    (∀ x ∈ s, a ≤ f x) ∧ ∃ x ∈ s, f x = a

/-- A sequence-style infimum certificate avoiding bundled `sInf` API choices. -/
def IsInfimumOn (s : Set Point) (f : Point → ℝ) (a : ℝ) : Prop :=
    (∀ x ∈ s, a ≤ f x) ∧ ∀ ε > 0, ∃ x ∈ s, f x < a + ε

/-- `f` is unbounded below on `s`. -/
def UnboundedBelowOn (s : Set Point) (f : Point → ℝ) : Prop :=
    ∀ B : ℝ, ∃ x ∈ s, f x < B

/-- Nonnegative multipliers for rows `-u ≥ 0`, `-v ≥ 0`. -/
def NonnegativeMultiplier (lam : Multiplier) : Prop := 0 ≤ LamU lam ∧ 0 ≤ LamV lam

/-- Multipliers parallel to the irrational normal `(sqrt(2),1)`. -/
def OnIrrationalRay (lam : Multiplier) : Prop :=
    ∃ t : ℝ, 0 ≤ t ∧ LamU lam = t * Real.sqrt 2 ∧ LamV lam = t

/-- Lagrangian objective `z + lam₁ u + lam₂ v` for the two relaxed rows. -/
def Lagrangian (lam : Multiplier) (x : Point) : ℝ :=
    Z x + LamU lam * U x + LamV lam * V x

/-- Exact pointwise behavior of the Lagrangian dual function. -/
def DualFunctionCertificate : Prop :=
    (∀ lam : Multiplier,
      NonnegativeMultiplier lam →
        (OnIrrationalRay lam ∧ IsInfimumOn Xset (Lagrangian lam) 0) ∨
          (¬ OnIrrationalRay lam ∧ UnboundedBelowOn Xset (Lagrangian lam))) ∧
    ∃ lam : Multiplier, NonnegativeMultiplier lam ∧ IsInfimumOn Xset (Lagrangian lam) 0

lemma inK_mkPoint_origin_ray (r : ℝ) (hr : 0 ≤ r) : InK (mkPoint 0 0 r 1) := by
  simp [InK, mkPoint, Z, R, ell, U, V, hr]

lemma integer_origin_ray_point (k : ℕ) : (mkPoint 0 0 k 1) ∈ Xset := by
  constructor
  · exact inK_mkPoint_origin_ray (k : ℝ) (by positivity)
  · intro i
    fin_cases i
    · exact ⟨0, by norm_num [mkPoint]⟩
    · exact ⟨0, by norm_num [mkPoint]⟩
    · exact ⟨(k : ℤ), by norm_num [mkPoint]⟩
    · exact ⟨1, by norm_num [mkPoint]⟩

/-- The rational two-row system cuts `K` in exactly the ray `(0,0,r,1)`. -/
theorem primal_slice_of_K (x : Point) : x ∈ Kset ∧ x ∈ Pset ↔ x ∈ PrimalRay := by
  constructor
  · rintro ⟨hK, hP⟩
    rcases hK with ⟨hz0, hz1, hr, hell_nonneg, hcone⟩
    rcases hP with ⟨hu_nonpos, hv_nonpos⟩
    have hsqrt_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    have hsqrt_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    have hmul_nonpos : Real.sqrt 2 * U x ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hsqrt_nonneg hu_nonpos
    have hell_nonpos : ell x ≤ 0 := by
      dsimp [ell]
      nlinarith
    have hell_eq : ell x = 0 := le_antisymm hell_nonpos hell_nonneg
    have hmul_eq : Real.sqrt 2 * U x = 0 := by
      dsimp [ell] at hell_eq
      nlinarith
    have hU : U x = 0 := by nlinarith
    have hV : V x = 0 := by
      dsimp [ell] at hell_eq
      nlinarith
    have hzsq : (1 - Z x) ^ 2 = 0 := by
      nlinarith [sq_nonneg (1 - Z x)]
    have hZ : Z x = 1 := by nlinarith
    exact ⟨hU, hV, hr, hZ⟩
  · intro h
    rcases h with ⟨hU, hV, hr, hZ⟩
    constructor
    · simp [Kset, InK, ell, hU, hV, hZ, hr]
    · simp [Pset, hU, hV]

/-- Coordinate projection `U` is continuous. -/
lemma continuous_U : Continuous U := by
  change Continuous (fun x : Point => x uIdx)
  exact continuous_apply uIdx

/-- Coordinate projection `V` is continuous. -/
lemma continuous_V : Continuous V := by
  change Continuous (fun x : Point => x vIdx)
  exact continuous_apply vIdx

/-- Coordinate projection `R` is continuous. -/
lemma continuous_R : Continuous R := by
  change Continuous (fun x : Point => x rIdx)
  exact continuous_apply rIdx

/-- Coordinate projection `Z` is continuous. -/
lemma continuous_Z : Continuous Z := by
  change Continuous (fun x : Point => x zIdx)
  exact continuous_apply zIdx

/-- The irrational linear form is continuous. -/
lemma continuous_ell : Continuous ell := by
  change Continuous (fun x : Point => Real.sqrt 2 * U x + V x)
  exact (continuous_const.mul continuous_U).add continuous_V

/-- Cross-term estimate for the two-dimensional rotated cone. -/
lemma rotatedCone_cross_le {s t r₁ l₁ r₂ l₂ : ℝ}
    (hr₁ : 0 ≤ r₁) (hl₁ : 0 ≤ l₁) (hr₂ : 0 ≤ r₂) (hl₂ : 0 ≤ l₂)
    (hc₁ : s ^ 2 ≤ r₁ * l₁) (hc₂ : t ^ 2 ≤ r₂ * l₂) :
    2 * s * t ≤ r₁ * l₂ + r₂ * l₁ := by
  have hsq : (2 * s * t) ^ 2 ≤ (r₁ * l₂ + r₂ * l₁) ^ 2 := by
    nlinarith [sq_nonneg (r₁ * l₂ - r₂ * l₁), hc₁, hc₂]
  exact le_of_sq_le_sq hsq (by nlinarith [mul_nonneg hr₁ hl₂, mul_nonneg hr₂ hl₁])

/-- Convexity estimate for a nonnegative weighted average in the rotated cone. -/
lemma rotatedCone_weighted_le {a b r₁ l₁ s₁ r₂ l₂ s₂ : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hr₁ : 0 ≤ r₁) (hl₁ : 0 ≤ l₁) (hc₁ : s₁ ^ 2 ≤ r₁ * l₁)
    (hr₂ : 0 ≤ r₂) (hl₂ : 0 ≤ l₂) (hc₂ : s₂ ^ 2 ≤ r₂ * l₂) :
    (a * s₁ + b * s₂) ^ 2 ≤ (a * r₁ + b * r₂) * (a * l₁ + b * l₂) := by
  have hcross : 2 * s₁ * s₂ ≤ r₁ * l₂ + r₂ * l₁ :=
    rotatedCone_cross_le hr₁ hl₁ hr₂ hl₂ hc₁ hc₂
  have ha2 : 0 ≤ a ^ 2 := sq_nonneg a
  have hb2 : 0 ≤ b ^ 2 := sq_nonneg b
  have hab_nonneg : 0 ≤ a * b := mul_nonneg ha hb
  nlinarith

lemma Z_combo (a b : ℝ) (x y : Point) : Z (a • x + b • y) = a * Z x + b * Z y := by
  simp [Z]

lemma R_combo (a b : ℝ) (x y : Point) : R (a • x + b • y) = a * R x + b * R y := by
  simp [R]

lemma ell_combo (a b : ℝ) (x y : Point) :
    ell (a • x + b • y) = a * ell x + b * ell y := by
  simp [ell, U, V]
  ring

/-- The conic set `K` is closed. -/
theorem K_isClosed : IsClosed Kset := by
  have hZ0 : IsClosed {x : Point | (0 : ℝ) ≤ Z x} := by
    exact isClosed_le continuous_const continuous_Z
  have hZ1 : IsClosed {x : Point | Z x ≤ 1} := by
    exact isClosed_le continuous_Z continuous_const
  have hR0 : IsClosed {x : Point | (0 : ℝ) ≤ R x} := by
    exact isClosed_le continuous_const continuous_R
  have hell0 : IsClosed {x : Point | (0 : ℝ) ≤ ell x} := by
    exact isClosed_le continuous_const continuous_ell
  have hcone : IsClosed {x : Point | (1 - Z x) ^ 2 ≤ R x * ell x} := by
    exact isClosed_le ((continuous_const.sub continuous_Z).pow 2) (continuous_R.mul continuous_ell)
  simpa [Kset, InK, Set.ofPred_and] using
    hZ0.inter (hZ1.inter (hR0.inter (hell0.inter hcone)))

/-- The conic set `K` is convex. -/
theorem K_isConvex : Convex ℝ Kset := by
  rw [convex_iff_add_mem]
  intro x hx y hy a b ha hb hab
  rcases hx with ⟨hzx0, hzx1, hrx, hellx, hconex⟩
  rcases hy with ⟨hzy0, hzy1, hry, helly, hconey⟩
  constructor
  · rw [Z_combo]
    nlinarith [mul_nonneg ha hzx0, mul_nonneg hb hzy0]
  constructor
  · rw [Z_combo]
    nlinarith [mul_le_mul_of_nonneg_left hzx1 ha, mul_le_mul_of_nonneg_left hzy1 hb]
  constructor
  · rw [R_combo]
    nlinarith [mul_nonneg ha hrx, mul_nonneg hb hry]
  constructor
  · rw [ell_combo]
    nlinarith [mul_nonneg ha hellx, mul_nonneg hb helly]
  · rw [Z_combo, R_combo, ell_combo]
    have hcone := rotatedCone_weighted_le (a := a) (b := b) (r₁ := R x)
      (l₁ := ell x) (s₁ := 1 - Z x) (r₂ := R y) (l₂ := ell y) (s₂ := 1 - Z y)
      ha hb hrx hellx hconex hry helly hconey
    have hleft : 1 - (a * Z x + b * Z y) = a * (1 - Z x) + b * (1 - Z y) := by
      nlinarith
    rw [hleft]
    exact hcone

lemma convexHull_X_subset_K : convexHull ℝ Xset ⊆ Kset := by
  exact convexHull_min (by intro x hx; exact hx.1) K_isConvex

lemma closure_convexHull_X_subset_K : closure (convexHull ℝ Xset) ⊆ Kset := by
  exact closure_minimal convexHull_X_subset_K K_isClosed

/-- Every point `(0,0,r,1)` with `r ≥ 0` lies already in `conv X`, not just its closure. -/
lemma primal_ray_subset_convexHull_X : PrimalRay ⊆ convexHull ℝ Xset := by
  intro x hx
  rcases hx with ⟨hU, hV, hr, hZ⟩
  let n : ℕ := Nat.floor (R x)
  let t : ℝ := R x - n
  have hn_le : (n : ℝ) ≤ R x := by
    simpa [n] using Nat.floor_le hr
  have ht0 : 0 ≤ t := by
    dsimp [t]
    linarith
  have ht1 : t ≤ 1 := by
    have hlt : R x < (n : ℝ) + 1 := by
      simpa [n] using Nat.lt_floor_add_one (R x)
    dsimp [t]
    linarith
  have hleft_nonneg : 0 ≤ 1 - t := by linarith
  have hsum : (1 - t) + t = 1 := by ring
  have hp0 : mkPoint 0 0 (n : ℝ) 1 ∈ convexHull ℝ Xset :=
    (subset_convexHull ℝ Xset) (integer_origin_ray_point n)
  have hp1 : mkPoint 0 0 ((n + 1 : ℕ) : ℝ) 1 ∈ convexHull ℝ Xset :=
    (subset_convexHull ℝ Xset) (integer_origin_ray_point (n + 1))
  have hcombo : (1 - t) • mkPoint 0 0 (n : ℝ) 1 +
      t • mkPoint 0 0 ((n + 1 : ℕ) : ℝ) 1 ∈ convexHull ℝ Xset :=
    (convex_convexHull ℝ Xset) hp0 hp1 hleft_nonneg ht0 hsum
  convert hcombo using 1
  ext i
  fin_cases i
  · simpa [U, uIdx, mkPoint] using hU
  · simpa [V, vIdx, mkPoint] using hV
  · change R x = (1 - t) * (n : ℝ) + t * ((n + 1 : ℕ) : ℝ)
    dsimp [t]
    norm_num
    ring
  · simpa [Z, zIdx, mkPoint, hsum] using hZ

theorem integer_primal_value_one : HasMinimumValue IntegerPrimalFeasible Z 1 := by
  constructor
  · intro x hx
    have hKP : x ∈ Kset ∧ x ∈ Pset := ⟨hx.1.1, hx.2⟩
    have hRay : x ∈ PrimalRay := (primal_slice_of_K x).mp hKP
    rcases hRay with ⟨hU, hV, hr, hZ⟩
    simp [hZ]
  · refine ⟨mkPoint 0 0 0 1, ?_, ?_⟩
    · constructor
      · simpa using integer_origin_ray_point 0
      · simp [Pset, mkPoint, U, V]
    · rfl

theorem convexified_primal_value_one : HasMinimumValue ConvexifiedPrimalFeasible Z 1 := by
  constructor
  · intro x hx
    have hKP : x ∈ Kset ∧ x ∈ Pset := ⟨convexHull_X_subset_K hx.1, hx.2⟩
    have hRay : x ∈ PrimalRay := (primal_slice_of_K x).mp hKP
    rcases hRay with ⟨hU, hV, hr, hZ⟩
    simp [hZ]
  · refine ⟨mkPoint 0 0 0 1, ?_, ?_⟩
    · constructor
      · apply primal_ray_subset_convexHull_X
        simp [PrimalRay, mkPoint, U, V, R, Z]
      · simp [Pset, mkPoint, U, V]
    · rfl

theorem closed_convexified_primal_value_one :
    HasMinimumValue ClosedConvexifiedPrimalFeasible Z 1 := by
  constructor
  · intro x hx
    have hKP : x ∈ Kset ∧ x ∈ Pset := ⟨closure_convexHull_X_subset_K hx.1, hx.2⟩
    have hRay : x ∈ PrimalRay := (primal_slice_of_K x).mp hKP
    rcases hRay with ⟨hU, hV, hr, hZ⟩
    simp [hZ]
  · refine ⟨mkPoint 0 0 0 1, ?_, ?_⟩
    · constructor
      · exact subset_closure (primal_ray_subset_convexHull_X (by
          simp [PrimalRay, mkPoint, U, V, R, Z]))
      · simp [Pset, mkPoint, U, V]
    · rfl

lemma isIntegerPoint_mkPoint_int (u v r z : ℤ) :
    IsIntegerPoint (mkPoint (u : ℝ) (v : ℝ) (r : ℝ) (z : ℝ)) := by
  intro i
  fin_cases i
  · exact ⟨u, by simp [mkPoint]⟩
  · exact ⟨v, by simp [mkPoint]⟩
  · exact ⟨r, by simp [mkPoint]⟩
  · exact ⟨z, by simp [mkPoint]⟩

lemma z0_ell_pos_of_mem (u v r : ℤ) :
    (mkPoint (u : ℝ) (v : ℝ) (r : ℝ) 0) ∈ Xset →
      0 < Real.sqrt 2 * (u : ℝ) + (v : ℝ) := by
  intro hx
  rcases hx.1 with ⟨_, _, _, hell_nonneg, hcone⟩
  have hcone' : (1 : ℝ) ≤ (r : ℝ) * (Real.sqrt 2 * (u : ℝ) + (v : ℝ)) := by
    simpa [mkPoint, Z, R, ell, U, V] using hcone
  have hell_nonneg' : 0 ≤ Real.sqrt 2 * (u : ℝ) + (v : ℝ) := by
    simpa [mkPoint, ell, U, V] using hell_nonneg
  by_contra hnot
  have hell_le : Real.sqrt 2 * (u : ℝ) + (v : ℝ) ≤ 0 := le_of_not_gt hnot
  have hell_eq : Real.sqrt 2 * (u : ℝ) + (v : ℝ) = 0 := le_antisymm hell_le hell_nonneg'
  have hprod_zero : (r : ℝ) * (Real.sqrt 2 * (u : ℝ) + (v : ℝ)) = 0 := by
    rw [hell_eq, mul_zero]
  nlinarith

lemma z0_mem_of_ell_pos (u v : ℤ)
    (hpos : 0 < Real.sqrt 2 * (u : ℝ) + (v : ℝ)) :
    ∃ r : ℤ, (mkPoint (u : ℝ) (v : ℝ) (r : ℝ) 0) ∈ Xset := by
  let L : ℝ := Real.sqrt 2 * (u : ℝ) + (v : ℝ)
  let r : ℤ := Int.ceil (1 / L)
  have hLpos : 0 < L := hpos
  have hLnonneg : 0 ≤ L := le_of_lt hLpos
  have hceil : 1 / L ≤ (r : ℝ) := by
    simpa [r] using Int.le_ceil (1 / L)
  have hone_div_nonneg : 0 ≤ 1 / L := div_nonneg zero_le_one hLnonneg
  have hr_nonneg_int : 0 ≤ r := by
    simpa [r] using Int.ceil_nonneg hone_div_nonneg
  have hcone : (1 : ℝ) ≤ (r : ℝ) * L := by
    exact (div_le_iff₀ hLpos).mp hceil
  refine ⟨r, ?_⟩
  constructor
  · have hcone' : (1 : ℝ) ≤ (r : ℝ) * (Real.sqrt 2 * (u : ℝ) + (v : ℝ)) := by
      simpa [L] using hcone
    simp [InK, mkPoint, Z, R, ell, U, V]
    exact ⟨hr_nonneg_int, by simpa [L] using hLnonneg, hcone'⟩
  · simpa using isIntegerPoint_mkPoint_int u v r 0

lemma rat_num_eq_den_mul (q : ℚ) : (q.num : ℝ) = (q.den : ℝ) * (q : ℝ) := by
  rw [Rat.cast_def]
  field_simp [Rat.den_ne_zero]

lemma sqrt_two_lt_two : Real.sqrt 2 < 2 := by
  rw [Real.sqrt_lt' (by norm_num)]
  norm_num

lemma mem_closure_sqrt_two_one_iff (x : ℝ) :
    x ∈ (AddSubgroup.closure ({Real.sqrt 2, 1} : Set ℝ) : AddSubgroup ℝ) ↔
      ∃ u v : ℤ, Real.sqrt 2 * (u : ℝ) + (v : ℝ) = x := by
  constructor
  · intro hx
    refine AddSubgroup.closure_induction
      (p := fun y hy => ∃ u v : ℤ, Real.sqrt 2 * (u : ℝ) + (v : ℝ) = y)
      ?mem ?zero ?add ?neg hx
    · intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · exact ⟨1, 0, by norm_num⟩
      · exact ⟨0, 1, by norm_num⟩
    · exact ⟨0, 0, by norm_num⟩
    · intro y z _ _ hyrep hzrep
      rcases hyrep with ⟨uy, vy, rfl⟩
      rcases hzrep with ⟨uz, vz, rfl⟩
      refine ⟨uy + uz, vy + vz, ?_⟩
      norm_num [Int.cast_add]
      ring
    · intro y _ hyrep
      rcases hyrep with ⟨uy, vy, rfl⟩
      refine ⟨-uy, -vy, ?_⟩
      norm_num
      ring
  · rintro ⟨u, v, rfl⟩
    let G : AddSubgroup ℝ := AddSubgroup.closure ({Real.sqrt 2, 1} : Set ℝ)
    have hsqrt : Real.sqrt 2 ∈ G := AddSubgroup.subset_closure (by simp)
    have hone : (1 : ℝ) ∈ G := AddSubgroup.subset_closure (by simp)
    have hu : Real.sqrt 2 * (u : ℝ) ∈ G := by
      simpa [zsmul_eq_mul, mul_comm] using G.zsmul_mem hsqrt u
    have hv : (v : ℝ) ∈ G := by
      simpa [zsmul_eq_mul] using G.zsmul_mem hone v
    exact G.add_mem hu hv

lemma dense_sqrt_two_int_combos :
    Dense ((AddSubgroup.closure ({Real.sqrt 2, 1} : Set ℝ) : AddSubgroup ℝ) : Set ℝ) := by
  simpa using (dense_addSubgroupClosure_pair_iff (a := Real.sqrt 2) (b := (1 : ℝ))).2
    (by simpa using irrational_sqrt_two)

/-- The objective infimum over `X`, before imposing the rational rows, is `0`. -/
theorem unconstrained_inf_X_zero : IsInfimumOn Xset Z 0 := by
  constructor
  · intro x hx
    exact hx.1.1
  · intro ε hε
    obtain ⟨r, hx⟩ := z0_mem_of_ell_pos (1 : ℤ) (0 : ℤ) (by norm_num)
    refine ⟨mkPoint ((1 : ℤ) : ℝ) ((0 : ℤ) : ℝ) (r : ℝ) 0, hx, ?_⟩
    simpa [Z, mkPoint] using hε

/-- The low-cost layer projects exactly to the open irrational lattice half-space. -/
theorem z0_layer_projection (u v : ℤ) :
    (∃ r : ℤ, (mkPoint u v r 0) ∈ Xset) ↔ 0 < Real.sqrt 2 * (u : ℝ) + (v : ℝ) := by
  constructor
  · rintro ⟨r, hr⟩
    exact z0_ell_pos_of_mem u v r hr
  · exact z0_mem_of_ell_pos u v

/-- Density gives positive, arbitrarily small violations of the irrational boundary. -/
theorem small_positive_violations :
    ∀ ε > 0, ∃ u v : ℤ,
      0 < Real.sqrt 2 * (u : ℝ) + (v : ℝ) ∧
        Real.sqrt 2 * (u : ℝ) + (v : ℝ) < ε := by
  intro ε hε
  have hhalf_mem : (ε / 2 : ℝ) ∈ Set.Ioo (0 : ℝ) ε := by
    constructor <;> nlinarith
  obtain ⟨x, hxG, hxI⟩ :=
    dense_sqrt_two_int_combos.exists_mem_open isOpen_Ioo ⟨ε / 2, hhalf_mem⟩
  rcases (mem_closure_sqrt_two_one_iff x).1 hxG with ⟨u, v, hcombo⟩
  refine ⟨u, v, ?_, ?_⟩
  · rw [hcombo]
    exact hxI.1
  · rw [hcombo]
    exact hxI.2

/-- Every nonnegative multiplier off the irrational ray has an integer descent direction. -/
theorem off_ray_integer_descent (lam : Multiplier) :
    NonnegativeMultiplier lam →
      ¬ OnIrrationalRay lam →
        ∃ u v : ℤ,
          0 < Real.sqrt 2 * (u : ℝ) + (v : ℝ) ∧
            LamU lam * (u : ℝ) + LamV lam * (v : ℝ) < 0 := by
  intro hnonneg hnotray
  by_cases hBzero : LamV lam = 0
  · have hApos : 0 < LamU lam := by
      have hAne : LamU lam ≠ 0 := by
        intro hAzero
        apply hnotray
        refine ⟨0, by norm_num, ?_, ?_⟩
        · simp [hAzero]
        · simp [hBzero]
      exact lt_of_le_of_ne hnonneg.1 (Ne.symm hAne)
    refine ⟨-1, 2, ?_, ?_⟩
    · norm_num
    · simp [hBzero]
      nlinarith
  · have hBpos : 0 < LamV lam := lt_of_le_of_ne hnonneg.2 (Ne.symm hBzero)
    have hratio_ne : LamU lam / LamV lam ≠ Real.sqrt 2 := by
      intro hratio
      apply hnotray
      refine ⟨LamV lam, hnonneg.2, ?_, rfl⟩
      have hmul := (div_eq_iff hBpos.ne').mp hratio
      simpa [mul_comm] using hmul
    rcases lt_trichotomy (LamU lam / LamV lam) (Real.sqrt 2) with hlt | heq | hgt
    · obtain ⟨q, hAq, hqS⟩ := exists_rat_btwn hlt
      refine ⟨(q.den : ℤ), -q.num, ?_, ?_⟩
      · have hden_pos : (0 : ℝ) < (q.den : ℝ) := by exact_mod_cast q.den_pos
        have hnum_lt : (q.num : ℝ) < (q.den : ℝ) * Real.sqrt 2 := by
          calc
            (q.num : ℝ) = (q.den : ℝ) * (q : ℝ) := rat_num_eq_den_mul q
            _ < (q.den : ℝ) * Real.sqrt 2 := mul_lt_mul_of_pos_left hqS hden_pos
        norm_num
        nlinarith
      · have hden_pos : (0 : ℝ) < (q.den : ℝ) := by exact_mod_cast q.den_pos
        have hA_lt : LamU lam < (q : ℝ) * LamV lam := (div_lt_iff₀ hBpos).mp hAq
        have hscaled : LamU lam * (q.den : ℝ) < LamV lam * (q.num : ℝ) := by
          calc
            LamU lam * (q.den : ℝ) < ((q : ℝ) * LamV lam) * (q.den : ℝ) :=
              mul_lt_mul_of_pos_right hA_lt hden_pos
            _ = LamV lam * (q.num : ℝ) := by
              rw [rat_num_eq_den_mul q]
              ring
        norm_num
        nlinarith
    · exact False.elim (hratio_ne heq)
    · obtain ⟨q, hSq, hqA⟩ := exists_rat_btwn hgt
      refine ⟨-(q.den : ℤ), q.num, ?_, ?_⟩
      · have hden_pos : (0 : ℝ) < (q.den : ℝ) := by exact_mod_cast q.den_pos
        have hnum_gt : (q.den : ℝ) * Real.sqrt 2 < (q.num : ℝ) := by
          calc
            (q.den : ℝ) * Real.sqrt 2 < (q.den : ℝ) * (q : ℝ) :=
              mul_lt_mul_of_pos_left hSq hden_pos
            _ = (q.num : ℝ) := by rw [rat_num_eq_den_mul q]
        norm_num
        nlinarith
      · have hden_pos : (0 : ℝ) < (q.den : ℝ) := by exact_mod_cast q.den_pos
        have hq_lt_A : (q : ℝ) * LamV lam < LamU lam := (lt_div_iff₀ hBpos).mp hqA
        have hscaled : LamV lam * (q.num : ℝ) < LamU lam * (q.den : ℝ) := by
          calc
            LamV lam * (q.num : ℝ) = ((q : ℝ) * LamV lam) * (q.den : ℝ) := by
              rw [rat_num_eq_den_mul q]
              ring
            _ < LamU lam * (q.den : ℝ) := mul_lt_mul_of_pos_right hq_lt_A hden_pos
        norm_num
        nlinarith

theorem dual_parallel_inf_zero (lam : Multiplier) :
    NonnegativeMultiplier lam → OnIrrationalRay lam → IsInfimumOn Xset (Lagrangian lam) 0 := by
  intro _ hRay
  rcases hRay with ⟨t, ht_nonneg, hLamU, hLamV⟩
  constructor
  · intro x hx
    rcases hx.1 with ⟨hz_nonneg, _, _, hell_nonneg, _⟩
    have hLag : Lagrangian lam x = Z x + t * ell x := by
      simp [Lagrangian, ell, hLamU, hLamV]
      ring
    rw [hLag]
    exact add_nonneg hz_nonneg (mul_nonneg ht_nonneg hell_nonneg)
  · intro ε hε
    have ht1_pos : 0 < t + 1 := by nlinarith
    have hδ_pos : 0 < ε / (t + 1) := div_pos hε ht1_pos
    obtain ⟨u, v, hell_pos, hell_lt⟩ := small_positive_violations (ε / (t + 1)) hδ_pos
    obtain ⟨r, hx⟩ := (z0_layer_projection u v).2 hell_pos
    refine ⟨mkPoint (u : ℝ) (v : ℝ) (r : ℝ) 0, hx, ?_⟩
    have hLag : Lagrangian lam (mkPoint (u : ℝ) (v : ℝ) (r : ℝ) 0) =
        t * (Real.sqrt 2 * (u : ℝ) + (v : ℝ)) := by
      simp [Lagrangian, mkPoint, Z, U, V, hLamU, hLamV]
      ring
    rw [hLag]
    have hmul_lt : (Real.sqrt 2 * (u : ℝ) + (v : ℝ)) * (t + 1) < ε :=
      (lt_div_iff₀ ht1_pos).mp hell_lt
    have hle : t * (Real.sqrt 2 * (u : ℝ) + (v : ℝ)) ≤
        (t + 1) * (Real.sqrt 2 * (u : ℝ) + (v : ℝ)) := by
      exact mul_le_mul_of_nonneg_right (by nlinarith) (le_of_lt hell_pos)
    nlinarith

theorem dual_off_ray_unbounded (lam : Multiplier) :
    NonnegativeMultiplier lam → ¬ OnIrrationalRay lam → UnboundedBelowOn Xset (Lagrangian lam) := by
  intro hnonneg hnotray B
  obtain ⟨u, v, hell_pos, hdesc⟩ := off_ray_integer_descent lam hnonneg hnotray
  let c : ℝ := LamU lam * (u : ℝ) + LamV lam * (v : ℝ)
  have hc_neg : c < 0 := hdesc
  let d : ℝ := -c
  have hd_pos : 0 < d := by dsimp [d]; nlinarith
  obtain ⟨N, hNgt⟩ := exists_nat_gt (max (1 : ℝ) ((-B) / d))
  have hNpos : 0 < (N : ℝ) := by
    have h1le : (1 : ℝ) ≤ max (1 : ℝ) ((-B) / d) := le_max_left _ _
    nlinarith
  have hminusB_div_lt_N : (-B) / d < (N : ℝ) := lt_of_le_of_lt (le_max_right _ _) hNgt
  have hminusB_lt_Nd : -B < (N : ℝ) * d := (div_lt_iff₀ hd_pos).mp hminusB_div_lt_N
  let uN : ℤ := (N : ℤ) * u
  let vN : ℤ := (N : ℤ) * v
  have hell_scaled : 0 < Real.sqrt 2 * (uN : ℝ) + (vN : ℝ) := by
    have hscale : Real.sqrt 2 * (uN : ℝ) + (vN : ℝ) =
        (N : ℝ) * (Real.sqrt 2 * (u : ℝ) + (v : ℝ)) := by
      dsimp [uN, vN]
      norm_num [Int.cast_mul]
      ring
    rw [hscale]
    exact mul_pos hNpos hell_pos
  obtain ⟨r, hx⟩ := (z0_layer_projection uN vN).2 hell_scaled
  refine ⟨mkPoint (uN : ℝ) (vN : ℝ) (r : ℝ) 0, hx, ?_⟩
  have hLag : Lagrangian lam (mkPoint (uN : ℝ) (vN : ℝ) (r : ℝ) 0) = (N : ℝ) * c := by
    dsimp [c, uN, vN]
    simp [Lagrangian, mkPoint, Z, U, V]
    ring
  rw [hLag]
  dsimp [d] at hminusB_lt_Nd
  nlinarith

theorem dual_function_certificate : DualFunctionCertificate := by
  constructor
  · intro lam hnonneg
    by_cases hRay : OnIrrationalRay lam
    · left
      exact ⟨hRay, dual_parallel_inf_zero lam hnonneg hRay⟩
    · right
      exact ⟨hRay, dual_off_ray_unbounded lam hnonneg hRay⟩
  · refine ⟨mkMultiplier 0 0, ?_, ?_⟩
    · simp [NonnegativeMultiplier, LamU, LamV, mkMultiplier]
    · apply dual_parallel_inf_zero
      · simp [NonnegativeMultiplier, LamU, LamV, mkMultiplier]
      · refine ⟨0, by norm_num, ?_, ?_⟩ <;> simp [LamU, LamV, mkMultiplier]

-- DOCS_BEGIN_MAIN
/-- The set is closed and convex, all three primal minima are one, the unconstrained
infimum is zero, and the dual function is zero on the irrational ray and unbounded
below off it. -/
theorem duality_gap :
    IsClosed Kset ∧
    Convex ℝ Kset ∧
    HasMinimumValue IntegerPrimalFeasible Z 1 ∧
    HasMinimumValue ConvexifiedPrimalFeasible Z 1 ∧
    HasMinimumValue ClosedConvexifiedPrimalFeasible Z 1 ∧
    IsInfimumOn Xset Z 0 ∧
    (∀ lam : Multiplier, NonnegativeMultiplier lam →
      (OnIrrationalRay lam ∧ IsInfimumOn Xset (Lagrangian lam) 0) ∨
      (¬ OnIrrationalRay lam ∧ UnboundedBelowOn Xset (Lagrangian lam))) ∧
    (∃ lam : Multiplier, NonnegativeMultiplier lam ∧
      IsInfimumOn Xset (Lagrangian lam) 0) := by
  exact ⟨K_isClosed, K_isConvex, integer_primal_value_one, convexified_primal_value_one,
    closed_convexified_primal_value_one, unconstrained_inf_X_zero, dual_function_certificate⟩

-- DOCS_END_MAIN

end

end Lemmata.LagrangianDualityGap
