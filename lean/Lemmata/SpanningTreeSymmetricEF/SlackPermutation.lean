module

public import Lemmata.SpanningTreeSymmetricEF.CoordinateLowerBounds

@[expose] public section


/-! Irredundant, normalized affine inequalities are permuted by genuine
polyhedron symmetries. No topology on the ambient module is required. -/
namespace Lemmata.SpanningTreeSymmetricEF.SlackPermutation

open CoordinateLowerBounds
noncomputable section

variable {E I : Type*} [AddCommGroup E] [Module ℝ E]

/-- Affine evaluation along a line is an ordinary scalar affine function. -/
lemma eval_line (f : E →ᵃ[ℝ] ℝ) (y z : E) (t : ℝ) :
    f (AffineMap.lineMap y z t) = (1 - t) * f y + t * f z := by
  rw [f.apply_lineMap, AffineMap.lineMap_apply_ring]

/-- Finitely many strict inequalities persist for small signed steps along any
line. The only continuity used is continuity of scalar affine functions. -/
theorem exists_small_step [Finite I] (s : I → E →ᵃ[ℝ] ℝ) (y z : E)
    (hy : ∀ i, 0 < s i y) :
    ∃ δ > 0, ∀ t : ℝ, |t| < δ → ∀ i, 0 < s i (AffineMap.lineMap y z t) := by
  have h : ∀ᶠ t : ℝ in nhds 0, ∀ i, 0 < s i (AffineMap.lineMap y z t) := by
    apply Filter.eventually_all.mpr
    intro i
    simp only [eval_line]
    apply ContinuousAt.eventually_lt continuousAt_const
      (by fun_prop)
    simpa using hy i
  obtain ⟨δ, hδ, hh⟩ := Metric.mem_nhds_iff.mp h
  refine ⟨δ, hδ, fun t ht => hh ?_⟩
  simpa [Metric.mem_ball, Real.dist_eq] using ht

/-- Every essential row has a feasible zero where every other row is strict. -/
theorem exists_isolated_zero (Q : AffineSubspace ℝ E) (s : I → E →ᵃ[ℝ] ℝ)
    (o : E) (ho : o ∈ Q) (hnorm : ∀ i, s i o = 1)
    (hessential : ∀ i, ∃ z ∈ Q, s i z < 0 ∧ ∀ j, j ≠ i → 0 ≤ s j z)
    (i : I) : ∃ q ∈ Q, s i q = 0 ∧ ∀ j, j ≠ i → 0 < s j q := by
  obtain ⟨z, hz, hzi, hzj⟩ := hessential i
  let t : ℝ := 1 / (1 - s i z)
  have hd : 0 < 1 - s i z := by linarith
  have ht : 0 < t := one_div_pos.mpr hd
  have ht1 : t < 1 := (div_lt_one hd).mpr (by linarith)
  refine ⟨AffineMap.lineMap o z t, AffineMap.lineMap_mem t ho hz, ?_, ?_⟩
  · rw [eval_line, hnorm]
    dsimp [t]
    field_simp
    ring
  · intro j hji
    rw [eval_line, hnorm]
    have := mul_nonneg ht.le (hzj j hji)
    nlinarith

/-- An affine function can be evaluated on a translated scalar displacement. -/
lemma eval_displacement (f : E →ᵃ[ℝ] ℝ) (x y z : E) (t : ℝ) :
    f (t • (y -ᵥ x) +ᵥ z) = t * (f y - f x) + f z := by
  rw [f.map_vadd, map_smul, f.linearMap_vsub]
  rfl

/-- A normalized supporting affine function vanishing at an isolated row zero
is exactly that row on the affine slice. -/
theorem supporting_eq_row [Finite I]
    (Q : AffineSubspace ℝ E) (s : I → E →ᵃ[ℝ] ℝ)
    (o : E) (ho : o ∈ Q) (hnorm : ∀ i, s i o = 1)
    (i : I) (q : E) (hq : q ∈ Q) (hqi : s i q = 0)
    (hqj : ∀ j, j ≠ i → 0 < s j q)
    (f : E →ᵃ[ℝ] ℝ) (hf : ∀ z ∈ feasible Q s, 0 ≤ f z)
    (hfq : f q = 0) (hfo : f o = 1) :
    ∀ z ∈ Q, f z = s i z := by
  have hkernel : ∀ z ∈ Q, s i z = 0 → f z = 0 := by
    intro z hz hzi
    obtain ⟨δ, hδ, hstep⟩ := exists_small_step
      (fun j : {j : I // j ≠ i} => s j.val) q z (fun j => hqj j.val j.property)
    have hmem (t : ℝ) (ht : |t| < δ) : AffineMap.lineMap q z t ∈ feasible Q s := by
      refine ⟨AffineMap.lineMap_mem t hq hz, ?_⟩
      intro j
      by_cases hji : j = i
      · subst j
        rw [eval_line, hqi, hzi]
        simp
      · exact (hstep t ht ⟨j, hji⟩).le
    have hp := hf _ (hmem (δ / 2) (by rw [abs_of_pos (by positivity)]; linarith))
    have hm := hf _ (hmem (-(δ / 2)) (by rw [abs_neg, abs_of_pos (by positivity)]; linarith))
    rw [eval_line, hfq] at hp hm
    nlinarith
  intro z hz
  let w := (s i z) • (q -ᵥ o) +ᵥ z
  have hw : w ∈ Q := Q.smul_vsub_vadd_mem _ hq ho hz
  have hwi : s i w = 0 := by
    dsimp only [w]
    rw [eval_displacement, hqi, hnorm]
    ring
  have hfw := hkernel w hw hwi
  dsimp only [w] at hfw
  rw [eval_displacement, hfq, hfo] at hfw
  linarith

/-- Essential rows are distinct even when restricted to the affine slice. -/
theorem row_injective (Q : AffineSubspace ℝ E) (s : I → E →ᵃ[ℝ] ℝ)
    (hessential : ∀ i, ∃ z ∈ Q, s i z < 0 ∧ ∀ j, j ≠ i → 0 ≤ s j z)
    {i j : I} (h : ∀ z ∈ Q, s i z = s j z) : i = j := by
  by_contra hij
  obtain ⟨z, hz, hzi, hzj⟩ := hessential i
  have hj := hzj j (Ne.symm hij)
  rw [← h z hz] at hj
  linarith

/-- A symmetry cannot send an isolated facet point to a strict feasible point:
a short step away from the fixed normalized point would contradict feasibility
of its preimage. -/
theorem exists_zero_image [Finite I]
    (Q : AffineSubspace ℝ E) (s : I → E →ᵃ[ℝ] ℝ)
    (o : E) (ho : o ∈ Q) (hnorm : ∀ i, s i o = 1)
    (e : E ≃ᵃ[ℝ] E) (hQ : ∀ z, e z ∈ Q ↔ z ∈ Q)
    (hP : ∀ z, e z ∈ feasible Q s ↔ z ∈ feasible Q s) (hfix : e o = o)
    (i : I) (q : E) (hq : q ∈ feasible Q s) (hqi : s i q = 0) :
    ∃ j, s j (e q) = 0 := by
  by_contra hn
  have hstrict : ∀ j, 0 < s j (e q) := by
    intro j
    have hnonneg := ((hP q).mpr hq).2 j
    have hne : s j (e q) ≠ 0 := fun hj => hn ⟨j, hj⟩
    exact lt_of_le_of_ne hnonneg (Ne.symm hne)
  obtain ⟨δ, hδ, hstep⟩ := exists_small_step s (e q) o hstrict
  let t : ℝ := -(δ / 2)
  have ht : |t| < δ := by
    dsimp [t]
    rw [abs_neg, abs_of_pos (by positivity)]
    linarith
  have hmem : e (AffineMap.lineMap q o t) ∈ feasible Q s := by
    rw [e.apply_lineMap, hfix]
    exact ⟨AffineMap.lineMap_mem t ((hQ q).mpr hq.1) ho,
      fun j => (hstep t ht j).le⟩
  have hh := ((hP _).mp hmem).2 i
  rw [eval_line, hqi, hnorm] at hh
  dsimp [t] at hh
  linarith

/-- Genuine polyhedron invariance, irredundancy and a fixed strict normalized
point force unique row covariance. No row/facet action is assumed. -/
theorem existsUnique_row [Finite I]
    (Q : AffineSubspace ℝ E) (s : I → E →ᵃ[ℝ] ℝ)
    (o : E) (ho : o ∈ Q) (hnorm : ∀ i, s i o = 1)
    (hessential : ∀ i, ∃ z ∈ Q, s i z < 0 ∧ ∀ j, j ≠ i → 0 ≤ s j z)
    (e : E ≃ᵃ[ℝ] E) (hQ : ∀ z, e z ∈ Q ↔ z ∈ Q)
    (hP : ∀ z, e z ∈ feasible Q s ↔ z ∈ feasible Q s) (hfix : e o = o)
    (i : I) : ∃! j, ∀ z ∈ Q, s j (e z) = s i z := by
  obtain ⟨q, hq, hqi, hqj⟩ := exists_isolated_zero Q s o ho hnorm hessential i
  have hqP : q ∈ feasible Q s := by
    refine ⟨hq, fun j => ?_⟩
    by_cases hji : j = i
    · subst j
      exact hqi.ge
    · exact (hqj j hji).le
  obtain ⟨j, hj⟩ := exists_zero_image Q s o ho hnorm e hQ hP hfix i q hqP hqi
  have hcov : ∀ z ∈ Q, s j (e z) = s i z := by
    apply supporting_eq_row Q s o ho hnorm i q hq hqi hqj ((s j).comp e.toAffineMap)
    · exact fun z hz => ((hP z).mpr hz).2 j
    · exact hj
    · change s j (e o) = 1
      rw [hfix, hnorm]
  refine ⟨j, hcov, ?_⟩
  intro k hk
  apply row_injective Q s hessential
  intro z hz
  have hz' : e.symm z ∈ Q := (hQ (e.symm z)).mp (by simpa using hz)
  have hh := (hk (e.symm z) hz').trans (hcov (e.symm z) hz').symm
  simpa using hh

section Permutation

variable [Finite I]
variable (Q : AffineSubspace ℝ E) (s : I → E →ᵃ[ℝ] ℝ)
variable (o : E) (ho : o ∈ Q) (hnorm : ∀ i, s i o = 1)
variable (hessential : ∀ i, ∃ z ∈ Q, s i z < 0 ∧ ∀ j, j ≠ i → 0 ≤ s j z)
variable (e : E ≃ᵃ[ℝ] E) (hQ : ∀ z, e z ∈ Q ↔ z ∈ Q)
variable (hP : ∀ z, e z ∈ feasible Q s ↔ z ∈ feasible Q s) (hfix : e o = o)

/-- The uniquely determined target row of a symmetry. -/
def rowIndex (i : I) : I :=
  Classical.choose (existsUnique_row Q s o ho hnorm hessential e hQ hP hfix i)

theorem rowIndex_covariance (i : I) (z : E) (hz : z ∈ Q) :
    s (rowIndex Q s o ho hnorm hessential e hQ hP hfix i) (e z) = s i z :=
  (Classical.choose_spec (existsUnique_row Q s o ho hnorm hessential e hQ hP hfix i)).1 z hz

theorem rowIndex_injective :
    Function.Injective (rowIndex Q s o ho hnorm hessential e hQ hP hfix) := by
  intro i j hij
  apply row_injective Q s hessential
  intro z hz
  rw [← rowIndex_covariance Q s o ho hnorm hessential e hQ hP hfix i z hz,
    ← rowIndex_covariance Q s o ho hnorm hessential e hQ hP hfix j z hz, hij]

/-- The canonical row permutation induced by an affine symmetry. -/
def rowPerm : Equiv.Perm I :=
  Equiv.ofBijective (rowIndex Q s o ho hnorm hessential e hQ hP hfix)
    ⟨rowIndex_injective Q s o ho hnorm hessential e hQ hP hfix,
      Finite.surjective_of_injective
        (rowIndex_injective Q s o ho hnorm hessential e hQ hP hfix)⟩

theorem rowPerm_covariance (i : I) (z : E) (hz : z ∈ Q) :
    s (rowPerm Q s o ho hnorm hessential e hQ hP hfix i) (e z) = s i z :=
  rowIndex_covariance Q s o ho hnorm hessential e hQ hP hfix i z hz

variable {G : Type*} [Group G]

/-- Genuine affine group symmetries induce a canonical permutation action on
normalized essential inequalities. Multiplication follows from covariance
uniqueness, rather than an assumed action on facets. -/
def rowAction (rho : G →* (E ≃ᵃ[ℝ] E))
    (hQ : ∀ g z, rho g z ∈ Q ↔ z ∈ Q)
    (hP : ∀ g z, rho g z ∈ feasible Q s ↔ z ∈ feasible Q s)
    (hfix : ∀ g, rho g o = o) : G →* Equiv.Perm I := by
  let p : G → Equiv.Perm I := fun g =>
    rowPerm Q s o ho hnorm hessential (rho g) (hQ g) (hP g) (hfix g)
  have hp (g : G) (i : I) (z : E) (hz : z ∈ Q) : s (p g i) (rho g z) = s i z :=
    rowPerm_covariance Q s o ho hnorm hessential (rho g) (hQ g) (hP g) (hfix g) i z hz
  refine { toFun := p, map_one' := ?_, map_mul' := ?_ }
  · ext i
    apply (existsUnique_row Q s o ho hnorm hessential
      (rho 1) (hQ 1) (hP 1) (hfix 1) i).unique (hp 1 i)
    intro z hz
    simp
  · intro g h
    ext i
    apply (existsUnique_row Q s o ho hnorm hessential
      (rho (g * h)) (hQ (g * h)) (hP (g * h)) (hfix (g * h)) i).unique (hp (g * h) i)
    intro z hz
    change s (p g (p h i)) (rho (g * h) z) = s i z
    have he : rho (g * h) z = rho g (rho h z) := by rw [map_mul]; rfl
    rw [he, hp g (p h i) (rho h z) ((hQ h z).mpr hz), hp h i z hz]

theorem rowAction_covariance (rho : G →* (E ≃ᵃ[ℝ] E))
    (hQ : ∀ g z, rho g z ∈ Q ↔ z ∈ Q)
    (hP : ∀ g z, rho g z ∈ feasible Q s ↔ z ∈ feasible Q s)
    (hfix : ∀ g, rho g o = o) (g : G) (i : I) (z : E) (hz : z ∈ Q) :
    s (rowAction Q s o ho hnorm hessential rho hQ hP hfix g i) (rho g z) = s i z :=
  rowPerm_covariance Q s o ho hnorm hessential (rho g) (hQ g) (hP g) (hfix g) i z hz

end Permutation
end
end Lemmata.SpanningTreeSymmetricEF.SlackPermutation
