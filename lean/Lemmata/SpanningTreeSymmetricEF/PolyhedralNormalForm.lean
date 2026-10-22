module

public import Lemmata.SpanningTreeSymmetricEF.PolyhedralReduction
public import Lemmata.SpanningTreeSymmetricEF.AffineReynolds
public import Lemmata.SpanningTreeSymmetricEF.SlackPermutation

@[expose] public section


/-! A coordinate-slack lift adds only affine equations, not inequalities.
The final normal-form theorem derives its row action from polyhedral invariance;
these helpers implement the actual affine slice and projection. -/
namespace Lemmata.SpanningTreeSymmetricEF.PolyhedralNormalForm
open scoped BigOperators
open CoordinateLowerBounds
noncomputable section

variable {G E F I : Type*} [Group G]
variable [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

/-- Pullback action on actual scalar slack coordinates. -/
def coordinateEquiv (e : Equiv.Perm I) : (I → ℝ) ≃ₗ[ℝ] (I → ℝ) where
  toFun u i := u (e.symm i)
  invFun u i := u (e i)
  left_inv u := by funext i; simp
  right_inv u := by funext i; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The old auxiliary action paired with literal coordinate permutations. -/
def liftedAction (rho : G →* (E ≃ᵃ[ℝ] E)) (sigma : G →* Equiv.Perm I) :
    G →* ((E × (I → ℝ)) ≃ᵃ[ℝ] (E × (I → ℝ))) where
  toFun g := (rho g).prodCongr (coordinateEquiv (sigma g)).toAffineEquiv
  map_one' := by
    ext z
    · simp
    · simp only [map_one]
      rfl
  map_mul' g h := by
    ext z
    · simp [map_mul]
    · simp only [map_mul]
      rfl

/-- Embedding as the graph of the affine slack map. -/
def graphMap (s : I → E →ᵃ[ℝ] ℝ) : E →ᵃ[ℝ] (E × (I → ℝ)) :=
  (AffineMap.id ℝ E).prod (AffineMap.pi s)

/-- The added graph conditions are affine equations and cost no inequalities. -/
def graphSlice (Q : AffineSubspace ℝ E) (s : I → E →ᵃ[ℝ] ℝ) :
    AffineSubspace ℝ (E × (I → ℝ)) := Q.map (graphMap s)

/-- One scalar inequality for each retained row, with no duplication. -/
def coordinateSlack (i : I) : (E × (I → ℝ)) →ᵃ[ℝ] ℝ :=
  ((LinearMap.proj i).comp (LinearMap.snd ℝ E (I → ℝ))).toAffineMap

/-- Actual affine projection, ignoring the additional slack coordinates. -/
def graphProjection (p : E →ᵃ[ℝ] F) : (E × (I → ℝ)) →ᵃ[ℝ] F :=
  p.comp AffineMap.fst

theorem lifted_graph (rho : G →* (E ≃ᵃ[ℝ] E)) (sigma : G →* Equiv.Perm I)
    (Q : AffineSubspace ℝ E) (s : I → E →ᵃ[ℝ] ℝ)
    (hc : ∀ g i z, z ∈ Q → s (sigma g i) (rho g z) = s i z)
    (g : G) (z : E) (hz : z ∈ Q) :
    liftedAction rho sigma g (graphMap s z) = graphMap s (rho g z) := by
  apply Prod.ext
  · rfl
  · funext i
    have hh := hc g ((sigma g).symm i) z hz
    simpa [liftedAction, coordinateEquiv, graphMap] using hh.symm

theorem graphSlice_stable (rho : G →* (E ≃ᵃ[ℝ] E)) (sigma : G →* Equiv.Perm I)
    (Q : AffineSubspace ℝ E) (s : I → E →ᵃ[ℝ] ℝ)
    (hQ : ∀ g z, z ∈ Q → rho g z ∈ Q)
    (hc : ∀ g i z, z ∈ Q → s (sigma g i) (rho g z) = s i z)
    (g : G) (z : E × (I → ℝ)) (hz : z ∈ graphSlice Q s) :
    liftedAction rho sigma g z ∈ graphSlice Q s := by
  obtain ⟨x, hx, rfl⟩ := AffineSubspace.mem_map.mp hz
  exact AffineSubspace.mem_map.mpr ⟨rho g x, hQ g x hx,
    (lifted_graph rho sigma Q s hc g x hx).symm⟩

theorem coordinateSlack_equivariant (rho : G →* (E ≃ᵃ[ℝ] E))
    (sigma : G →* Equiv.Perm I) (g : G) (i : I) (z : E × (I → ℝ)) :
    coordinateSlack (sigma g i) (liftedAction rho sigma g z) = coordinateSlack i z := by
  simp [coordinateSlack, liftedAction, coordinateEquiv]

theorem graphImage_eq (Q : AffineSubspace ℝ E) (s : I → E →ᵃ[ℝ] ℝ)
    (p q : E →ᵃ[ℝ] F) (hpq : ∀ z ∈ feasible Q s, q z = p z) :
    SignedLift.lpImage (graphSlice Q s) coordinateSlack (graphProjection q) =
      SignedLift.lpImage Q s p := by
  ext y
  constructor
  · rintro ⟨w, hw, hs, hy⟩
    obtain ⟨z, hz, rfl⟩ := AffineSubspace.mem_map.mp hw
    have hz' : z ∈ feasible Q s := ⟨hz, hs⟩
    exact ⟨z, hz, hs, (hpq z hz').symm.trans hy⟩
  · rintro ⟨z, hz, hs, hy⟩
    exact ⟨graphMap s z, AffineSubspace.mem_map.mpr ⟨z, hz, rfl⟩, hs,
      (hpq z ⟨hz, hs⟩).trans hy⟩

/-- Stabilizing a set stabilizes its affine hull. No full-dimensionality is assumed. -/
theorem affineSpan_stable (rho : G →* (E ≃ᵃ[ℝ] E)) (P : Set E)
    (hP : ∀ g z, z ∈ P → rho g z ∈ P) (g : G) (z : E)
    (hz : z ∈ affineSpan ℝ P) : rho g z ∈ affineSpan ℝ P := by
  have hm : (affineSpan ℝ P).map (rho g).toAffineMap ≤ affineSpan ℝ P := by
    rw [AffineSubspace.map_span]
    exact affineSpan_mono ℝ (by rintro _ ⟨x,hx,rfl⟩; exact hP g x hx)
  exact hm (AffineSubspace.mem_map_of_mem _ hz)

/-- Canonical linear target action used to average an affine projection. -/
def edgeLinearAction (N : ℕ) : Equiv.Perm (Fin N) →*
    ((Sym2 (Fin N) → ℝ) ≃ₗ[ℝ] (Sym2 (Fin N) → ℝ)) where
  toFun g := edgeRelabel g
  map_one' := by ext x e; induction e using Sym2.inductionOn with | _ a b => rfl
  map_mul' g h := by ext x e; induction e using Sym2.inductionOn with | _ a b => rfl

/-- Covariance on an affine slice suffices: adding the slack graph produces
literal coordinate covariance on the whole new ambient space. -/
def graphSymmetry {N : ℕ} (rho : Equiv.Perm (Fin N) →* (E ≃ᵃ[ℝ] E))
    (sigma : Equiv.Perm (Fin N) →* Equiv.Perm I)
    (Q : AffineSubspace ℝ E) (s : I → E →ᵃ[ℝ] ℝ)
    (p : E →ᵃ[ℝ] (Sym2 (Fin N) → ℝ))
    (hQ : ∀ g z, z ∈ Q → rho g z ∈ Q)
    (hc : ∀ g i z, z ∈ Q → s (sigma g i) (rho g z) = s i z)
    (hp : ∀ g z, p (rho g z) = edgeAction N g (p z)) :
    letI := MulAction.compHom I sigma
    ScalarSymmetry (graphSlice Q s) coordinateSlack (graphProjection p) := by
  letI := MulAction.compHom I sigma
  exact ⟨liftedAction rho sigma, graphSlice_stable rho sigma Q s hQ hc,
    coordinateSlack_equivariant rho sigma, fun g z => hp g z.1⟩

/-- Rescaling actual rows by their value at a strict point does not alter
feasibility or introduce inequalities. -/
def normalizedSlack (a : I → E →ᵃ[ℝ] ℝ) (o : E) (i : I) : E →ᵃ[ℝ] ℝ :=
  (a i o)⁻¹ • a i

theorem normalizedSlack_one (a : I → E →ᵃ[ℝ] ℝ) (o : E)
    (ho : ∀ i, 0 < a i o) (i : I) : normalizedSlack a o i o = 1 := by
  change (a i o)⁻¹ * a i o = 1
  exact inv_mul_cancel₀ (ne_of_gt (ho i))

theorem normalized_feasible (Q : AffineSubspace ℝ E) (a : I → E →ᵃ[ℝ] ℝ)
    (o : E) (ho : ∀ i, 0 < a i o) :
    feasible Q (normalizedSlack a o) = feasible Q a := by
  ext z
  simp only [feasible, Set.mem_setOf_eq, normalizedSlack, AffineMap.coe_smul,
    Pi.smul_apply, smul_eq_mul]
  exact and_congr_right (fun _ => forall_congr' (fun i =>
    mul_nonneg_iff_of_pos_left (inv_pos.mpr (ho i))))

theorem normalized_essential (Q : AffineSubspace ℝ E) (a : I → E →ᵃ[ℝ] ℝ)
    (o : E) (ho : ∀ i, 0 < a i o)
    (ha : ∀ i, ∃ z ∈ Q, a i z < 0 ∧ ∀ j, j ≠ i → 0 ≤ a j z) :
    ∀ i, ∃ z ∈ Q, normalizedSlack a o i z < 0 ∧
      ∀ j, j ≠ i → 0 ≤ normalizedSlack a o j z := by
  intro i
  obtain ⟨z, hz, hi, hj⟩ := ha i
  exact ⟨z, hz, mul_neg_of_pos_of_neg (inv_pos.mpr (ho i)) hi,
    fun j hji => mul_nonneg (inv_pos.mpr (ho j)).le (hj j hji)⟩

/-- The output records an actual affine lift with a subset of the original
inequality indices, literal coordinate symmetry, and exactly the old image.
These fields are constructed below, not additional assumptions on an input LP. -/
structure NormalForm {N : ℕ} {J : Type*} (Q : AffineSubspace ℝ E)
    (a : J → E →ᵃ[ℝ] ℝ) (p : E →ᵃ[ℝ] (Sym2 (Fin N) → ℝ)) where
  rows : Finset J
  rowAction : Equiv.Perm (Fin N) →* Equiv.Perm rows
  slice : AffineSubspace ℝ (E × (rows → ℝ))
  projection : (E × (rows → ℝ)) →ᵃ[ℝ] (Sym2 (Fin N) → ℝ)
  symmetry : letI := MulAction.compHom rows rowAction
    ScalarSymmetry slice coordinateSlack projection
  image_eq : SignedLift.lpImage slice coordinateSlack projection = SignedLift.lpImage Q a p

theorem NormalForm.card_le {N : ℕ} {J : Type*} [Fintype J]
    {Q : AffineSubspace ℝ E} {a : J → E →ᵃ[ℝ] ℝ}
    {p : E →ᵃ[ℝ] (Sym2 (Fin N) → ℝ)} (d : NormalForm Q a p) :
    Fintype.card d.rows ≤ Fintype.card J := Fintype.card_subtype_le _

/-- Any nonempty finite affine LP with genuine affine group symmetry has a
normalized coordinate-slack presentation with no more inequalities and the
same projected relaxation. The input supplies only feasible-set preservation
and projection covariance there: no facet permutation, strict point, full
dimensionality, normalized slacks, or equivariant section is assumed. -/
theorem normalForm_exists {N : ℕ} {J : Type*} [Fintype J]
    (Q : AffineSubspace ℝ E) (a : J → E →ᵃ[ℝ] ℝ)
    (p : E →ᵃ[ℝ] (Sym2 (Fin N) → ℝ))
    (rho : Equiv.Perm (Fin N) →* (E ≃ᵃ[ℝ] E))
    (hne : (feasible Q a).Nonempty)
    (hstable : ∀ g z, z ∈ feasible Q a → rho g z ∈ feasible Q a)
    (hp : ∀ g z, z ∈ feasible Q a → p (rho g z) = edgeAction N g (p z)) :
    Nonempty (NormalForm Q a p) := by
  classical
  let d := Classical.choice (PolyhedralReduction.reducedDescription_exists Q a hne)
  let H := affineSpan ℝ (feasible Q a)
  let b : d.I → E →ᵃ[ℝ] ℝ := fun i => a i
  have hb : feasible H b = feasible Q a := d.feasible_eq
  have hbstable : ∀ g z, z ∈ feasible H b → rho g z ∈ feasible H b := by
    simpa only [hb] using hstable
  obtain ⟨o, ho, hbpos, hofix⟩ := AffineReynolds.exists_fixed_strict H b rho hbstable
    d.strict.choose d.strict.choose_spec.1 d.strict.choose_spec.2
  let s := normalizedSlack b o
  have hs : feasible H s = feasible Q a := (normalized_feasible H b o hbpos).trans hb
  have hn : ∀ i, s i o = 1 := normalizedSlack_one b o hbpos
  have he : ∀ i, ∃ z ∈ H, s i z < 0 ∧ ∀ j, j ≠ i → 0 ≤ s j z :=
    normalized_essential H b o hbpos d.essential
  have hH : ∀ g z, rho g z ∈ H ↔ z ∈ H := by
    intro g z
    constructor
    · intro hz
      have hh := affineSpan_stable rho _ hstable g⁻¹ (rho g z) hz
      simpa [map_inv, AffineEquiv.inv_def] using hh
    · exact affineSpan_stable rho _ hstable g z
  have hS : ∀ g z, rho g z ∈ feasible H s ↔ z ∈ feasible H s := by
    simp only [hs]
    intro g z
    constructor
    · intro hz
      have hh := hstable g⁻¹ (rho g z) hz
      simpa [map_inv, AffineEquiv.inv_def] using hh
    · exact hstable g z
  let sigma := SlackPermutation.rowAction H s o ho.1 hn he rho hH hS hofix
  have hc : ∀ g i z, z ∈ H → s (sigma g i) (rho g z) = s i z :=
    SlackPermutation.rowAction_covariance H s o ho.1 hn he rho hH hS hofix
  let p' := AffineReynolds.avgProjection rho (edgeLinearAction N) p
  have hp' : ∀ g z, p' (rho g z) = edgeAction N g (p' z) :=
    AffineReynolds.avgProjection_equivariant rho (edgeLinearAction N) p
  have hp'eq : ∀ z ∈ feasible H s, p' z = p z := by
    intro z hz
    exact AffineReynolds.avgProjection_eq_on rho (edgeLinearAction N) p
      (feasible Q a) hp z (hs ▸ hz)
  refine ⟨⟨d.I, sigma, graphSlice H s, graphProjection p',
    graphSymmetry rho sigma H s p' (fun g z => (hH g z).mpr) hc hp', ?_⟩⟩
  rw [graphImage_eq H s p p' hp'eq]
  ext x
  simp only [SignedLift.lpImage, Set.mem_setOf_eq, ← and_assoc]
  change (∃ z, z ∈ feasible H s ∧ p z = x) ↔
    (∃ z, z ∈ feasible Q a ∧ p z = x)
  rw [hs]

/-- General affine-symmetric LP lower bound. Only the named small-index theorem
remains external. Normalization, row action, and signed membership are derived. -/
theorem affine_lp_factor_lower {N : ℕ} {J : Type*} [Fintype J]
    (Q : AffineSubspace ℝ E) (a : J → E →ᵃ[ℝ] ℝ)
    (p : E →ᵃ[ℝ] (Sym2 (Fin N) → ℝ))
    (rho : Equiv.Perm (Fin N) →* (E ≃ᵃ[ℝ] E))
    (hstable : ∀ g z, z ∈ feasible Q a → rho g z ∈ feasible Q a)
    (hp : ∀ g z, z ∈ feasible Q a → p (rho g z) = edgeAction N g (p z))
    (smallIndex : SmallIndexK3Criterion) (hN : 13 ≤ N)
    (hrows : Fintype.card J < Nat.choose N 3) (beta : ℝ)
    (happrox : Approximation.MaxApproximation (ApproximationUpper.treeIncidence (V := Fin N))
      (SignedLift.lpImage Q a p) beta) :
    (3 / 2 : ℝ) * (1 - 1 / (N : ℝ)) ≤ beta := by
  classical
  have ht := happrox.contains
    ⟨HamiltonPath.graph (1 : Equiv.Perm (Fin N)), HamiltonPath.graph_isTree (by omega) 1⟩
  obtain ⟨z, hz, ha, _⟩ := ht
  obtain ⟨d⟩ := normalForm_exists Q a p rho ⟨z, hz, ha⟩ hstable hp
  letI := MulAction.compHom d.rows d.rowAction
  apply scalar_factor_lower d.slice coordinateSlack d.projection d.symmetry smallIndex hN
    (lt_of_le_of_lt d.card_le hrows) beta
  simpa only [d.image_eq] using happrox

/-- Better than the finite-n threshold requires at least choose(n,3) original
inequalities in any affine-symmetric LP description, not just normalized ones. -/
theorem affine_lp_size_lower {N : ℕ} {J : Type*} [Fintype J]
    (Q : AffineSubspace ℝ E) (a : J → E →ᵃ[ℝ] ℝ)
    (p : E →ᵃ[ℝ] (Sym2 (Fin N) → ℝ))
    (rho : Equiv.Perm (Fin N) →* (E ≃ᵃ[ℝ] E))
    (hstable : ∀ g z, z ∈ feasible Q a → rho g z ∈ feasible Q a)
    (hp : ∀ g z, z ∈ feasible Q a → p (rho g z) = edgeAction N g (p z))
    (smallIndex : SmallIndexK3Criterion) (hN : 13 ≤ N) (beta : ℝ)
    (hbeta : beta < (3 / 2 : ℝ) * (1 - 1 / (N : ℝ)))
    (happrox : Approximation.MaxApproximation (ApproximationUpper.treeIncidence (V := Fin N))
      (SignedLift.lpImage Q a p) beta) : Nat.choose N 3 ≤ Fintype.card J := by
  by_contra h
  exact (not_le_of_gt hbeta) (affine_lp_factor_lower Q a p rho hstable hp smallIndex hN
    (Nat.lt_of_not_ge h) beta happrox)

/-- Explicit sufficiently-large-n version for any fixed factor below 3/2. -/
theorem affine_lp_size_lower_of_fixed_factor {N : ℕ} {J : Type*} [Fintype J]
    (Q : AffineSubspace ℝ E) (a : J → E →ᵃ[ℝ] ℝ)
    (p : E →ᵃ[ℝ] (Sym2 (Fin N) → ℝ))
    (rho : Equiv.Perm (Fin N) →* (E ≃ᵃ[ℝ] E))
    (hstable : ∀ g z, z ∈ feasible Q a → rho g z ∈ feasible Q a)
    (hp : ∀ g z, z ∈ feasible Q a → p (rho g z) = edgeAction N g (p z))
    (smallIndex : SmallIndexK3Criterion) (hN : 13 ≤ N) (beta : ℝ)
    (hbeta : beta < 3 / 2) (hlarge : 3 / (3 - 2 * beta) < (N : ℝ))
    (happrox : Approximation.MaxApproximation (ApproximationUpper.treeIncidence (V := Fin N))
      (SignedLift.lpImage Q a p) beta) : Nat.choose N 3 ≤ Fintype.card J := by
  apply affine_lp_size_lower Q a p rho hstable hp smallIndex hN beta _ happrox
  apply (Approximation.threshold_exceeds_fixed_factor (N : ℝ) beta
    (by exact_mod_cast (show 0 < N by omega))).mpr
  have hh := (div_lt_iff₀ (show 0 < 3 - 2 * beta by linarith)).mp hlarge
  nlinarith

/-- The stronger path threshold already exceeds the old 5/4 threshold for n≥7. -/
theorem five_quarters_lt_threshold (N : ℕ) (hN : 7 ≤ N) :
    (5 / 4 : ℝ) < (3 / 2 : ℝ) * (1 - 1 / (N : ℝ)) := by
  apply (Approximation.threshold_exceeds_fixed_factor (N : ℝ) (5 / 4)
    (by exact_mod_cast (show 0 < N by omega))).mpr
  have hh : (7 : ℝ) ≤ N := by exact_mod_cast hN
  nlinarith

/-- The old factor-5/4 lower-bound result is subsumed (including its endpoint)
by the Hamilton-path proof. This does not formalize the original leaf-lift route. -/
theorem affine_lp_size_lower_of_factor_le_five_quarters {N : ℕ} {J : Type*} [Fintype J]
    (Q : AffineSubspace ℝ E) (a : J → E →ᵃ[ℝ] ℝ)
    (p : E →ᵃ[ℝ] (Sym2 (Fin N) → ℝ))
    (rho : Equiv.Perm (Fin N) →* (E ≃ᵃ[ℝ] E))
    (hstable : ∀ g z, z ∈ feasible Q a → rho g z ∈ feasible Q a)
    (hp : ∀ g z, z ∈ feasible Q a → p (rho g z) = edgeAction N g (p z))
    (smallIndex : SmallIndexK3Criterion) (hN : 13 ≤ N) (beta : ℝ)
    (hbeta : beta ≤ 5 / 4)
    (happrox : Approximation.MaxApproximation (ApproximationUpper.treeIncidence (V := Fin N))
      (SignedLift.lpImage Q a p) beta) : Nat.choose N 3 ≤ Fintype.card J :=
  affine_lp_size_lower Q a p rho hstable hp smallIndex hN beta
    (lt_of_le_of_lt hbeta (five_quarters_lt_threshold N (by omega))) happrox

end
end Lemmata.SpanningTreeSymmetricEF.PolyhedralNormalForm
