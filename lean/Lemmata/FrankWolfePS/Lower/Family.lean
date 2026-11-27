module

public import Lemmata.FrankWolfePS.Lower.Measurable
public import Lemmata.FrankWolfePS.Lower.Results
public import Lemmata.FrankWolfePS.Upper.Main
public import Lemmata.FrankWolfe.Defs
public import Lemmata.FrankWolfeLDS.Defs

@[expose] public section

/-!
# Facts about the hard family

The hard body `physicalBody a r I` (the simplex `{(a u, r) : u ∈ Δ_I}` plus the ball of radius
`r`) has `1/r`-Lipschitz unit normals and no better constant; it is not uniformly convex for any
modulus (its bottom face is flat). The hard objective has the explicit minimizer `z⋆`: the
nearest point to the center `(0, -32 r)`. At `z⋆` the vertex oracle returns a vertex of the
optimal face, at distance from `z⋆`, while `⟪∇f(z⋆), z⋆ - lmo⟫ = 0`: local dual sharpness fails
at the optimum, for every constant.
-/

namespace Lemmata.FrankWolfePS
open Finset
open scoped BigOperators RealInnerProductSpace Pointwise

section FamilyFacts
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
theorem scalePt_core {a : ℝ} (ha : a ≠ 0) (r : ℝ) (u : ι → ℝ) :
    scalePt a ((u, r / a) : Pt ι) = (a • u, r) := by
  ext i
  · simp [scalePt]
  · simp only [scalePt]; field_simp

omit [DecidableEq ι] in
/-- Membership in the hard body. -/
theorem mem_physicalBody {a r : ℝ} (ha : 0 < a) (I : Finset ι) (z : Ambient ι) :
    z ∈ physicalBody a r I ↔ ∃ u, Base I u ∧ ‖z - embed (a • u, r)‖ ≤ r := by
  rw [physical_parallel ha]
  constructor
  · rintro ⟨_, ⟨w, ⟨u, hu, rfl⟩, rfl⟩, hz⟩
    refine ⟨u, hu, ?_⟩
    rwa [← scalePt_core ha.ne' r u, scale_embed]
  · rintro ⟨u, hu, hz⟩
    refine ⟨embed (a • u, r), ⟨embed (u, r / a), ⟨u, hu, rfl⟩, ?_⟩, hz⟩
    show a • embed (u, r / a) = embed (a • u, r)
    rw [← scale_embed, scalePt_core ha.ne' r u]

/-- The upward unit vector. -/
noncomputable def vert : Ambient ι := embed (fun _ => 0, 1)

omit [DecidableEq ι] in
theorem inner_vert (z : Ambient ι) : ⟪vert, z⟫ = z none := by
  conv_lhs => rw [← embed_coords z]
  rw [inner_embed]; simp [vert, embed, coords]

omit [DecidableEq ι] in
theorem norm_vert : ‖(vert : Ambient ι)‖ = 1 := by
  have h := real_inner_self_eq_norm_sq (vert : Ambient ι)
  rw [inner_vert] at h
  have hv : (vert : Ambient ι) none = 1 := rfl
  rw [hv] at h
  nlinarith [norm_nonneg (vert : Ambient ι)]

omit [Fintype ι] [DecidableEq ι] in
theorem embed_none (z : Pt ι) : embed z none = z.2 := rfl

omit [Fintype ι] [DecidableEq ι] in
theorem embed_sub_embed (z w : Pt ι) : embed z - embed w = embed (z - w) := by
  ext i; cases i <;> rfl

omit [DecidableEq ι] in
theorem inner_embed_embed (x y : Pt ι) :
    ⟪embed x, embed y⟫ = ∑ i, x.1 i * y.1 i + x.2 * y.2 := by
  rw [inner_embed]; rfl

omit [DecidableEq ι] in
/-- Heights in the hard body lie in `[0, 2r]`. -/
theorem physicalBody_height {a r : ℝ} (ha : 0 < a) {I : Finset ι} {z : Ambient ι}
    (hz : z ∈ physicalBody a r I) : 0 ≤ z none ∧ z none ≤ 2 * r := by
  obtain ⟨u, hu, hd⟩ := (mem_physicalBody ha I z).mp hz
  have h1 := PiLp.norm_apply_le (z - embed (a • u, r)) none
  rw [PiLp.sub_apply, embed_none, Real.norm_eq_abs] at h1
  have := abs_le.mp (h1.trans hd)
  have hr : 0 ≤ r := (norm_nonneg _).trans hd
  constructor <;> linarith [this.1, this.2]

omit [DecidableEq ι] in
theorem vertical_dist {r : ℝ} (hr : 0 ≤ r) (x : ι → ℝ) (t : ℝ) :
    ‖embed ((x, t) : Pt ι) - embed (x, t + r)‖ = r := by
  have H := embed_dist_sq ((x, t) : Pt ι) (x, t + r)
  have h2 : ‖embed ((x, t) : Pt ι) - embed (x, t + r)‖ ^ 2 = r ^ 2 := by
    rw [H]; simp [sq]
  exact (pow_left_inj₀ (norm_nonneg _) hr two_ne_zero).mp h2

/-- **The smoothness constant is exact.** No constant below `1/r` bounds the normals. -/
theorem not_lipschitzNormals_of_lt {a r : ℝ} (ha : 0 < a) (hr : 0 < r) {I : Finset ι}
    (hne : I.Nonempty) {β' : ℝ} (hβ' : β' < 1 / r) :
    ¬ Upper.LipschitzNormals (physicalBody a r I) β' := by
  intro h
  obtain ⟨i, hi⟩ := hne
  set v : Ambient ι := embed (a • atom i, r) with hvdef
  have nr : ‖r • (vert : Ambient ι)‖ = r := by
    rw [norm_smul, norm_vert, Real.norm_eq_abs, abs_of_pos hr, mul_one]
  have hz : v + r • vert ∈ physicalBody a r I := (mem_physicalBody ha I _).mpr
    ⟨atom i, atom_base hi, by rw [← hvdef, add_sub_cancel_left, nr]⟩
  have hw : v - r • vert ∈ physicalBody a r I := (mem_physicalBody ha I _).mpr
    ⟨atom i, atom_base hi, by rw [← hvdef, sub_sub_cancel_left, norm_neg, nr]⟩
  have hvn : v none = r := rfl
  have hvert : (vert : Ambient ι) none = 1 := rfl
  have sz : Supports (physicalBody a r I) (v + r • vert) vert := fun y hy => by
    rw [inner_vert, inner_vert, PiLp.add_apply, PiLp.smul_apply, hvn, hvert, smul_eq_mul]
    linarith [(physicalBody_height ha hy).2]
  have sw : Supports (physicalBody a r I) (v - r • vert) (-vert) := fun y hy => by
    rw [inner_neg_left, inner_neg_left, inner_vert, inner_vert, PiLp.sub_apply, PiLp.smul_apply,
      hvn, hvert, smul_eq_mul]
    linarith [(physicalBody_height ha hy).1]
  have H := h _ hz _ hw vert (-vert) norm_vert (by rw [norm_neg, norm_vert]) sz sw
  have e1 : vert - -vert = (2 : ℝ) • (vert : Ambient ι) := by rw [sub_neg_eq_add, two_smul]
  have e2 : v + r • vert - (v - r • vert) = (2 * r) • (vert : Ambient ι) := by
    rw [mul_smul, two_smul]; abel
  rw [e1, e2, norm_smul, norm_smul, norm_vert, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos (by positivity : 0 < 2 * r)] at H
  have : 1 / r ≤ β' := by
    rw [div_le_iff₀ hr]; nlinarith
  linarith

/-- **The hard body is not uniformly convex**, for any modulus: its bottom face is flat. -/
theorem not_uniformlyConvex {a r : ℝ} (ha : 0 < a) (hr : 0 < r) {I : Finset ι}
    (hI : 1 < I.card) {α : ℝ} (hα : 0 < α) :
    ¬ Lemmata.FrankWolfe.IsUniformlyConvexSet (physicalBody a r I) α 2 := by
  intro h
  obtain ⟨i, hi, j, hj, hij⟩ := one_lt_card.mp hI
  have bottom (k : ι) (hk : k ∈ I) : embed (a • atom k, 0) ∈ physicalBody a r I :=
    (mem_physicalBody ha I _).mpr ⟨atom k, atom_base hk, by
      have := vertical_dist hr.le (a • atom k) 0
      rw [zero_add] at this; exact this.le⟩
  have hxy : (embed (a • atom i, 0) : Ambient ι) ≠ embed (a • atom j, 0) := by
    intro e
    have := congrArg (fun z : Ambient ι => z (some i)) e
    simp [embed, atom, hij, ha.ne'] at this
  have hpos : 0 < ‖(embed (a • atom i, 0) : Ambient ι) - embed (a • atom j, 0)‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hp := h _ (bottom i hi) _ (bottom j hj) (1 / 2) ⟨by norm_num, by norm_num⟩ (-vert)
    (by rw [norm_neg, norm_vert])
  have ht := (physicalBody_height ha hp).1
  have hvert : (vert : Ambient ι) none = 1 := rfl
  simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.neg_apply, embed_none, hvert,
    smul_eq_mul] at ht
  have hX := mul_pos hα (pow_pos hpos 2)
  norm_num at ht
  nlinarith

/-! ## The explicit minimizer and local dual sharpness -/

/-- The barycenter `(a 1_I / |I|, r)` of the core. -/
noncomputable def baryPoint (a r : ℝ) (I : Finset ι) : Ambient ι :=
  embed (a • simplexBarycenter I, r)

/-- The center `(0, -32 r)` of the hard objective. -/
noncomputable def hardCenter (r : ℝ) : Ambient ι := embed (fun _ => 0, -32 * r)

/-- The minimizer of the hard objective on the hard body: the point of the body nearest to the
center, `b₀ + (r / ‖b₀ - c‖) (c - b₀)` with `b₀` the barycenter of the core. -/
noncomputable def hardMinimizer (a r : ℝ) (I : Finset ι) : Ambient ι :=
  baryPoint a r I + (r / ‖baryPoint a r I - hardCenter r‖) • (hardCenter r - baryPoint a r I)

omit [DecidableEq ι] in
theorem hardObjective_eq (L r : ℝ) (z : Ambient ι) :
    hardObjective L r z =
      L / 2 * ‖z - hardCenter r‖ ^ 2 - L / 2 * ‖(hardCenter r : Ambient ι)‖ ^ 2 := by
  have e : (embed (fun _ : ι => 0, 32 * L * r) : Ambient ι) = (-L) • hardCenter r := by
    rw [hardCenter, ← scale_embed]; congr 1; ext i <;> simp [scalePt]; ring
  rw [hardObjective, quadratic, e, norm_sub_sq_real, real_inner_smul_left,
    real_inner_comm (hardCenter r) z]
  ring

/-- Every core point is orthogonal to `b₀ - c` relative to `b₀`. -/
theorem core_orthogonal {a r : ℝ} {I : Finset ι} (hne : I.Nonempty) {u : ι → ℝ}
    (hu : Base I u) :
    ⟪embed (a • u, r) - baryPoint a r I, baryPoint a r I - hardCenter r⟫ = 0 := by
  rw [baryPoint, hardCenter, embed_sub_embed, embed_sub_embed, inner_embed_embed]
  have hc : (I.card : ℝ) ≠ 0 := by exact_mod_cast (card_pos.mpr hne).ne'
  simp only [Prod.fst_sub, Prod.snd_sub, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_self,
    zero_mul, add_zero, sub_zero]
  have term (i : ι) : (a * u i - a * simplexBarycenter I i) * (a * simplexBarycenter I i) =
      if i ∈ I then a ^ 2 / I.card * u i - a ^ 2 / (I.card : ℝ) ^ 2 else 0 := by
    by_cases hi : i ∈ I
    · simp only [simplexBarycenter, hi, ite_true]; field_simp
    · simp [simplexBarycenter, hi, hu.2.1 i hi]
  rw [Finset.sum_congr rfl fun i _ => term i, Finset.sum_ite_mem, Finset.univ_inter,
    Finset.sum_sub_distrib, ← Finset.mul_sum, hu.2.2, Finset.sum_const, nsmul_eq_mul]
  field_simp; ring

theorem dist_center_ge {a r : ℝ} (hr : 0 ≤ r) (I : Finset ι) :
    33 * r ≤ ‖baryPoint a r I - hardCenter r‖ := by
  have h1 := PiLp.norm_apply_le (baryPoint a r I - hardCenter r) none
  have e : ((baryPoint a r I - hardCenter r : Ambient ι)) none = 33 * r := by
    rw [PiLp.sub_apply, baryPoint, hardCenter, embed_none, embed_none]; ring
  rw [e, Real.norm_eq_abs, abs_of_nonneg (by linarith)] at h1
  exact h1

/-- **The explicit minimizer** of the hard objective on the hard body. -/
theorem hardMinimizer_spec {L a r : ℝ} (hL : 0 < L) (ha : 0 < a) (hr : 0 < r) {I : Finset ι}
    (hne : I.Nonempty) :
    hardMinimizer a r I ∈ physicalBody a r I ∧
      ∀ z ∈ physicalBody a r I, hardObjective L r (hardMinimizer a r I) ≤ hardObjective L r z := by
  have H33 := dist_center_ge (a := a) hr.le I
  have orth (u : ι → ℝ) (hu : Base I u) := core_orthogonal (a := a) (r := r) hne hu
  set b := baryPoint a r I with hb
  set c : Ambient ι := hardCenter r with hc
  set H := ‖b - c‖ with hH
  have Hpos : 0 < H := by linarith
  have hm : hardMinimizer a r I = b + (r / H) • (c - b) := rfl
  constructor
  · refine (mem_physicalBody ha I _).mpr ⟨_, barycenter_base hne, ?_⟩
    rw [hm, show (embed (a • simplexBarycenter I, r) : Ambient ι) = b from rfl,
      add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hr Hpos),
      norm_sub_rev, ← hH, div_mul_cancel₀ _ Hpos.ne']
  · intro z hz
    obtain ⟨u, hu, hd⟩ := (mem_physicalBody ha I z).mp hz
    have key : H * (H - r) ≤ ⟪z - c, b - c⟫ := by
      have e : z - c = (embed (a • u, r) - b) + (b - c) + (z - embed (a • u, r)) := by abel
      rw [e, inner_add_left, inner_add_left, orth u hu, real_inner_self_eq_norm_sq, ← hH]
      have h2 := neg_le_of_abs_le (abs_real_inner_le_norm (z - embed (a • u, r)) (b - c))
      rw [← hH] at h2
      nlinarith [mul_le_mul_of_nonneg_right hd Hpos.le]
    have hz' : H - r ≤ ‖z - c‖ := by
      have := real_inner_le_norm (z - c) (b - c)
      rw [← hH] at this
      nlinarith
    have hHr : 0 ≤ H - r := by linarith
    have hstar : ‖hardMinimizer a r I - c‖ = H - r := by
      have e : hardMinimizer a r I - c = (1 - r / H) • (b - c) := by
        rw [hm, sub_smul, one_smul, smul_sub, smul_sub]; abel
      have h1 : 0 ≤ 1 - r / H := by rw [sub_nonneg, div_le_one Hpos]; linarith
      rw [e, norm_smul, Real.norm_eq_abs, abs_of_nonneg h1, ← hH]
      field_simp
    rw [hardObjective_eq, hardObjective_eq, ← hc, hstar]
    nlinarith [pow_le_pow_left₀ hHr hz' 2]

end FamilyFacts

section Sharpness
variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- **Local dual sharpness fails at the optimum** for the vertex oracle: for every constant
`A > 0`, every exponent `q` and every set `M` containing the minimizer. -/
theorem not_localDualSharpness {a r : ℝ} (ha : 0 < a) (hr : 0 < r) {anchor : ι}
    {I : Finset ι} (hI : 1 < I.card) (M : Set (Ambient ι)) (hM : hardMinimizer a r I ∈ M)
    {A q : ℝ} (hA : 0 < A) :
    ¬ Lemmata.FrankWolfeLDS.LocalDualSharpness (physicalBody a r I) (physOracle a r anchor I)
      M A q := by
  rintro ⟨ρ, hρ, H⟩
  have hne : I.Nonempty := card_pos.mp (by omega)
  have H33 := dist_center_ge (a := a) hr.le I
  have orth (u : ι → ℝ) (hu : Base I u) := core_orthogonal (a := a) (r := r) hne hu
  have mem := (hardMinimizer_spec (L := 1) one_pos ha hr hne).1
  set b := baryPoint a r I with hb
  set c : Ambient ι := hardCenter r with hc
  set g := b - c with hg
  have gpos : 0 < ‖g‖ := by linarith
  have g0 : g ≠ 0 := norm_pos_iff.mp gpos
  have hm : hardMinimizer a r I = b + (r / ‖g‖) • (c - b) := rfl
  -- the vertex oracle returns a vertex of the optimal face
  obtain ⟨j, hj, hf, -⟩ := first_rank_spec (fun i => g (some i)) hne
  have hf' : first I (orderFor g) = some j := by rw [orderFor, ite_eq_right g0]; exact hf
  have har : a * (r / a) = r := by field_simp
  have hor : physOracle a r anchor I g = embed (a • atom j, r) - r • unit g := by
    rw [physOracle, oracle, hf', decode, smul_sub, smul_smul, har, ← scale_embed,
      scalePt_core ha.ne' r (atom j)]
  have hstar : hardMinimizer a r I - physOracle a r anchor I g = b - embed (a • atom j, r) := by
    rw [hor, hm, unit, smul_smul]
    have e : (r / ‖g‖) • (c - b) + (r * ‖g‖⁻¹) • g = 0 := by
      rw [div_eq_mul_inv, ← smul_add, hg]
      rw [show c - b + (b - c) = 0 by abel, smul_zero]
    rw [show b + (r / ‖g‖) • (c - b) - (embed (a • atom j, r) - (r * ‖g‖⁻¹) • g) =
      b - embed (a • atom j, r) + ((r / ‖g‖) • (c - b) + (r * ‖g‖⁻¹) • g) by abel, e, add_zero]
  have zero : ⟪g, hardMinimizer a r I - physOracle a r anchor I g⟫ = 0 := by
    rw [hstar, ← neg_sub (embed (a • atom j, r)) b, inner_neg_right, real_inner_comm,
      orth _ (atom_base hj), neg_zero]
  have far : 0 < ‖hardMinimizer a r I - physOracle a r anchor I g‖ := by
    rw [hstar, norm_pos_iff, sub_ne_zero]
    obtain ⟨i, hi, hij⟩ := exists_mem_ne hI j
    intro e
    have := congrArg (fun z : Ambient ι => z (some i)) e
    have hc' : (I.card : ℝ) ≠ 0 := by exact_mod_cast (card_pos.mpr hne).ne'
    simp [b, baryPoint, embed, simplexBarycenter, hi, atom, hij, ha.ne', hc'] at this
  have hd : Metric.infDist (hardMinimizer a r I) M < ρ := by
    rw [Metric.infDist_zero_of_mem hM]; exact hρ
  have key := H _ mem hd g
  rw [zero] at key
  have : 0 < A * ‖g‖ * ‖hardMinimizer a r I - physOracle a r anchor I g‖ ^ q :=
    mul_pos (mul_pos hA gpos) (Real.rpow_pos_of_pos far q)
  linarith

end Sharpness

end Lemmata.FrankWolfePS
