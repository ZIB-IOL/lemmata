module

public import Lemmata.Centroid.Proof.Linear.MaximalRank
public import Mathlib.Data.Nat.Find
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Nilpotent.Lemmas
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public section

namespace Lemmata.Centroid.Symmetric

open Classical

noncomputable section

variable {F A W : Type*} [Field F] [CommRing A] [Algebra F A]
variable [AddCommGroup W] [Module F W]

def evaluation (ρ : A →ₐ[F] Module.End F W) (v : W) : A →ₗ[F] W where
  toFun a := ρ a v
  map_add' a b := by simp
  map_smul' c a := by simp

@[simp] theorem evaluation_apply (ρ : A →ₐ[F] Module.End F W) (v : W) (a : A) :
    evaluation ρ v a = ρ a v := rfl

theorem evaluation_add_smul (ρ : A →ₐ[F] Module.End F W) (v w : W) (t : F) :
    evaluation ρ (v + t • w) = evaluation ρ v + t • evaluation ρ w := by
  ext a
  simp

def orbitIdeal (ρ : A →ₐ[F] Module.End F W) (v : W) : Ideal A where
  carrier := {a | ρ a v = 0}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    change ρ a v = 0 at ha
    change ρ b v = 0 at hb
    simp [ha, hb]
  smul_mem' := by
    intro a b hb
    change ρ (a * b) v = 0
    rw [map_mul, Module.End.mul_apply, hb, map_zero]

@[simp] theorem mem_orbitIdeal (ρ : A →ₐ[F] Module.End F W) (v : W) (a : A) :
    a ∈ orbitIdeal ρ v ↔ ρ a v = 0 := Iff.rfl

theorem orbitIdeal_kills_orbit (ρ : A →ₐ[F] Module.End F W) {v : W}
    {a : A} (ha : a ∈ orbitIdeal ρ v) {w : W} (hw : w ∈ (evaluation ρ v).range) :
    ρ a w = 0 := by
  obtain ⟨b, rfl⟩ := hw
  change ρ a (ρ b v) = 0
  rw [← Module.End.mul_apply, ← map_mul, mul_comm a b, map_mul, Module.End.mul_apply,
    ha, map_zero]

theorem orbitIdeal_restrictScalars (ρ : A →ₐ[F] Module.End F W) (v : W) :
    (orbitIdeal ρ v).restrictScalars F = (evaluation ρ v).ker := rfl

variable [Module.Finite F W]

theorem exists_maximal_orbit (ρ : A →ₐ[F] Module.End F W) :
    ∃ v : W, ∀ w : W,
      Module.finrank F (evaluation ρ w).range ≤ Module.finrank F (evaluation ρ v).range := by
  let P : ℕ → Prop := fun n => ∃ w : W, Module.finrank F (evaluation ρ w).range = n
  have hzero : P 0 := by
    refine ⟨0, ?_⟩
    have heq : evaluation ρ (0 : W) = 0 := by ext a; simp
    rw [heq, LinearMap.range_zero]
    simp
  have hspec : P (Nat.findGreatest P (Module.finrank F W)) :=
    Nat.findGreatest_spec (P := P) (Nat.zero_le _) hzero
  obtain ⟨v, hv⟩ := hspec
  refine ⟨v, fun w => ?_⟩
  rw [hv]
  exact Nat.le_findGreatest (Submodule.finrank_le _) ⟨w, rfl⟩

variable [Infinite F]

theorem orbitIdeal_apply_mem_orbit (ρ : A →ₐ[F] Module.End F W) {v : W}
    (hmax : ∀ w : W,
      Module.finrank F (evaluation ρ w).range ≤ Module.finrank F (evaluation ρ v).range)
    {a : A} (ha : a ∈ orbitIdeal ρ v) (w : W) :
    ρ a w ∈ (evaluation ρ v).range := by
  apply Linear.maximal_rank_maps_kernel_to_range (evaluation ρ v) (evaluation ρ w)
  · intro t
    rw [← evaluation_add_smul]
    exact hmax (v + t • w)
  · exact ha

theorem orbitIdeal_mul_eq_zero (ρ : A →ₐ[F] Module.End F W) (hρ : Function.Injective ρ)
    {v : W} (hmax : ∀ w : W,
      Module.finrank F (evaluation ρ w).range ≤ Module.finrank F (evaluation ρ v).range)
    {a b : A} (ha : a ∈ orbitIdeal ρ v) (hb : b ∈ orbitIdeal ρ v) : a * b = 0 := by
  apply hρ
  ext w
  rw [map_zero, LinearMap.zero_apply, map_mul, Module.End.mul_apply]
  obtain ⟨c, hc⟩ := orbitIdeal_apply_mem_orbit ρ hmax hb w
  change ρ c v = ρ b w at hc
  rw [← hc, ← Module.End.mul_apply, ← map_mul, mul_comm a c, map_mul,
    Module.End.mul_apply, ha, map_zero]

omit [Module.Finite F W] [Infinite F] in
theorem exists_nilpotent_hyperplane [Nontrivial A] :
    ∃ ℓ : A →ₗ[F] F, ℓ 1 = 1 ∧ ∀ a : A, IsNilpotent a → ℓ a = 0 := by
  let R : Submodule F A := (nilradical A).restrictScalars F
  have hnot : (1 : A) ∉ R := by
    change (1 : A) ∉ nilradical A
    simpa only [mem_nilradical] using (not_isNilpotent_one : ¬ IsNilpotent (1 : A))
  obtain ⟨f, hf, hmap⟩ := R.exists_dual_map_eq_bot_of_notMem hnot inferInstance
  refine ⟨(f 1)⁻¹ • f, ?_, ?_⟩
  · simp [hf]
  · intro a ha
    have hmem : f a ∈ R.map f := ⟨a, mem_nilradical.2 ha, rfl⟩
    rw [hmap] at hmem
    have hzero : f a = 0 := (Submodule.mem_bot F).1 hmem
    simp [hzero]

omit [Module.Finite F W] [Infinite F] in
theorem finrank_restrict_hyperplane [Module.Finite F A] (f : A →ₗ[F] W)
    (ℓ : A →ₗ[F] F) (hℓ : ℓ 1 = 1) (hker : f.ker ≤ ℓ.ker) :
    Module.finrank F (f.domRestrict ℓ.ker).range + 1 = Module.finrank F f.range := by
  have hsurj : Function.Surjective ℓ := by
    intro c
    refine ⟨c • (1 : A), ?_⟩
    simp [hℓ]
  have hrange : Module.finrank F ℓ.range = 1 := by
    rw [LinearMap.range_eq_top.2 hsurj]
    simp
  have hdim := ℓ.finrank_range_add_finrank_ker
  have hf := f.finrank_range_add_finrank_ker
  have hrestrict := (f.domRestrict ℓ.ker).finrank_range_add_finrank_ker
  have hkerdim : Module.finrank F (f.domRestrict ℓ.ker).ker = Module.finrank F f.ker := by
    change Module.finrank F (Submodule.comap ℓ.ker.subtype f.ker) = _
    exact (Submodule.comapSubtypeEquivOfLe hker).finrank_eq
  omega

theorem maximal_orbit_hyperplane_rank [Module.Finite F A]
    (ρ : A →ₐ[F] Module.End F W) (hρ : Function.Injective ρ)
    (ℓ : A →ₗ[F] F) (hℓ : ℓ 1 = 1)
    (hnil : ∀ a : A, IsNilpotent a → ℓ a = 0) {v : W}
    (hmax : ∀ w : W,
      Module.finrank F (evaluation ρ w).range ≤ Module.finrank F (evaluation ρ v).range) :
    Module.finrank F ((evaluation ρ v).domRestrict ℓ.ker).range + 1 =
      Module.finrank F (evaluation ρ v).range := by
  apply finrank_restrict_hyperplane _ ℓ hℓ
  intro a ha
  apply hnil
  refine ⟨2, ?_⟩
  rw [pow_two]
  exact orbitIdeal_mul_eq_zero ρ hρ hmax ha ha

theorem maximal_orbit_hyperplane_is_max [Module.Finite F A]
    (ρ : A →ₐ[F] Module.End F W) (hρ : Function.Injective ρ)
    (ℓ : A →ₗ[F] F) (hℓ : ℓ 1 = 1)
    (hnil : ∀ a : A, IsNilpotent a → ℓ a = 0) {v : W}
    (hmax : ∀ w : W,
      Module.finrank F (evaluation ρ w).range ≤ Module.finrank F (evaluation ρ v).range)
    (w : W) :
    Module.finrank F ((evaluation ρ w).domRestrict ℓ.ker).range ≤
      Module.finrank F ((evaluation ρ v).domRestrict ℓ.ker).range := by
  have hv := maximal_orbit_hyperplane_rank ρ hρ ℓ hℓ hnil hmax
  by_cases hw : Module.finrank F (evaluation ρ w).range =
      Module.finrank F (evaluation ρ v).range
  · have hmaxw : ∀ z : W,
        Module.finrank F (evaluation ρ z).range ≤ Module.finrank F (evaluation ρ w).range := by
      intro z
      rw [hw]
      exact hmax z
    have hw' := maximal_orbit_hyperplane_rank ρ hρ ℓ hℓ hnil hmaxw
    omega
  · have hle : ((evaluation ρ w).domRestrict ℓ.ker).range ≤ (evaluation ρ w).range := by
      rintro z ⟨a, rfl⟩
      exact ⟨a.val, rfl⟩
    have hdim := Submodule.finrank_mono hle
    have hmax' := hmax w
    omega

omit [Module.Finite F W] [Infinite F] in
theorem orbit_dimension_identity [Module.Finite F A] (ρ : A →ₐ[F] Module.End F W) (v : W) :
    Module.finrank F (evaluation ρ v).range +
      Module.finrank F ((orbitIdeal ρ v).restrictScalars F) = Module.finrank F A := by
  rw [orbitIdeal_restrictScalars]
  exact (evaluation ρ v).finrank_range_add_finrank_ker

end

end Lemmata.Centroid.Symmetric
