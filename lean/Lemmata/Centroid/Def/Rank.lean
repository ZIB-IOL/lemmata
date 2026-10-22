module

public import Lemmata.Centroid.Def.Tensor

@[expose] public section

set_option autoImplicit false

open scoped BigOperators
open Classical

namespace Lemmata.Centroid.Tensor

universe u v w z

variable {R : Type u} {ι : Type v} {V : ι → Type w} {W : ι → Type z}
variable [CommSemiring R] [Fintype ι]

/-- A CP decomposition using exactly `r` simple summands; zero summands are allowed. -/
def RankAtMost (T : Tensor R ι V) (r : ℕ) : Prop :=
  ∃ u : Fin r → ∀ i, V i → R, T = ∑ j, simple (u j)

theorem rankAtMost_zero : RankAtMost (0 : Tensor R ι V) 0 := by
  refine ⟨Fin.elim0, ?_⟩
  simp

theorem rankAtMost_simple (u : ∀ i, V i → R) : RankAtMost (simple u) 1 := by
  refine ⟨fun _ => u, ?_⟩
  simp

theorem RankAtMost.add {T S : Tensor R ι V} {r s : ℕ}
    (hT : RankAtMost T r) (hS : RankAtMost S s) : RankAtMost (T + S) (r + s) := by
  obtain ⟨u, rfl⟩ := hT
  obtain ⟨v, rfl⟩ := hS
  refine ⟨Fin.append u v, ?_⟩
  rw [Fin.sum_univ_add]
  simp

theorem RankAtMost.restrict {T : Tensor R ι V} {r : ℕ}
    (hT : RankAtMost T r) (f : ∀ i, W i → V i) : RankAtMost (restrict f T) r := by
  obtain ⟨u, rfl⟩ := hT
  refine ⟨fun j i y => u j i (f i y), ?_⟩
  rw [restrict_sum]
  rfl

theorem RankAtMost.localMap [∀ i, Fintype (V i)]
    {T : Tensor R ι V} {r : ℕ} (hT : RankAtMost T r)
    (A : ∀ i, W i → V i → R) : RankAtMost (localMap A T) r := by
  obtain ⟨u, rfl⟩ := hT
  refine ⟨fun j i y => ∑ x, A i y x * u j i x, ?_⟩
  rw [localMap_sum]
  simp only [localMap_simple]

theorem RankAtMost.mapCoefficients {S : Type*} [CommSemiring S]
    {T : Tensor R ι V} {r : ℕ} (hT : RankAtMost T r) (f : R →+* S) :
    RankAtMost (mapCoefficients f T) r := by
  obtain ⟨u, rfl⟩ := hT
  refine ⟨fun j i x => f (u j i x), ?_⟩
  rw [mapCoefficients_sum]
  simp only [mapCoefficients_simple]

theorem RankAtMost.kronecker {T : Tensor R ι V} {S : Tensor R ι W}
    {r s : ℕ} (hT : RankAtMost T r) (hS : RankAtMost S s) :
    RankAtMost (kronecker T S) (r * s) := by
  obtain ⟨u, rfl⟩ := hT
  obtain ⟨v, rfl⟩ := hS
  let e : Fin (r * s) ≃ Fin r × Fin s := finProdFinEquiv.symm
  refine ⟨fun j i p => u (e j).1 i p.1 * v (e j).2 i p.2, ?_⟩
  funext x
  simp only [Lemmata.Centroid.Tensor.kronecker, Finset.sum_apply, Lemmata.TensorRank.Tensor.product]
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  have he := Fintype.sum_equiv e
    (fun j => simple (fun i p => u (e j).1 i p.1 * v (e j).2 i p.2) x)
    (fun j => simple (u j.1) (fun i => (x i).1) *
      simple (v j.2) (fun i => (x i).2))
    (fun j => by simp only [simple, Lemmata.TensorRank.Tensor.pure]; exact Finset.prod_mul_distrib)
  rw [he, Fintype.sum_prod_type]

theorem RankAtMost.power {T : Tensor R ι V} {r : ℕ}
    (hT : RankAtMost T r) (n : ℕ) : RankAtMost (power T n) (r ^ n) := by
  obtain ⟨u, rfl⟩ := hT
  let e : Fin (r ^ n) ≃ (Fin n → Fin r) :=
    (Fintype.equivFinOfCardEq (by simp : Fintype.card (Fin n → Fin r) = r ^ n)).symm
  refine ⟨fun a i x => ∏ j, u (e a j) i (x j), ?_⟩
  funext x
  simp only [Lemmata.Centroid.Tensor.power, Finset.sum_apply, Lemmata.TensorRank.Tensor.power]
  rw [Fintype.prod_sum]
  have he := Fintype.sum_equiv e
    (fun a => simple (fun i y => ∏ j, u (e a j) i (y j)) x)
    (fun f => ∏ j, simple (u (f j)) (fun i => x i j))
    (fun a => by simp only [simple, Lemmata.TensorRank.Tensor.pure]; exact Finset.prod_comm)
  rw [he]

section NonemptyParties

variable [Nonempty ι]

@[simp] theorem simple_zero : simple (fun i => (0 : V i → R)) = (0 : Tensor R ι V) := by
  funext x
  exact Finset.prod_eq_zero (Finset.mem_univ (Classical.arbitrary ι)) rfl

theorem rankAtMost_zero_any (r : ℕ) : RankAtMost (0 : Tensor R ι V) r := by
  refine ⟨fun _ i => 0, ?_⟩
  simp

theorem RankAtMost.mono {T : Tensor R ι V} {r s : ℕ}
    (hT : RankAtMost T r) (hrs : r ≤ s) : RankAtMost T s := by
  have h := hT.add (rankAtMost_zero_any (R := R) (V := V) (s - r))
  simpa only [add_zero, Nat.add_sub_of_le hrs] using h

omit [Nonempty ι] in
theorem rankAtMost_zero_iff (T : Tensor R ι V) : RankAtMost T 0 ↔ T = 0 := by
  constructor
  · rintro ⟨u, hu⟩
    simpa using hu
  · rintro rfl
    exact rankAtMost_zero

omit [Nonempty ι] in
/-- Scalar absorption into any one party of a simple tensor. -/
theorem smul_simple (c : R) (u : ∀ i, V i → R) (i₀ : ι) :
    c • simple u = simple (Function.update u i₀ (fun x => c * u i₀ x)) := by
  funext x
  have h (i : ι) : Function.update u i₀ (fun y => c * u i₀ y) i (x i) =
      (if i = i₀ then c else 1) * u i (x i) := by
    by_cases hi : i = i₀
    · subst i
      simp
    · simp [hi]
  change c * (∏ i, u i (x i)) = ∏ i, Function.update u i₀ (fun y => c * u i₀ y) i (x i)
  simp_rw [h]
  rw [Finset.prod_mul_distrib]
  simp

theorem RankAtMost.smul {T : Tensor R ι V} {r : ℕ}
    (hT : RankAtMost T r) (c : R) : RankAtMost (c • T) r := by
  obtain ⟨u, hu⟩ := hT
  refine ⟨fun j i x => (if i = Classical.arbitrary ι then c else 1) * u j i x, ?_⟩
  rw [hu, Finset.smul_sum]
  funext x
  simp only [Finset.sum_apply, simple, Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, Lemmata.TensorRank.Tensor.pure]
  simp

theorem rankAtMost_iff_rankLE (T : Tensor R ι V) (r : ℕ) :
    RankAtMost T r ↔ Lemmata.TensorRank.Tensor.RankLE T r := by
  rw [Lemmata.TensorRank.Tensor.rankLE_iff_sum_pure]
  constructor
  · rintro ⟨v, h⟩
    refine ⟨v, ?_⟩
    funext x
    simpa only [Finset.sum_apply] using congrFun h x
  · rintro ⟨v, h⟩
    refine ⟨v, ?_⟩
    funext x
    simpa only [Finset.sum_apply] using congrFun h x

variable [∀ i, Fintype (V i)]

theorem rankAtMost_card (T : Tensor R ι V) :
    RankAtMost T (Fintype.card (∀ i, V i)) :=
  (rankAtMost_iff_rankLE T _).mpr (Lemmata.TensorRank.Tensor.rankLE_card T)

theorem exists_rankAtMost (T : Tensor R ι V) : ∃ r, RankAtMost T r :=
  ⟨_, rankAtMost_card T⟩

/-- Ordinary tensor rank, shared with the tensor-rank entry. -/
noncomputable abbrev rank (T : Tensor R ι V) : ℕ := Lemmata.TensorRank.Tensor.rank T

theorem rankAtMost_rank (T : Tensor R ι V) : RankAtMost T (rank T) :=
  (rankAtMost_iff_rankLE T _).mpr (Lemmata.TensorRank.Tensor.rankLE_rank T)

theorem rank_le_of_rankAtMost {T : Tensor R ι V} {r : ℕ} (h : RankAtMost T r) :
    rank T ≤ r :=
  (Lemmata.TensorRank.Tensor.rank_le_iff T r).mpr ((rankAtMost_iff_rankLE T r).mp h)

theorem rank_le_iff {T : Tensor R ι V} {r : ℕ} : rank T ≤ r ↔ RankAtMost T r := by
  constructor
  · exact (rankAtMost_rank T).mono
  · exact rank_le_of_rankAtMost

@[simp] theorem rank_zero : rank (0 : Tensor R ι V) = 0 :=
  Nat.eq_zero_of_le_zero (rank_le_of_rankAtMost rankAtMost_zero)

@[simp] theorem rank_eq_zero_iff {T : Tensor R ι V} : rank T = 0 ↔ T = 0 := by
  constructor
  · intro h
    exact (rankAtMost_zero_iff T).mp (by simpa only [h] using rankAtMost_rank T)
  · rintro rfl
    exact rank_zero

theorem rank_simple_le (u : ∀ i, V i → R) : rank (simple u) ≤ 1 :=
  rank_le_of_rankAtMost (rankAtMost_simple u)

theorem rank_add_le (T S : Tensor R ι V) : rank (T + S) ≤ rank T + rank S :=
  rank_le_of_rankAtMost ((rankAtMost_rank T).add (rankAtMost_rank S))

theorem rank_sum_le {J : Type*} (s : Finset J) (T : J → Tensor R ι V) :
    rank (∑ j ∈ s, T j) ≤ ∑ j ∈ s, rank (T j) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    exact (rank_add_le _ _).trans (Nat.add_le_add_left ih _)

theorem rank_smul_le (c : R) (T : Tensor R ι V) : rank (c • T) ≤ rank T :=
  rank_le_of_rankAtMost ((rankAtMost_rank T).smul c)

theorem rank_le_card (T : Tensor R ι V) : rank T ≤ Fintype.card (∀ i, V i) :=
  rank_le_of_rankAtMost (rankAtMost_card T)

theorem rank_le_prod_card (T : Tensor R ι V) : rank T ≤ ∏ i, Fintype.card (V i) := by
  simpa only [Fintype.card_pi] using rank_le_card T

theorem rank_restrict_le [∀ i, Fintype (W i)]
    (f : ∀ i, W i → V i) (T : Tensor R ι V) : rank (restrict f T) ≤ rank T :=
  rank_le_of_rankAtMost ((rankAtMost_rank T).restrict f)

/-- Independent coordinate bijections at the parties preserve ordinary CP rank. -/
theorem rank_reindex [∀ i, Fintype (W i)]
    (e : ∀ i, W i ≃ V i) (T : Tensor R ι V) :
    rank (restrict (fun i => e i) T) = rank T := by
  apply le_antisymm (rank_restrict_le _ _)
  have hback : restrict (fun i => (e i).symm) (restrict (fun i => e i) T) = T := by
    funext x
    simp only [restrict, Equiv.apply_symm_apply, Lemmata.TensorRank.Tensor.reindex]
  calc
    rank T = rank (restrict (fun i => (e i).symm) (restrict (fun i => e i) T)) :=
      congrArg rank hback.symm
    _ ≤ rank (restrict (fun i => e i) T) := rank_restrict_le _ _

theorem rank_localMap_le [∀ i, Fintype (W i)]
    (A : ∀ i, W i → V i → R) (T : Tensor R ι V) : rank (localMap A T) ≤ rank T :=
  rank_le_of_rankAtMost ((rankAtMost_rank T).localMap A)

theorem rank_mapCoefficients_le {S : Type*} [CommSemiring S]
    (f : R →+* S) (T : Tensor R ι V) : rank (mapCoefficients f T) ≤ rank T :=
  rank_le_of_rankAtMost ((rankAtMost_rank T).mapCoefficients f)

theorem rank_kronecker_le [∀ i, Fintype (W i)]
    (T : Tensor R ι V) (S : Tensor R ι W) :
    rank (kronecker T S) ≤ rank T * rank S :=
  rank_le_of_rankAtMost ((rankAtMost_rank T).kronecker (rankAtMost_rank S))

theorem rank_power_le (T : Tensor R ι V) (n : ℕ) : rank (power T n) ≤ rank T ^ n :=
  rank_le_of_rankAtMost ((rankAtMost_rank T).power n)

end NonemptyParties

section Field

variable {F : Type u} [Field F] [Nonempty ι] [∀ i, Fintype (V i)]

theorem rank_smul_of_ne_zero (c : F) (hc : c ≠ 0) (T : Tensor F ι V) :
    rank (c • T) = rank T := by
  apply le_antisymm (rank_smul_le c T)
  have hcancel : c⁻¹ • (c • T) = T := by
    rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
  calc
    rank T = rank (c⁻¹ • (c • T)) := congrArg rank hcancel.symm
    _ ≤ rank (c • T) := rank_smul_le _ _

end Field

end Lemmata.Centroid.Tensor
