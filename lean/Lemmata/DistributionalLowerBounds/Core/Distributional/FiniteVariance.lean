module

public import Lemmata.DistributionalLowerBounds.Core.Distributional.FerrersPosterior
public import Mathlib.Tactic

@[expose] public section

/-! Finite uniform means and variances used for Ferrers posteriors. -/

namespace Lemmata.DistributionalLowerBounds.Core.Distributional

noncomputable def uniformMean {Ω : Type*} [Fintype Ω] (X : Ω → ℝ) : ℝ :=
  (∑ ω, X ω) / Fintype.card Ω

noncomputable def uniformVariance {Ω : Type*} [Fintype Ω] (X : Ω → ℝ) : ℝ :=
  (∑ ω, (X ω - uniformMean X) ^ 2) / Fintype.card Ω

lemma card_cast_pos {Ω : Type*} [Fintype Ω] [Nonempty Ω] :
    (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos

noncomputable def uniformAverage {Ω : Type*} [Fintype Ω] (X : Ω → ℝ) : ℝ :=
  (∑ ω, X ω) / Fintype.card Ω

lemma uniformAverage_eq_mean {Ω : Type*} [Fintype Ω] (X : Ω → ℝ) :
    uniformAverage X = uniformMean X := rfl

lemma uniformVariance_nonneg {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (X : Ω → ℝ) : 0 ≤ uniformVariance X := by
  unfold uniformVariance
  positivity

/-- The mean minimizes average squared distance. -/
theorem uniformVariance_le_average_sq
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (X : Ω → ℝ) (x : ℝ) :
    uniformVariance X ≤ uniformAverage (fun ω => (x - X ω) ^ 2) := by
  unfold uniformVariance uniformAverage
  let mu := uniformMean X
  have hN : (0 : ℝ) < Fintype.card Ω := card_cast_pos
  have hzero : ∑ ω, (X ω - mu) = 0 := by
    dsimp [mu]
    unfold uniformMean
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
      Finset.card_univ]
    field_simp [hN.ne']
    ring
  have hexpand : ∀ ω,
      (x - X ω) ^ 2 = (X ω - mu) ^ 2 +
        2 * (mu - x) * (X ω - mu) + (x - mu) ^ 2 := by
    intro ω
    ring
  simp_rw [hexpand]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hcross : (∑ ω, 2 * (mu - x) * (X ω - mu)) = 0 := by
    rw [← Finset.mul_sum, hzero, mul_zero]
  change (∑ ω, (X ω - mu) ^ 2) / Fintype.card Ω ≤ _
  rw [hcross, Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  apply div_le_div_of_nonneg_right _ hN.le
  nlinarith [sq_nonneg (x - mu)]

/-- Independent-copy formula `Var X = 1/2 E(X-X')²`. -/
theorem uniformVariance_eq_pairwise {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (X : Ω → ℝ) :
    uniformVariance X =
      (∑ a, ∑ b, (X a - X b) ^ 2) /
        (2 * (Fintype.card Ω : ℝ) ^ 2) := by
  let N : ℝ := Fintype.card Ω
  let S : ℝ := ∑ a, X a
  let Q : ℝ := ∑ a, X a ^ 2
  have hN : 0 < N := card_cast_pos
  have hvar : (∑ a, (X a - S / N) ^ 2) = Q - 2 * (S / N) * S + N * (S / N) ^ 2 := by
    have hcross : (∑ a, 2 * X a * (S / N)) = 2 * (S / N) * S := by
      rw [show (∑ a, 2 * X a * (S / N)) = (2 * (S / N)) * ∑ a, X a by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        ring]
    have hconst : (∑ _a : Ω, (S / N) ^ 2) = N * (S / N) ^ 2 := by
      rw [Finset.sum_const, nsmul_eq_mul]
      simp [N]
    simp_rw [sub_sq]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hcross, hconst]
  have hpair : (∑ a, ∑ b, (X a - X b) ^ 2) = 2 * N * Q - 2 * S ^ 2 := by
    have hinner : ∀ a,
        (∑ b, (X a - X b) ^ 2) = N * X a ^ 2 - 2 * X a * S + Q := by
      intro a
      have hconst : (∑ _b : Ω, X a ^ 2) = N * X a ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]
        simp [N]
      have hcross : (∑ b, 2 * X a * X b) = 2 * X a * S := by
        rw [← Finset.mul_sum]
      simp_rw [sub_sq]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hconst, hcross]
    rw [show (∑ a, ∑ b, (X a - X b) ^ 2) =
        ∑ a, (N * X a ^ 2 - 2 * X a * S + Q) by
      apply Finset.sum_congr rfl
      intro a _
      exact hinner a]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    have hQ : (∑ _a : Ω, Q) = N * Q := by
      rw [Finset.sum_const, nsmul_eq_mul]
      simp [N]
    have hfirst : (∑ a, N * X a ^ 2) = N * Q := by rw [← Finset.mul_sum]
    have hcross : (∑ a, 2 * X a * S) = 2 * S ^ 2 := by
      rw [show (∑ a, 2 * X a * S) = (2 * S) * ∑ a, X a by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        ring]
      dsimp [S]
      ring
    rw [hQ, hfirst, hcross]
    ring
  unfold uniformVariance uniformMean
  change (∑ a, (X a - S / N) ^ 2) / N = _
  rw [hvar, hpair]
  field_simp [hN.ne']
  ring

/-- Variance increases under maps that expand every pairwise distance. -/
theorem uniformVariance_comp_ge
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (X Y : Ω → ℝ)
    (h : ∀ a b, |X a - X b| ≤ |Y a - Y b|) :
    uniformVariance X ≤ uniformVariance Y := by
  rw [uniformVariance_eq_pairwise, uniformVariance_eq_pairwise]
  have hterm : ∀ a b, (X a - X b) ^ 2 ≤ (Y a - Y b) ^ 2 := by
    intro a b
    calc
      (X a - X b) ^ 2 = |X a - X b| ^ 2 := (sq_abs _).symm
      _ ≤ |Y a - Y b| ^ 2 :=
        (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).2 (h a b)
      _ = (Y a - Y b) ^ 2 := sq_abs _
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => hterm a b))

/-- The mean of a product-valued family is the mean of its fiber means. -/
lemma uniformMean_product
    {A B : Type*} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (X : A × B → ℝ) :
    uniformMean X = uniformMean (fun a => uniformMean (fun b => X (a, b))) := by
  unfold uniformMean
  have hA : (0 : ℝ) < Fintype.card A := card_cast_pos
  have hB : (0 : ℝ) < Fintype.card B := card_cast_pos
  rw [show (∑ x : A × B, X x) = ∑ a : A, ∑ b : B, X (a, b) by
    simp only [Fintype.sum_prod_type]]
  simp_rw [← Finset.sum_div]
  rw [Fintype.card_prod]
  push_cast
  field_simp [hA.ne', hB.ne']

lemma sum_sub_uniformMean_eq_zero
    {Ω : Type*} [Fintype Ω] [Nonempty Ω] (X : Ω → ℝ) :
    ∑ ω, (X ω - uniformMean X) = 0 := by
  unfold uniformMean
  have hN : (0 : ℝ) < Fintype.card Ω := card_cast_pos
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
    Finset.card_univ]
  field_simp [hN.ne']
  ring

/-- Finite law of total variance for a uniform product. -/
theorem uniformVariance_product_eq
    {A B : Type*} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (X : A × B → ℝ) :
    uniformVariance X =
      (∑ a, uniformVariance (fun b => X (a, b))) / Fintype.card A +
        uniformVariance (fun a => uniformMean (fun b => X (a, b))) := by
  let muA : A → ℝ := fun a => uniformMean (fun b => X (a, b))
  let mu : ℝ := uniformMean muA
  have hmu : uniformMean X = mu := by
    rw [uniformMean_product]
  have hfiber : ∀ a,
      (∑ b, (X (a, b) - mu) ^ 2) =
        (∑ b, (X (a, b) - muA a) ^ 2) +
          (Fintype.card B : ℝ) * (muA a - mu) ^ 2 := by
    intro a
    have hzero : ∑ b, (X (a, b) - muA a) = 0 := by
      exact sum_sub_uniformMean_eq_zero (fun b => X (a, b))
    have hexpand : ∀ b,
        (X (a, b) - mu) ^ 2 =
          (X (a, b) - muA a) ^ 2 +
            2 * (X (a, b) - muA a) * (muA a - mu) +
            (muA a - mu) ^ 2 := by
      intro b
      ring
    simp_rw [hexpand]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    have hcross : (∑ b, 2 * (X (a, b) - muA a) * (muA a - mu)) = 0 := by
      rw [show (∑ b, 2 * (X (a, b) - muA a) * (muA a - mu)) =
          (2 * (muA a - mu)) * ∑ b, (X (a, b) - muA a) by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b _
        ring, hzero, mul_zero]
    rw [hcross, Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    ring
  change (∑ x : A × B, (X x - uniformMean X) ^ 2) / Fintype.card (A × B) =
    (∑ a : A, (∑ b : B, (X (a, b) - muA a) ^ 2) / Fintype.card B) /
        Fintype.card A +
      (∑ a : A, (muA a - mu) ^ 2) / Fintype.card A
  rw [hmu]
  rw [show (∑ x : A × B, (X x - mu) ^ 2) =
      ∑ a : A, ∑ b : B, (X (a, b) - mu) ^ 2 by
    simp only [Fintype.sum_prod_type]]
  rw [show (∑ a : A, ∑ b : B, (X (a, b) - mu) ^ 2) =
      ∑ a : A, ((∑ b : B, (X (a, b) - muA a) ^ 2) +
        (Fintype.card B : ℝ) * (muA a - mu) ^ 2) by
    apply Finset.sum_congr rfl
    intro a _
    exact hfiber a]
  rw [Finset.sum_add_distrib, Fintype.card_prod]
  push_cast
  have hA : (0 : ℝ) < Fintype.card A := card_cast_pos
  have hB : (0 : ℝ) < Fintype.card B := card_cast_pos
  rw [← Finset.sum_div]
  field_simp [hA.ne', hB.ne']
  rw [Finset.mul_sum]

/-- Total variance dominates the average variance inside product fibers. -/
theorem uniformVariance_product_ge_fiber
    {A B : Type*} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (X : A × B → ℝ) :
    (∑ a, uniformVariance (fun b => X (a, b))) / Fintype.card A ≤
      uniformVariance X := by
  rw [uniformVariance_product_eq]
  exact le_add_of_nonneg_right (uniformVariance_nonneg _)

/-- Coordinatewise variance lower bound for any fixed estimator. -/
theorem uniformAverage_loss_ge_totalVariance
    {Ω I : Type*} [Fintype Ω] [Fintype I] [Nonempty Ω]
    (target : Ω → I → ℝ) (estimate : I → ℝ) (loss : Ω → ℝ)
    (hloss : ∀ ω, (1 / 2 : ℝ) * ∑ i, (estimate i - target ω i) ^ 2 ≤ loss ω) :
    (1 / 2 : ℝ) * ∑ i, uniformVariance (fun ω => target ω i) ≤
      uniformAverage loss := by
  have hpoint : ∀ i,
      uniformVariance (fun ω => target ω i) ≤
        uniformAverage (fun ω => (estimate i - target ω i) ^ 2) :=
    fun i => uniformVariance_le_average_sq _ _
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset I)) => hpoint i)
  have hinterchange :
      (∑ i, uniformAverage (fun ω => (estimate i - target ω i) ^ 2)) =
        uniformAverage (fun ω => ∑ i, (estimate i - target ω i) ^ 2) := by
    unfold uniformAverage
    rw [← Finset.sum_div]
    rw [Finset.sum_comm]
  calc
    (1 / 2 : ℝ) * ∑ i, uniformVariance (fun ω => target ω i) ≤
        (1 / 2 : ℝ) * ∑ i,
          uniformAverage (fun ω => (estimate i - target ω i) ^ 2) :=
      mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = uniformAverage (fun ω =>
        (1 / 2 : ℝ) * ∑ i, (estimate i - target ω i) ^ 2) := by
      rw [hinterchange]
      unfold uniformAverage
      rw [show (∑ ω, (1 / 2 : ℝ) * ∑ i, (estimate i - target ω i) ^ 2) =
          (1 / 2 : ℝ) * ∑ ω, ∑ i, (estimate i - target ω i) ^ 2 by
        rw [Finset.mul_sum]]
      ring
    _ ≤ uniformAverage loss := by
      unfold uniformAverage
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact Finset.sum_le_sum (fun ω _ => hloss ω)

lemma uniformMean_comp_equiv
    {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (X : B → ℝ) :
    uniformMean (fun a => X (e a)) = uniformMean X := by
  unfold uniformMean
  rw [Equiv.sum_comp e X, Fintype.card_congr e]

lemma uniformVariance_comp_equiv
    {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (X : B → ℝ) :
    uniformVariance (fun a => X (e a)) = uniformVariance X := by
  unfold uniformVariance
  rw [uniformMean_comp_equiv e X]
  rw [Equiv.sum_comp e (fun b => (X b - uniformMean X) ^ 2),
    Fintype.card_congr e]

lemma uniformMean_const {Ω : Type*} [Fintype Ω] [Nonempty Ω] (c : ℝ) :
    uniformMean (fun _ : Ω => c) = c := by
  unfold uniformMean
  have hN : (0 : ℝ) < Fintype.card Ω := card_cast_pos
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  field_simp [hN.ne']

lemma uniformVariance_const {Ω : Type*} [Fintype Ω] [Nonempty Ω] (c : ℝ) :
    uniformVariance (fun _ : Ω => c) = 0 := by
  unfold uniformVariance
  rw [uniformMean_const]
  simp

lemma uniformMean_const_mul
    {Ω : Type*} [Fintype Ω] [Nonempty Ω] (X : Ω → ℝ) (c : ℝ) :
    uniformMean (fun ω => c * X ω) = c * uniformMean X := by
  unfold uniformMean
  rw [← Finset.mul_sum]
  ring

lemma uniformVariance_const_mul
    {Ω : Type*} [Fintype Ω] [Nonempty Ω] (X : Ω → ℝ) (c : ℝ) :
    uniformVariance (fun ω => c * X ω) = c ^ 2 * uniformVariance X := by
  unfold uniformVariance
  rw [uniformMean_const_mul]
  rw [show (∑ ω, (c * X ω - c * uniformMean X) ^ 2) =
      c ^ 2 * ∑ ω, (X ω - uniformMean X) ^ 2 by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ω _
    ring]
  ring

lemma uniformMean_add_const
    {Ω : Type*} [Fintype Ω] [Nonempty Ω] (X : Ω → ℝ) (c : ℝ) :
    uniformMean (fun ω => c + X ω) = c + uniformMean X := by
  unfold uniformMean
  have hN : (0 : ℝ) < Fintype.card Ω := card_cast_pos
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  field_simp [hN.ne']

lemma uniformVariance_add_const
    {Ω : Type*} [Fintype Ω] [Nonempty Ω] (X : Ω → ℝ) (c : ℝ) :
    uniformVariance (fun ω => c + X ω) = uniformVariance X := by
  unfold uniformVariance
  rw [uniformMean_add_const]
  congr 1
  apply Finset.sum_congr rfl
  intro ω _
  ring

lemma uniformVariance_fst
    {A B : Type*} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (f : A → ℝ) :
    uniformVariance (fun x : A × B => f x.1) = uniformVariance f := by
  rw [uniformVariance_product_eq]
  simp_rw [uniformVariance_const]
  simp_rw [uniformMean_const]
  simp

lemma succAbove_gap {n : ℕ} (p : Fin (n + 1)) (i j : Fin n) (hij : i ≤ j) :
    j.val - i.val ≤ (p.succAbove j).val - (p.succAbove i).val := by
  by_cases hip : i.castSucc < p
  · rw [Fin.succAbove_of_castSucc_lt p i hip]
    by_cases hjp : j.castSucc < p
    · rw [Fin.succAbove_of_castSucc_lt p j hjp]
      simp only [Fin.val_castSucc]
      rfl
    · rw [Fin.succAbove_of_le_castSucc p j (Fin.not_lt.mp hjp)]
      simp only [Fin.val_castSucc, Fin.val_succ]
      omega
  · have hpi : p ≤ i.castSucc := Fin.not_lt.mp hip
    have hpj : p ≤ j.castSucc := hpi.trans (by exact_mod_cast hij)
    rw [Fin.succAbove_of_le_castSucc p i hpi,
      Fin.succAbove_of_le_castSucc p j hpj]
    simp only [Fin.val_succ]
    omega

lemma succAbove_abs_expands {n : ℕ} (p : Fin (n + 1)) (i j : Fin n) :
    |(i.val : ℝ) - (j.val : ℝ)| ≤
      |((p.succAbove i).val : ℝ) - ((p.succAbove j).val : ℝ)| := by
  by_cases hij : i ≤ j
  · have hiR : (i.val : ℝ) ≤ j.val := by exact_mod_cast hij
    have hsij : p.succAbove i ≤ p.succAbove j :=
      (Fin.succAboveOrderEmb p).monotone hij
    have hsR : ((p.succAbove i).val : ℝ) ≤ (p.succAbove j).val := by
      exact_mod_cast hsij
    rw [abs_of_nonpos (sub_nonpos.mpr hiR), abs_of_nonpos (sub_nonpos.mpr hsR)]
    have hgR : ((j.val - i.val : ℕ) : ℝ) ≤
        (((p.succAbove j).val - (p.succAbove i).val : ℕ) : ℝ) := by
      exact_mod_cast succAbove_gap p i j hij
    have hcast1 : ((j.val - i.val : ℕ) : ℝ) = (j.val : ℝ) - i.val := Nat.cast_sub hij
    have hcast2 : (((p.succAbove j).val - (p.succAbove i).val : ℕ) : ℝ) =
        ((p.succAbove j).val : ℝ) - (p.succAbove i).val := Nat.cast_sub hsij
    linarith
  · have hji : j ≤ i := le_of_not_ge hij
    rw [abs_sub_comm (i.val : ℝ), abs_sub_comm ((p.succAbove i).val : ℝ)]
    have hjR : (j.val : ℝ) ≤ i.val := by exact_mod_cast hji
    have hsji : p.succAbove j ≤ p.succAbove i :=
      (Fin.succAboveOrderEmb p).monotone hji
    have hsR : ((p.succAbove j).val : ℝ) ≤ (p.succAbove i).val := by
      exact_mod_cast hsji
    rw [abs_of_nonpos (sub_nonpos.mpr hjR), abs_of_nonpos (sub_nonpos.mpr hsR)]
    have hgR : ((i.val - j.val : ℕ) : ℝ) ≤
        (((p.succAbove i).val - (p.succAbove j).val : ℕ) : ℝ) := by
      exact_mod_cast succAbove_gap p j i hji
    have hcast1 : ((i.val - j.val : ℕ) : ℝ) = (i.val : ℝ) - j.val := Nat.cast_sub hji
    have hcast2 : (((p.succAbove i).val - (p.succAbove j).val : ℕ) : ℝ) =
        ((p.succAbove i).val : ℝ) - (p.succAbove j).val := Nat.cast_sub hsji
    linarith

lemma sum_fin_val (n : ℕ) :
    (∑ i : Fin n, (i.val : ℝ)) = (n : ℝ) * (n - 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [ih]
      push_cast
      ring

lemma sum_fin_val_sq (n : ℕ) :
    (∑ i : Fin n, (i.val : ℝ) ^ 2) =
      (n : ℝ) * (n - 1) * (2 * n - 1) / 6 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [ih]
      push_cast
      ring

/-- Variance of `k` consecutive integer columns. -/
theorem uniformVariance_fin_val {k : ℕ} (hk : 0 < k) :
    uniformVariance (fun i : Fin k => (i.val : ℝ)) = ((k : ℝ) ^ 2 - 1) / 12 := by
  letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  unfold uniformVariance uniformMean
  rw [sum_fin_val]
  have hcard : (Fintype.card (Fin k) : ℝ) = k := by simp
  rw [hcard]
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hexpand :
      (∑ i : Fin k, ((i.val : ℝ) - ((k : ℝ) * (k - 1) / 2) / k) ^ 2) =
        (∑ i : Fin k, (i.val : ℝ) ^ 2) -
          2 * (((k : ℝ) * (k - 1) / 2) / k) * (∑ i : Fin k, (i.val : ℝ)) +
          (k : ℝ) * (((k : ℝ) * (k - 1) / 2) / k) ^ 2 := by
    let mu : ℝ := ((k : ℝ) * (k - 1) / 2) / k
    have hcross : (∑ i : Fin k, 2 * (i.val : ℝ) * mu) =
        2 * mu * ∑ i : Fin k, (i.val : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have hconst : (∑ _i : Fin k, mu ^ 2) = (k : ℝ) * mu ^ 2 := by
      rw [Finset.sum_const, nsmul_eq_mul]
      simp
    change (∑ i : Fin k, ((i.val : ℝ) - mu) ^ 2) = _
    simp_rw [sub_sq]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hcross, hconst]
  rw [hexpand, sum_fin_val_sq, sum_fin_val]
  field_simp [hkR.ne']
  ring

end Lemmata.DistributionalLowerBounds.Core.Distributional
