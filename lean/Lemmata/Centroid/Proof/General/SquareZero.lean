module

public import Lemmata.Centroid.Proof.General.ResidueAlgebra
public import Lemmata.Centroid.Proof.General.SupportConstraints
public import Lemmata.Centroid.Proof.Tensor.SharpSupportBound
public import Lemmata.Centroid.Proof.Tensor.ArraySupports

@[expose] public section

open Classical

noncomputable section

namespace Lemmata.Centroid.Tensor

private theorem small_kernel_first_band {x k q n s N : ℕ} (hn : 0 < n) (hs : s ≤ n)
    (hN : N = n * (n + 1) + s) (hk : k < n) (hprofile : k + q = N) (hx : x ≤ k * q) :
    x ≤ n ^ 3 - 1 := by
  have hnsub : n - 1 + 1 = n := by omega
  have hkn : k ≤ n - 1 := by omega
  have hq : N - (n - 1) = n ^ 2 + s + 1 := by
    have heq : N = (n - 1) + (n ^ 2 + s + 1) := by nlinarith
    rw [heq, Nat.add_sub_cancel_left]
  have htwo : 2 * (n - 1) ≤ N := by nlinarith
  have hcast : (k : ℤ) * q ≤ ((n - 1 : ℕ) : ℤ) * ((N - (n - 1) : ℕ) : ℤ) := by
    have hk' : (k : ℤ) ≤ (n - 1 : ℕ) := by exact_mod_cast hkn
    have htwo' : 2 * ((n - 1 : ℕ) : ℤ) ≤ N := by exact_mod_cast htwo
    have hp' : (k : ℤ) + q = N := by exact_mod_cast hprofile
    have hm := mul_nonneg (sub_nonneg.mpr hk')
      (show (0 : ℤ) ≤ (N : ℤ) - ((n - 1 : ℕ) : ℤ) - k by omega)
    rw [Nat.cast_sub (show n - 1 ≤ N by omega)]
    nlinarith
  have hprod : k * q ≤ (n - 1) * (n ^ 2 + s + 1) := by
    rw [hq] at hcast
    exact_mod_cast hcast
  have hcomp := Nat.mul_le_mul_left (n - 1) (show n ^ 2 + s + 1 ≤ n ^ 2 + n + 1 by omega)
  have hring : (n - 1) * (n ^ 2 + n + 1) + 1 = n ^ 3 := by
    have hp := congrArg (fun z => z * (n ^ 2 + n + 1)) hnsub
    nlinarith
  omega

private theorem first_band_two_small {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (AB : Finset (α × β)) (AC : Finset (α × γ)) (BC : Finset (β × γ)) {n s : ℕ}
    (hs : 1 ≤ s) (hsn : s ≤ n) (hAB : AB.card ≤ n ^ 2 + s)
    (hAC : AC.card < n ^ 2 + s) (hBC : BC.card < n ^ 2 + s) :
    (Combinatorics.triangles AB AC BC).card ≤ n ^ 3 + s * (s - 1) := by
  exact Combinatorics.positive_budget_finite AB AC BC (e₁ := s) (e₂ := s - 1) (e₃ := s - 1)
    le_rfl (by omega) hsn hAB (by omega) (by omega)

variable {F : Type*} [Field F] {V : Fin 3 → Type*} [∀ i, Fintype (V i)]

private theorem square_zero_first_band {T : Tensor F (Fin 3) V} (hT : Concise T)
    {J : Submodule F (∀ i, Matrix (V i) (V i) F)} (hJ : J ≤ centroid T)
    (hzero : ∀ A ∈ J, ∀ B ∈ J, A * B = 0) {N n s : ℕ}
    (hs : 2 ≤ s) (hsn : s ≤ n) (hN : N = n * (n + 1) + s)
    (hformat : ∀ i, Fintype.card (V i) = N)
    (hbound : ∀ i, Module.finrank F J ≤ Module.finrank F (commonKernel J i) * operatorCodim J i) :
    Module.finrank F J ≤ n ^ 3 + s * (s - 1) := by
  let _ : ∀ i, Nonempty (V i) := fun i => Fintype.card_pos_iff.mp (by rw [hformat]; omega)
  let S := imageAt T J 0
  let k (i : Fin 3) := Module.finrank F (commonKernel J i)
  let q := operatorCodim J
  have hprofile (i : Fin 3) : k i + q i = N := by
    have hk : k i ≤ Fintype.card (V i) := by
      simpa only [Module.finrank_pi] using Submodule.finrank_le (commonKernel J i)
    change k i + (Fintype.card (V i) - k i) = N
    rw [Nat.add_sub_of_le hk, hformat]
  have hSdim : Module.finrank F S = Module.finrank F J := finrank_imageAt hT hJ 0
  have hpdim (i : Fin 3) : Module.finrank F (oppositeSupportAt S i) = q i := by
    change Module.finrank F (oppositeSupportAt (imageAt T J 0) i) = q i
    rw [imageAt_eq hJ 0 i]
    exact finrank_oppositeSupportAt_imageAt hT J i
  have hone (i : Fin 3) : Module.finrank F (oneSupportAt S i) ≤ k i :=
    Submodule.finrank_mono (square_zero_image_oneSupportAt hJ hzero i)
  by_contra hlarge
  have hk (i : Fin 3) : n ≤ k i := by
    by_contra hn
    have hb := small_kernel_first_band (by omega : 0 < n) hsn hN
      (by omega : k i < n) (hprofile i) (hbound i)
    omega
  have hq (i : Fin 3) : q i ≤ n ^ 2 + s := by
    have hp := hprofile i
    have hki := hk i
    nlinarith
  have hcertificate (i j k' : Fin 3) (hij : i ≠ j) (hik : i ≠ k') (hjk : j ≠ k')
      (hi : q i = n ^ 2 + s) (hj : q j = n ^ 2 + s) : False := by
    have hki : k i = n := by have hp := hprofile i; nlinarith
    have hkj : k j = n := by have hp := hprofile j; nlinarith
    have hcodim := centroid_image_oneSupport_codim_bound hT hJ k' i j hik.symm hjk.symm hij
    rw [← imageAt_eq hJ 0 k'] at hcodim
    change Fintype.card (V k') - Module.finrank F (oneSupportAt S k') ≤ k i * k j at hcodim
    rw [hformat, hki, hkj] at hcodim
    have hρle : Module.finrank F (oneSupportAt S k') ≤ N := by
      rw [← hformat k']
      simpa only [Module.finrank_pi] using Submodule.finrank_le (oneSupportAt S k')
    have hsub := Nat.sub_add_cancel hρle
    have hW : n + s ≤ Module.finrank F (oneSupportAt S k') := by nlinarith
    have hupper := large_oneSupport_bound_at S k' i j hik.symm hjk.symm hij
      (hki ▸ hone i) (hkj ▸ hone j) hs hsn hW
      ((hpdim i).trans_le (hq i)) ((hpdim j).trans_le (hq j))
    rw [hSdim] at hupper
    exact hlarge hupper
  obtain ⟨AB, AC, BC, htri, hAB, hAC, hBC⟩ := exists_triangle_majorant S
  rw [hSdim] at htri
  rw [hpdim] at hAB hAC hBC
  by_cases hq₀ : q 0 = n ^ 2 + s
  · have hq₁ : q 1 < n ^ 2 + s := lt_of_le_of_ne (hq 1) (fun h => hcertificate 0 1 2 (by decide) (by decide) (by decide) hq₀ h)
    have hq₂ : q 2 < n ^ 2 + s := lt_of_le_of_ne (hq 2) (fun h => hcertificate 0 2 1 (by decide) (by decide) (by decide) hq₀ h)
    have hg := first_band_two_small BC (Combinatorics.transposeEdges AB) (Combinatorics.transposeEdges AC)
      (by omega) hsn (hBC.trans (hq 0)) (by simpa using hAB.trans_lt hq₂) (by simpa using hAC.trans_lt hq₁)
    rw [Combinatorics.card_triangles_cycle] at hg
    exact hlarge (htri.trans hg)
  · have hq₀lt : q 0 < n ^ 2 + s := lt_of_le_of_ne (hq 0) hq₀
    by_cases hq₁ : q 1 = n ^ 2 + s
    · have hq₂ : q 2 < n ^ 2 + s := lt_of_le_of_ne (hq 2) (fun h => hcertificate 1 2 0 (by decide) (by decide) (by decide) hq₁ h)
      have hg := first_band_two_small (Combinatorics.transposeEdges AC) (Combinatorics.transposeEdges BC) AB
        (by omega) hsn (by simpa using hAC.trans (hq 1)) (by simpa using hBC.trans_lt hq₀lt) (hAB.trans_lt hq₂)
      rw [Combinatorics.card_triangles_swap_outer] at hg
      exact hlarge (htri.trans hg)
    · have hq₁lt : q 1 < n ^ 2 + s := lt_of_le_of_ne (hq 1) hq₁
      exact hlarge (htri.trans (first_band_two_small AB AC BC (by omega) hsn (hAB.trans (hq 2))
        (hAC.trans_lt hq₁lt) (hBC.trans_lt hq₀lt)))

end Lemmata.Centroid.Tensor

namespace Lemmata.Centroid

private theorem supportBoundAt_eq_general_pred {n s : ℕ} (h : ¬ (2 ≤ s ∧ s ≤ n)) :
    supportBoundAt n s = generalBoundAt n s - 1 := by
  by_cases hs₀ : s = 0
  · subst s; simp [supportBoundAt]
  by_cases hs₁ : s = 1
  · subst s; simp [supportBoundAt, generalBoundAt]
  have hsn : ¬ s ≤ n := by omega
  simp [supportBoundAt, hsn]

end Lemmata.Centroid

namespace Lemmata.Centroid.Tensor

variable {F : Type*} [Field F] {V : Fin 3 → Type*} [∀ i, Fintype (V i)]

theorem square_zero_centroid_dimension_bound {T : Tensor F (Fin 3) V} (hT : Concise T)
    {J : Submodule F (∀ i, Matrix (V i) (V i) F)} (hJ : J ≤ centroid T)
    (hzero : ∀ A ∈ J, ∀ B ∈ J, A * B = 0) (N : ℕ)
    (hformat : ∀ i, Fintype.card (V i) = N)
    (hbound : ∀ i, Module.finrank F J ≤ Module.finrank F (commonKernel J i) * operatorCodim J i) :
    Module.finrank F J ≤ generalBound N - 1 := by
  have hU := square_zero_centroid_support_bound hT hJ hzero N (fun i => (hformat i).le)
  by_cases hN : N ≤ 1
  · have h0 : Module.finrank F J ≤ 0 := by simpa only [supportBound, hN, ite_true] using hU
    exact h0.trans (Nat.zero_le _)
  have hN₂ : 2 ≤ N := by omega
  let n := generalIndex N
  let s := N - n * (n + 1)
  have hs : s ≤ 2 * n + 1 := general_remainder_le hN₂
  have hdecomp : N = n * (n + 1) + s := general_decomposition N
  rw [generalBound_eq hN₂ hs hdecomp]
  by_cases hmiddle : 2 ≤ s ∧ s ≤ n
  · have h := square_zero_first_band hT hJ hzero hmiddle.1 hmiddle.2 hdecomp hformat hbound
    simpa only [generalBoundAt, show s ≠ 0 by omega, show s ≠ 1 by omega,
      hmiddle.2, ite_false, ite_true, Nat.add_sub_cancel] using h
  · rwa [supportBound_eq hN₂ hs hdecomp, supportBoundAt_eq_general_pred hmiddle] at hU

namespace BalancedAlgebra

variable {A : Type*} [CommRing A] [Algebra F A] [FiniteDimensional F A]
  (T : Tensor F (Fin 3) V) (hT : Concise T) (f : A →ₐ[F] centroidAlgebra T hT)

omit [FiniteDimensional F A] in
theorem idealSpace_square_zero (I : Ideal A) (hzero : I ^ 2 = 0) :
    ∀ X ∈ idealSpace T hT f I, ∀ Y ∈ idealSpace T hT f I, X * Y = 0 := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  have hab : a * b = 0 := by
    have hm : a * b ∈ I ^ 2 := by simpa only [pow_two] using Ideal.mul_mem_mul ha hb
    simpa only [hzero, Ideal.zero_eq_bot, Submodule.mem_bot] using hm
  change (f a).val * (f b).val = 0
  change (f a * f b).val = 0
  rw [← map_mul, hab, map_zero]
  rfl

theorem square_zero_ideal_dimension_bound (hf : Function.Injective f) (I : Ideal A)
    (hzero : I ^ 2 = 0) (N : ℕ) (hformat : ∀ i, Fintype.card (V i) = N) :
    Module.finrank F I ≤ generalBound N - 1 := by
  have hnil : IsNilpotent I := ⟨2, hzero⟩
  have h := square_zero_centroid_dimension_bound hT (idealSpace_le T hT f I)
    (idealSpace_square_zero T hT f I hzero) N hformat (fun i => by
      rw [idealSpace_finrank T hT f hf I]
      exact nilpotent_ideal_kernel_bound T hT f hf I hnil i)
  rwa [idealSpace_finrank T hT f hf I] at h

theorem square_zero_algebra_dimension_bound (hf : Function.Injective f) (I : Ideal A)
    (hzero : I ^ 2 = 0) (he : Module.finrank F (A ⧸ I) = 1) (N : ℕ)
    (hN : 0 < N) (hformat : ∀ i, Fintype.card (V i) = N) : Module.finrank F A ≤ generalBound N := by
  have h := square_zero_ideal_dimension_bound T hT f hf I hzero N hformat
  have hsplit := General.ideal_dimension_split (F := F) I
  rw [he] at hsplit
  have hD : 1 ≤ generalBound N := hN.trans_le (General.le_generalBound N)
  omega

end BalancedAlgebra

end Lemmata.Centroid.Tensor
