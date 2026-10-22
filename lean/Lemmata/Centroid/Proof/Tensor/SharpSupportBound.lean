module

public import Lemmata.Centroid.Proof.Tensor.SupportBound
public import Lemmata.Centroid.Proof.Tensor.SupportTensor
public import Lemmata.Centroid.Proof.Combinatorics.TripartiteDeficits
public import Lemmata.Centroid.Proof.General.Numeric

@[expose] public section

open scoped BigOperators
open Classical

noncomputable section

namespace Lemmata.Centroid.Tensor

private theorem product_budget_mono {r p k N : ℕ} (hr : r ≤ k) (hk : 2 * k ≤ N)
    (hbudget : r + p ≤ N) : r * p ≤ k * (N - k) := by
  have hr' : (r : ℤ) ≤ k := by exact_mod_cast hr
  have hk' : 2 * (k : ℤ) ≤ N := by exact_mod_cast hk
  have hb' : (r : ℤ) + p ≤ N := by exact_mod_cast hbudget
  have hp := mul_le_mul_of_nonneg_left hb' (Int.natCast_nonneg r)
  have hq := mul_nonneg (sub_nonneg.mpr hr') (show (0 : ℤ) ≤ (N : ℤ) - k - r by omega)
  have hz : (r : ℤ) * p ≤ (k : ℤ) * ((N : ℤ) - k) := by nlinarith
  have hkn : k ≤ N := by omega
  have hcast : ((r * p : ℕ) : ℤ) ≤ ((k * (N - k) : ℕ) : ℤ) := by
    simpa only [Nat.cast_mul, Nat.cast_sub hkn] using hz
  exact_mod_cast hcast

private theorem first_band_small {x r p n s N : ℕ} (hn : 0 < n) (hs : s ≤ n)
    (hN : N = n * (n + 1) + s) (hr : r < n) (hbudget : r + p ≤ N) (hx : x ≤ r * p) :
    x ≤ n ^ 3 + s ^ 2 := by
  have hnsub : n - 1 + 1 = n := by omega
  have htwo : 2 * (n - 1) ≤ N := by nlinarith
  have hprod := product_budget_mono (by omega : r ≤ n - 1) htwo hbudget
  have hNsub : N - (n - 1) = n ^ 2 + s + 1 := by
    have hN' : N = (n - 1) + (n ^ 2 + s + 1) := by nlinarith
    rw [hN', Nat.add_sub_cancel_left]
  rw [hNsub] at hprod
  have hcomp := Nat.mul_le_mul_left (n - 1) (show n ^ 2 + s + 1 ≤ n ^ 2 + n + 1 by omega)
  have hring : (n - 1) * (n ^ 2 + n + 1) + 1 = n ^ 3 := by
    have hp := congrArg (fun z => z * (n ^ 2 + n + 1)) hnsub
    nlinarith
  omega

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

theorem triangle_support_budget_at (AB : Finset (α × β)) (AC : Finset (α × γ))
    (BC : Finset (β × γ)) (x : ℕ) (ρ p : Fin 3 → ℕ) {N n s : ℕ}
    (hn : 0 < n) (hs : s ≤ 2 * n + 1) (hN : N = n * (n + 1) + s)
    (htri : x ≤ (Combinatorics.triangles AB AC BC).card)
    (hAB : AB.card ≤ p 2) (hAC : AC.card ≤ p 1) (hBC : BC.card ≤ p 0)
    (hprod : ∀ i, x ≤ ρ i * p i) (hbudget : ∀ i, ρ i + p i ≤ N) : x ≤ supportBoundAt n s := by
  by_cases hsn : s ≤ n
  · rw [supportBoundAt, ite_eq_left hsn]
    by_cases hsmall : ∃ i, ρ i < n
    · obtain ⟨i, hi⟩ := hsmall
      exact first_band_small hn hsn hN hi (hbudget i) (hprod i)
    · have hρ (i : Fin 3) : n ≤ ρ i := Nat.le_of_not_gt (fun h => hsmall ⟨i, h⟩)
      have hp (i : Fin 3) : p i ≤ n ^ 2 + s := by
        have hb := hbudget i
        have hr := hρ i
        nlinarith
      have hgraph := Combinatorics.positive_budget_finite AB AC BC (h := n)
        (e₁ := s) (e₂ := s) (e₃ := s) le_rfl le_rfl hsn
        (hAB.trans (hp 2)) (hAC.trans (hp 1)) (hBC.trans (hp 0))
      simpa only [pow_two] using htri.trans hgraph
  · let t := s - n - 1
    have ht : t ≤ n := by dsimp only [t]; omega
    have hsEq : s = n + 1 + t := by dsimp only [t]; omega
    have hN' : N = (n + 1) ^ 2 + t := by nlinarith
    rw [hsEq, General.supportBoundAt_second n t hn]
    by_cases hsmall : ∃ i, ρ i ≤ n
    · obtain ⟨i, hi⟩ := hsmall
      have hp := product_budget_mono hi (show 2 * n ≤ N by nlinarith) (hbudget i)
      have hNsub : N - n = n ^ 2 + n + t + 1 := by
        have heq : N = n + (n ^ 2 + n + t + 1) := by nlinarith
        rw [heq, Nat.add_sub_cancel_left]
      rw [hNsub] at hp
      have hm := le_max_left n (t ^ 2)
      nlinarith [hprod i]
    · have hρ (i : Fin 3) : n + 1 ≤ ρ i := by
        have hnot : ¬ρ i ≤ n := fun h => hsmall ⟨i, h⟩
        omega
      let d := n + 1 - t
      have hd : d ≤ n + 1 := Nat.sub_le _ _
      have hdt : d + t = n + 1 := by dsimp only [d]; omega
      have hQ : (n + 1) ^ 2 - d = n ^ 2 + n + t := by
        have heq : (n + 1) ^ 2 = (n ^ 2 + n + t) + d := by nlinarith
        omega
      have hp (i : Fin 3) : p i ≤ (n + 1) ^ 2 - d := by
        rw [hQ]
        have hb := hbudget i
        have hr := hρ i
        nlinarith only [hN, hsEq, hb, hr]
      have hgraph := Combinatorics.equal_deficit_finite AB AC BC (by omega) hd
        (hAB.trans (hp 2)) (hAC.trans (hp 1)) (hBC.trans (hp 0))
      have heq : (n + 1) ^ 3 + d ^ 2 + d =
          (n * (n ^ 2 + n + t) + t ^ 2) + 3 * (n + 1) * d := by
        have h₁ := congrArg (fun z => z * d) hdt
        have h₂ := congrArg (fun z => z * t) hdt
        have h₃ := congrArg (fun z => z * n) hdt
        nlinarith only [h₁, h₂, h₃, hdt]
      rw [heq, Nat.add_sub_cancel] at hgraph
      exact (htri.trans hgraph).trans (Nat.add_le_add_left (le_max_right _ _) _)

theorem triangle_support_budget (AB : Finset (α × β)) (AC : Finset (α × γ))
    (BC : Finset (β × γ)) (x : ℕ) (ρ p : Fin 3 → ℕ) (N : ℕ)
    (htri : x ≤ (Combinatorics.triangles AB AC BC).card)
    (hAB : AB.card ≤ p 2) (hAC : AC.card ≤ p 1) (hBC : BC.card ≤ p 0)
    (hprod : ∀ i, x ≤ ρ i * p i) (hbudget : ∀ i, ρ i + p i ≤ N) : x ≤ supportBound N := by
  by_cases hN : N ≤ 1
  · rw [supportBound, ite_eq_left hN]
    have hp := hprod 0
    have hb := hbudget 0
    have hr : ρ 0 = 0 ∨ ρ 0 = 1 := by omega
    rcases hr with hr | hr
    · simpa only [hr, zero_mul] using hp
    · have hz : p 0 = 0 := by omega
      simpa only [hz, mul_zero] using hp
  · have hN₂ : 2 ≤ N := by omega
    have hs := general_remainder_le hN₂
    have hdecomp := general_decomposition N
    rw [supportBound_eq hN₂ hs hdecomp]
    exact triangle_support_budget_at AB AC BC x ρ p (generalIndex_pos hN₂) hs hdecomp
      htri hAB hAC hBC hprod hbudget

variable {F : Type*} [Field F] {V : Fin 3 → Type*} [∀ i, Fintype (V i)]

theorem exists_triangle_majorant_ordered [∀ i, LinearOrder (V i)] [∀ i, Nonempty (V i)]
    (S : Submodule F (Tensor F (Fin 3) V)) :
    ∃ (AB : Finset (V 0 × V 1)) (AC : Finset (V 0 × V 2)) (BC : Finset (V 1 × V 2)),
      Module.finrank F S ≤ (Combinatorics.triangles AB AC BC).card ∧
      AB.card ≤ Module.finrank F (oppositeSupportAt S 2) ∧
      AC.card ≤ Module.finrank F (oppositeSupportAt S 1) ∧
      BC.card ≤ Module.finrank F (oppositeSupportAt S 0) := by
  let _ : ∀ i, DecidableEq (V i) := fun _ => Classical.decEq _
  let a₀ (i : Fin 3) : V i := Finset.univ.min' Finset.univ_nonempty
  have ha₀ (i : Fin 3) (a : V i) : a₀ i ≤ a := Finset.min'_le _ _ (Finset.mem_univ _)
  let L := (lexLeading S).image (fun x => threeCoordinates V (ofLex x))
  have hcard : L.card = Module.finrank F S := by
    dsimp only [L]
    calc
      _ = (lexLeading S).card := Finset.card_image_of_injective _
        (fun x y h => ofLex.injective ((threeCoordinates V).injective h))
      _ = _ := card_lexLeading S
  have hAB : (L.image (fun p => (p.1, p.2.1))).card ≤
      Module.finrank F (oppositeSupportAt S 2) := by
    dsimp only [L]
    rw [Finset.image_image]
    apply card_projection_le_oppositeSupportAt S 2 (a₀ 2) (ha₀ 2)
    intro x
    exact congrArg₂ Prod.mk
      (project_update_of_ne x 2 0 (a₀ 2) (by decide))
      (project_update_of_ne x 2 1 (a₀ 2) (by decide))
  have hAC : (L.image (fun p => (p.1, p.2.2))).card ≤
      Module.finrank F (oppositeSupportAt S 1) := by
    dsimp only [L]
    rw [Finset.image_image]
    apply card_projection_le_oppositeSupportAt S 1 (a₀ 1) (ha₀ 1)
    intro x
    exact congrArg₂ Prod.mk
      (project_update_of_ne x 1 0 (a₀ 1) (by decide))
      (project_update_of_ne x 1 2 (a₀ 1) (by decide))
  have hBC : (L.image (fun p => (p.2.1, p.2.2))).card ≤
      Module.finrank F (oppositeSupportAt S 0) := by
    dsimp only [L]
    rw [Finset.image_image]
    apply card_projection_le_oppositeSupportAt S 0 (a₀ 0) (ha₀ 0)
    intro x
    exact congrArg₂ Prod.mk
      (project_update_of_ne x 0 1 (a₀ 0) (by decide))
      (project_update_of_ne x 0 2 (a₀ 0) (by decide))
  refine ⟨_, _, _, ?_, hAB, hAC, hBC⟩
  rw [← hcard]
  apply Finset.card_le_card
  intro p hp
  exact (Combinatorics.mem_triangles_iff _ _ _ p).2
    ⟨Finset.mem_image_of_mem _ hp, Finset.mem_image_of_mem _ hp, Finset.mem_image_of_mem _ hp⟩

theorem exists_triangle_majorant (S : Submodule F (Tensor F (Fin 3) V)) :
    ∃ (AB : Finset (V 0 × V 1)) (AC : Finset (V 0 × V 2)) (BC : Finset (V 1 × V 2)),
      Module.finrank F S ≤ (Combinatorics.triangles AB AC BC).card ∧
      AB.card ≤ Module.finrank F (oppositeSupportAt S 2) ∧
      AC.card ≤ Module.finrank F (oppositeSupportAt S 1) ∧
      BC.card ≤ Module.finrank F (oppositeSupportAt S 0) := by
  cases isEmpty_or_nonempty (∀ i, V i) with
  | inl h =>
    let _ : IsEmpty (∀ i, V i) := h
    refine ⟨∅, ∅, ∅, ?_, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _⟩
    rw [Module.finrank_zero_of_subsingleton]
    exact Nat.zero_le _
  | inr h =>
    let _ : ∀ i, Nonempty (V i) := fun i => ⟨(Classical.choice h) i⟩
    let _ : ∀ i, LinearOrder (V i) := fun i =>
      LinearOrder.lift' (Fintype.equivFin (V i)) (Fintype.equivFin (V i)).injective
    exact exists_triangle_majorant_ordered S

theorem support_budget_bound (S : Submodule F (Tensor F (Fin 3) V)) (N : ℕ)
    (hbudget : ∀ i, Module.finrank F (oneSupportAt S i) +
      Module.finrank F (oppositeSupportAt S i) ≤ N) : Module.finrank F S ≤ supportBound N := by
  obtain ⟨AB, AC, BC, htri, hAB, hAC, hBC⟩ := exists_triangle_majorant S
  exact triangle_support_budget AB AC BC (Module.finrank F S)
    (fun i => Module.finrank F (oneSupportAt S i))
    (fun i => Module.finrank F (oppositeSupportAt S i)) N htri hAB hAC hBC
    (finrank_le_oneSupportAt_mul_oppositeSupportAt S) hbudget

theorem square_zero_centroid_support_bound {T : Tensor F (Fin 3) V} (hT : Concise T)
    {J : Submodule F (∀ i, Matrix (V i) (V i) F)} (hJ : J ≤ centroid T)
    (hzero : ∀ A ∈ J, ∀ B ∈ J, A * B = 0) (N : ℕ) (hformat : ∀ i, Fintype.card (V i) ≤ N) :
    Module.finrank F J ≤ supportBound N := by
  have h := support_budget_bound (imageAt T J 0) N (fun i =>
    (square_zero_image_support_budget hT hJ hzero i).trans (hformat i))
  rw [finrank_imageAt hT hJ] at h
  exact h

end Lemmata.Centroid.Tensor
