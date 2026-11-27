module

public import Lemmata.CocubicCovering.Proof.Linear
public meta import Lemmata.CocubicCovering.Proof.Linear
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.Ring

@[expose] public section

set_option Elab.async false

namespace Lemmata.CocubicCovering.CoveringSymplectic

open Module LinearMap
open LinearMap (BilinForm)
open scoped BigOperators

universe u v

variable {K : Type u} {E : Type v} [Field K] [AddCommGroup E] [Module K E]

theorem exists_normalized_pair (B : BilinForm K E) (hB : B ≠ 0) :
    ∃ u v : E, B u v = 1 := by
  classical
  have hexists : ∃ u v : E, B u v ≠ 0 := by
    by_contra! hzero
    exact hB (by ext u v; exact hzero u v)
  obtain ⟨u, v, huv⟩ := hexists
  refine ⟨u, (B u v)⁻¹ • v, ?_⟩
  rw [BilinForm.smul_right, inv_mul_cancel₀ huv]

def pairProjection (B : BilinForm K E) (u v : E) : E →ₗ[K] E :=
  LinearMap.id - (B.flip v).smulRight u + (B.flip u).smulRight v

@[simp] theorem pairProjection_apply (B : BilinForm K E) (u v z : E) :
    pairProjection B u v z = z - B z v • u + B z u • v := rfl

theorem pairProjection_left (B : BilinForm K E) (hB : B.IsAlt)
    {u v : E} (huv : B u v = 1) (z : E) : B u (pairProjection B u v z) = 0 := by
  rw [pairProjection_apply]
  simp only [BilinForm.add_right, BilinForm.sub_right, BilinForm.smul_right,
    hB.self_eq_zero u, huv, mul_zero, sub_zero, mul_one]
  rw [← hB.neg_eq u z]
  ring

theorem pairProjection_right (B : BilinForm K E) (hB : B.IsAlt)
    {u v : E} (huv : B u v = 1) (z : E) : B v (pairProjection B u v z) = 0 := by
  have hvu : B v u = -1 := by rw [← hB.neg_eq u v, huv]
  rw [pairProjection_apply]
  simp only [BilinForm.add_right, BilinForm.sub_right, BilinForm.smul_right,
    hB.self_eq_zero v, hvu, mul_zero, add_zero]
  rw [← hB.neg_eq v z]
  ring

@[simp] theorem pairProjection_first (B : BilinForm K E) (hB : B.IsAlt)
    {u v : E} (huv : B u v = 1) : pairProjection B u v u = 0 := by
  simp only [pairProjection_apply, huv, hB.self_eq_zero, one_smul, zero_smul,
    sub_self, add_zero]

@[simp] theorem pairProjection_second (B : BilinForm K E) (hB : B.IsAlt)
    {u v : E} (huv : B u v = 1) : pairProjection B u v v = 0 := by
  have hvu : B v u = -1 := by rw [← hB.neg_eq u v, huv]
  simp only [pairProjection_apply, hB.self_eq_zero, hvu, zero_smul, sub_zero,
    neg_one_smul, add_neg_cancel]

theorem pair_decomposition (B : BilinForm K E) (u v z : E) :
    B z v • u - B z u • v + pairProjection B u v z = z := by
  rw [pairProjection_apply]
  module

def pairOrthogonal (B : BilinForm K E) (u v : E) : Submodule K E :=
  LinearMap.ker (B u) ⊓ LinearMap.ker (B v)

@[simp] theorem mem_pairOrthogonal (B : BilinForm K E) (u v z : E) :
    z ∈ pairOrthogonal B u v ↔ B u z = 0 ∧ B v z = 0 := Iff.rfl

theorem pairProjection_eq_self (B : BilinForm K E) (hB : B.IsAlt)
    {u v z : E} (hz : z ∈ pairOrthogonal B u v) : pairProjection B u v z = z := by
  have hzu : B z u = 0 := (hB.isRefl u z) hz.1
  have hzv : B z v = 0 := (hB.isRefl v z) hz.2
  simp [pairProjection_apply, hzu, hzv]

def pairProjectionToOrthogonal (B : BilinForm K E) (hB : B.IsAlt)
    {u v : E} (huv : B u v = 1) : E →ₗ[K] pairOrthogonal B u v :=
  (pairProjection B u v).codRestrict _ fun z =>
    ⟨pairProjection_left B hB huv z, pairProjection_right B hB huv z⟩

theorem pair_gram_identity (B : BilinForm K E) (hB : B.IsAlt)
    {u v : E} (huv : B u v = 1) (x y : E) :
    B x y = B x v * (-B y u) - (-B x u) * B y v +
      B (pairProjection B u v x) (pairProjection B u v y) := by
  have hvu : B v u = -1 := by rw [← hB.neg_eq u v, huv]
  simp only [pairProjection_apply, BilinForm.add_left, BilinForm.sub_left,
    BilinForm.smul_left, BilinForm.add_right, BilinForm.sub_right, BilinForm.smul_right,
    hB.self_eq_zero u, hB.self_eq_zero v, huv, hvu]
  rw [← hB.neg_eq u y, ← hB.neg_eq v y]
  ring

def pairSplitLinear (B : BilinForm K E) (hB : B.IsAlt)
    {u v : E} (huv : B u v = 1) : E →ₗ[K] (K × K) × pairOrthogonal B u v :=
  ((B.flip v).prod (-B.flip u)).prod (pairProjectionToOrthogonal B hB huv)

def pairEquiv (B : BilinForm K E) (hB : B.IsAlt)
    {u v : E} (huv : B u v = 1) : E ≃ₗ[K] (K × K) × pairOrthogonal B u v where
  __ := pairSplitLinear B hB huv
  invFun p := p.1.1 • u + p.1.2 • v + p.2.val
  left_inv z := by
    change B z v • u + (-B z u) • v + pairProjection B u v z = z
    simpa only [neg_smul, sub_eq_add_neg] using pair_decomposition B u v z
  right_inv p := by
    rcases p with ⟨⟨a, b⟩, w⟩
    have hvu : B v u = -1 := by rw [← hB.neg_eq u v, huv]
    have hwu : B w.val u = 0 := (hB.isRefl u w.val) w.property.1
    have hwv : B w.val v = 0 := (hB.isRefl v w.val) w.property.2
    apply Prod.ext
    · apply Prod.ext
      · change B (a • u + b • v + w.val) v = a
        simp [BilinForm.add_left, BilinForm.smul_left, huv, hB.self_eq_zero, hwv]
      · change -B (a • u + b • v + w.val) u = b
        simp [BilinForm.add_left, BilinForm.smul_left, hvu, hB.self_eq_zero, hwu]
    · apply Subtype.ext
      change pairProjection B u v (a • u + b • v + w.val) = w.val
      rw [map_add, map_add, map_smul, map_smul,
        pairProjection_first B hB huv, pairProjection_second B hB huv,
        pairProjection_eq_self B hB w.property]
      simp

theorem finrank_pairOrthogonal [FiniteDimensional K E] (B : BilinForm K E)
    (hB : B.IsAlt) {u v : E} (huv : B u v = 1) :
    finrank K E = 2 + finrank K (pairOrthogonal B u v) := by
  simpa only [Module.finrank_prod, Module.finrank_self] using (pairEquiv B hB huv).finrank_eq

theorem pair_kernel_map (B : BilinForm K E) (hB : B.IsAlt)
    {u v : E} (huv : B u v = 1) :
    (LinearMap.ker (B.restrict (pairOrthogonal B u v))).map
      (pairOrthogonal B u v).subtype = LinearMap.ker B := by
  ext x
  constructor
  · rintro ⟨w, hw, rfl⟩
    change B w.val = 0
    ext z
    change B w.val z = 0
    have hwu : B w.val u = 0 := (hB.isRefl u w.val) w.property.1
    have hwv : B w.val v = 0 := (hB.isRefl v w.val) w.property.2
    have hp : B w.val (pairProjection B u v z) = 0 :=
      LinearMap.congr_fun hw
        ⟨pairProjection B u v z,
          pairProjection_left B hB huv z, pairProjection_right B hB huv z⟩
    rw [← pair_decomposition B u v z, BilinForm.add_right, BilinForm.sub_right,
      BilinForm.smul_right, BilinForm.smul_right, hwu, hwv, hp]
    ring
  · intro hx
    have hN : x ∈ pairOrthogonal B u v :=
      ⟨hB.isRefl x u (LinearMap.congr_fun hx u),
        hB.isRefl x v (LinearMap.congr_fun hx v)⟩
    refine ⟨⟨x, hN⟩, ?_, rfl⟩
    change (B.restrict (pairOrthogonal B u v)) ⟨x, hN⟩ = 0
    ext y
    exact LinearMap.congr_fun hx y.val

theorem rank_pairOrthogonal [FiniteDimensional K E] (B : BilinForm K E)
    (hB : B.IsAlt) {u v : E} (huv : B u v = 1) :
    finrank K (LinearMap.range B) =
      2 + finrank K (LinearMap.range (B.restrict (pairOrthogonal B u v))) := by
  have hkernel : finrank K (LinearMap.ker B) =
      finrank K (LinearMap.ker (B.restrict (pairOrthogonal B u v))) := by
    rw [← pair_kernel_map B hB huv]
    exact Submodule.finrank_map_subtype_eq _ _
  have hwhole := B.finrank_range_add_finrank_ker
  have hrest := (B.restrict (pairOrthogonal B u v)).finrank_range_add_finrank_ker
  have hdim := finrank_pairOrthogonal B hB huv
  omega

private theorem rank_even_aux (n : ℕ) :
    ∀ (V : Type v) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
      (B : BilinForm K V), B.IsAlt → finrank K (LinearMap.range B) ≤ n →
        Even (finrank K (LinearMap.range B)) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V _ _ _ B hB hn
    by_cases hzero : B = 0
    · refine ⟨0, ?_⟩
      simp [hzero]
    · obtain ⟨u, v, huv⟩ := exists_normalized_pair B hzero
      let N := pairOrthogonal B u v
      let C : BilinForm K N := B.restrict N
      have hC : C.IsAlt := fun z => hB z.val
      have hrank : finrank K (LinearMap.range B) =
          2 + finrank K (LinearMap.range C) := rank_pairOrthogonal B hB huv
      have hsmall : finrank K (LinearMap.range C) < n := by omega
      obtain ⟨r, hr⟩ := ih (finrank K (LinearMap.range C)) hsmall N C hC le_rfl
      exact ⟨r + 1, by omega⟩

theorem rank_even [FiniteDimensional K E] (B : BilinForm K E) (hB : B.IsAlt) :
    Even (finrank K (LinearMap.range B)) :=
  rank_even_aux (finrank K (LinearMap.range B)) E B hB le_rfl

theorem rank_le_ten_of_lt_twelve [FiniteDimensional K E] (B : BilinForm K E)
    (hB : B.IsAlt) (hrank : finrank K (LinearMap.range B) < 12) :
    finrank K (LinearMap.range B) ≤ 10 := by
  obtain ⟨r, hr⟩ := rank_even B hB
  omega

theorem exists_frame_partner [FiniteDimensional K E]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (B : BilinForm K E) (frame : ι → E)
    (hinjective : Function.Injective
      (LinearMap.comp B (Fintype.linearCombination K frame))) (j : ι) :
    ∃ v : E, ∀ i : ι, B (frame i) v = if i = j then 1 else 0 := by
  let F := LinearMap.comp B (Fintype.linearCombination K frame)
  have hsurjective : Function.Surjective F.flip :=
    LinearMap.flip_surjective_iff₂.mpr hinjective
  obtain ⟨v, hv⟩ := hsurjective (LinearMap.proj j)
  refine ⟨v, ?_⟩
  intro i
  have h := LinearMap.congr_fun hv (Pi.single i (1 : K))
  change B ((Fintype.linearCombination K frame) (Pi.single i 1)) v =
    (Pi.single i (1 : K) : ι → K) j at h
  rw [Fintype.linearCombination_apply_single, one_smul] at h
  simpa only [Pi.single_apply, eq_comm] using h

abbrev Standard (K : Type*) (r : ℕ) := (Fin r → K) × (Fin r → K)

def standardBilin (r : ℕ) : BilinForm K (Standard K r) :=
  let p : Standard K r →ₗ[K] (Fin r → K) := LinearMap.fst K _ _
  let q : Standard K r →ₗ[K] (Fin r → K) := LinearMap.snd K _ _
  (dotProductBilin K K).compl₁₂ p q - (dotProductBilin K K).compl₁₂ q p

@[simp] theorem standardBilin_apply (r : ℕ) (x y : Standard K r) :
    standardBilin r x y = (∑ i, x.1 i * y.2 i) - ∑ i, x.2 i * y.1 i := rfl

theorem standardBilin_isAlt (r : ℕ) : (standardBilin (K := K) r).IsAlt := by
  intro x
  simp only [standardBilin_apply, mul_comm, sub_self]

def standardConsLinear (r : ℕ) : ((K × K) × Standard K r) →ₗ[K] Standard K (r + 1) where
  toFun p := (Fin.cons p.1.1 p.2.1, Fin.cons p.1.2 p.2.2)
  map_add' p q := by
    apply Prod.ext <;> funext i <;> exact Fin.cases rfl (fun _ => rfl) i
  map_smul' c p := by
    apply Prod.ext <;> funext i <;> exact Fin.cases rfl (fun _ => rfl) i

@[simp] theorem standardConsLinear_apply (r : ℕ) (p : (K × K) × Standard K r) :
    standardConsLinear r p = (Fin.cons p.1.1 p.2.1, Fin.cons p.1.2 p.2.2) := rfl

theorem standardCons_gram (r : ℕ) (p q : (K × K) × Standard K r) :
    standardBilin (r + 1) (standardConsLinear r p) (standardConsLinear r q) =
      p.1.1 * q.1.2 - p.1.2 * q.1.1 + standardBilin r p.2 q.2 := by
  simp only [standardConsLinear_apply, standardBilin_apply,
    Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
  ring

private theorem exists_gram_map_aux (r : ℕ) :
    ∀ (V : Type v) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
      (B : BilinForm K V), B.IsAlt → finrank K (LinearMap.range B) ≤ 2 * r →
        ∃ L : V →ₗ[K] Standard K r, ∀ x y : V, standardBilin r (L x) (L y) = B x y := by
  induction r with
  | zero =>
    intro V _ _ _ B hB hrank
    have hzero : B = 0 := by
      by_contra hnonzero
      obtain ⟨u, v, huv⟩ := exists_normalized_pair B hnonzero
      have hsplit := rank_pairOrthogonal B hB huv
      omega
    refine ⟨0, ?_⟩
    intro x y
    simp [hzero]
  | succ r ih =>
    intro V _ _ _ B hB hrank
    by_cases hzero : B = 0
    · refine ⟨0, ?_⟩
      intro x y
      simp [hzero]
    · obtain ⟨u, v, huv⟩ := exists_normalized_pair B hzero
      let N := pairOrthogonal B u v
      let C : BilinForm K N := B.restrict N
      have hC : C.IsAlt := fun z => hB z.val
      have hsplit := rank_pairOrthogonal B hB huv
      have hrest : finrank K (LinearMap.range C) ≤ 2 * r := by
        change finrank K (LinearMap.range (B.restrict (pairOrthogonal B u v))) ≤ _
        omega
      obtain ⟨L, hL⟩ := ih N C hC hrest
      let f : V →ₗ[K] (K × K) × Standard K r :=
        ((B.flip v).prod (-B.flip u)).prod
          (L.comp (pairProjectionToOrthogonal B hB huv))
      refine ⟨(standardConsLinear r).comp f, ?_⟩
      intro x y
      change standardBilin (r + 1)
        (standardConsLinear r ((B x v, -B x u),
          L (pairProjectionToOrthogonal B hB huv x)))
        (standardConsLinear r ((B y v, -B y u),
          L (pairProjectionToOrthogonal B hB huv y))) = B x y
      rw [standardCons_gram, hL]
      exact (pair_gram_identity B hB huv x y).symm

theorem exists_gram_map [FiniteDimensional K E] (r : ℕ) (B : BilinForm K E)
    (hB : B.IsAlt) (hrank : finrank K (LinearMap.range B) ≤ 2 * r) :
    ∃ L : E →ₗ[K] Standard K r, ∀ x y : E, standardBilin r (L x) (L y) = B x y :=
  exists_gram_map_aux r E B hB hrank

theorem tail_frame_independent [FiniteDimensional K E] {t : ℕ}
    (B : BilinForm K E) (hB : B.IsAlt) {u v : E} (huv : B u v = 1)
    (frame : Fin (t + 1) → E)
    (hinjective : Function.Injective
      (LinearMap.comp B (Fintype.linearCombination K frame)))
    (hmem : ∀ i : Fin t, frame i.succ ∈ pairOrthogonal B u v) :
    Function.Injective
      (LinearMap.comp (B.restrict (pairOrthogonal B u v))
        (Fintype.linearCombination K (fun i : Fin t => ⟨frame i.succ, hmem i⟩))) := by
  let N := pairOrthogonal B u v
  let tail : Fin t → N := fun i => ⟨frame i.succ, hmem i⟩
  let g := LinearMap.comp (B.restrict N) (Fintype.linearCombination K tail)
  change Function.Injective g
  apply LinearMap.ker_eq_bot.mp
  apply (Submodule.eq_bot_iff _).mpr
  intro a ha
  have hwhole : ((Fintype.linearCombination K tail) a).val ∈ LinearMap.ker B := by
    rw [← pair_kernel_map B hB huv]
    exact ⟨(Fintype.linearCombination K tail) a, ha, rfl⟩
  have hcombination : ((Fintype.linearCombination K tail) a).val =
      (Fintype.linearCombination K frame) (Fin.cons 0 a) := by
    calc
      ((Fintype.linearCombination K tail) a).val = ∑ i, a i • frame i.succ := by
        change N.subtype ((Fintype.linearCombination K tail) a) = _
        rw [Fintype.linearCombination_apply, map_sum]
        simp only [map_smul]
        rfl
      _ = (Fintype.linearCombination K frame) (Fin.cons 0 a) := by
        rw [Fintype.linearCombination_apply, Fin.sum_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ, zero_smul, zero_add]
  have hfull : (LinearMap.comp B (Fintype.linearCombination K frame)) (Fin.cons 0 a) = 0 := by
    change B ((Fintype.linearCombination K frame) (Fin.cons 0 a)) = 0
    rw [← hcombination]
    exact hwhole
  have hzero : Fin.cons (0 : K) a = 0 :=
    hinjective (by simpa only [map_zero] using hfull)
  funext i
  simpa only [Fin.cons_succ, Pi.zero_apply] using congrFun hzero i.succ

def standardFrame (r i : ℕ) : Standard K r :=
  (fun j => if j.val = i then 1 else 0, 0)

theorem standardFrame_cons_zero (r : ℕ) :
    standardConsLinear r ((1, 0), (0 : Standard K r)) = standardFrame (r + 1) 0 := by
  rw [standardConsLinear_apply]
  apply Prod.ext
  · funext j
    refine Fin.cases ?_ (fun i => ?_) j <;> simp [standardFrame]
  · funext j
    exact Fin.cases rfl (fun _ => rfl) j

theorem standardFrame_cons_succ (r i : ℕ) :
    standardConsLinear r ((0, 0), standardFrame (K := K) r i) =
      standardFrame (r + 1) (i + 1) := by
  rw [standardConsLinear_apply]
  apply Prod.ext
  · funext j
    refine Fin.cases ?_ (fun k => ?_) j <;> simp [standardFrame]
  · funext j
    exact Fin.cases rfl (fun _ => rfl) j

private theorem exists_gram_frame_aux (t : ℕ) :
    ∀ (r : ℕ) (V : Type v) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
      (B : BilinForm K V), B.IsAlt → finrank K (LinearMap.range B) ≤ 2 * r →
      ∀ frame : Fin t → V, (∀ i j, B (frame i) (frame j) = 0) →
      Function.Injective (LinearMap.comp B (Fintype.linearCombination K frame)) → t ≤ r →
      ∃ L : V →ₗ[K] Standard K r,
        (∀ x y : V, standardBilin r (L x) (L y) = B x y) ∧
        ∀ i : Fin t, L (frame i) = standardFrame r i.val := by
  induction t with
  | zero =>
    intro r V _ _ _ B hB hrank frame _ _ _
    obtain ⟨L, hL⟩ := exists_gram_map r B hB hrank
    exact ⟨L, hL, fun i => Fin.elim0 i⟩
  | succ t ih =>
    intro r V _ _ _ B hB hrank frame hisotropic hinjective htr
    cases r with
    | zero => omega
    | succ r =>
      obtain ⟨v, hpartner⟩ := exists_frame_partner B frame hinjective 0
      let u := frame 0
      have huv : B u v = 1 := by simpa [u] using hpartner 0
      let N := pairOrthogonal B u v
      let C : BilinForm K N := B.restrict N
      have hmem : ∀ i : Fin t, frame i.succ ∈ N := by
        intro i
        refine ⟨hisotropic 0 i.succ, hB.isRefl (frame i.succ) v ?_⟩
        simpa using hpartner i.succ
      let tail : Fin t → N := fun i => ⟨frame i.succ, hmem i⟩
      have hC : C.IsAlt := fun z => hB z.val
      have htail : Function.Injective
          (LinearMap.comp C (Fintype.linearCombination K tail)) :=
        tail_frame_independent B hB huv frame hinjective hmem
      have hsplit := rank_pairOrthogonal B hB huv
      have hrest : finrank K (LinearMap.range C) ≤ 2 * r := by
        change finrank K (LinearMap.range (B.restrict (pairOrthogonal B u v))) ≤ _
        omega
      obtain ⟨L, hL, hframe⟩ := ih r N C hC hrest tail
        (fun i j => hisotropic i.succ j.succ) htail (by omega)
      let f : V →ₗ[K] (K × K) × Standard K r :=
        ((B.flip v).prod (-B.flip u)).prod
          (L.comp (pairProjectionToOrthogonal B hB huv))
      refine ⟨(standardConsLinear r).comp f, ?_, ?_⟩
      · intro x y
        change standardBilin (r + 1)
          (standardConsLinear r ((B x v, -B x u),
            L (pairProjectionToOrthogonal B hB huv x)))
          (standardConsLinear r ((B y v, -B y u),
            L (pairProjectionToOrthogonal B hB huv y))) = B x y
        rw [standardCons_gram, hL]
        exact (pair_gram_identity B hB huv x y).symm
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · have hprojection : pairProjectionToOrthogonal B hB huv u = 0 := by
            apply Subtype.ext
            exact pairProjection_first B hB huv
          change standardConsLinear r ((B u v, -B u u),
            L (pairProjectionToOrthogonal B hB huv u)) = standardFrame (r + 1) 0
          rw [huv, hB.self_eq_zero, hprojection, map_zero, neg_zero]
          exact standardFrame_cons_zero r
        · have hpair : B (frame j.succ) v = 0 := by simpa using hpartner j.succ
          have horth : B (frame j.succ) u = 0 := hisotropic j.succ 0
          have hprojection : pairProjectionToOrthogonal B hB huv (frame j.succ) = tail j := by
            apply Subtype.ext
            exact pairProjection_eq_self B hB (hmem j)
          change standardConsLinear r ((B (frame j.succ) v, -B (frame j.succ) u),
            L (pairProjectionToOrthogonal B hB huv (frame j.succ))) =
              standardFrame (r + 1) (j.val + 1)
          rw [hpair, horth, neg_zero, hprojection, hframe j]
          exact standardFrame_cons_succ r j.val

theorem exists_gram_map_with_frame [FiniteDimensional K E]
    (r : ℕ) (B : BilinForm K E) (hB : B.IsAlt)
    (hrank : finrank K (LinearMap.range B) ≤ 2 * r) {t : ℕ} (frame : Fin t → E)
    (hisotropic : ∀ i j, B (frame i) (frame j) = 0)
    (hinjective : Function.Injective
      (LinearMap.comp B (Fintype.linearCombination K frame))) (htr : t ≤ r) :
    ∃ L : E →ₗ[K] Standard K r,
      (∀ x y : E, standardBilin r (L x) (L y) = B x y) ∧
      ∀ i : Fin t, L (frame i) = standardFrame r i.val :=
  exists_gram_frame_aux t r E B hB hrank frame hisotropic hinjective htr

theorem standardFrame_left_pairing {r : ℕ} (i : Fin r) (z : Standard K r) :
    standardBilin r (standardFrame r i.val) z = z.2 i := by
  classical
  rw [standardBilin_apply]
  change (∑ j : Fin r, (if j.val = i.val then (1 : K) else 0) * z.2 j) -
    (∑ j : Fin r, (0 : K) * z.1 j) = z.2 i
  simp only [zero_mul, Finset.sum_const_zero, sub_zero]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    have hval : j.val ≠ i.val := fun h => hji (Fin.ext h)
    simp [hval]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

theorem gram_map_frame_coordinate {r t : ℕ} (B : BilinForm K E)
    (L : E →ₗ[K] Standard K r) (frame : Fin t → E)
    (hgram : ∀ x y, standardBilin r (L x) (L y) = B x y)
    (hframe : ∀ i, L (frame i) = standardFrame r i.val) (htr : t ≤ r)
    (i : Fin t) (z : E) : (L z).2 (Fin.castLE htr i) = B (frame i) z := by
  have h := hgram (frame i) z
  rw [hframe i] at h
  exact (standardFrame_left_pairing (Fin.castLE htr i) (L z)).symm.trans h

end Lemmata.CocubicCovering.CoveringSymplectic
