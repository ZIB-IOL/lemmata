module

public import Lemmata.SpanningTreeSymmetricEF.PathLabeling

@[expose] public section


/-!
Parity pairing of the actual finite permutation measure by an unused B
transposition, and exact identification of alternating point-stabilizer orbits
on permutations. Tree pushforward is separate. The small-index subgroup
classification is not assumed or proved here.
-/
namespace Lemmata.SpanningTreeSymmetricEF.PathOrbit
open scoped BigOperators
open PathLabeling
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- An unused B transposition preserves weights and every prescribed label
position in W, and reverses permutation parity. -/
theorem unused_swap (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Fin 3 ↪ V) (W : Finset V) {b c : V}
    (hb : b ∈ background s) (hc : c ∈ background s) (hbc : b ≠ c)
    (hbW : b ∉ W) (hcW : c ∉ W) (π : Equiv.Perm V) :
    weight G s (π * Equiv.swap b c) = weight G s π ∧
    (∀ w ∈ W, (π * Equiv.swap b c) w = π w) ∧
    Equiv.Perm.sign (π * Equiv.swap b c) = -Equiv.Perm.sign π := by
  refine ⟨weight_mul_of_fixes G s _ (swap_fixes s hb hc) π, ?_, ?_⟩
  · intro w hw
    have hwb : w ≠ b := fun h => hbW (h ▸ hw)
    have hwc : w ≠ c := fun h => hcW (h ▸ hw)
    simp [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hwb hwc]
  · simp [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hbc]

/-- Any event invariant under an unused B transposition has equally weighted
parity halves, even though individual weights may be negative. -/
theorem parity_mass_eq (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Fin 3 ↪ V) {b c : V} (hb : b ∈ background s) (hc : c ∈ background s)
    (hbc : b ≠ c) (P : Equiv.Perm V → Prop) [DecidablePred P]
    (hP : ∀ π, P (π * Equiv.swap b c) ↔ P π) :
    mass G s (fun π => P π ∧ Equiv.Perm.sign π = 1) =
      mass G s (fun π => P π ∧ Equiv.Perm.sign π = -1) := by
  have h := mass_mul_of_fixes G s (Equiv.swap b c) (swap_fixes s hb hc)
    (fun π => P π ∧ Equiv.Perm.sign π = 1)
  simpa [hP, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hbc, neg_eq_iff_eq_neg] using h.symm

/-- The even part is exactly half of the full signed event mass. -/
theorem parity_mass_half (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Fin 3 ↪ V) {b c : V} (hb : b ∈ background s) (hc : c ∈ background s)
    (hbc : b ≠ c) (P : Equiv.Perm V → Prop) [DecidablePred P]
    (hP : ∀ π, P (π * Equiv.swap b c) ↔ P π) :
    mass G s (fun π => P π ∧ Equiv.Perm.sign π = 1) = mass G s P / 2 := by
  have he := parity_mass_eq G s hb hc hbc P hP
  have hadd : mass G s (fun π => P π ∧ Equiv.Perm.sign π = 1) +
      mass G s (fun π => P π ∧ Equiv.Perm.sign π = -1) = mass G s P := by
    unfold mass
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro π _
    rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;>
      by_cases hp : P π <;> simp [h, hp]
  linarith

/-- There are exactly N-3 background labels, derived from the injective S labeling. -/
theorem card_background (s : Fin 3 ↪ V) :
    (background s).card = Fintype.card V - 3 := by
  have he : background s = Finset.univ \ Finset.univ.image s := by
    ext b
    simp [mem_background, eq_comm]
  rw [he, Finset.card_sdiff_of_subset (Finset.subset_univ _),
    Finset.card_image_of_injective _ s.injective]
  simp

/-- An unused B transposition exists already at N>=7, hence at N>=13. -/
theorem exists_unused_pair (s : Fin 3 ↪ V) (hn : 7 ≤ Fintype.card V)
    (W : Finset V) (hW : W.card ≤ 2) :
    ∃ b c, b ∈ background s ∧ c ∈ background s ∧ b ≠ c ∧ b ∉ W ∧ c ∉ W := by
  have hc : 1 < (background s \ W).card := by
    have h := Finset.le_card_sdiff W (background s)
    rw [card_background s] at h
    omega
  obtain ⟨b,hb,c,hc,hbc⟩ := Finset.one_lt_card.mp hc
  exact ⟨b,c,(Finset.mem_sdiff.mp hb).1,(Finset.mem_sdiff.mp hc).1,hbc,
    (Finset.mem_sdiff.mp hb).2,(Finset.mem_sdiff.mp hc).2⟩

/-- Exact even-parity split for prescribing at most two named labels.
The odd transposition is constructed, not supplied as an orbit hypothesis. -/
theorem fixing_parity_half (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Fin 3 ↪ V) (hn : 7 ≤ Fintype.card V) (W : Finset V) (hW : W.card ≤ 2)
    (f : V → V) :
    mass G s (fun π => (∀ w ∈ W, π w = f w) ∧ Equiv.Perm.sign π = 1) =
      mass G s (fun π => ∀ w ∈ W, π w = f w) / 2 := by
  obtain ⟨b,c,hb,hc,hbc,hbW,hcW⟩ := exists_unused_pair s hn W hW
  apply parity_mass_half G s hb hc hbc
  intro π
  have h := (unused_swap G s W hb hc hbc hbW hcW π).2.1
  constructor <;> intro hp w hw
  · simpa only [h w hw] using hp w hw
  · simpa only [h w hw] using hp w hw

/-- Every at-most-two-label fiber restricted to even permutations has
nonnegative signed mass. -/
theorem fixing_even_nonneg (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Fin 3 ↪ V) (hd : ∀ i, G.degree i = 2) (hn : 7 ≤ Fintype.card V)
    (W : Finset V) (hW : W.card ≤ 2) (f : V → V) :
    0 ≤ mass G s (fun π => (∀ w ∈ W, π w = f w) ∧ Equiv.Perm.sign π = 1) := by
  rw [fixing_parity_half G s hn W hW]
  exact div_nonneg (mass_fixing_nonneg G s hd (by omega) W hW f) (by norm_num)

/-- Doubling the even restriction gives a normalized signed permutation
certificate on the alternating group, with all small named-label fibers
nonnegative. This does not assert a tree-orbit classification. -/
theorem alternating_certificate (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Fin 3 ↪ V) (hd : ∀ i, G.degree i = 2) (hn : 7 ≤ Fintype.card V) :
    2 * mass G s (fun π => Equiv.Perm.sign π = 1) = 1 ∧
    ∀ W : Finset V, W.card ≤ 2 → ∀ f : V → V,
      0 ≤ 2 * mass G s (fun π => (∀ w ∈ W, π w = f w) ∧ Equiv.Perm.sign π = 1) := by
  constructor
  · have h := fixing_parity_half G s hn ∅ (by simp) id
    simp at h
    have ht : mass G s (fun _ => True) = 1 := by
      simpa [mass] using weight_total G s hd (by omega)
    rw [ht] at h
    linarith
  · intro W hW f
    exact mul_nonneg (by norm_num) (fixing_even_nonneg G s hd hn W hW f)

/-- Either prescribed sign has half of an at-most-two-label cylinder's mass. -/
theorem fixing_sign_half (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Fin 3 ↪ V) (hn : 7 ≤ Fintype.card V) (W : Finset V) (hW : W.card ≤ 2)
    (f : V → V) (ε : ℤˣ) :
    mass G s (fun π => (∀ w ∈ W, π w = f w) ∧ Equiv.Perm.sign π = ε) =
      mass G s (fun π => ∀ w ∈ W, π w = f w) / 2 := by
  rcases Int.units_eq_one_or ε with hε | hε
  · rw [hε]; exact fixing_parity_half G s hn W hW f
  · rw [hε]
    obtain ⟨b,c,hb,hc,hbc,hbW,hcW⟩ := exists_unused_pair s hn W hW
    have hp (π : Equiv.Perm V) : (∀ w ∈ W, (π * Equiv.swap b c) w = f w) ↔
        (∀ w ∈ W, π w = f w) := by
      have h := (unused_swap G s W hb hc hbc hbW hcW π).2.1
      constructor <;> intro hp w hw <;> simpa only [h w hw] using hp w hw
    rw [← parity_mass_eq G s hb hc hbc _ hp]
    exact fixing_parity_half G s hn W hW f

/-- The actual right orbit under even permutations fixing W pointwise.
This is an explicit action on full label permutations, not a tree orbit. -/
def alternatingOrbit (W : Finset V) (π ρ : Equiv.Perm V) : Prop :=
  ∃ τ : Equiv.Perm V, Equiv.Perm.sign τ = 1 ∧
    (∀ w ∈ W, τ w = w) ∧ ρ = π * τ

/-- Exact classification of these permutation orbits by label positions and
sign, proved by constructing the connecting permutation π⁻¹ρ. -/
theorem alternatingOrbit_iff (W : Finset V) (π ρ : Equiv.Perm V) :
    alternatingOrbit W π ρ ↔
      (∀ w ∈ W, ρ w = π w) ∧ Equiv.Perm.sign ρ = Equiv.Perm.sign π := by
  constructor
  · rintro ⟨τ,hτ,hW,rfl⟩
    constructor
    · intro w hw; simp [Equiv.Perm.mul_apply, hW w hw]
    · simp [Equiv.Perm.sign_mul, hτ]
  · rintro ⟨hW,hs⟩
    refine ⟨π⁻¹ * ρ, ?_, ?_, ?_⟩
    · simp [Equiv.Perm.sign_mul, hs]
    · intro w hw
      simp [Equiv.Perm.mul_apply, hW w hw]
    · simp

/-- The same orbit in the manuscript's inverse-relabeling convention πg⁻¹. -/
theorem alternatingOrbit_iff_inverse_relabel (W : Finset V) (π ρ : Equiv.Perm V) :
    alternatingOrbit W π ρ ↔ ∃ g : Equiv.Perm V, Equiv.Perm.sign g = 1 ∧
      (∀ w ∈ W, g w = w) ∧ ρ = π * g⁻¹ := by
  constructor
  · rintro ⟨τ,hτ,hW,hρ⟩
    refine ⟨τ⁻¹, by simp [hτ], ?_, by simpa using hρ⟩
    intro w hw
    apply τ.injective
    simpa using (hW w hw).symm
  · rintro ⟨g,hg,hW,hρ⟩
    refine ⟨g⁻¹, by simp [hg], ?_, hρ⟩
    intro w hw
    apply g.injective
    simpa using (hW w hw).symm

attribute [local instance] Classical.propDecidable

/-- Actual alternating point-stabilizer orbits have half their label cylinder
mass. No subgroup classification or assumed orbit-mass formula is used. -/
theorem alternatingOrbit_mass (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Fin 3 ↪ V) (hn : 7 ≤ Fintype.card V) (W : Finset V) (hW : W.card ≤ 2)
    (π : Equiv.Perm V) :
    (∑ ρ, if alternatingOrbit W π ρ then weight G s ρ else 0) =
      mass G s (fun ρ => ∀ w ∈ W, ρ w = π w) / 2 := by
  classical
  have h := fixing_sign_half G s hn W hW π (Equiv.Perm.sign π)
  simpa only [mass, alternatingOrbit_iff] using h

/-- Unconditional nonnegative orbit mass on full permutations for the
alternating point stabilizer of any W with at most two labels. -/
theorem alternatingOrbit_nonneg (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Fin 3 ↪ V) (hd : ∀ i, G.degree i = 2) (hn : 7 ≤ Fintype.card V)
    (W : Finset V) (hW : W.card ≤ 2) (π : Equiv.Perm V) :
    0 ≤ ∑ ρ, if alternatingOrbit W π ρ then weight G s ρ else 0 := by
  rw [alternatingOrbit_mass G s hn W hW]
  exact div_nonneg (mass_fixing_nonneg G s hd (by omega) W hW π) (by norm_num)

end
end Lemmata.SpanningTreeSymmetricEF.PathOrbit
