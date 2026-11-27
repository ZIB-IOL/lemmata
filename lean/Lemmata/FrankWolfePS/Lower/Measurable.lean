module

public import Lemmata.FrankWolfePS.Lower.Scaling
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace

@[expose] public section

/-!
# The vertex oracle is measurable

For a nonzero direction the vertex oracle returns the vertex of the lexicographically first
minimizing label, minus `R` times the unit direction; the set of directions with a given first
label is cut out by finitely many coordinate comparisons. So the oracle is a finite sum of
measurable pieces, and a measurable randomized method has a measurable output against it.
-/

namespace Lemmata.FrankWolfePS
open Finset MeasureTheory
variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- The first label of the scan is the lexicographic minimum of `(q j, j)` over `I`. -/
theorem first_rank_eq_some_iff (q : ι → ℝ) {I : Finset ι} (hne : I.Nonempty) (j : ι) :
    first I (listing (rankOrder inferInstance q)) = some j ↔
      j ∈ I ∧ ∀ i ∈ I, q j < q i ∨ (q j = q i ∧ j ≤ i) := by
  obtain ⟨i₀, hi₀, hf, hm⟩ := first_rank_spec q hne
  rw [hf, Option.some.injEq]
  constructor
  · rintro rfl
    refine ⟨hi₀, fun i hi => ?_⟩
    rcases (hm i hi).1.lt_or_eq with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, (hm i hi).2 h⟩
  · rintro ⟨hj, hjm⟩
    have h1 := hm j hj
    rcases hjm i₀ hi₀ with h | ⟨h, h'⟩
    · exact absurd h (not_lt.mpr h1.1)
    · exact le_antisymm (h1.2 h.symm) h'

omit [Fintype ι] [LinearOrder ι] in
theorem continuous_coords : Continuous (coords (ι := ι)) :=
  (continuous_pi fun i => PiLp.continuous_apply 2 _ (some i)).prodMk
    (PiLp.continuous_apply 2 _ none)

/-- The vertex oracle is measurable. -/
theorem oracle_measurable (R : ℝ) (a : ι) {I : Finset ι} (hne : I.Nonempty) :
    Measurable (oracle R a I) := by
  classical
  let cell : ι → Set (Ambient ι) := fun j => {q | q ≠ 0 ∧ j ∈ I ∧
    ∀ i ∈ I, q (some j) < q (some i) ∨ (q (some j) = q (some i) ∧ j ≤ i)}
  have coord (i : ι) : Measurable fun q : Ambient ι => q (some i) :=
    (PiLp.continuous_apply 2 _ (some i)).measurable
  have hcell (j : ι) : MeasurableSet (cell j) := by
    have e : cell j = ({0}ᶜ : Set (Ambient ι)) ∩ ({_q | j ∈ I} ∩ ⋂ i ∈ (I : Set ι),
        ({q : Ambient ι | q (some j) < q (some i)} ∪
          ({q | q (some j) = q (some i)} ∩ {_q | j ≤ i}))) := by
      ext q; simp [cell]
    rw [e]
    exact (measurableSet_singleton 0).compl.inter ((MeasurableSet.const _).inter
      (MeasurableSet.biInter (Set.to_countable _) fun i _ => (measurableSet_lt (coord j)
        (coord i)).union ((measurableSet_eq_fun (coord j) (coord i)).inter
          (MeasurableSet.const _))))
  have hunit : Measurable (unit : Ambient ι → Ambient ι) :=
    (measurable_norm.inv).smul measurable_id
  have key : oracle R a I = fun q => ({0} : Set (Ambient ι)).indicator
      (fun _ => embed (atom a, 0)) q +
      ∑ j, (cell j).indicator (fun q => embed (atom j, R) - R • unit q) q := by
    funext q
    by_cases hq : q = 0
    · subst hq
      simp [oracle, orderFor, first, decode, cell]
    · obtain ⟨j, hj⟩ : ∃ j, first I (orderFor q) = some j := by
        obtain ⟨i, _, hf, _⟩ := first_rank_spec (fun i => q (some i)) hne
        exact ⟨i, by simpa [orderFor, hq] using hf⟩
      have hj' : first I (listing (rankOrder inferInstance fun i => q (some i))) = some j := by
        simpa [orderFor, hq] using hj
      have hcj : q ∈ cell j := ⟨hq, (first_rank_eq_some_iff (fun i => q (some i)) hne j).mp hj'⟩
      have hother (i : ι) (hi : i ≠ j) : q ∉ cell i := fun h => by
        have := (first_rank_eq_some_iff (fun i => q (some i)) hne i).mpr h.2
        rw [hj'] at this
        exact hi (Option.some.inj this).symm
      rw [Finset.sum_eq_single j (fun i _ hi => Set.indicator_of_notMem (hother i hi) _)
        (fun h => absurd (mem_univ j) h)]
      simp [oracle, hj, decode, hcj, hq]
  rw [key]
  exact (measurable_const.indicator (measurableSet_singleton 0)).add
    (Finset.measurable_sum _ fun j _ =>
      (measurable_const.sub (hunit.const_smul R)).indicator (hcell j))

/-- The physical vertex oracle is measurable. -/
theorem physOracle_measurable (a r : ℝ) (anchor : ι) {I : Finset ι} (hne : I.Nonempty) :
    Measurable (physOracle a r anchor I) :=
  (oracle_measurable (r / a) anchor hne).const_smul a

/-- A measurable randomized method has measurable outputs against every instance. -/
theorem physicalRun_measurable {Ω : Type*} [MeasurableSpace Ω] {T : ℕ}
    {s : Ω → Method (Ambient ι) T} (hs : Method.IsMeasurable s) (a r : ℝ) (anchor : ι)
    {I : Finset ι} (hne : I.Nonempty) :
    Measurable fun ω => (s ω).physicalRun a r anchor I :=
  continuous_coords.measurable.comp (hs _ (physOracle_measurable a r anchor hne))

end Lemmata.FrankWolfePS
