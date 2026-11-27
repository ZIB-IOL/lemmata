module

public import Lemmata.FrankWolfePS.Statement
public import Lemmata.FrankWolfePS.Lower.Prescribed
public import Lemmata.FrankWolfePS.Unique.Feasible
public import Lemmata.FrankWolfePS.Lower.Deterministic
public import Lemmata.FrankWolfePS.Lower.Penalized

@[expose] public section

/-!
# Proofs of the statements

Each proposition of `Statement.lean` follows from the developed results by unfolding the
user-facing names (`hardBody`, `vertexLMO`, `uniqueLMO`) and converting between ambient
points and coordinates.
-/

namespace Lemmata.FrankWolfePS
open MeasureTheory Finset
open scoped RealInnerProductSpace Pointwise

section Bridge
variable {ι : Type*} [Fintype ι] [LinearOrder ι]

theorem cast_succ (T : ℕ) : ((T + 1 : ℕ) : ℝ) = (T : ℝ) + 1 := by push_cast; ring

theorem shell_card {T : ℕ} {anchor : ι} {S : Finset ι} (hS : S ∈ shells T anchor) :
    (insert anchor S).card = 8 * (T + 1) ∧ anchor ∈ insert anchor S :=
  ⟨(Unique.shell_info hS).2, mem_insert_self _ _⟩

end Bridge

theorem lower_bound_unique_lmo_proof : LowerBoundUniqueLMO := by
  intro ι Ω _ _ _ T anchor hN L β D hL hβ hD μ _ s hs
  obtain ⟨C, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
    Unique.prescribed_unique_lower_bound T anchor hN hL hβ hD μ s hs
  rw [cast_succ] at h9
  exact ⟨C, ⟨h1, h2, h3, h4, h5, h6, h7⟩, h8, h9⟩

theorem lower_bound_unique_feasible_proof : LowerBoundUniqueFeasible := by
  intro ι Ω _ _ _ T anchor hN L β D hL hβ hD μ _ s hs hfeas
  have feas : ∀ Dt : Unique.Draw ι T, ∀ J ∈ shells T anchor, ∀ ω,
      (s ω).run (Unique.reply ((1 / β) • Unique.instanceBody (Unique.unitScale β D) anchor T Dt
        (insert anchor J)) (Unique.hardStart β D anchor)) ∈
        (1 / β) • Unique.instanceBody (Unique.unitScale β D) anchor T Dt (insert anchor J) := by
    intro Dt J hJ ω
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, -, -⟩ := Unique.scaled_instance hβ hD T anchor Dt hJ
    exact hfeas _ ⟨h1, h2, h3, h4, h5, h6, h7⟩ ω
  obtain ⟨Dt, J, hJ, hp, he⟩ :=
    Unique.prescribed_unique_feasible T anchor hN hL hβ hD μ s hs feas
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, -, -⟩ := Unique.scaled_instance hβ hD T anchor Dt hJ
  refine ⟨_, ⟨h1, h2, h3, h4, h5, h6, h7⟩, fun q => Unique.reply_min h1 h7 q, ?_, ?_⟩
  · rw [cast_succ] at hp; exact hp
  · rw [cast_succ] at he
    have hT : (0 : ℝ) < (T : ℝ) + 1 := by positivity
    calc 3 * L * (D - 2 / β) ^ 2 / (256 * ((T : ℝ) + 1)) =
        3 / 4 * (L * (D - 2 / β) ^ 2 / (64 * ((T : ℝ) + 1))) := by field_simp; ring
      _ ≤ _ := he

theorem lower_bound_vertex_lmo_proof : LowerBoundVertexLMO := by
  intro ι Ω _ _ _ T anchor hN L β D hL hβ hD μ _ s hs
  have meas : ∀ S ∈ shells T anchor, Measurable fun ω =>
      (s ω).physicalRun ((D - 2 / β) / Real.sqrt 2) (1 / β) anchor (insert anchor S) :=
    fun S _ => physicalRun_measurable hs _ _ anchor (insert_nonempty anchor S)
  obtain ⟨I, hc, ha, h1, h2, h3, h4, h5⟩ :=
    fixed_smoothness_lower_bound μ T anchor hN hL hβ hD s meas
  refine ⟨I, hc, ha, h1, h2, h3, h4, fun q => ?_, ?_⟩
  · have hr : (0 : ℝ) < 1 / β := by positivity
    have hapos : 0 < (D - 2 / β) / Real.sqrt 2 :=
      (prescribed_parameters (L := L) hβ hD 1).2.1
    exact physical_oracle_correct hapos hr anchor ha q
  · rw [cast_succ] at h5
    simpa only [Method.physicalRun, embed_coords, ← hardObjective_coords, physicalOpt_eq_sInf,
      hardBody, vertexLMO] using h5

theorem lower_bound_feasible_proof : LowerBoundFeasible := by
  intro ι Ω _ _ _ T anchor hN L β D hL hβ hD μ _ s hs hfeas
  have meas : ∀ S ∈ shells T anchor, Measurable fun ω =>
      (s ω).physicalRun ((D - 2 / β) / Real.sqrt 2) (1 / β) anchor (insert anchor S) :=
    fun S _ => physicalRun_measurable hs _ _ anchor (insert_nonempty anchor S)
  have feas : ∀ S ∈ shells T anchor, ∀ ω, embed ((s ω).physicalRun ((D - 2 / β) / Real.sqrt 2)
      (1 / β) anchor (insert anchor S)) ∈
        physicalBody ((D - 2 / β) / Real.sqrt 2) (1 / β) (insert anchor S) := by
    intro S _ ω
    simpa only [Method.physicalRun, embed_coords, hardBody, vertexLMO] using
      hfeas (insert anchor S) (mem_insert_self _ _) ω
  obtain ⟨S, hS, h1, h2, h3⟩ :=
    fixed_smoothness_expected_lower_bound μ T anchor hN hL hβ hD s meas feas
  obtain ⟨hc, ha⟩ := shell_card hS
  refine ⟨insert anchor S, hc, ha, h1, ?_, ?_⟩
  · rw [cast_succ] at h2
    simpa only [Method.physicalRun, ← hardObjective_coords, physicalOpt_eq_sInf, hardBody,
      vertexLMO] using h2
  · rw [cast_succ] at h3
    simpa only [Method.physicalRun, ← hardObjective_coords, physicalOpt_eq_sInf, hardBody,
      vertexLMO] using h3

theorem lower_bound_deterministic_proof : LowerBoundDeterministic := by
  intro ι _ _ T anchor hN L β D hL hβ hD s
  obtain ⟨I, hc, hI, hdiam, f⟩ := deterministic_prescribed T anchor hN hL hβ hD s
  refine ⟨I, hc, hI, hdiam, ?_⟩
  rw [cast_succ] at f
  simpa only [Method.physicalRun, embed_coords, ← hardObjective_coords, physicalOpt_eq_sInf,
    hardBody, vertexLMO] using f

theorem lower_bound_penalized_proof : LowerBoundPenalized := by
  intro ι Ω _ _ _ T anchor hN L β D ρ hL hβ hD hρ μ _ s hs
  obtain ⟨hr, ha, -, hdiam, hcut, -⟩ := prescribed_parameters (L := L) hβ hD (T + 1)
  have hρ' : L * (2 * ((D - 2 / β) / Real.sqrt 2) + 34 * (1 / β)) ≤ ρ := by
    have hdiff : 0 ≤ D - 2 / β := sub_nonneg.mpr ((div_le_iff₀ hβ).mpr (by linarith))
    have h1 : (D - 2 / β) / Real.sqrt 2 ≤ D - 2 / β :=
      div_le_self hdiff Real.one_lt_sqrt_two.le
    have h2 : 2 * ((D - 2 / β) / Real.sqrt 2) + 34 * (1 / β) ≤ 2 * D + 32 / β := by
      have : (0 : ℝ) ≤ 1 / β := by positivity
      have e : 2 * (D - 2 / β) + 34 * (1 / β) = 2 * D + 30 * (1 / β) := by ring
      have e' : 32 / β = 32 * (1 / β) := by ring
      linarith
    exact (mul_le_mul_of_nonneg_left h2 hL.le).trans hρ
  have meas : ∀ S ∈ shells T anchor, Measurable fun ω =>
      (s ω).run (physOracle ((D - 2 / β) / Real.sqrt 2) (1 / β) anchor (insert anchor S)) :=
    fun S _ => hs _ (physOracle_measurable _ _ anchor (insert_nonempty anchor S))
  obtain ⟨S, hS, hp, he⟩ := penalized_lower_bound T anchor hN hL ha hr hρ' μ s meas
  obtain ⟨hc, hI⟩ := shell_card hS
  refine ⟨insert anchor S, hc, hI,
    (physical_parameters ha hr _ (by omega : 1 < (insert anchor S).card)).1.trans hdiam, ?_, ?_⟩
  · have e : L * ((D - 2 / β) / Real.sqrt 2) ^ 2 / (128 * ((T + 1 : ℕ) : ℝ)) =
        L * (D - 2 / β) ^ 2 / (256 * ((T : ℝ) + 1)) := by
      rw [← cast_succ]
      generalize ((T + 1 : ℕ) : ℝ) = k at hcut ⊢
      calc _ = (L * ((D - 2 / β) / Real.sqrt 2) ^ 2 / (16 * k)) / 8 := by ring
        _ = (L * (D - 2 / β) ^ 2 / (32 * k)) / 8 := by rw [hcut]
        _ = _ := by ring
    rw [e] at hp
    simpa only [penalizedError, physicalPenalized, hardBody, vertexLMO] using hp
  · have e : L * ((D - 2 / β) / Real.sqrt 2) ^ 2 / (512 * ((T + 1 : ℕ) : ℝ)) =
        L * (D - 2 / β) ^ 2 / (1024 * ((T : ℝ) + 1)) := by
      rw [← cast_succ]
      generalize ((T + 1 : ℕ) : ℝ) = k at hcut ⊢
      calc _ = (L * ((D - 2 / β) / Real.sqrt 2) ^ 2 / (16 * k)) / 32 := by ring
        _ = (L * (D - 2 / β) ^ 2 / (32 * k)) / 32 := by rw [hcut]
        _ = _ := by ring
    rw [e] at he
    simpa only [penalizedError, physicalPenalized, hardBody, vertexLMO] using he

theorem posterior_identity_proof : PosteriorIdentity := by
  intro ι _ _ T anchor hN s R
  exact posterior_identity T anchor hN s R

theorem hard_body_geometry_proof : HardBodyGeometry := by
  intro ι _ _ β D hβ hD anchor I ha hI
  have hr : (0 : ℝ) < 1 / β := by positivity
  obtain ⟨-, hapos, hinv, hdiam, -, -⟩ := prescribed_parameters (L := 1) hβ hD 1
  set a := (D - 2 / β) / Real.sqrt 2
  have par := physical_parameters hapos hr I hI
  have cc := physical_body_compact_convex (a := a) (r := 1 / β) I
  refine ⟨cc.1, cc.2, ?_, par.1.trans hdiam, ?_, ?_, ?_, ?_⟩
  · show (interior (physicalBody a (1 / β) I)).Nonempty
    rw [physical_parallel hapos]
    obtain ⟨i, hi⟩ := Finset.card_pos.mp (by omega : 0 < I.card)
    exact rounded_interior_nonempty hr ⟨_, ⟨_, ⟨atom i, atom_base hi, rfl⟩, rfl⟩⟩
  · intro z hz w hw n m hn hm hs ht
    simpa only [hinv] using par.2 z hz w hw n m hn hm hs ht
  · intro β' hβ'
    exact not_lipschitzNormals_of_lt hapos hr (Finset.card_pos.mp (by omega)) (by rwa [hinv])
  · intro α hα
    exact not_uniformlyConvex hapos hr hI hα
  · intro q
    exact physical_oracle_correct hapos hr anchor ha q

theorem hard_body_optimum_proof : HardBodyOptimum := by
  intro ι _ _ L β D hL hβ hD anchor I hI
  have hr : (0 : ℝ) < 1 / β := by positivity
  have hapos : 0 < (D - 2 / β) / Real.sqrt 2 := (prescribed_parameters (L := L) hβ hD 1).2.1
  have hne : I.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨hm, hmin⟩ := hardMinimizer_spec hL hapos hr hne
  exact ⟨hm, hmin, fun M hM A q hA => not_localDualSharpness hapos hr hI M hM hA⟩

theorem symmetric_thickening_reveals_proof : SymmetricThickeningReveals := by
  intro ι _ _ A s hs I hne x hx i
  exact Unique.symmetric_lowest_point hs hne hx i

theorem rolling_ball_proof : RollingBall := by
  intro E _ _ _ _ C hc hv hne β hβ regular
  have hr : (0 : ℝ) < 1 / β := by positivity
  have nb := Upper.radius_regular hβ regular
  obtain ⟨e, he⟩ := exists_ne (0 : E)
  have par := Upper.parallel_of_normals hc hv hne hr nb he
  refine ⟨fun z hz n hn hs => Upper.rolling_of_normals hc hv hr nb hz hn hs, par, ?_⟩
  have hK := (Upper.erosion_compact_convex hc hv hr.le).1
  have hKne : (Upper.erosion C (1 / β)).Nonempty := by
    obtain ⟨z, hz⟩ := hne
    rw [par] at hz
    obtain ⟨u, hu, -⟩ := hz
    exact ⟨u, hu⟩
  conv_lhs => rw [par]
  exact Upper.parallel_diameter hK hKne hr e he

theorem quadratic_upper_bound_proof : QuadraticUpperBound := by
  intro E _ _ _ T hT L β hL hβ u e he
  obtain ⟨n, rfl⟩ : ∃ n, T = n + 2 := ⟨T - 2, by omega⟩
  refine ⟨Upper.innerFrankWolfe L (1 / β) u e n, fun C hc hv regular hD O => ?_⟩
  have hD' : 2 * (1 / β) ≤ Metric.diam C := by rwa [mul_one_div]
  obtain ⟨hm, hg⟩ := Upper.inner_frank_wolfe_upper hc hv hβ hL regular hD' O u e he n
  refine ⟨hm, fun w hw => (hg w hw).trans (le_of_eq ?_)⟩
  rw [mul_one_div]; push_cast; ring

theorem sliding_upper_bound_proof : SlidingUpperBound := by
  intro E _ _ _ C hc hv β hβ regular hD O f L hL hf hconv hLip e he n hn
  exact Upper.smooth_body_sliding_upper hc hv hβ regular hD O hL hf hconv hLip e he hn

theorem tangent_balls_linear_rate_proof : TangentBallsLinearRate := by
  intro E _ _ _ _ C hc cv r R μ hr hR inner outer O f L hμ df sc smooth ball cert x₀ hx n
  exact Joint.joint_body_linear_upper hc cv hr hR inner outer O hμ df sc smooth ball cert hx n

theorem grimmer_liu_comparison_proof : GrimmerLiuComparison := by
  intro β δ d T hβ hδ hT hd
  exact glExpression_le hβ hδ hT hd

end Lemmata.FrankWolfePS
