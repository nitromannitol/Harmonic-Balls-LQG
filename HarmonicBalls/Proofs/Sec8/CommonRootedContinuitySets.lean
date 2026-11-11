import HarmonicBalls.Proofs.Sec8.RootedContinuitySets

/-! # Common continuity sets for two random measures

The imported phase-frequency argument uses Leonardo Bonanno's
`LatticeProb.Prob.Birkhoff` formalization.
-/

open MeasureTheory Filter Set Metric
open scoped ENNReal Topology

namespace HarmonicBalls

/-- Two locally finite random measures, possibly on different probability
spaces, have a common continuity ball, generating π-system, and buffered
exhaustion. -/
theorem exists_common_continuity_system_of_ae_locallyFinite
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (P : Measure Ω) [IsProbabilityMeasure P] (Q : Measure Ξ) [IsProbabilityMeasure Q]
    (μ : Ω → Measure ℂ) (ν : Ξ → Measure ℂ)
    (hμ : AEMeasurable μ P) (hν : AEMeasurable ν Q)
    (hμloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω))
    (hνloc : ∀ᵐ ω ∂Q, IsLocallyFiniteMeasure (ν ω))
    {R : ℝ} (hR : 0 < R) :
    ∃ ε ∈ Ioo (0 : ℝ) R, ∃ T : Set (Set ℂ),
      T.Countable ∧ IsPiSystem T ∧ univ ∈ T ∧ (∀ V ∈ T, IsOpen V) ∧
      (inferInstance : MeasurableSpace ℂ) = MeasurableSpace.generateFrom T ∧
      ∃ E : ℕ → Set ℂ, (∀ n, MeasurableSet (E n)) ∧ Monotone E ∧
        (⋃ n, E n) = ball 0 ε ∧
        (∀ n w, w ∈ E n → closedBall w (dyadicScale n) ⊆ ball 0 ε) ∧
        (∀ᵐ ω ∂P, ∀ V ∈ T, (∀ n, μ ω (frontier (E n)) = 0 ∧
          μ ω (frontier (V ∩ E n)) = 0) ∧ μ ω (frontier (⋃ n, E n)) = 0 ∧
          μ ω (frontier (V ∩ ⋃ n, E n)) = 0) ∧
        (∀ᵐ ω ∂Q, ∀ V ∈ T, (∀ n, ν ω (frontier (E n)) = 0 ∧
          ν ω (frontier (V ∩ E n)) = 0) ∧ ν ω (frontier (⋃ n, E n)) = 0 ∧
          ν ω (frontier (V ∩ ⋃ n, E n)) = 0) := by
  obtain ⟨μ', hμm, hμ'loc, hμeq⟩ := Section6.exists_measurable_locallyFinite_rep hμ hμloc
  obtain ⟨ν', hνm, hν'loc, hνeq⟩ := Section6.exists_measurable_locallyFinite_rep hν hνloc
  let η : Ω × Ξ → Measure ℂ := fun x => μ' x.1 + ν' x.2
  have hηm : Measurable η := (hμm.comp measurable_fst).add (hνm.comp measurable_snd)
  have hηloc (x : Ω × Ξ) : IsLocallyFiniteMeasure (η x) := by
    let : IsLocallyFiniteMeasure (μ' x.1) := hμ'loc x.1
    let : IsLocallyFiniteMeasure (ν' x.2) := hν'loc x.2
    refine ⟨fun z => ⟨ball z 1, ball_mem_nhds z zero_lt_one, ?_⟩⟩
    change (μ' x.1 + ν' x.2) (ball z 1) < ∞
    rw [Measure.add_apply]
    exact ENNReal.add_lt_top.mpr ⟨measure_ball_lt_top, measure_ball_lt_top⟩
  obtain ⟨ε, hε, T, hc, hp, hu, ho, hg, E, hEm, hmono, hunion, hbuffer, h⟩ :=
    exists_recentered_continuity_system (P.prod Q) η hηm.aemeasurable
      (Eventually.of_forall hηloc) (fun _ => 0) measurable_const hR
  have h' : ∀ᵐ x ∂(P.prod Q), ∀ V ∈ T,
      (∀ n, η x (frontier (E n)) = 0 ∧ η x (frontier (V ∩ E n)) = 0) ∧
      η x (frontier (⋃ n, E n)) = 0 ∧ η x (frontier (V ∩ ⋃ n, E n)) = 0 := by
    simpa only [sub_zero, show (fun v : ℂ => v) = id from rfl, Measure.map_id] using h
  have hpair := Measure.ae_ae_of_ae_prod h'
  have hsplit (ω : Ω) (ξ : Ξ) (H : ∀ V ∈ T,
      (∀ n, η (ω, ξ) (frontier (E n)) = 0 ∧ η (ω, ξ) (frontier (V ∩ E n)) = 0) ∧
      η (ω, ξ) (frontier (⋃ n, E n)) = 0 ∧ η (ω, ξ) (frontier (V ∩ ⋃ n, E n)) = 0) :
      (∀ V ∈ T, (∀ n, μ' ω (frontier (E n)) = 0 ∧ μ' ω (frontier (V ∩ E n)) = 0) ∧
        μ' ω (frontier (⋃ n, E n)) = 0 ∧ μ' ω (frontier (V ∩ ⋃ n, E n)) = 0) ∧
      (∀ V ∈ T, (∀ n, ν' ξ (frontier (E n)) = 0 ∧ ν' ξ (frontier (V ∩ E n)) = 0) ∧
        ν' ξ (frontier (⋃ n, E n)) = 0 ∧ ν' ξ (frontier (V ∩ ⋃ n, E n)) = 0) := by
    have hz (A : Set ℂ) (hA : η (ω, ξ) A = 0) : μ' ω A = 0 ∧ ν' ξ A = 0 := by
      simpa only [η, Measure.add_apply, add_eq_zero] using hA
    constructor <;> intro V hV
    · exact ⟨fun n => ⟨(hz _ ((H V hV).1 n).1).1, (hz _ ((H V hV).1 n).2).1⟩,
        (hz _ (H V hV).2.1).1, (hz _ (H V hV).2.2).1⟩
    · exact ⟨fun n => ⟨(hz _ ((H V hV).1 n).1).2, (hz _ ((H V hV).1 n).2).2⟩,
        (hz _ (H V hV).2.1).2, (hz _ (H V hV).2.2).2⟩
  refine ⟨ε, hε, T, hc, hp, hu, ho, hg, E, hEm, hmono, hunion, hbuffer, ?_, ?_⟩
  · filter_upwards [hpair, hμeq] with ω hω he
    obtain ⟨ξ, hξ⟩ := hω.exists
    simpa only [he] using (hsplit ω ξ hξ).1
  · obtain ⟨ω, hω⟩ := hpair.exists
    filter_upwards [hω, hνeq] with ξ hξ he
    simpa only [he] using (hsplit ω ξ hξ).2

end HarmonicBalls
