import HarmonicBalls.Proofs.Sec5.ContainmentEventNullMeasurable
import HarmonicBalls.Proofs.Sec5.LocalMeasureEvaluations

/-! # Field-local representation of exact uniform containment -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter

universe u

/-- The analytic representation of containment failure works with any decoder
of the continuous Green potential. -/
theorem exists_analyticSet_unitClusterContainmentEvent_compl_of_decoder
    (Q : Measure ℂ → C(closedBall (0 : ℂ) 1, ℝ))
    (hQeq : ∀ ν, ContinuousOn (greenPotentialBall ν 1) (closedBall 0 1) →
      ∀ y, Q ν y = greenPotentialBall ν 1 y) (m : ℕ) :
    ∃ S : Set C(closedBall (0 : ℂ) 1, ℝ), AnalyticSet S ∧
      ∀ ν : Measure ℂ, IsLocallyFiniteMeasure ν →
        (∃ βm βp, VolumeGrowth ν 1 βm βp) →
        (Q ν ∈ S ↔ ν ∉ unitClusterContainmentEvent m) := by
  let T := {q : ℚ // (q : ℝ) ∈ Ioo (0 : ℝ) ((2 : ℝ)⁻¹ ^ m)}
  choose S hS hgood using fun q : T =>
    exists_analyticSet_cluster_boundary_contact_potential q.property.1 Q hQeq
  refine ⟨⋃ q : T, S q, AnalyticSet.iUnion hS, ?_⟩
  intro ν hloc hvol
  have hmono : ∀ z ∈ ball (0 : ℂ) (1 / 2), ∀ s t : ℝ, 0 < s → s ≤ t →
      cluster ν 1 z s ⊆ cluster ν 1 z t := by
    intro z hz s t hs hst
    obtain ⟨βm, βp, hv⟩ := hvol
    exact cluster_subset_of_general obstacleMonotoneGeneral_holds obstacleCompatibilityShiftStep_holds
      hloc zero_lt_one hv (ball_subset_ball (by norm_num) hz) hs hst
  rw [not_mem_unitClusterContainmentEvent_iff ν m hmono]
  simp only [mem_iUnion]
  constructor
  · rintro ⟨q, hq⟩
    obtain ⟨z, hz⟩ := (hgood q ν hloc hvol).mp hq
    exact ⟨q, q.property, z, (not_cluster_closure_subset_ball_iff ν q z).mp hz⟩
  · rintro ⟨q, hq, z, hz⟩
    let q' : T := ⟨q, hq⟩
    exact ⟨q', (hgood q' ν hloc hvol).mpr
      ⟨z, (not_cluster_closure_subset_ball_iff ν q z).mpr hz⟩⟩

/-- Exact all-centre unit containment has a representative measurable with
respect to the field on the unit disc. The proposed LQG measure locality input
is explicit. -/
theorem exists_local_lqg_unitClusterContainmentEvent
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hloc : LQGMeasureLocality P γ α₀ hC hcirc) (m : ℕ) :
    ∃ E : Set Ω, MeasurableSet[fieldSigmaAlgebra α₀ hC (ball 0 1)] E ∧
      (μ ⁻¹' unitClusterContainmentEvent m) =ᵐ[P] E := by
  let : IsProbabilityMeasure P := hGFF.isProbabilityMeasure
  obtain ⟨βm, βp, hae⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
  have hcont : ∀ᵐ ω ∂P, ContinuousOn (greenPotentialBall (μ ω) 1) (closedBall 0 1) := by
    filter_upwards [hae] with ω hω
    exact greenPotentialBallContinuousStep_holds _ hω.1 1 βm βp zero_lt_one (hω.2 1 zero_lt_one)
  obtain ⟨Qloc, hQloc, hQlocEq⟩ := exists_local_lqg_greenPotentialBall_continuous_representative
    hγ hγ2 hα hGFF hμ hloc zero_lt_one hcont
  have hQambient : Measurable Qloc := hQloc.mono (hGFF.fieldSigmaAlgebra_le α₀ (ball 0 1)) le_rfl
  obtain ⟨Q, _hQ, hQeq⟩ := exists_measurable_greenPotentialBall_decoder zero_lt_one
  obtain ⟨S, hSa, hScorrect⟩ := exists_analyticSet_unitClusterContainmentEvent_compl_of_decoder Q hQeq m
  obtain ⟨B, _hBS, hBm, hBae⟩ :=
    (AnalyticSet.nullMeasurableSet_of_finite (Measure.map Qloc P) hSa).exists_measurable_subset_ae_eq
  refine ⟨(Qloc ⁻¹' B)ᶜ, (hQloc hBm).compl, ?_⟩
  have hpre := (hQambient.quasiMeasurePreserving P).preimage_ae_eq hBae
  filter_upwards [hae, hcont, hQlocEq, hpre] with ω hω hc hq hb
  have heq : Qloc ω = Q (μ ω) := by
    apply ContinuousMap.ext
    intro x
    exact (hq x).trans (hQeq (μ ω) hc x).symm
  have hs := hScorrect (μ ω) hω.1 ⟨βm, βp, hω.2 1 zero_lt_one⟩
  change (μ ω ∈ unitClusterContainmentEvent m) = (Qloc ω ∉ B)
  have hb' : (Qloc ω ∈ B) ↔ Qloc ω ∈ S := propext_iff.mp hb
  rw [heq] at hb' ⊢
  exact propext (by tauto)

/-- The exact containment events admit field-local representatives that are
simultaneously correct almost surely. -/
theorem exists_local_lqg_unitClusterContainmentEvents
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hloc : LQGMeasureLocality P γ α₀ hC hcirc) :
    ∃ E : ℕ → Set Ω, (∀ m, MeasurableSet[fieldSigmaAlgebra α₀ hC (ball 0 1)] (E m)) ∧
      ∀ᵐ ω ∂P, ∀ m, μ ω ∈ unitClusterContainmentEvent m ↔ ω ∈ E m := by
  choose E hE heq using fun m =>
    exists_local_lqg_unitClusterContainmentEvent hI2 hγ hγ2 hα hGFF hμ hloc m
  refine ⟨E, hE, ?_⟩
  filter_upwards [ae_all_iff.mpr heq] with ω hω
  intro m
  exact propext_iff.mp (hω m)

end HarmonicBalls
