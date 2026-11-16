import HarmonicBalls.FirstPass.Phase2.Step8IdentificationProved

/-!
# Step 8 frequencies for all insertion parameters

A single calibrated event and its common probability yield the physical certificate frequencies for every admissible
insertion parameter and every dyadic scale.
-/

universe u

namespace HarmonicBalls

open MeasureTheory Set Metric
open FirstPassS11iStep8PhysExists Step8PerModelUniv

/-- A calibrated event and its probability work for all insertion parameters on sample spaces in `Type`. -/
theorem step8_uniformInsertion_canonical_zero
    (U V W T Q' Q : Set ℂ) (δ : ℝ) (hgeom : IsBufferedPinchGeometry U V W T Q' Q δ)
    (γ M : ℝ) (hγ0 : 0 < γ) (hγ2 : γ < 2) (hM : 0 < M) :
    ∃ E : Set Step8Code, ∃ q : ℝ,
      PinchEventGammaCanonicalStmt.{0} U T Q' Q γ M E ∧ CommonProb.{0} γ E q ∧
      ∀ α : ℝ, α < lqgQ γ → ∀ k : ℕ,
        AllModelsAt.{0} γ (lqgXi γ) α q U V W T Q' Q δ M k := by
  have hN2 := localMetricReplacement_zero_derived
  have hCanonM := lqgCanonicalDecodersMeasurableExist_of_xi_derived xi_eq_xiGamma_derived
  have hPE := step8PinchEventCanonical_zero_of_decoders hN2 hCanonM
  have hCal := step8EventCalibration_zero_of_decoders hN2 hCanonM
  obtain ⟨E, F, hPG, hcal, hU⟩ :=
    hCal U V W T Q' Q δ M γ hgeom hγ0 hγ2 hM (hPE U V W T Q' Q δ hgeom γ M hγ0 hγ2 hM)
  obtain ⟨q, hq⟩ := exists_localModConstField_prob γ hPG.1
  refine ⟨E, q, hPG, hq, ?_⟩
  intro α hα k
  exact allModelsAt_all_scales_of_scale_zero_univ hγ0 hγ2 hα coordChangeAlpha0Stmt_holds
    (FirstPassS11iInsertionTransfer.allModelsAt_insertion_of_zero_k0_of_normalizedMetric_univ hgeom hγ0 hγ2 hα
      S11aj.cameronMartinGFFReweighting_derived
      (fun Ω _ P hC hcirc => lqgMeasureExistence_forall_zero γ Ω P hC hcirc)
      (fun Ω _ P hC hcirc => lqgMeasureNonatomic_holds Ω P γ α hC hcirc)
      (fun c₁ c₂ r₁ r₂ => LocalDecoderCommon.localMeasureKernelStmt_derived γ c₁ c₂ r₁ r₂)
      localLQGMetricNormalizedMeasurableFixedMetric_derived lqgMetricFieldAxiomsUnivFrozen_derived
      (allModelsAt_zero_scale_zero_of_unit_univ hU (hcal q hq))) k

/-- The same calibrated event witnesses the Step 8 identity for all admissible insertions. -/
theorem step8_uniformIdentity_canonical_zero
    (U V W T Q' Q : Set ℂ) (δ : ℝ) (hgeom : IsBufferedPinchGeometry U V W T Q' Q δ)
    (γ M : ℝ) (hγ0 : 0 < γ) (hγ2 : γ < 2) (hM : 0 < M) :
    ∃ E : Set Step8Code, ∃ q : ℝ,
      PinchEventGammaCanonicalStmt.{0} U T Q' Q γ M E ∧ CommonProb.{0} γ E q ∧
      ∀ α : ℝ, α < lqgQ γ → Step8IdentityCanonicalStmt.{0} γ α U V W T Q' Q δ M E := by
  obtain ⟨E, q, hPG, hq, hall⟩ := step8_uniformInsertion_canonical_zero U V W T Q' Q δ hgeom γ M hγ0 hγ2 hM
  refine ⟨E, q, hPG, hq, fun α hα => ⟨q, ?_, ?_⟩⟩
  · intro Ω _ P hC hcirc μ D hG _ _
    exact hq Ω P hC hcirc hG
  · intro Ω _ P hC hcirc μ D hG hμ hD
    exact FirstPassS11iStep8Zoom.step8_zoom_family_of_ae_frequency P U V W T Q' Q δ M q μ D
      (fun k => hall α hα k Ω P hC hcirc μ D hG hμ hD)

/-- The physical frequency holds with one event and probability for all insertions and sample spaces. -/
theorem step8_uniformInsertion
    (U V W T Q' Q : Set ℂ) (δ : ℝ) (hgeom : IsBufferedPinchGeometry U V W T Q' Q δ)
    (γ ξ M : ℝ) (hγ0 : 0 < γ) (hγ2 : γ < 2) (hM : 0 < M) :
    ∃ E : Set Step8Code, ∃ q : ℝ,
      PinchEventGammaStmt.{u} U T Q' Q γ ξ M E ∧
      (∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
        (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ),
        IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ γ hcirc μ →
        IsLQGMetricOfField P γ ξ γ hC D →
        (P {ω | localModConstField γ hC (ball (0 : ℂ) 7) ω ∈ E}).toReal = q) ∧
      ∀ α : ℝ, α < lqgQ γ → ∀ k : ℕ, AllModelsAt.{u} γ ξ α q U V W T Q' Q δ M k := by
  by_cases hcan : ξ = lqgXi γ
  · subst ξ
    obtain ⟨E, q, hPG, hq, hall⟩ := step8_uniformInsertion_canonical_zero U V W T Q' Q δ hgeom γ M hγ0 hγ2 hM
    refine ⟨E, q, ⟨hPG.1, ?_⟩, ?_, ?_⟩
    · intro Ω _ P hC hcirc μ D hG hμ hD
      have hG' := isWholePlaneGFF_modelRangeMeasure (P := P) μ D hG
      have hμ' : IsLQGMeasureOfField (modelRangeMeasure P (modelPoint hC hcirc μ D)) γ γ
          (fun y => y.1.circle) (fun y => y.1.measure) := by
        unfold IsLQGMeasureOfField IsLQGMeasure at hμ ⊢
        exact ae_modelRangeMeasure_iff.2 hμ
      obtain ⟨𝔇, h𝔇, hDae⟩ := hD
      have hD' : IsLQGMetricOfField (modelRangeMeasure P (modelPoint hC hcirc μ D)) γ (lqgXi γ) γ
          (fun y => y.1.pairing) (fun y => y.1.metric) := ⟨𝔇, h𝔇, ae_modelRangeMeasure_iff.2 hDae⟩
      obtain ⟨_, hpos, hae⟩ := hPG.2 _ _ _ _ _ _ hG' hμ' hD'
      let : IsProbabilityMeasure P := FirstPassS11af.isProbabilityMeasure_of_isWholePlaneGFF hG
      let : IsProbabilityMeasure (modelRangeMeasure P (modelPoint hC hcirc μ D)) :=
        FirstPassS11af.isProbabilityMeasure_of_isWholePlaneGFF hG'
      have heq : P {ω | localModConstField γ hC (ball (0 : ℂ) 7) ω ∈ E} =
          modelRangeMeasure P (modelPoint hC hcirc μ D)
            {y | localModConstField γ (fun y => y.1.pairing) (ball (0 : ℂ) 7) y ∈ E} := by
        have h := S11iCert.prob_ballRestrict_alphaCanon_indep hG hG' γ E hPG.1
        simpa only [S11iCert.ballRestrict_alphaCanon_eq] using h
      exact ⟨localModConstField_measurable γ hC _ hPG.1, heq.symm ▸ hpos, ae_modelRangeMeasure_iff.1 hae⟩
    · intro Ω _ P hC hcirc μ D hG _ _
      have hG' := isWholePlaneGFF_modelRangeMeasure (P := P) μ D hG
      let : IsProbabilityMeasure P := FirstPassS11af.isProbabilityMeasure_of_isWholePlaneGFF hG
      let : IsProbabilityMeasure (modelRangeMeasure P (modelPoint hC hcirc μ D)) :=
        FirstPassS11af.isProbabilityMeasure_of_isWholePlaneGFF hG'
      have heq : P {ω | localModConstField γ hC (ball (0 : ℂ) 7) ω ∈ E} =
          modelRangeMeasure P (modelPoint hC hcirc μ D)
            {y | localModConstField γ (fun y => y.1.pairing) (ball (0 : ℂ) 7) y ∈ E} := by
        have h := S11iCert.prob_ballRestrict_alphaCanon_indep hG hG' γ E hPG.1
        simpa only [S11iCert.ballRestrict_alphaCanon_eq] using h
      rw [heq]
      exact hq _ _ _ _ hG'
    · intro α hα k Ω _ P hC hcirc μ D hG hμ hD
      have hG' := isWholePlaneGFF_modelRangeMeasure (P := P) μ D hG
      have hμ' : IsLQGMeasureOfField (modelRangeMeasure P (modelPoint hC hcirc μ D)) γ α
          (fun y => y.1.circle) (fun y => y.1.measure) := by
        unfold IsLQGMeasureOfField IsLQGMeasure at hμ ⊢
        exact ae_modelRangeMeasure_iff.2 hμ
      obtain ⟨𝔇, h𝔇, hDae⟩ := hD
      have hD' : IsLQGMetricOfField (modelRangeMeasure P (modelPoint hC hcirc μ D)) γ (lqgXi γ) α
          (fun y => y.1.pairing) (fun y => y.1.metric) := ⟨𝔇, h𝔇, ae_modelRangeMeasure_iff.2 hDae⟩
      exact ae_modelRangeMeasure_iff.1 (hall α hα k _ _ _ _ _ _ hG' hμ' hD')
  · have hξ := weylExponentEq_lqgXi_of_xiGamma xi_eq_xiGamma_derived lqgXi_eq_xiGamma_derived
    have hno : ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (α : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
        (D : Ω → ℂ → ℂ → ℝ), ¬ IsLQGMetricOfField P γ ξ α hC D := by
      rintro Ω _ P α hC D ⟨𝔇, h𝔇, -⟩
      exact hcan (hξ γ ξ hγ0 hγ2 𝔇 h𝔇)
    refine ⟨univ, 0, ⟨MeasurableSet.univ, ?_⟩, ?_, ?_⟩
    · intro Ω _ P hC _ _ D _ _ hD
      exact (hno P γ hC D hD).elim
    · intro Ω _ P hC _ _ D _ _ hD
      exact (hno P γ hC D hD).elim
    · intro α _ k Ω _ P hC _ _ D _ _ hD
      exact (hno P α hC D hD).elim

/-- A common event witnesses the Step 8 identity for every admissible insertion. -/
theorem step8_uniformIdentity
    (U V W T Q' Q : Set ℂ) (δ : ℝ) (hgeom : IsBufferedPinchGeometry U V W T Q' Q δ)
    (γ ξ M : ℝ) (hγ0 : 0 < γ) (hγ2 : γ < 2) (hM : 0 < M) :
    ∃ E : Set Step8Code, PinchEventGammaStmt.{u} U T Q' Q γ ξ M E ∧
      ∀ α : ℝ, α < lqgQ γ → Step8IdentityStmt.{u} γ ξ α U V W T Q' Q δ M E := by
  obtain ⟨E, q, hPG, hq, hall⟩ := step8_uniformInsertion U V W T Q' Q δ hgeom γ ξ M hγ0 hγ2 hM
  refine ⟨E, hPG, fun α hα => ⟨q, hq, ?_⟩⟩
  intro Ω _ P hC hcirc μ D hG hμ hD
  exact FirstPassS11iStep8Zoom.step8_zoom_family_of_ae_frequency P U V W T Q' Q δ M q μ D
    (fun k => hall α hα k Ω P hC hcirc μ D hG hμ hD)

end HarmonicBalls
