import HarmonicBalls.FirstPass.Phase2.Step8IdentificationProved

/-!
# Step 8 frequencies for all insertion parameters

A single calibrated event and its common probability yield the physical certificate frequencies for every admissible
insertion parameter and every dyadic scale.
-/

universe u

namespace HarmonicBalls

open MeasureTheory Set Metric
open FirstPassS11iStep8PhysExists Step8PerModelUniv FirstPassS11i

open Filter
open S11i.Step8CalibrationCanonical FirstPassS11iInsertionZeroUnitE FirstPassS11rRootedHrefGlobal
open FirstPassS11rFrozenCanonDecoders FirstPassS11iFinal11_13

/-- Calibration with the event identified as the physical certificate. -/
def Step8EventCalibrationWithCertificate : Prop :=
    ∀ (U V W T Q' Q : Set ℂ) (δ M γ : ℝ), IsBufferedPinchGeometry U V W T Q' Q δ →
      0 < γ → γ < 2 → 0 < M →
      (∃ E : Set Step8Code, PinchEventGammaCanonicalStmt.{0} U T Q' Q γ M E) →
      ∃ E F : Set Step8Code, PinchEventGammaCanonicalStmt.{0} U T Q' Q γ M E ∧
        EventCalibration.{0} γ E F ∧ InsertionZeroUnitStmt.{0} γ F U V W T Q' Q δ M ∧
        ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
          (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ),
          IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ γ hcirc μ →
          IsLQGMetricOfField P γ (lqgXi γ) γ hC D →
          ∀ᵐ ω ∂P, (localModConstField γ hC (ball (0 : ℂ) 7) ω ∈ E ↔
            CertificateEvent (μ ω) (D ω) (pinchOmegaGeom W Q δ) U V W T Q' Q δ M 1 0)

private theorem step8EventCalibrationWithCertificate
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{0})
    (hLen : LQGMetricLengthUnivFrozen.{0})
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementStmt.{0} γ ξ c₁ c₂ r₁ r₂)
    (hBase : HarmonicBalls.S11ak.LQGMetricBaseComparisonStmt.{0})
    (hμW : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ α₀ hC hcirc)
    (hLoc : LocalLQGDecoderCommonFrozen.{0})
    (hNonat : HarmonicBalls.S11n.MeasureDecoder.LQGMeasureNonatomicAll.{0})
    (hFull : LQGMeasureFullSupportStmt.{0})
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{0})
    (hWeylAe : LQGInternalMetricWeylAeMeasurableFrozen.{0})
    (hmass : LQGMassFunctionalMeasurableFrozen.{0})
    (hCMAbs : CameronMartinGFFMutualAbsCont.{0})
    (hCMRew : HarmonicBalls.S11aj.CameronMartinGFFReweighting.{0})
    (hCompW : WeylScalingCompositionFrozen.{0})
    (hDsm : SmallMetricDiameterLargeMassStmt.{0})
    (hMf : LQGMassInnerMeasurableFrozen.{0})
    (hDiam : LQGInternalDiamInnerMeasurableFrozen.{0})
    (hMk : DomainMarkovConditionalPositiveFrozen.{0})
    (hS : BundleParts.PinchSecondAnnulusStep.{0})
    (hK : ∀ (γ : ℝ) (c₁ c₂ : ℂ) (r₁ r₂ : ℝ), LocalMeasureKernelStmt.{0} γ c₁ c₂ r₁ r₂)
    (hRootFr : RootedPhysicalMetricContinuousAtInsertionFrozen.{0})
    (hPos : LQGMeasureSquarePositiveFrozen.{0})
    (hA10 : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), DMSLemmaA10WholePlaneMarkedSub P γ hC hcirc μ)
    (hBirk : BirkhoffPointwiseErgodic.{0})
    (hProf : LQGMeasureOfProfileMeasurableFrozen.{0})
    (hWCont : WeylMetricCompositionContinuousOuterFrozen)
    (hCCα : HarmonicBalls.FirstPassS11iStep8PhysReduction.CoordChangeAlpha0Stmt.{0})
    (hνex : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hCanonM : LQGCanonicalDecodersMeasurableExistStmt.{0})
    (hExists : WholePlaneGFFExistsFrozen.{0}) :
    Step8EventCalibrationWithCertificate := by
  intro U V W T Q' Q δ M γ hgeo hγ0 hγ2 hM _
  have hξ : 0 < lqgXi γ := div_pos hγ0 (HarmonicBalls.lqgGraphDimension_pos γ)
  have hαQ : γ < lqgQ γ := lt_lqgQ_of_mem_Ioo hγ0 hγ2
  have hΩ : insert (0 : ℂ) (sphere (0 : ℂ) 5) ⊆ pinchOmegaGeom W Q δ :=
    FirstPassS11ap.zero_union_sphere_subset_pinchOmegaGeom hgeo
  obtain ⟨E, hPG, hEq⟩ := pinchLocalCertificate_canonical_of_inputs hAx hLen hN2 hBase hμW hLoc hNonat hFull hgrowth hWeylAe
    hmass hCMAbs hCMRew hCompW hDsm hMf hDiam hMk hS U V W T Q' Q δ hgeo hΩ γ M hγ0 hγ2 hM
  obtain ⟨D⟩ := canonDecoderData_of_frozen (ξ := lqgXi γ) (α₀ := γ) hCanonM hγ0 hγ2 hαQ
  have hEm : MeasurableSet E := by
    unfold PinchEventGammaCanonicalStmt PinchEventGammaStmt at hPG
    exact hPG.1
  have hR : ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ, LocalMetricReplacementStmt.{0} γ (lqgXi γ) c₁ c₂ r₁ r₂ :=
    fun c₁ c₂ r₁ r₂ => hN2 γ (lqgXi γ) hγ0 hγ2 hξ c₁ c₂ r₁ r₂
  have hNon : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ 0 hC hcirc :=
    fun Ω _ P hC hcirc => hNonat γ 0 Ω P hC hcirc
  have hUax : LQGMetricSatisfiesAxiomsUnivFrozen.{0} := lqgMetricSatisfiesAxiomsUnivFrozen_zero
  have hXi : LQGMetricExponentPositive := lqgMetricExponentPositive_derived hExists
  have hCCU : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (z : ℂ),
      LQGMeasureCoordChange P γ γ (HarmonicBalls.S11c.translatedPairing hC hcirc z)
        (HarmonicBalls.S11c.translatedCircle hcirc z) :=
    fun Ω _ P hC hcirc z => hCCα γ γ Ω P (HarmonicBalls.S11c.translatedPairing hC hcirc z)
      (HarmonicBalls.S11c.translatedCircle hcirc z)
  have hνexU : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ γ hC hcirc :=
    fun Ω _ P hC hcirc => hνex Ω P γ γ hC hcirc
  have hHref := hHref_of_global hγ0 hγ2 hgeo (hK γ) hR hRootFr hPos hCMAbs hBirk hProf hLen hAx hRootFr hUax hXi hWCont
    D hEm hνexU hEq hCCU (fun Ω _ P hC hcirc μ => hA10 Ω P γ hC hcirc μ)
  refine ⟨E, E, hPG, (fun q hq => hq), ?_, hEq⟩
  exact insertionZeroUnit_of_href hγ0 hγ2 hgeo (hK γ) hR hRootFr hPos hNon
    (fun Ω _ P hC hcirc μ => hA10 Ω P γ hC hcirc μ) hHref


private theorem step8EventCalibrationWithCertificate_zero_of_decoders
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementStmt.{0} γ ξ c₁ c₂ r₁ r₂)
    (hCanonM : LQGCanonicalDecodersMeasurableExistStmt.{0}) :
    Step8EventCalibrationWithCertificate := by
  have hS : BundleParts.PinchSecondAnnulusStep.{0} :=
    HarmonicBalls.PinchSecondAnnulusS11t.pinchSecondAnnulusStep_of_N2_inputs lqgMassInnerMeasurable_derived'
      greenPotentialHolderStmt_holds
      (fun γ Ω _ P hC hcirc => lqgMeasureExistence_forall_exponents γ 0 Ω P hC hcirc)
      (fun γ Ω _ P hC hcirc => Section6.lqgMeasureWeylScaling Ω P γ 0 hC hcirc)
      (fun γ Ω _ P hC hcirc => lqgMeasureNonatomicAll_holds γ 0 Ω P hC hcirc)
      (fun γ α₀ Ω _ P hC hcirc => lqgMeasureNonatomicAll_holds γ α₀ Ω P hC hcirc)
  have hBase : S11ak.LQGMetricBaseComparisonStmt.{0} :=
    S11ak.lqgMetricBaseComparison_of_canonical
      (FirstPassS11iFinal11_13.lqgCanonicalDecodersExist_of_measurable hCanonM) lqgMetricLengthUniv_derived
      (fun γ Ω _ P hC hcirc => lqgMeasureExistence_forall_field Ω P γ 0 hC hcirc)
  exact step8EventCalibrationWithCertificate lqgMetricFieldAxiomsUnivFrozen_derived
    lqgMetricLengthUniv_derived hN2 hBase
    (fun Ω _ P γ α₀ hC hcirc => Section6.lqgMeasureWeylScaling Ω P γ α₀ hC hcirc)
    LocalDecoderCommon.localLQGDecoderCommonFrozen_derived lqgMeasureNonatomicAll_holds
    lqgMeasureFullSupportStmt_holds lqgVolumeGrowthAllScalesStmt_holds lqgInternalMetricWeylAeMeasurableFrozen_derived
    MassFunctionalDerived.lqgMassFunctionalMeasurable_derived DerivedInputs9.cameronMartinGFFMutualAbsCont_derived
    S11aj.cameronMartinGFFReweighting_derived weylScalingCompositionFrozen_holds firstPass_11_9_derived
    lqgMassInnerMeasurable_derived'
    (lqgInternalDiamInnerMeasurable_derived fun γ ξ α₀ Ω _ P hC hcirc =>
      lqgMetricFieldAxiomsUnivFrozen_derived Ω P γ ξ α₀ hC hcirc)
    domainMarkovConditionalPositive_holds hS LocalDecoderCommon.localMeasureKernelStmt_derived
    rootedPhysicalMetricContinuousAtInsertion_derived lqgMeasureSquarePositiveFrozen_holds
    (fun Ω _ P γ hC hcirc μ => dmsLemmaA10WholePlaneMarkedSub_holds P γ hC hcirc μ)
    birkhoffPointwiseErgodic_derived lqgMeasureOfProfileMeasurable_derived
    weylMetricCompositionContinuousOuter_derived coordChangeAlpha0Stmt_holds lqgMeasureExistence_forall_field
    hCanonM wholePlaneGFFExistsFrozen_derived'

/-- A calibrated event and its probability work for all insertion parameters on sample spaces in `Type`. -/
theorem step8_uniform_insertion_canonical_zero
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

/-- The uniform canonical event is the physical scale-one certificate. -/
theorem step8_uniform_insertion_certificate_canonical_zero
    (U V W T Q' Q : Set ℂ) (δ : ℝ) (hgeom : IsBufferedPinchGeometry U V W T Q' Q δ)
    (γ M : ℝ) (hγ0 : 0 < γ) (hγ2 : γ < 2) (hM : 0 < M) :
    ∃ E : Set Step8Code, ∃ q : ℝ,
      PinchEventGammaCanonicalStmt.{0} U T Q' Q γ M E ∧ CommonProb.{0} γ E q ∧
      (∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
        (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ),
        IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ γ hcirc μ →
        IsLQGMetricOfField P γ (lqgXi γ) γ hC D →
        ∀ᵐ ω ∂P, (localModConstField γ hC (ball (0 : ℂ) 7) ω ∈ E ↔
          CertificateEvent (μ ω) (D ω) (pinchOmegaGeom W Q δ) U V W T Q' Q δ M 1 0)) ∧
      ∀ α : ℝ, α < lqgQ γ → ∀ k : ℕ,
        AllModelsAt.{0} γ (lqgXi γ) α q U V W T Q' Q δ M k := by
  have hN2 := localMetricReplacement_zero_derived
  have hCanonM := lqgCanonicalDecodersMeasurableExist_of_xi_derived xi_eq_xiGamma_derived
  have hPE := step8PinchEventCanonical_zero_of_decoders hN2 hCanonM
  have hCal := step8EventCalibrationWithCertificate_zero_of_decoders hN2 hCanonM
  obtain ⟨E, F, hPG, hcal, hU, hEq⟩ :=
    hCal U V W T Q' Q δ M γ hgeom hγ0 hγ2 hM (hPE U V W T Q' Q δ hgeom γ M hγ0 hγ2 hM)
  obtain ⟨q, hq⟩ := exists_localModConstField_prob γ hPG.1
  refine ⟨E, q, hPG, hq, hEq, ?_⟩
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
theorem step8_uniform_identity_canonical_zero
    (U V W T Q' Q : Set ℂ) (δ : ℝ) (hgeom : IsBufferedPinchGeometry U V W T Q' Q δ)
    (γ M : ℝ) (hγ0 : 0 < γ) (hγ2 : γ < 2) (hM : 0 < M) :
    ∃ E : Set Step8Code, ∃ q : ℝ,
      PinchEventGammaCanonicalStmt.{0} U T Q' Q γ M E ∧ CommonProb.{0} γ E q ∧
      ∀ α : ℝ, α < lqgQ γ → Step8IdentityCanonicalStmt.{0} γ α U V W T Q' Q δ M E := by
  obtain ⟨E, q, hPG, hq, hall⟩ := step8_uniform_insertion_canonical_zero U V W T Q' Q δ hgeom γ M hγ0 hγ2 hM
  refine ⟨E, q, hPG, hq, fun α hα => ⟨q, ?_, ?_⟩⟩
  · intro Ω _ P hC hcirc μ D hG _ _
    exact hq Ω P hC hcirc hG
  · intro Ω _ P hC hcirc μ D hG hμ hD
    exact FirstPassS11iStep8Zoom.step8_zoom_family_of_ae_frequency P U V W T Q' Q δ M q μ D
      (fun k => hall α hα k Ω P hC hcirc μ D hG hμ hD)

/-- The physical frequency holds with one event and probability for all insertions and sample spaces. -/
theorem step8_uniform_insertion
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
    obtain ⟨E, q, hPG, hq, hall⟩ := step8_uniform_insertion_canonical_zero U V W T Q' Q δ hgeom γ M hγ0 hγ2 hM
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

/-- The common event is the physical scale-one certificate and gives all insertion frequencies. -/
theorem step8_uniform_insertion_certificate
    (U V W T Q' Q : Set ℂ) (δ : ℝ) (hgeom : IsBufferedPinchGeometry U V W T Q' Q δ)
    (γ ξ M : ℝ) (hγ0 : 0 < γ) (hγ2 : γ < 2) (hM : 0 < M) :
    ∃ E : Set Step8Code, ∃ q : ℝ,
      PinchEventGammaStmt.{u} U T Q' Q γ ξ M E ∧
      (∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
        (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ),
        IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ γ hcirc μ →
        IsLQGMetricOfField P γ ξ γ hC D →
        (P {ω | localModConstField γ hC (ball (0 : ℂ) 7) ω ∈ E}).toReal = q) ∧
      (∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
        (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ),
        IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ γ hcirc μ →
        IsLQGMetricOfField P γ ξ γ hC D →
        ∀ᵐ ω ∂P, (localModConstField γ hC (ball (0 : ℂ) 7) ω ∈ E ↔
          CertificateEvent (μ ω) (D ω) (pinchOmegaGeom W Q δ) U V W T Q' Q δ M 1 0)) ∧
      ∀ α : ℝ, α < lqgQ γ → ∀ k : ℕ, AllModelsAt.{u} γ ξ α q U V W T Q' Q δ M k := by
  by_cases hcan : ξ = lqgXi γ
  · subst ξ
    obtain ⟨E, q, hPG, hq, hEq, hall⟩ := step8_uniform_insertion_certificate_canonical_zero U V W T Q' Q δ hgeom γ M hγ0 hγ2 hM
    refine ⟨E, q, ⟨hPG.1, ?_⟩, ?_, ?_, ?_⟩
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
    · intro Ω _ P hC hcirc μ D hG hμ hD
      have hG' := isWholePlaneGFF_modelRangeMeasure (P := P) μ D hG
      have hμ' : IsLQGMeasureOfField (modelRangeMeasure P (modelPoint hC hcirc μ D)) γ γ
          (fun y => y.1.circle) (fun y => y.1.measure) := by
        unfold IsLQGMeasureOfField IsLQGMeasure at hμ ⊢
        exact ae_modelRangeMeasure_iff.2 hμ
      obtain ⟨𝔇, h𝔇, hDae⟩ := hD
      have hD' : IsLQGMetricOfField (modelRangeMeasure P (modelPoint hC hcirc μ D)) γ (lqgXi γ) γ
          (fun y => y.1.pairing) (fun y => y.1.metric) := ⟨𝔇, h𝔇, ae_modelRangeMeasure_iff.2 hDae⟩
      exact ae_modelRangeMeasure_iff.1 (hEq _ _ _ _ _ _ hG' hμ' hD')
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
    refine ⟨univ, 0, ⟨MeasurableSet.univ, ?_⟩, ?_, ?_, ?_⟩
    · intro Ω _ P hC _ _ D _ _ hD
      exact (hno P γ hC D hD).elim
    · intro Ω _ P hC _ _ D _ _ hD
      exact (hno P γ hC D hD).elim
    · intro Ω _ P hC _ _ D _ _ hD
      exact (hno P γ hC D hD).elim
    · intro α _ k Ω _ P hC _ _ D _ _ hD
      exact (hno P α hC D hD).elim


/-- A common event witnesses the Step 8 identity for every admissible insertion. -/
theorem step8_uniform_identity
    (U V W T Q' Q : Set ℂ) (δ : ℝ) (hgeom : IsBufferedPinchGeometry U V W T Q' Q δ)
    (γ ξ M : ℝ) (hγ0 : 0 < γ) (hγ2 : γ < 2) (hM : 0 < M) :
    ∃ E : Set Step8Code, PinchEventGammaStmt.{u} U T Q' Q γ ξ M E ∧
      ∀ α : ℝ, α < lqgQ γ → Step8IdentityStmt.{u} γ ξ α U V W T Q' Q δ M E := by
  obtain ⟨E, q, hPG, hq, hall⟩ := step8_uniform_insertion U V W T Q' Q δ hgeom γ ξ M hγ0 hγ2 hM
  refine ⟨E, hPG, fun α hα => ⟨q, hq, ?_⟩⟩
  intro Ω _ P hC hcirc μ D hG hμ hD
  exact FirstPassS11iStep8Zoom.step8_zoom_family_of_ae_frequency P U V W T Q' Q δ M q μ D
    (fun k => hall α hα k Ω P hC hcirc μ D hG hμ hD)

end HarmonicBalls
