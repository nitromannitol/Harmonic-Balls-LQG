import HarmonicBalls.FirstPass.S11i.Step8CalibrationCanonical
import HarmonicBalls.FirstPass.S11i.InsertionZeroUnitE
import HarmonicBalls.FirstPass.S11r.RootedHrefGlobal
import HarmonicBalls.FirstPass.S11i.Final11_13

/-!
# Step 8 event calibration, closed

`step8EventCalibration` proves `Step8EventCalibrationStmt.{0}` (`S11i/Step8PhysExists.lean:109`), route 2 (c) of Lemma 11.13.
The witness is the calibrated Lemma 11.12 event `E` of `pinchLocalCertificate_canonical_of_inputs`
(`S11i/Step8CalibrationCanonical.lean`): `PinchEventGammaCanonicalStmt E` at insertion `γ` with the almost-sure equivalence to
`CertificateEvent`. The pair is `(E, E)`, so the calibration `EventCalibration γ E E` is the identity. The insertion-zero unit
frequency of `E` is `insertionZeroUnit_of_href` (`S11i/InsertionZeroUnitE.lean:44`), applied to `hHref_of_global`
 (`S11r/RootedHrefGlobal.lean:163`).

The Ω-inclusion `insert 0 (sphere 0 5) ⊆ pinchOmegaGeom W Q δ` is not a hypothesis of `Step8EventCalibrationStmt`. It is derived
from `IsBufferedPinchGeometry` by `FirstPassS11ap.zero_union_sphere_subset_pinchOmegaGeom` (`S11ap.lean:93`).

Binders: the frozen and proposed inputs, named as in `firstPass_11_13` (`S11i/Final11_13.lean:213`). Two facts are proved, not
assumed: `hXi` (`lqgMetricExponentPositive_derived`) and `hUax` (`lqgMetricSatisfiesAxiomsUnivFrozen_zero`), both in
`S11i/Final11_13.lean`. The decoder data `D` comes from `hCanonM` by `canonDecoderData_of_frozen`. The coordinate change
`hCCU` of `hHref_of_global` is `hCCα` at the translated fields. Each literature input is stated for all `γ`, as in
`firstPass_11_13`, and is used only through its guarded definition: `LQGMeasureCoordChange` assumes `IsWholePlaneGFF`,
`0 < γ < 2` and `α₀ < Q(γ)` internally.
-/

namespace HarmonicBalls.S11i.Step8CalibrationClose

open MeasureTheory Set Metric Filter
open HarmonicBalls.FirstPassS11iStep8PhysExists HarmonicBalls.FirstPassS11iInsertionZeroUnitE
open HarmonicBalls.FirstPassS11rRootedHrefGlobal HarmonicBalls.S11i.Step8CalibrationCanonical
open HarmonicBalls.FirstPassS11rFrozenCanonDecoders HarmonicBalls.FirstPassS11iFinal11_13

/-- **Step 8 event calibration (`Step8EventCalibrationStmt.{0}`, route 2 (c)).** Closed from the frozen and proposed inputs listed
as binders, with the witness `E` of `pinchLocalCertificate_canonical_of_inputs`. -/
theorem step8EventCalibration
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
    Step8EventCalibrationStmt.{0} := by
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
  refine ⟨E, E, hPG, fun q hq => hq, ?_⟩
  exact insertionZeroUnit_of_href hγ0 hγ2 hgeo (hK γ) hR hRootFr hPos hNon
    (fun Ω _ P hC hcirc μ => hA10 Ω P γ hC hcirc μ) hHref


end HarmonicBalls.S11i.Step8CalibrationClose
