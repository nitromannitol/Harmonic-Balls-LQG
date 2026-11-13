import HarmonicBalls.FirstPass.Phase2.ForallXiCanonicalReduction
import HarmonicBalls.FirstPass.Phase2.Step8WholePlaneFromSeed
import HarmonicBalls.FirstPass.S11i.Step8CalibrationClose
import HarmonicBalls.FirstPass.Phase2.DerivedInputs37
import HarmonicBalls.FirstPass.Phase2.Step8IdentityUniv
import HarmonicBalls.FirstPass.S11ak.BaseComparison
import HarmonicBalls.FirstPass.Phase2.CampbellMarkedExt
import HarmonicBalls.FirstPass.Phase2.CoordChangeHolds
import HarmonicBalls.FirstPass.S8c.BirkhoffDerived
import HarmonicBalls.FirstPass.Phase2.ProfileDecoderDerived
import HarmonicBalls.FirstPass.Phase2.WeylCompositionOuterDerived
import HarmonicBalls.FirstPass.Phase2.RootedInsertionContinuityDerived
import HarmonicBalls.FirstPass.Phase2.GFFExistsDerived2
import HarmonicBalls.FirstPass.Phase2.BallMassBoundsHolds
import HarmonicBalls.FirstPass.Phase2.FieldAxiomsConsequencesDerived
import HarmonicBalls.FirstPass.Phase2.LocalDecoderCommonDerived
import HarmonicBalls.FirstPass.Closure.C1112Clean
import HarmonicBalls.FirstPass.Phase2.Step8PerModelUniv

/-!
# The canonical Step 8 identification on sample spaces in `Type`, from the local metric replacement and the decoders

`Step8IdentificationCanonicalStmt` (`S11i/Corrected11_13.lean:91`) splits into the Lemma 11.12 event at the canonical
exponent (part (c), `Step8PinchEventCanonicalStmt`) and the Step 8 identity (part (d),
`Step8IdentityGivenPinchEventCanonicalStmt`), `step8Identification_canonical_of_split`. On sample spaces in `Type`:

* part (c) is `pinchEventGamma_exists` applied to the corrected Lemma 11.12, which is `closure_11_12_clean_derivedInputs37`
  (`Phase2/DerivedInputs37.lean:75`) with every binder supplied by its derived theorem, except the local metric
  replacement `hN2` and the canonical decoders (from `hCanonM` by `lqgCanonicalDecodersExist_of_measurable`);
* part (d) is `step8Identity_given_pinchEvent_canonical_of_calibration_fieldAxioms_univ` (`Phase2/Step8IdentityUniv.lean:514`)
  applied to the event calibration `step8EventCalibration` (`S11i/Step8CalibrationClose.lean:36`), again with every binder
  supplied by its derived theorem except `hN2` and `hCanonM`. The base comparison of two γ-LQG metrics of the same Weyl
  exponent (the uniqueness of the LQG metric up to a constant, Gwynne-Miller, Theorem 1.2) is
  `lqgMetricBaseComparison_of_canonical` from the canonical decoders.

So the canonical Step 8 identification holds on sample spaces in `Type` from `hN2` and `hCanonM` alone, and with the Weyl
exponent identification (`hXi`, `hDim` of `ForallXiCanonicalReduction.lean`) so does Lemma 11.13 (corrected) for every
`ξ`. Its density is chosen before the model, so it passes to sample spaces in every universe through the range of the
sample point (`correctedLemma11_13Stmt_univ_of_zero`), and Proposition 11.11 and Theorem 1.2 for every `ξ` follow at every
universe. The statements of the draft are unchanged.
-/

universe u

namespace HarmonicBalls

open MeasureTheory
open FirstPassS11i HarmonicBalls.FirstPassS11iStep8PhysExists

/-- **Part (c) of the canonical Step 8 identification on sample spaces in `Type`**: the Lemma 11.12 event at the
canonical exponent, from the closed corrected Lemma 11.12 with its derived binders. Inputs: the local metric replacement
`hN2` and the measurable canonical decoders `hCanonM`. -/
theorem step8PinchEventCanonical_zero_of_decoders
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementStmt.{0} γ ξ c₁ c₂ r₁ r₂)
    (hCanonM : LQGCanonicalDecodersMeasurableExistStmt.{0}) :
    Step8PinchEventCanonicalStmt.{0} := by
  have h12 : CorrectedLemma11_12Stmt.{0} :=
    Closure.correctedLemma11_12_of_clean
      (Closure.closure_11_12_clean_derivedInputs37 lqgMetricFieldAxiomsUnivFrozen_derived hN2
        (FirstPassS11iFinal11_13.lqgCanonicalDecodersExist_of_measurable hCanonM)
        wholePlaneGFFExistsFrozen_derived' wholePlaneLQGBallMassBounds_holds
        (fun Ω _ P γ hC hcirc => coordChangeAlpha0Stmt_holds γ 0 Ω P hC hcirc)
        lqgMeasureExistence_forall_field lqgInternalMetricWeylAeMeasurableFrozen_derived
        lqgMetricFieldAxioms_forall_derived domainMarkovConditionalPositive_holds greenPotentialHolderStmt_holds
        lqgMetricContinuousShiftFactI_derived dyadicCellDiamSmallFrozen_derived
        cameronMartinEventTransferFrozen_derived lqgMetricSupMeasurableFrozen_derived
        connectedSquareUnionDiamFiniteFrozen_derived)
  intro U V W T Q' Q δ₀ hgeo γ M hγ0 hγ2 hM
  exact pinchEventGamma_exists (ξ := lqgXi γ) h12 hgeo hγ0 hγ2 hM

/-- **The Step 8 event calibration on sample spaces in `Type`** (`Step8EventCalibrationStmt.{0}`), from
`step8EventCalibration` with every binder supplied by its derived theorem, except the local metric replacement `hN2` and
the measurable canonical decoders `hCanonM`; the base comparison of two γ-LQG metrics is
`lqgMetricBaseComparison_of_canonical` from the canonical decoders. -/
theorem step8EventCalibration_zero_of_decoders
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementStmt.{0} γ ξ c₁ c₂ r₁ r₂)
    (hCanonM : LQGCanonicalDecodersMeasurableExistStmt.{0}) :
    Step8EventCalibrationStmt.{0} := by
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
  exact S11i.Step8CalibrationClose.step8EventCalibration lqgMetricFieldAxiomsUnivFrozen_derived
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

/-- **The canonical Step 8 identification on sample spaces in `Type`** (`Step8IdentificationCanonicalStmt.{0}`), from
the local metric replacement `hN2` and the measurable canonical decoders `hCanonM`: part (c) is
`step8PinchEventCanonical_zero_of_decoders`, part (d) is the Step 8 identity from the event calibration
`step8EventCalibration_zero_of_decoders` and the field axioms. -/
theorem step8IdentificationCanonical_zero_of_decoders
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementStmt.{0} γ ξ c₁ c₂ r₁ r₂)
    (hCanonM : LQGCanonicalDecodersMeasurableExistStmt.{0}) :
    Step8IdentificationCanonicalStmt.{0} :=
  step8Identification_canonical_of_split (step8PinchEventCanonical_zero_of_decoders hN2 hCanonM)
    (step8Identity_given_pinchEvent_canonical_of_calibration_fieldAxioms_univ
      (step8EventCalibration_zero_of_decoders hN2 hCanonM) lqgMetricFieldAxiomsUnivFrozen_derived)

/-- **Lemma 11.13 (corrected, every `ξ`) on sample spaces in `Type`**, from the local metric replacement `hN2`, the
measurable canonical decoders `hCanonM`, the Weyl exponent of every γ-LQG metric `hXi` and the identification `hDim` of
the paper's canonical exponent with Gwynne-Miller's. -/
theorem correctedLemma11_13_zero_of_decoders
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementStmt.{0} γ ξ c₁ c₂ r₁ r₂)
    (hCanonM : LQGCanonicalDecodersMeasurableExistStmt.{0})
    (hXi : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → ∀ 𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ, IsLQGMetric γ ξ 𝔇 →
      ξ = LQGMetric.xiGamma γ)
    (hDim : ∀ γ : ℝ, 0 < γ → γ < 2 → lqgXi γ = LQGMetric.xiGamma γ) :
    CorrectedLemma11_13Stmt.{0} :=
  correctedLemma11_13_of_canonicalStep8 hXi hDim (step8IdentificationCanonical_zero_of_decoders hN2 hCanonM)

open Step8PerModelUniv in
/-- **Lemma 11.13 (corrected) at every universe from sample spaces in `Type`.** The density `δ` of
`CorrectedLemma11_13Stmt` is chosen before the model, so the one given on sample spaces in `Type` serves on `Ω : Type u`:
the model is represented on the range of its sample point `(h^ℂ, h_·(·), μ, D)` (`Step8PerModelUniv.ModelRange`, a type in
`Type`), where the whole-plane GFF, the LQG measure and the LQG metric clauses hold, and the almost sure conclusion on the
range is an almost sure conclusion on `Ω` (`ae_modelRangeMeasure_iff`). -/
theorem correctedLemma11_13Stmt_univ_of_zero (h0 : CorrectedLemma11_13Stmt.{0}) : CorrectedLemma11_13Stmt.{u} := by
  intro U V W T Q' Q δ₀ hgeom γ α₀ ξ hγ0 hγ2 hα M hM
  obtain ⟨δ, hδ, hall⟩ := h0 U V W T Q' Q δ₀ hgeom γ α₀ ξ hγ0 hγ2 hα M hM
  refine ⟨δ, hδ, ?_⟩
  intro Ω _ P hC hcirc μ D hG hμ hD
  have hG' := isWholePlaneGFF_modelRangeMeasure (P := P) μ D hG
  have hμ' : IsLQGMeasureOfField (modelRangeMeasure P (modelPoint hC hcirc μ D)) γ α₀ (fun y => y.1.circle)
      (fun y => y.1.measure) := by
    unfold IsLQGMeasureOfField IsLQGMeasure at hμ ⊢
    exact ae_modelRangeMeasure_iff.2 hμ
  obtain ⟨𝔇, h𝔇, hDae⟩ := hD
  have hD' : IsLQGMetricOfField (modelRangeMeasure P (modelPoint hC hcirc μ D)) γ ξ α₀
      (fun y => y.1.pairing) (fun y => y.1.metric) :=
    ⟨𝔇, h𝔇, ae_modelRangeMeasure_iff.2 hDae⟩
  exact ae_modelRangeMeasure_iff.1
    (hall (ModelRange P (modelPoint hC hcirc μ D)) (modelRangeMeasure P (modelPoint hC hcirc μ D)) _ _ _ _ hG' hμ' hD')

/-- **Lemma 11.13 (corrected, every `ξ`, every universe)** from the local metric replacement `hN2`, the measurable
canonical decoders `hCanonM`, the Weyl exponent of every γ-LQG metric `hXi` and the identification `hDim` of the paper's
canonical exponent with Gwynne-Miller's. -/
theorem correctedLemma11_13_of_decoders
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementStmt.{0} γ ξ c₁ c₂ r₁ r₂)
    (hCanonM : LQGCanonicalDecodersMeasurableExistStmt.{0})
    (hXi : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → ∀ 𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ, IsLQGMetric γ ξ 𝔇 →
      ξ = LQGMetric.xiGamma γ)
    (hDim : ∀ γ : ℝ, 0 < γ → γ < 2 → lqgXi γ = LQGMetric.xiGamma γ) :
    CorrectedLemma11_13Stmt.{u} :=
  correctedLemma11_13Stmt_univ_of_zero (correctedLemma11_13_zero_of_decoders hN2 hCanonM hXi hDim)

/-- **Proposition 11.11 (every `ξ`, every universe)** from `hN2`, `hCanonM`, `hXi` and `hDim`, through the corrected and
the printed Lemma 11.13. -/
theorem firstPass_11_11_of_decoders
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementStmt.{0} γ ξ c₁ c₂ r₁ r₂)
    (hCanonM : LQGCanonicalDecodersMeasurableExistStmt.{0})
    (hXi : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → ∀ 𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ, IsLQGMetric γ ξ 𝔇 →
      ξ = LQGMetric.xiGamma γ)
    (hDim : ∀ γ : ℝ, 0 < γ → γ < 2 → lqgXi γ = LQGMetric.xiGamma γ) :
    HarmonicBallNotMetricBallStmt.{u} :=
  firstPass_11_11_derived (Closure.manyPinchScales_of_corrected (correctedLemma11_13_of_decoders hN2 hCanonM hXi hDim))

/-- **Theorem 1.2 (every `ξ`, every universe)** from `hN2`, `hCanonM`, `hXi` and `hDim`, through Proposition 11.11. -/
theorem firstPass_1_2_of_decoders
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementStmt.{0} γ ξ c₁ c₂ r₁ r₂)
    (hCanonM : LQGCanonicalDecodersMeasurableExistStmt.{0})
    (hXi : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → ∀ 𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ, IsLQGMetric γ ξ 𝔇 →
      ξ = LQGMetric.xiGamma γ)
    (hDim : ∀ γ : ℝ, 0 < γ → γ < 2 → lqgXi γ = LQGMetric.xiGamma γ) :
    HarmonicBallNoveltyStmt.{u} :=
  firstPass_1_2_derivedInputs47 (firstPass_11_11_of_decoders hN2 hCanonM hXi hDim)

end HarmonicBalls
