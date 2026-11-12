import HarmonicBalls.Assembly.ExistenceUniqueness
import HarmonicBalls.Assembly.Novelty
import HarmonicBalls.FirstPass.Canonical.NotMetricBall
import HarmonicBalls.FirstPass.Canonical.Novelty
import HarmonicBalls.FirstPass.Closure.RetiredInputs
import HarmonicBalls.FirstPass.Phase2.BallMassBoundsHolds
import HarmonicBalls.FirstPass.Phase2.CameronMartinLipschitzShiftHolds
import HarmonicBalls.FirstPass.Phase2.CampbellCountedForms
import HarmonicBalls.FirstPass.Phase2.CampbellDerivedWrappers
import HarmonicBalls.FirstPass.Phase2.CampbellRestrictionHolds
import HarmonicBalls.FirstPass.Phase2.CoordChangeHolds
import HarmonicBalls.FirstPass.Phase2.CoordChangeZeroHolds
import HarmonicBalls.FirstPass.Phase2.DerivedInputs36
import HarmonicBalls.FirstPass.Phase2.DerivedInputs38
import HarmonicBalls.FirstPass.Phase2.DerivedInputs39
import HarmonicBalls.FirstPass.Phase2.DerivedInputs40
import HarmonicBalls.FirstPass.Phase2.DerivedInputs41
import HarmonicBalls.FirstPass.Phase2.DerivedInputs42
import HarmonicBalls.FirstPass.Phase2.DerivedInputs9
import HarmonicBalls.FirstPass.Phase2.LQGMeasureExistenceDerived
import HarmonicBalls.FirstPass.Phase2.WeylLogTruncationDerivedInputs
import HarmonicBalls.FirstPass.Phase2.WeylScalingCompositionDerived
import HarmonicBalls.FirstPass.S11
import HarmonicBalls.FirstPass.S1S10
import HarmonicBalls.Proofs.Sec10.PrevalenceCrossingAssembly
import HarmonicBalls.Proofs.Sec9.ExistenceResultsAssembly
import HarmonicBalls.Proofs.Sec9.LQGExistenceConsequences

/-!
# Derived-input forms, round 43: unused hypotheses removed

Each theorem below has the conclusion of the declaration named in its docstring and a subset of its hypotheses:
the conclusion already follows from that subset by theorems of this repository. The kept hypotheses are
unchanged; the proofs are chains of applications.

Generated from the types of the wrapped declarations; do not edit by hand.
-/

universe u

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

namespace HarmonicBalls

/-- `ExistenceUniquenessHarmonicBallsStmt` with no hypothesis; the hypotheses `h55`, `h56` of `firstPass_1_1` are not used. -/
theorem firstPass_1_1_derivedInputs43 :
    ExistenceUniquenessHarmonicBallsStmt.{u} := by
  have d1 := HarmonicBalls.wholePlaneLQGBallMassBounds_holds.{u}
  have d2 := HarmonicBalls.Closure.closure_5_5_derivedInputsCampbell.{u} (hDG := d1)
  have d3 := HarmonicBalls.Closure.closure_5_6_derivedInputs40.{u} (hDG := d1)
  exact HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5.{u} (h55 := d2) (h56 := d3)

/-- `HarmonicBallNoveltyStmt` from the hypotheses `hjordan`, `hmetric` of `firstPass_1_2` alone:
the hypotheses `h55`, `h56`, `hlip` of that declaration are not used. -/
theorem firstPass_1_2_derivedInputs43
    (hjordan : HarmonicBallComplementBoundaryJordanStmt.{u})
    (hmetric : HarmonicBallNotMetricBallStmt.{u}) :
    HarmonicBallNoveltyStmt.{u} := by
  have d1 := HarmonicBalls.cameronMartinLocallyLipschitzShiftAbsCont_holds.{u}
  have d2 := HarmonicBalls.localCampbellMarkedRestriction_holds.{u}
  have d3 := HarmonicBalls.localRootedFieldMeasureDomination_holds.{u}
  have d4 := HarmonicBalls.lqgMeasureCoordChange_holds.{u}
  have d5 := HarmonicBalls.lqgMeasureExistence_forall_field.{u}
  have d6 := HarmonicBalls.wholePlaneLQGBallMassBounds_holds.{u}
  have d7 := HarmonicBalls.Closure.closure_5_5_derivedInputsCampbell.{u} (hDG := d6)
  have d8 := HarmonicBalls.Closure.closure_5_6_derivedInputs40.{u} (hDG := d6)
  have d9 := HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5.{u} (h55 := d7) (h56 := d8)
  have d10 := HarmonicBalls.Closure.closure_11_2_derivedInputs36.{u} (hDG := d6) (hCC := d4) (hE := d5) (hL1 := d3) (hCamp := d2) (hCM := d1)
  exact HarmonicBalls.harmonicBallNoveltyStmt_of_existence_and_results.{u} (hex := d9) (hjordan := hjordan) (hlip := d10) (hmetric := hmetric)

/-- `TypicalPointManyGoodScalesStmt` with no hypothesis; the hypotheses `hSub`, `hDG` of `firstPass_8_2_S8d_noWeyl_derivedInputs41` are not used. -/
theorem firstPass_8_2_S8d_noWeyl_derivedInputs43 :
    TypicalPointManyGoodScalesStmt.{u} := by
  have d1 := HarmonicBalls.wholePlaneLQGBallMassBounds_holds.{u}
  exact HarmonicBalls.firstPass_8_2_S8d_noWeyl_derivedInputsCampbell.{u} (hDG := d1)

/-- `HarmonicBallBoundarySubsetStmt` with no hypothesis; the hypotheses `hDG` of `firstPass_9_3_derivedInputs41` are not used. -/
theorem firstPass_9_3_derivedInputs43 :
    HarmonicBallBoundarySubsetStmt.{u} := by
  have d1 := HarmonicBalls.wholePlaneLQGBallMassBounds_holds.{u}
  exact HarmonicBalls.firstPass_9_3_derivedInputs40.{u} (hDG := d1)

/-- `RegularOpenEqOfAEEqStmt` with no hypothesis; the hypotheses `hDG` of `firstPass_9_4_derivedInputs41` are not used. -/
theorem firstPass_9_4_derivedInputs43 :
    RegularOpenEqOfAEEqStmt.{u} := by
  have d1 := HarmonicBalls.wholePlaneLQGBallMassBounds_holds.{u}
  exact HarmonicBalls.firstPass_9_4_derivedInputs40.{u} (hDG := d1)

/-- `ClusterBoundedCrossingsStmt` with no hypothesis; the hypotheses `hI2`, `hE0` of `firstPass_10_1` are not used. -/
theorem firstPass_10_1_derivedInputs43 :
    ClusterBoundedCrossingsStmt.{u} := by
  have d1 := HarmonicBalls.lqgMeasureCoordChange_zero_holds.{u}
  have d2 := HarmonicBalls.lqgMeasureExistence_forall_field.{u}
  have d3 := HarmonicBalls.wholePlaneLQGBallMassBounds_holds.{u}
  exact HarmonicBalls.clusterBoundedCrossings_of_three_staged_inputs.{u} (hDG := d3) (hCC := d1) (hE := d2)

/-- `ComplementComponentBoundarySimpleLoopStmt` from the hypotheses `hTor` of `firstPass_10_6` alone:
the hypotheses `h10`, `h32` of that declaration are not used. -/
theorem firstPass_10_6_derivedInputs43
    (hTor : TorhorstSimpleLoopFrozen) :
    ComplementComponentBoundarySimpleLoopStmt.{u} := by
  have d1 := HarmonicBalls.lqgMeasureCoordChange_zero_holds.{u}
  have d2 := HarmonicBalls.lqgMeasureExistence_forall_field.{u}
  have d3 := HarmonicBalls.wholePlaneLQGBallMassBounds_holds.{u}
  have d4 := HarmonicBalls.Closure.closure_3_2_derivedInputs40.{u} (hDG := d3)
  have d5 := HarmonicBalls.clusterBoundedCrossings_of_three_staged_inputs.{u} (hDG := d3) (hCC := d1) (hE := d2)
  exact HarmonicBalls.firstPass_10_6.{u} (h10 := d5) (h32 := d4) (hTor := hTor)

/-- `HarmonicBallNotLipschitzStmt` with no hypothesis; the hypotheses `h5` of `firstPass_11_2` are not used. -/
theorem firstPass_11_2_derivedInputs43 :
    HarmonicBallNotLipschitzStmt.{u} := by
  have d1 := HarmonicBalls.cameronMartinLocallyLipschitzShiftAbsCont_holds.{u}
  have d2 := HarmonicBalls.localCampbellMarkedRestriction_holds.{u}
  have d3 := HarmonicBalls.localRootedFieldMeasureDomination_holds.{u}
  have d4 := HarmonicBalls.lqgMeasureCoordChange_holds.{u}
  have d5 := HarmonicBalls.lqgMeasureExistence_forall_field.{u}
  have d6 := HarmonicBalls.wholePlaneLQGBallMassBounds_holds.{u}
  exact HarmonicBalls.Closure.closure_11_2_derivedInputs36.{u} (hDG := d6) (hCC := d4) (hE := d5) (hL1 := d3) (hCamp := d2) (hCM := d1)

/-- `NoConeConditionStmt` with no hypothesis; the hypotheses `h6`, `h7`, `hI2` of `firstPass_11_5` are not used. -/
theorem firstPass_11_5_derivedInputs43 :
    NoConeConditionStmt.{u} := by
  have d1 := HarmonicBalls.cameronMartinLocallyLipschitzShiftAbsCont_holds.{u}
  have d2 := HarmonicBalls.localCampbellMarkedRestriction_holds.{u}
  have d3 := HarmonicBalls.localRootedFieldMeasureDomination_holds.{u}
  have d4 := HarmonicBalls.lqgMeasureCoordChange_holds.{u}
  have d5 := HarmonicBalls.lqgMeasureExistence_forall_field.{u}
  have d6 := HarmonicBalls.wholePlaneLQGBallMassBounds_holds.{u}
  exact HarmonicBalls.Closure.closure_11_5_derivedInputs36.{u} (hDG := d6) (hCC := d4) (hE := d5) (hL1 := d3) (hCamp := d2) (hCM := d1)

/-- `ManyConeBadScalesStmt` from the hypotheses `hFreq`, `hTr` of `firstPass_11_7_derivedInputs39` alone:
the hypothesis `h8` of that declaration is not used. -/
theorem firstPass_11_7_derivedInputs43
    (hFreq : OriginRootedConeFrequencyFrozen.{u})
    (hTr : RootedConeFrequencyTransferFrozen.{u}) :
    ManyConeBadScalesStmt.{u} := by
  have d1 := HarmonicBalls.wholePlaneLQGBallMassBounds_holds.{u}
  have d2 := HarmonicBalls.Closure.closure_11_8_derivedInputs40.{u} (hDG := d1)
  exact HarmonicBalls.firstPass_11_7_derivedInputs39.{u} (h8 := d2) (hFreq := hFreq) (hTr := hTr)

/-- `HarmonicBallNotMetricBallStmt` from the hypotheses `h13`, `hmetricAxioms` of `firstPass_11_11` alone:
the hypotheses `h6`, `hI2` of that declaration are not used. -/
theorem firstPass_11_11_derivedInputs43
    (h13 : ManyPinchScalesStmt.{u})
    (hmetricAxioms : ∀ (γ α₀ ξ : ℝ), LT.lt.{0} 0 γ → LT.lt.{0} γ 2 → LT.lt.{0} α₀ (lqgQ γ) → ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF.{u} P hC hcirc → LQGMetricFieldAxioms.{u} P γ ξ α₀ hC hcirc) :
    HarmonicBallNotMetricBallStmt.{u} := by
  have d1 := HarmonicBalls.lqgMeasureCoordChange_zero_holds.{u}
  have d2 := HarmonicBalls.lqgMeasureExistence_forall_field.{u}
  have d3 := HarmonicBalls.wholePlaneLQGBallMassBounds_holds.{u}
  have d4 := HarmonicBalls.Closure.closure_11_6_derivedInputsCampbell.{u} (hDG := d3)
  have d5 := HarmonicBalls.lqgVolumeGrowthAllScalesStmt_of_existence.{u} (hDG := d3) (hCC := d1) (hE := d2)
  exact HarmonicBalls.firstPass_11_11.{u} (h6 := d4) (h13 := h13) (hI2 := d5) (hmetricAxioms := hmetricAxioms)

/-- `LiouvilleVolumeGrowthStmt` with no hypothesis; the hypotheses `h` of `liouvilleVolumeGrowthStmt_of_ballMass` are not used. -/
theorem liouvilleVolumeGrowthStmt_of_ballMass_derivedInputs43 :
    LiouvilleVolumeGrowthStmt.{u} := by
  have d1 := HarmonicBalls.lqgMeasureCoordChange_zero_holds.{u}
  have d2 := HarmonicBalls.lqgMeasureExistence_forall_field.{u}
  have d3 := HarmonicBalls.wholePlaneLQGBallMassBounds_holds.{u}
  exact HarmonicBalls.liouvilleVolumeGrowthStmt_of_existence.{u} (hDG := d3) (hCC := d1) (hE := d2)

/-- `SubharmonicBallUniquenessWeakStmt` with no hypothesis; the hypotheses `hDG`, `hCC`, `hW`, `hE`, `hN`, `h82` of `firstPass_9_2_corrected` are not used. -/
theorem firstPass_9_2_corrected_derivedInputs43 :
    SubharmonicBallUniquenessWeakStmt.{u} := by
  have d1 := HarmonicBalls.wholePlaneLQGBallMassBounds_holds.{u}
  have d2 := HarmonicBalls.firstPass_8_2_S8d_noWeyl_derivedInputsCampbell.{u} (hDG := d1)
  exact HarmonicBalls.firstPass_9_2_corrected_derivedInputs40.{u} (hDG := d1) (h82 := d2)

/-- `PinchSecondEventFaithfulStmt` from the hypotheses `hAx`, `hholder`, `hNa0`, `hNa`, `hD` of `firstPass_11_16_corrected_derivedInputs39` alone:
the hypothesis `hPos` of that declaration is not used. -/
theorem firstPass_11_16_corrected_derivedInputs43
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hholder : GreenPotentialHolderStmt.{u})
    (hNa0 : ∀ (γ : ℝ) (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic.{u} P γ 0 hC hcirc)
    (hNa : ∀ (γ α₀ : ℝ) (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic.{u} P γ α₀ hC hcirc)
    (hD : SmallMetricDiameterLargeMassStmt.{u}) :
    PinchSecondEventFaithfulStmt.{u} := by
  have d1 := HarmonicBalls.DerivedInputs9.cameronMartinGFFMutualAbsCont_derived.{u}
  have d2 := HarmonicBalls.weylScalingCompositionFrozen_holds.{u}
  have d3 := HarmonicBalls.lqgInternalMetricWeylAeMeasurable_of_fieldAxioms.{u} (hAx := hAx)
  have d4 := HarmonicBalls.Closure.closure_11_15_derived.{u} (hCM := d1) (hMet := d3) (hWSC := d2) (hAx := hAx)
  exact HarmonicBalls.firstPass_11_16_corrected_derivedInputs39.{u} (hAx := hAx) (hholder := hholder) (hNa0 := hNa0) (hNa := hNa) (hPos := d4) (hD := hD)

/-- `PinchThirdEventFaithfulStmt` from the hypotheses `h16`, `hAx` of `firstPass_11_17_corrected_derivedInputs38` alone:
the hypothesis `hdec` of that declaration is not used. -/
theorem firstPass_11_17_corrected_derivedInputs43
    (h16 : PinchSecondEventFaithfulStmt.{u})
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u}) :
    PinchThirdEventFaithfulStmt.{u} := by
  have d1 := HarmonicBalls.lqgInternalMetricWeylAeMeasurable_of_fieldAxioms.{u} (hAx := hAx)
  exact HarmonicBalls.firstPass_11_17_corrected_derivedInputs38.{u} (h16 := h16) (hAx := hAx) (hdec := d1)

/-- `HarmonicBallNoveltyCanonicalStmt` from the hypotheses `hjordan`, `hmetric` of `harmonicBallNoveltyStmt_of_existence_and_results_canonical` alone:
the hypotheses `hex`, `hlip` of that declaration are not used. -/
theorem harmonicBallNoveltyStmt_of_existence_and_results_canonical_derivedInputs43
    (hjordan : HarmonicBallComplementBoundaryJordanStmt.{u})
    (hmetric : HarmonicBallNotMetricBallCanonicalStmt.{u}) :
    HarmonicBallNoveltyCanonicalStmt.{u} := by
  have d1 := HarmonicBalls.cameronMartinLocallyLipschitzShiftAbsCont_holds.{u}
  have d2 := HarmonicBalls.localCampbellMarkedRestriction_holds.{u}
  have d3 := HarmonicBalls.localRootedFieldMeasureDomination_holds.{u}
  have d4 := HarmonicBalls.lqgMeasureCoordChange_holds.{u}
  have d5 := HarmonicBalls.lqgMeasureExistence_forall_field.{u}
  have d6 := HarmonicBalls.wholePlaneLQGBallMassBounds_holds.{u}
  have d7 := HarmonicBalls.Closure.closure_5_5_derivedInputsCampbell.{u} (hDG := d6)
  have d8 := HarmonicBalls.Closure.closure_5_6_derivedInputs40.{u} (hDG := d6)
  have d9 := HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5.{u} (h55 := d7) (h56 := d8)
  have d10 := HarmonicBalls.Closure.closure_11_2_derivedInputs36.{u} (hDG := d6) (hCC := d4) (hE := d5) (hL1 := d3) (hCamp := d2) (hCM := d1)
  exact HarmonicBalls.harmonicBallNoveltyStmt_of_existence_and_results_canonical.{u} (hex := d9) (hjordan := hjordan) (hlip := d10) (hmetric := hmetric)

/-- `HarmonicBallNotMetricBallCanonicalStmt` from the hypotheses `hmany`, `hmetricAxioms` of `harmonicBallNotMetricBallCanonicalStmt_of_comparison_pinch_and_volumeGrowth` alone:
the hypotheses `hbound`, `hgrowth` of that declaration are not used. -/
theorem harmonicBallNotMetricBallCanonicalStmt_of_comparison_pinch_and_volumeGrowth_derivedInputs43
    (hmany : Closure.ManyPinchScalesCanonicalModelStmt.{u})
    (hmetricAxioms : ∀ (γ α₀ ξ : ℝ), LT.lt.{0} 0 γ → LT.lt.{0} γ 2 → LT.lt.{0} α₀ (lqgQ γ) → ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF.{u} P hC hcirc → LQGMetricFieldAxioms.{u} P γ ξ α₀ hC hcirc) :
    HarmonicBallNotMetricBallCanonicalStmt.{u} := by
  have d1 := HarmonicBalls.lqgMeasureCoordChange_zero_holds.{u}
  have d2 := HarmonicBalls.lqgMeasureExistence_forall_field.{u}
  have d3 := HarmonicBalls.wholePlaneLQGBallMassBounds_holds.{u}
  have d4 := HarmonicBalls.Closure.closure_11_6_derivedInputsCampbell.{u} (hDG := d3)
  have d5 := HarmonicBalls.lqgVolumeGrowthAllScalesStmt_of_existence.{u} (hDG := d3) (hCC := d1) (hE := d2)
  exact HarmonicBalls.firstPass_11_11_canonical.{u} (h6 := d4) (h13 := hmany) (hI2 := d5) (hmetricAxioms := hmetricAxioms)

end HarmonicBalls

namespace HarmonicBalls.Closure

/-- `HarmonicBallLocalSetStmt` with no hypothesis; the hypotheses `hL1`, `hDG` of `closure_1_3_derivedInputs41` are not used. -/
theorem closure_1_3_derivedInputs43 :
    HarmonicBallLocalSetStmt.{u} := by
  have d1 := HarmonicBalls.wholePlaneLQGBallMassBounds_holds.{u}
  exact HarmonicBalls.Closure.closure_1_3_derivedInputsCampbell.{u} (hDG := d1)

/-- `LeastSupersolutionMemStmt` with no hypothesis; the hypotheses `hDG` of `closure_3_1_derivedInputs41` are not used. -/
theorem closure_3_1_derivedInputs43 :
    LeastSupersolutionMemStmt.{u} := by
  have d1 := HarmonicBalls.wholePlaneLQGBallMassBounds_holds.{u}
  exact HarmonicBalls.Closure.closure_3_1_derivedInputs40.{u} (hDG := d1)

/-- `ClusterOpenLaplacianStmt` with no hypothesis; the hypotheses `hDG` of `closure_3_2_derivedInputs41` are not used. -/
theorem closure_3_2_derivedInputs43 :
    ClusterOpenLaplacianStmt.{u} := by
  have d1 := HarmonicBalls.wholePlaneLQGBallMassBounds_holds.{u}
  exact HarmonicBalls.Closure.closure_3_2_derivedInputs40.{u} (hDG := d1)

/-- `ClusterMonotoneStmt` with no hypothesis; the hypotheses `hDG` of `closure_3_3_derivedInputs41` are not used. -/
theorem closure_3_3_derivedInputs43 :
    ClusterMonotoneStmt.{u} := by
  have d1 := HarmonicBalls.wholePlaneLQGBallMassBounds_holds.{u}
  exact HarmonicBalls.Closure.closure_3_3_derivedInputs40.{u} (hDG := d1)

/-- `ClusterConservationOfMassStmt` with no hypothesis; the hypotheses `hDG` of `closure_3_4_derivedInputs41` are not used. -/
theorem closure_3_4_derivedInputs43 :
    ClusterConservationOfMassStmt.{u} := by
  have d1 := HarmonicBalls.wholePlaneLQGBallMassBounds_holds.{u}
  exact HarmonicBalls.Closure.closure_3_4_derivedInputs40.{u} (hDG := d1)

/-- `ClusterCompatibilityStmt` with no hypothesis; the hypotheses `hDG` of `closure_3_5_derivedInputs41` are not used. -/
theorem closure_3_5_derivedInputs43 :
    ClusterCompatibilityStmt.{u} := by
  have d1 := HarmonicBalls.wholePlaneLQGBallMassBounds_holds.{u}
  exact HarmonicBalls.Closure.closure_3_5_derivedInputs40.{u} (hDG := d1)

/-- `ClusterLowerBoundStmt` with no hypothesis; the hypotheses `hDG` of `closure_4_1_derivedInputs41` are not used. -/
theorem closure_4_1_derivedInputs43 :
    ClusterLowerBoundStmt.{u} := by
  have d1 := HarmonicBalls.wholePlaneLQGBallMassBounds_holds.{u}
  exact HarmonicBalls.Closure.closure_4_1_derivedInputs40.{u} (hDG := d1)

/-- `LeastSupersolutionHolderStmt` with no hypothesis; the hypotheses `hDG` of `closure_4_2_derivedInputs41` are not used. -/
theorem closure_4_2_derivedInputs43 :
    LeastSupersolutionHolderStmt.{u} := by
  have d1 := HarmonicBalls.wholePlaneLQGBallMassBounds_holds.{u}
  exact HarmonicBalls.Closure.closure_4_2_derivedInputs40.{u} (hDG := d1)

/-- `ClusterSubharmonicBallStmt` with no hypothesis; the hypotheses `hDG` of `closure_4_3_derivedInputs41` are not used. -/
theorem closure_4_3_derivedInputs43 :
    ClusterSubharmonicBallStmt.{u} := by
  have d1 := HarmonicBalls.wholePlaneLQGBallMassBounds_holds.{u}
  exact HarmonicBalls.Closure.closure_4_3_derivedInputs40.{u} (hDG := d1)

/-- `ClusterUpperBoundStmt` with no hypothesis; the hypotheses `hDG` of `closure_5_1_derivedInputs41` are not used. -/
theorem closure_5_1_derivedInputs43 :
    ClusterUpperBoundStmt.{u} := by
  have d1 := HarmonicBalls.wholePlaneLQGBallMassBounds_holds.{u}
  exact HarmonicBalls.Closure.closure_5_1_derivedInputs40.{u} (hDG := d1)

/-- `ClusterContinuityStmt` with no hypothesis; the hypotheses `hDG`, `hSub` of `closure_5_2_derivedInputs41` are not used. -/
theorem closure_5_2_derivedInputs43 :
    ClusterContinuityStmt.{u} := by
  have d1 := HarmonicBalls.wholePlaneLQGBallMassBounds_holds.{u}
  exact HarmonicBalls.Closure.closure_5_2_derivedInputsCampbell.{u} (hDG := d1)

/-- `ClusterBoundaryMeasureZeroStmt` with no hypothesis; the hypotheses `hDG`, `hL1` of `closure_5_3_derivedInputs41` are not used. -/
theorem closure_5_3_derivedInputs43 :
    ClusterBoundaryMeasureZeroStmt.{u} := by
  have d1 := HarmonicBalls.wholePlaneLQGBallMassBounds_holds.{u}
  exact HarmonicBalls.Closure.closure_5_3_derivedInputsCampbell.{u} (hDG := d1)

/-- `RegularizedClusterHarmonicBallsStmt` with no hypothesis; the hypotheses `hDG`, `hL1` of `closure_5_4_derivedInputs41` are not used. -/
theorem closure_5_4_derivedInputs43 :
    RegularizedClusterHarmonicBallsStmt.{u} := by
  have d1 := HarmonicBalls.wholePlaneLQGBallMassBounds_holds.{u}
  exact HarmonicBalls.Closure.closure_5_4_derivedInputsCampbell.{u} (hDG := d1)

/-- `ExistenceHarmonicBallsStmt` with no hypothesis; the hypotheses `hDG`, `hL1` of `closure_5_5_derivedInputs41` are not used. -/
theorem closure_5_5_derivedInputs43 :
    ExistenceHarmonicBallsStmt.{u} := by
  have d1 := HarmonicBalls.wholePlaneLQGBallMassBounds_holds.{u}
  exact HarmonicBalls.Closure.closure_5_5_derivedInputsCampbell.{u} (hDG := d1)

/-- `UniquenessHarmonicBallsStmt` with no hypothesis; the hypotheses `hDG` of `closure_5_6_derivedInputs41` are not used. -/
theorem closure_5_6_derivedInputs43 :
    UniquenessHarmonicBallsStmt.{u} := by
  have d1 := HarmonicBalls.wholePlaneLQGBallMassBounds_holds.{u}
  exact HarmonicBalls.Closure.closure_5_6_derivedInputs40.{u} (hDG := d1)

/-- `ClusterScaleInvarianceStmt` with no hypothesis; the hypotheses `hDG` of `closure_5_7_derivedInputs41` are not used. -/
theorem closure_5_7_derivedInputs43 :
    ClusterScaleInvarianceStmt.{u} := by
  have d1 := HarmonicBalls.wholePlaneLQGBallMassBounds_holds.{u}
  exact HarmonicBalls.Closure.closure_5_7_derivedInputs41.{u} (hDG := d1)

/-- `ClusterStrongCompatibilityStmt` with no hypothesis; the hypotheses `hDG` of `closure_5_8_derivedInputs41` are not used. -/
theorem closure_5_8_derivedInputs43 :
    ClusterStrongCompatibilityStmt.{u} := by
  have d1 := HarmonicBalls.wholePlaneLQGBallMassBounds_holds.{u}
  exact HarmonicBalls.Closure.closure_5_8_derivedInputs40.{u} (hDG := d1)

/-- `HarnackTypeEstimateStmt` with no hypothesis; the hypotheses `hDG` of `closure_6_1_derivedInputs41` are not used. -/
theorem closure_6_1_derivedInputs43 :
    HarnackTypeEstimateStmt.{u} := by
  have d1 := HarmonicBalls.wholePlaneLQGBallMassBounds_holds.{u}
  exact HarmonicBalls.Closure.closure_6_1_derivedInputs40.{u} (hDG := d1)

/-- `HarnackTypeComponentStmt` with no hypothesis; the hypotheses `hDG` of `closure_6_2_derivedInputs41` are not used. -/
theorem closure_6_2_derivedInputs43 :
    HarnackTypeComponentStmt.{u} := by
  have d1 := HarmonicBalls.wholePlaneLQGBallMassBounds_holds.{u}
  exact HarmonicBalls.Closure.closure_6_2_derivedInputs40.{u} (hDG := d1)

/-- `ManyGoodAnnuliStmt` with no hypothesis; the hypotheses `hDG` of `closure_6_3_derivedInputs41` are not used. -/
theorem closure_6_3_derivedInputs43 :
    ManyGoodAnnuliStmt.{u} := by
  have d1 := HarmonicBalls.wholePlaneLQGBallMassBounds_holds.{u}
  exact HarmonicBalls.Closure.closure_6_3_derivedInputs40.{u} (hDG := d1)

/-- `GoodAnnulusProbabilityStmt` with no hypothesis; the hypotheses `hDG` of `closure_6_4_derivedInputs41` are not used. -/
theorem closure_6_4_derivedInputs43 :
    GoodAnnulusProbabilityStmt.{u} := by
  have d1 := HarmonicBalls.wholePlaneLQGBallMassBounds_holds.{u}
  exact HarmonicBalls.Closure.closure_6_4_derivedInputs40.{u} (hDG := d1)

/-- `ManyVeryGoodAnnuliStmt` with no hypothesis; the hypotheses `hDG` of `closure_6_6_derivedInputs41` are not used. -/
theorem closure_6_6_derivedInputs43 :
    ManyVeryGoodAnnuliStmt.{u} := by
  have d1 := HarmonicBalls.wholePlaneLQGBallMassBounds_holds.{u}
  exact HarmonicBalls.Closure.closure_6_6_derivedInputs40.{u} (hDG := d1)

/-- `VeryGoodAnnulusProbabilityStmt` with no hypothesis; the hypotheses `hDG` of `closure_6_7_derivedInputs41` are not used. -/
theorem closure_6_7_derivedInputs43 :
    VeryGoodAnnulusProbabilityStmt.{u} := by
  have d1 := HarmonicBalls.wholePlaneLQGBallMassBounds_holds.{u}
  exact HarmonicBalls.Closure.closure_6_7_derivedInputs40.{u} (hDG := d1)

/-- `AnnulusMassBoundByOdometerStmt` with no hypothesis; the hypotheses `hDG` of `closure_6_8_derivedInputs41` are not used. -/
theorem closure_6_8_derivedInputs43 :
    AnnulusMassBoundByOdometerStmt.{u} := by
  have d1 := HarmonicBalls.wholePlaneLQGBallMassBounds_holds.{u}
  exact HarmonicBalls.Closure.closure_6_8_derivedInputs40.{u} (hDG := d1)

/-- `OdometerHarmonicMeasureBoundStmt` with no hypothesis; the hypotheses `hDG` of `closure_6_9_derivedInputs41` are not used. -/
theorem closure_6_9_derivedInputs43 :
    OdometerHarmonicMeasureBoundStmt.{u} := by
  have d1 := HarmonicBalls.wholePlaneLQGBallMassBounds_holds.{u}
  exact HarmonicBalls.Closure.closure_6_9_derivedInputs40.{u} (hDG := d1)

/-- `OdometerBoundByAnnulusMassStmt` with no hypothesis; the hypotheses `hDG` of `closure_6_10_derivedInputs41` are not used. -/
theorem closure_6_10_derivedInputs43 :
    OdometerBoundByAnnulusMassStmt.{u} := by
  have d1 := HarmonicBalls.wholePlaneLQGBallMassBounds_holds.{u}
  exact HarmonicBalls.Closure.closure_6_10_derivedInputs40.{u} (hDG := d1)

/-- `VeryGoodAnnulusHarnackTypeStmt` with no hypothesis; the hypotheses `hDG` of `closure_6_11_derivedInputs41` are not used. -/
theorem closure_6_11_derivedInputs43 :
    VeryGoodAnnulusHarnackTypeStmt.{u} := by
  have d1 := HarmonicBalls.wholePlaneLQGBallMassBounds_holds.{u}
  exact HarmonicBalls.Closure.closure_6_11_derivedInputs40.{u} (hDG := d1)

/-- `LowMassSmallOdometerStmt` with no hypothesis; the hypotheses `hDG` of `closure_6_13_derivedInputs41` are not used. -/
theorem closure_6_13_derivedInputs43 :
    LowMassSmallOdometerStmt.{u} := by
  have d1 := HarmonicBalls.wholePlaneLQGBallMassBounds_holds.{u}
  exact HarmonicBalls.Closure.closure_6_13_derivedInputs40.{u} (hDG := d1)

/-- `ClusterUpperBoundPolyHighProbStmt` with no hypothesis; the hypotheses `hDG` of `closure_7_1_derivedInputs41` are not used. -/
theorem closure_7_1_derivedInputs43 :
    ClusterUpperBoundPolyHighProbStmt.{u} := by
  have d1 := HarmonicBalls.wholePlaneLQGBallMassBounds_holds.{u}
  exact HarmonicBalls.Closure.closure_7_1_derivedInputs40.{u} (hDG := d1)

/-- `ClusterTimeContinuityStmt` with no hypothesis; the hypotheses `hL1`, `hDG` of `closure_7_2_derivedInputs41` are not used. -/
theorem closure_7_2_derivedInputs43 :
    ClusterTimeContinuityStmt.{u} := by
  have d1 := HarmonicBalls.wholePlaneLQGBallMassBounds_holds.{u}
  exact HarmonicBalls.Closure.closure_7_2_derivedInputsCampbell.{u} (hDG := d1)

/-- `BoundaryMeasureZeroOfCompactClusterStmt` with no hypothesis; the hypotheses `hL1`, `hDG` of `closure_8_1_derivedInputs41` are not used. -/
theorem closure_8_1_derivedInputs43 :
    BoundaryMeasureZeroOfCompactClusterStmt.{u} := by
  have d1 := HarmonicBalls.wholePlaneLQGBallMassBounds_holds.{u}
  exact HarmonicBalls.Closure.closure_8_1_derivedInputsCampbell.{u} (hDG := d1)

/-- `OriginManyGoodScalesStmt` from the hypotheses `hholder` of `closure_8_3_derivedInputs42` alone:
the hypothesis `hDG` of that declaration is not used. -/
theorem closure_8_3_derivedInputs43
    (hholder : GreenPotentialHolderStmt.{u}) :
    OriginManyGoodScalesStmt.{u} := by
  have d1 := HarmonicBalls.wholePlaneLQGBallMassBounds_holds.{u}
  exact HarmonicBalls.Closure.closure_8_3_derivedInputs42.{u} (hholder := hholder) (hDG := d1)

/-- `HarmonicBallComplementBoundaryJordanStmt` from the hypotheses `hTor` of `closure_10_7_derivedInputs41` alone:
the hypotheses `hL1`, `hDG` of that declaration are not used. -/
theorem closure_10_7_derivedInputs43
    (hTor : TorhorstSimpleLoopFrozen) :
    HarmonicBallComplementBoundaryJordanStmt.{u} := by
  have d1 := HarmonicBalls.wholePlaneLQGBallMassBounds_holds.{u}
  exact HarmonicBalls.Closure.closure_10_7_derivedInputsCampbell.{u} (hDG := d1) (hTor := hTor)

/-- `AnnulusMassBoundByHarmonicChainStmt` with no hypothesis; the hypotheses `hDG`, `hSub` of `closure_11_6_derivedInputs41` are not used. -/
theorem closure_11_6_derivedInputs43 :
    AnnulusMassBoundByHarmonicChainStmt.{u} := by
  have d1 := HarmonicBalls.wholePlaneLQGBallMassBounds_holds.{u}
  exact HarmonicBalls.Closure.closure_11_6_derivedInputsCampbell.{u} (hDG := d1)

/-- `ConeBadEventProbabilityStmt` with no hypothesis; the hypotheses `hDG` of `closure_11_8_derivedInputs41` are not used. -/
theorem closure_11_8_derivedInputs43 :
    ConeBadEventProbabilityStmt.{u} := by
  have d1 := HarmonicBalls.wholePlaneLQGBallMassBounds_holds.{u}
  exact HarmonicBalls.Closure.closure_11_8_derivedInputs40.{u} (hDG := d1)

/-- `SubharmonicBallUniquenessC51Stmt` from the hypotheses `hSub` of `closure_9_2_derivedInputs41` alone:
the hypothesis `hDG` of that declaration is not used. -/
theorem closure_9_2_derivedInputs43
    (hSub : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure.{0} ℂ), DMSLemmaA10WholePlaneMarkedSub.{u} P γ hC hcirc μ) :
    S9c.SubharmonicBallUniquenessC51Stmt.{u} := by
  have d1 := HarmonicBalls.wholePlaneLQGBallMassBounds_holds.{u}
  exact HarmonicBalls.Closure.closure_9_2_derivedInputs41.{u} (hSub := hSub) (hDG := d1)

end HarmonicBalls.Closure
