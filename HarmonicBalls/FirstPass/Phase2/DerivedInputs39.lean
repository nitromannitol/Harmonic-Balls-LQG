import HarmonicBalls.FirstPass.Closure
import HarmonicBalls.FirstPass.Closure.Sec11
import HarmonicBalls.FirstPass.Closure.Sec6
import HarmonicBalls.FirstPass.Closure.Sec78910
import HarmonicBalls.FirstPass.Closure.SecA45
import HarmonicBalls.FirstPass.Phase2.DerivedInputs35
import HarmonicBalls.FirstPass.Phase2.DerivedInputs36
import HarmonicBalls.FirstPass.Phase2.DomainMarkovConditionalPositiveHolds
import HarmonicBalls.FirstPass.Phase2.LQGMeasureExistenceDerived
import HarmonicBalls.FirstPass.Phase2.RootedDominationCanonical
import HarmonicBalls.FirstPass.S11b
import HarmonicBalls.Proofs.Sec3.Basic
import HarmonicBalls.Proofs.Sec3.ClusterCompatibility
import HarmonicBalls.Proofs.Sec3.ConservationOfMassLemma
import HarmonicBalls.Proofs.Sec3.OpenLaplacian
import HarmonicBalls.Proofs.Sec4.ClusterGreenIdentity
import HarmonicBalls.Proofs.Sec4.ClusterLowerBound
import HarmonicBalls.Proofs.Sec4.LeastSupersolutionHolder
import HarmonicBalls.Proofs.Sec9.ExistenceResultsAssembly
import HarmonicBalls.Proofs.Sec9.HarmonicBoundaryAssembly
import HarmonicBalls.Proofs.Sec9.LQGExistenceConsequences
import HarmonicBalls.Proofs.Sec9.RegularOpenEqOfAEEq
import HarmonicBalls.Proofs.SecA.ObstacleNonCoincidenceHarmonic
import HarmonicBalls.Steps.Sec3.ClusterConservationOfMass
import HarmonicBalls.Steps.Sec3.ClusterOpenLaplacian

/-!
# Derived-input forms, round 39: unused hypotheses removed

Each theorem below has the conclusion of the declaration named in its docstring and a subset of its hypotheses:
the conclusion already follows from that subset by theorems of this repository. The kept hypotheses are
unchanged; the proofs are chains of applications.

Generated from the types of the wrapped declarations; do not edit by hand.
-/

universe u

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

namespace HarmonicBalls

/-- `TypicalPointManyGoodScalesStmt` from the hypotheses `hSub`, `hDG`, `hCC` of `firstPass_8_2_S8d_noWeyl_derivedInputs36` alone:
the hypothesis `hEx` of that declaration is not used. -/
theorem firstPass_8_2_S8d_noWeyl_derivedInputs39
    (hSub : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure.{0} ℂ), DMSLemmaA10WholePlaneMarkedSub.{u} P γ hC hcirc μ)
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange.{u} P γ α₀ hC hcirc) :
    TypicalPointManyGoodScalesStmt.{u} := by
  have d1 := HarmonicBalls.lqgMeasureExistence_forall_field.{u}
  have d2 := HarmonicBalls.localRootedFieldMeasureDomination_of_sub.{u} (hSub := hSub)
  exact HarmonicBalls.Closure.typicalPointManyGoodScales_closed_derivedInputs36.{u} (hDG := hDG) (hCC := hCC) (hE := d1) (hL1 := d2)

/-- `HarmonicBallBoundarySubsetStmt` from the hypotheses `hDG`, `hCC` of `firstPass_9_3_derivedInputs38` alone:
the hypotheses `hW`, `hE`, `hN` of that declaration are not used. -/
theorem firstPass_9_3_derivedInputs39
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange.{u} P γ 0 hC hcirc) :
    HarmonicBallBoundarySubsetStmt.{u} := by
  have d1 := HarmonicBalls.lqgMeasureExistence_forall_field.{u}
  have d2 := HarmonicBalls.lqgVolumeGrowthAllScalesStmt_of_existence.{u} (hDG := hDG) (hCC := hCC) (hE := d1)
  exact HarmonicBalls.harmonicBallBoundarySubset_of_volumeGrowth.{u} (hI2 := d2)

/-- `RegularOpenEqOfAEEqStmt` from the hypotheses `hDG`, `hCC` of `firstPass_9_4_derivedInputs38` alone:
the hypotheses `hW`, `hE`, `hN` of that declaration are not used. -/
theorem firstPass_9_4_derivedInputs39
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange.{u} P γ 0 hC hcirc) :
    RegularOpenEqOfAEEqStmt.{u} := by
  have d1 := HarmonicBalls.lqgMeasureExistence_forall_field.{u}
  have d2 := HarmonicBalls.lqgMeasureFullSupportStmt_of_existence.{u} (hDG := hDG) (hCC := hCC) (hE := d1)
  exact HarmonicBalls.regularOpenEqOfAEEq.{u} (hI1 := d2)

/-- `ManyConeBadScalesStmt` from the hypotheses `h8`, `hFreq`, `hTr` of `firstPass_11_7` alone:
the hypothesis `hE` of that declaration is not used. -/
theorem firstPass_11_7_derivedInputs39
    (h8 : ConeBadEventProbabilityStmt.{u})
    (hFreq : OriginRootedConeFrequencyFrozen.{u})
    (hTr : RootedConeFrequencyTransferFrozen.{u}) :
    ManyConeBadScalesStmt.{u} := by
  have d1 := HarmonicBalls.lqgMeasureExistence_forall_field.{u}
  exact HarmonicBalls.firstPass_11_7.{u} (h8 := h8) (hE := d1) (hFreq := hFreq) (hTr := hTr)

/-- `SubharmonicBallUniquenessWeakStmt` from the hypotheses `hDG`, `hCC`, `h82` of `firstPass_9_2_corrected` alone:
the hypotheses `hW`, `hE`, `hN` of that declaration are not used. -/
theorem firstPass_9_2_corrected_derivedInputs39
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange.{u} P γ 0 hC hcirc)
    (h82 : TypicalPointManyGoodScalesStmt.{u}) :
    SubharmonicBallUniquenessWeakStmt.{u} := by
  have d1 := HarmonicBalls.lqgMeasureExistence_forall_field.{u}
  exact HarmonicBalls.subharmonicBallUniquenessWeak_of_existence.{u} (hDG := hDG) (hCC := hCC) (hE := d1) (h82 := h82)

/-- `PinchSecondEventFaithfulStmt` from the hypotheses `hAx`, `hholder`, `hNa0`, `hNa`, `hPos`, `hD` of `firstPass_11_16_corrected_derivedInputs35` alone:
the hypotheses `hEx`, `hMk` of that declaration are not used. -/
theorem firstPass_11_16_corrected_derivedInputs39
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hholder : GreenPotentialHolderStmt.{u})
    (hNa0 : ∀ (γ : ℝ) (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic.{u} P γ 0 hC hcirc)
    (hNa : ∀ (γ α₀ : ℝ) (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic.{u} P γ α₀ hC hcirc)
    (hPos : PinchFirstEventFaithfulStmt.{u})
    (hD : SmallMetricDiameterLargeMassStmt.{u}) :
    PinchSecondEventFaithfulStmt.{u} := by
  have d1 := HarmonicBalls.domainMarkovConditionalPositive_holds.{u}
  have d2 := HarmonicBalls.lqgMeasureExistence_forall_zero.{u}
  exact HarmonicBalls.firstPass_11_16_corrected_derivedInputs35.{u} (hAx := hAx) (hholder := hholder) (hEx := d2) (hNa0 := hNa0) (hNa := hNa) (hPos := hPos) (hD := hD) (hMk := d1)

end HarmonicBalls

namespace HarmonicBalls.Closure

/-- `HarmonicBallLocalSetStmt` from the hypotheses `hL1`, `hDG`, `hCC` of `closure_1_3_derivedInputs36` alone:
the hypothesis `hE` of that declaration is not used. -/
theorem closure_1_3_derivedInputs39
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange.{u} P γ α₀ hC hcirc) :
    HarmonicBallLocalSetStmt.{u} := by
  have d1 := HarmonicBalls.lqgMeasureExistence_forall_field.{u}
  exact HarmonicBalls.Closure.closure_1_3_derivedInputs36.{u} (hL1 := hL1) (hDG := hDG) (hCC := hCC) (hE := d1)

/-- `LeastSupersolutionMemStmt` from the hypotheses `hDG`, `hCC` of `closure_3_1_derivedInputs38` alone:
the hypotheses `hE`, `hN` of that declaration are not used. -/
theorem closure_3_1_derivedInputs39
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange.{u} P γ 0 hC hcirc) :
    LeastSupersolutionMemStmt.{u} := by
  have d1 := HarmonicBalls.lqgMeasureExistence_forall_field.{u}
  have d2 := HarmonicBalls.lqgVolumeGrowthAllScalesStmt_of_existence.{u} (hDG := hDG) (hCC := hCC) (hE := d1)
  exact HarmonicBalls.leastSupersolutionMem_proved.{u} (hI2 := d2)

/-- `ClusterOpenLaplacianStmt` from the hypotheses `hDG`, `hCC` of `closure_3_2_derivedInputs38` alone:
the hypotheses `hE`, `hN` of that declaration are not used. -/
theorem closure_3_2_derivedInputs39
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange.{u} P γ 0 hC hcirc) :
    ClusterOpenLaplacianStmt.{u} := by
  have d1 := HarmonicBalls.Closure.closure_2_3
  have d2 := HarmonicBalls.lqgMeasureExistence_forall_field.{u}
  have d3 := HarmonicBalls.obstacleCompatibilityShiftStep_holds
  have d4 := HarmonicBalls.obstacleNonCoincidenceHarmonicGeneral_holds
  have d5 := HarmonicBalls.shiftedOdometerLaplacianGeneral_holds
  have d6 := HarmonicBalls.lqgVolumeGrowthAllScalesStmt_of_existence.{u} (hDG := hDG) (hCC := hCC) (hE := d2)
  exact HarmonicBalls.clusterOpenLaplacian_of_steps.{u} (hI2 := d6) (h23 := d1) (hA2 := d4) (hA5 := d5) (hS := d3)

/-- `ClusterMonotoneStmt` from the hypotheses `hDG`, `hCC` of `closure_3_3_derivedInputs38` alone:
the hypotheses `hE`, `hN` of that declaration are not used. -/
theorem closure_3_3_derivedInputs39
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange.{u} P γ 0 hC hcirc) :
    ClusterMonotoneStmt.{u} := by
  have d1 := HarmonicBalls.lqgMeasureExistence_forall_field.{u}
  have d2 := HarmonicBalls.lqgVolumeGrowthAllScalesStmt_of_existence.{u} (hDG := hDG) (hCC := hCC) (hE := d1)
  exact HarmonicBalls.clusterMonotone_proved.{u} (hI2 := d2)

/-- `ClusterConservationOfMassStmt` from the hypotheses `hDG`, `hCC` of `closure_3_4_derivedInputs38` alone:
the hypotheses `hE`, `hN` of that declaration are not used. -/
theorem closure_3_4_derivedInputs39
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange.{u} P γ 0 hC hcirc) :
    ClusterConservationOfMassStmt.{u} := by
  have d1 := HarmonicBalls.lqgMeasureExistence_forall_field.{u}
  have d2 := HarmonicBalls.obstacleCompatibilityShiftStep_holds
  have d3 := HarmonicBalls.obstacleConservationOfMassGeneral_holds
  have d4 := HarmonicBalls.obstacleOdometerZeroBoundaryGeneral_holds
  have d5 := HarmonicBalls.lqgVolumeGrowthAllScalesStmt_of_existence.{u} (hDG := hDG) (hCC := hCC) (hE := d1)
  exact HarmonicBalls.clusterConservationOfMass_of_steps.{u} (hI2 := d5) (hA4 := d4) (hA5 := d3) (hS := d2)

/-- `ClusterCompatibilityStmt` from the hypotheses `hDG`, `hCC` of `closure_3_5_derivedInputs38` alone:
the hypotheses `hE`, `hN` of that declaration are not used. -/
theorem closure_3_5_derivedInputs39
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange.{u} P γ 0 hC hcirc) :
    ClusterCompatibilityStmt.{u} := by
  have d1 := HarmonicBalls.lqgMeasureExistence_forall_field.{u}
  have d2 := HarmonicBalls.lqgVolumeGrowthAllScalesStmt_of_existence.{u} (hDG := hDG) (hCC := hCC) (hE := d1)
  exact HarmonicBalls.clusterCompatibility_proved.{u} (hI2 := d2)

/-- `ClusterLowerBoundStmt` from the hypotheses `hDG`, `hCC` of `closure_4_1` alone:
the hypotheses `hW`, `hE`, `hN` of that declaration are not used. -/
theorem closure_4_1_derivedInputs39
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange.{u} P γ 0 hC hcirc) :
    ClusterLowerBoundStmt.{u} := by
  have d1 := HarmonicBalls.lqgMeasureExistence_forall_field.{u}
  have d2 := HarmonicBalls.lqgVolumeGrowthAllScalesStmt_of_existence.{u} (hDG := hDG) (hCC := hCC) (hE := d1)
  exact HarmonicBalls.clusterLowerBound_proved.{u} (hI2 := d2)

/-- `LeastSupersolutionHolderStmt` from the hypotheses `hDG`, `hCC` of `closure_4_2` alone:
the hypotheses `hW`, `hE`, `hN` of that declaration are not used. -/
theorem closure_4_2_derivedInputs39
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange.{u} P γ 0 hC hcirc) :
    LeastSupersolutionHolderStmt.{u} := by
  have d1 := HarmonicBalls.lqgMeasureExistence_forall_field.{u}
  have d2 := HarmonicBalls.lqgVolumeGrowthAllScalesStmt_of_existence.{u} (hDG := hDG) (hCC := hCC) (hE := d1)
  exact HarmonicBalls.leastSupersolutionHolder_proved.{u} (hI2 := d2)

/-- `ClusterSubharmonicBallStmt` from the hypotheses `hDG`, `hCC` of `closure_4_3` alone:
the hypotheses `hW`, `hE`, `hN` of that declaration are not used. -/
theorem closure_4_3_derivedInputs39
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange.{u} P γ 0 hC hcirc) :
    ClusterSubharmonicBallStmt.{u} := by
  have d1 := HarmonicBalls.lqgMeasureExistence_forall_field.{u}
  have d2 := HarmonicBalls.lqgVolumeGrowthAllScalesStmt_of_existence.{u} (hDG := hDG) (hCC := hCC) (hE := d1)
  exact HarmonicBalls.clusterSubharmonicBall_proved.{u} (hI2 := d2)

/-- `ClusterUpperBoundStmt` from the hypotheses `hDG`, `hCC` of `closure_5_1` alone:
the hypothesis `hE` of that declaration is not used. -/
theorem closure_5_1_derivedInputs39
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange.{u} P γ 0 hC hcirc) :
    ClusterUpperBoundStmt.{u} := by
  have d1 := HarmonicBalls.lqgMeasureExistence_forall_field.{u}
  exact HarmonicBalls.Closure.closure_5_1.{u} (hDG := hDG) (hCC := hCC) (hE := d1)

/-- `ClusterContinuityStmt` from the hypotheses `hDG`, `hCC`, `hSub` of `closure_5_2_derivedInputs36` alone:
the hypothesis `hE` of that declaration is not used. -/
theorem closure_5_2_derivedInputs39
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange.{u} P γ α₀ hC hcirc)
    (hSub : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure.{0} ℂ), DMSLemmaA10WholePlaneMarkedSub.{u} P γ hC hcirc μ) :
    ClusterContinuityStmt.{u} := by
  have d1 := HarmonicBalls.lqgMeasureExistence_forall_field.{u}
  exact HarmonicBalls.Closure.closure_5_2_derivedInputs36.{u} (hDG := hDG) (hCC := hCC) (hE := d1) (hSub := hSub)

/-- `ClusterBoundaryMeasureZeroStmt` from the hypotheses `hDG`, `hCC`, `hL1` of `closure_5_3_derivedInputs36` alone:
the hypothesis `hE` of that declaration is not used. -/
theorem closure_5_3_derivedInputs39
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange.{u} P γ α₀ hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{u}) :
    ClusterBoundaryMeasureZeroStmt.{u} := by
  have d1 := HarmonicBalls.lqgMeasureExistence_forall_field.{u}
  exact HarmonicBalls.Closure.closure_5_3_derivedInputs36.{u} (hDG := hDG) (hCC := hCC) (hE := d1) (hL1 := hL1)

/-- `RegularizedClusterHarmonicBallsStmt` from the hypotheses `hDG`, `hCC`, `hL1` of `closure_5_4_derivedInputs36` alone:
the hypothesis `hE` of that declaration is not used. -/
theorem closure_5_4_derivedInputs39
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange.{u} P γ α₀ hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{u}) :
    RegularizedClusterHarmonicBallsStmt.{u} := by
  have d1 := HarmonicBalls.lqgMeasureExistence_forall_field.{u}
  exact HarmonicBalls.Closure.closure_5_4_derivedInputs36.{u} (hDG := hDG) (hCC := hCC) (hE := d1) (hL1 := hL1)

/-- `ExistenceHarmonicBallsStmt` from the hypotheses `hDG`, `hCC`, `hL1` of `closure_5_5_derivedInputs36` alone:
the hypothesis `hE` of that declaration is not used. -/
theorem closure_5_5_derivedInputs39
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange.{u} P γ α₀ hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{u}) :
    ExistenceHarmonicBallsStmt.{u} := by
  have d1 := HarmonicBalls.lqgMeasureExistence_forall_field.{u}
  exact HarmonicBalls.Closure.closure_5_5_derivedInputs36.{u} (hDG := hDG) (hCC := hCC) (hE := d1) (hL1 := hL1)

/-- `UniquenessHarmonicBallsStmt` from the hypotheses `hDG`, `hCC` of `closure_5_6` alone:
the hypothesis `hE` of that declaration is not used. -/
theorem closure_5_6_derivedInputs39
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange.{u} P γ 0 hC hcirc) :
    UniquenessHarmonicBallsStmt.{u} := by
  have d1 := HarmonicBalls.lqgMeasureExistence_forall_field.{u}
  exact HarmonicBalls.Closure.closure_5_6.{u} (hDG := hDG) (hCC := hCC) (hE := d1)

/-- `ClusterScaleInvarianceStmt` from the hypotheses `hDG`, `hCC` of `closure_5_7` alone:
the hypothesis `hE` of that declaration is not used. -/
theorem closure_5_7_derivedInputs39
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange.{u} P γ α₀ hC hcirc) :
    ClusterScaleInvarianceStmt.{u} := by
  have d1 := HarmonicBalls.lqgMeasureExistence_forall_field.{u}
  exact HarmonicBalls.Closure.closure_5_7.{u} (hDG := hDG) (hCC := hCC) (hE := d1)

/-- `ClusterStrongCompatibilityStmt` from the hypotheses `hDG`, `hCC` of `closure_5_8` alone:
the hypothesis `hE` of that declaration is not used. -/
theorem closure_5_8_derivedInputs39
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange.{u} P γ 0 hC hcirc) :
    ClusterStrongCompatibilityStmt.{u} := by
  have d1 := HarmonicBalls.lqgMeasureExistence_forall_field.{u}
  exact HarmonicBalls.Closure.closure_5_8.{u} (hDG := hDG) (hCC := hCC) (hE := d1)

/-- `HarnackTypeEstimateStmt` from the hypotheses `hDG`, `hCC` of `closure_6_1` alone:
the hypothesis `hE` of that declaration is not used. -/
theorem closure_6_1_derivedInputs39
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange.{u} P γ 0 hC hcirc) :
    HarnackTypeEstimateStmt.{u} := by
  have d1 := HarmonicBalls.lqgMeasureExistence_forall_field.{u}
  exact HarmonicBalls.Closure.closure_6_1.{u} (hDG := hDG) (hCC := hCC) (hE := d1)

/-- `HarnackTypeComponentStmt` from the hypotheses `hDG`, `hCC` of `closure_6_2` alone:
the hypothesis `hE` of that declaration is not used. -/
theorem closure_6_2_derivedInputs39
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange.{u} P γ 0 hC hcirc) :
    HarnackTypeComponentStmt.{u} := by
  have d1 := HarmonicBalls.lqgMeasureExistence_forall_field.{u}
  exact HarmonicBalls.Closure.closure_6_2.{u} (hDG := hDG) (hCC := hCC) (hE := d1)

/-- `ManyGoodAnnuliStmt` from the hypotheses `hDG`, `hCC` of `closure_6_3` alone:
the hypothesis `hE` of that declaration is not used. -/
theorem closure_6_3_derivedInputs39
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange.{u} P γ 0 hC hcirc) :
    ManyGoodAnnuliStmt.{u} := by
  have d1 := HarmonicBalls.lqgMeasureExistence_forall_field.{u}
  exact HarmonicBalls.Closure.closure_6_3.{u} (hDG := hDG) (hCC := hCC) (hE := d1)

/-- `GoodAnnulusProbabilityStmt` from the hypotheses `hDG`, `hCC` of `closure_6_4` alone:
the hypothesis `hE` of that declaration is not used. -/
theorem closure_6_4_derivedInputs39
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange.{u} P γ 0 hC hcirc) :
    GoodAnnulusProbabilityStmt.{u} := by
  have d1 := HarmonicBalls.lqgMeasureExistence_forall_field.{u}
  exact HarmonicBalls.Closure.closure_6_4.{u} (hDG := hDG) (hCC := hCC) (hE := d1)

/-- `ManyVeryGoodAnnuliStmt` from the hypotheses `hDG`, `hCC` of `closure_6_6` alone:
the hypothesis `hE` of that declaration is not used. -/
theorem closure_6_6_derivedInputs39
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange.{u} P γ 0 hC hcirc) :
    ManyVeryGoodAnnuliStmt.{u} := by
  have d1 := HarmonicBalls.lqgMeasureExistence_forall_field.{u}
  exact HarmonicBalls.Closure.closure_6_6.{u} (hDG := hDG) (hCC := hCC) (hE := d1)

/-- `VeryGoodAnnulusProbabilityStmt` from the hypotheses `hDG`, `hCC` of `closure_6_7` alone:
the hypothesis `hE` of that declaration is not used. -/
theorem closure_6_7_derivedInputs39
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange.{u} P γ 0 hC hcirc) :
    VeryGoodAnnulusProbabilityStmt.{u} := by
  have d1 := HarmonicBalls.lqgMeasureExistence_forall_field.{u}
  exact HarmonicBalls.Closure.closure_6_7.{u} (hDG := hDG) (hCC := hCC) (hE := d1)

/-- `AnnulusMassBoundByOdometerStmt` from the hypotheses `hDG`, `hCC` of `closure_6_8` alone:
the hypothesis `hE` of that declaration is not used. -/
theorem closure_6_8_derivedInputs39
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange.{u} P γ 0 hC hcirc) :
    AnnulusMassBoundByOdometerStmt.{u} := by
  have d1 := HarmonicBalls.lqgMeasureExistence_forall_field.{u}
  exact HarmonicBalls.Closure.closure_6_8.{u} (hDG := hDG) (hCC := hCC) (hE := d1)

/-- `OdometerHarmonicMeasureBoundStmt` from the hypotheses `hDG`, `hCC` of `closure_6_9` alone:
the hypothesis `hE` of that declaration is not used. -/
theorem closure_6_9_derivedInputs39
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange.{u} P γ 0 hC hcirc) :
    OdometerHarmonicMeasureBoundStmt.{u} := by
  have d1 := HarmonicBalls.lqgMeasureExistence_forall_field.{u}
  exact HarmonicBalls.Closure.closure_6_9.{u} (hDG := hDG) (hCC := hCC) (hE := d1)

/-- `OdometerBoundByAnnulusMassStmt` from the hypotheses `hDG`, `hCC` of `closure_6_10` alone:
the hypothesis `hE` of that declaration is not used. -/
theorem closure_6_10_derivedInputs39
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange.{u} P γ 0 hC hcirc) :
    OdometerBoundByAnnulusMassStmt.{u} := by
  have d1 := HarmonicBalls.lqgMeasureExistence_forall_field.{u}
  exact HarmonicBalls.Closure.closure_6_10.{u} (hDG := hDG) (hCC := hCC) (hE := d1)

/-- `VeryGoodAnnulusHarnackTypeStmt` from the hypotheses `hDG`, `hCC` of `closure_6_11` alone:
the hypothesis `hE` of that declaration is not used. -/
theorem closure_6_11_derivedInputs39
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange.{u} P γ 0 hC hcirc) :
    VeryGoodAnnulusHarnackTypeStmt.{u} := by
  have d1 := HarmonicBalls.lqgMeasureExistence_forall_field.{u}
  exact HarmonicBalls.Closure.closure_6_11.{u} (hDG := hDG) (hCC := hCC) (hE := d1)

/-- `LowMassSmallOdometerStmt` from the hypotheses `hDG`, `hCC` of `closure_6_13` alone:
the hypothesis `hE` of that declaration is not used. -/
theorem closure_6_13_derivedInputs39
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange.{u} P γ 0 hC hcirc) :
    LowMassSmallOdometerStmt.{u} := by
  have d1 := HarmonicBalls.lqgMeasureExistence_forall_field.{u}
  exact HarmonicBalls.Closure.closure_6_13.{u} (hDG := hDG) (hCC := hCC) (hE := d1)

/-- `ClusterUpperBoundPolyHighProbStmt` from the hypotheses `hDG`, `hCC` of `closure_7_1` alone:
the hypothesis `hE` of that declaration is not used. -/
theorem closure_7_1_derivedInputs39
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange.{u} P γ α₀ hC hcirc) :
    ClusterUpperBoundPolyHighProbStmt.{u} := by
  have d1 := HarmonicBalls.lqgMeasureExistence_forall_field.{u}
  exact HarmonicBalls.Closure.closure_7_1.{u} (hDG := hDG) (hCC := hCC) (hE := d1)

/-- `ClusterTimeContinuityStmt` from the hypotheses `hL1`, `hDG`, `hCC` of `closure_7_2_derivedInputs36` alone:
the hypothesis `hE` of that declaration is not used. -/
theorem closure_7_2_derivedInputs39
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange.{u} P γ α₀ hC hcirc) :
    ClusterTimeContinuityStmt.{u} := by
  have d1 := HarmonicBalls.lqgMeasureExistence_forall_field.{u}
  exact HarmonicBalls.Closure.closure_7_2_derivedInputs36.{u} (hL1 := hL1) (hDG := hDG) (hCC := hCC) (hE := d1)

/-- `BoundaryMeasureZeroOfCompactClusterStmt` from the hypotheses `hL1`, `hDG`, `hCC` of `closure_8_1_derivedInputs36` alone:
the hypothesis `hE` of that declaration is not used. -/
theorem closure_8_1_derivedInputs39
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange.{u} P γ α₀ hC hcirc) :
    BoundaryMeasureZeroOfCompactClusterStmt.{u} := by
  have d1 := HarmonicBalls.lqgMeasureExistence_forall_field.{u}
  exact HarmonicBalls.Closure.closure_8_1_derivedInputs36.{u} (hL1 := hL1) (hDG := hDG) (hCC := hCC) (hE := d1)

/-- `OriginManyGoodScalesStmt` from the hypotheses `hholder`, `hDG`, `hN`, `hCC` of `closure_8_3_derivedInputs35` alone:
the hypothesis `hE` of that declaration is not used. -/
theorem closure_8_3_derivedInputs39
    (hholder : GreenPotentialHolderStmt.{u})
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic.{u} P γ α₀ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange.{u} P γ α₀ hC hcirc) :
    OriginManyGoodScalesStmt.{u} := by
  have d1 := HarmonicBalls.lqgMeasureExistence_forall_field.{u}
  exact HarmonicBalls.Closure.closure_8_3_derivedInputs35.{u} (hholder := hholder) (hDG := hDG) (hN := hN) (hCC := hCC) (hE := d1)

/-- `HarmonicBallComplementBoundaryJordanStmt` from the hypotheses `hL1`, `hDG`, `hCC`, `hTor` of `closure_10_7_derivedInputs36` alone:
the hypothesis `hE` of that declaration is not used. -/
theorem closure_10_7_derivedInputs39
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange.{u} P γ α₀ hC hcirc)
    (hTor : TorhorstSimpleLoopFrozen) :
    HarmonicBallComplementBoundaryJordanStmt.{u} := by
  have d1 := HarmonicBalls.lqgMeasureExistence_forall_field.{u}
  exact HarmonicBalls.Closure.closure_10_7_derivedInputs36.{u} (hL1 := hL1) (hDG := hDG) (hCC := hCC) (hE := d1) (hTor := hTor)

/-- `AnnulusMassBoundByHarmonicChainStmt` from the hypotheses `hDG`, `hCC`, `hSub` of `closure_11_6_derivedInputs36` alone:
the hypothesis `hE` of that declaration is not used. -/
theorem closure_11_6_derivedInputs39
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange.{u} P γ α₀ hC hcirc)
    (hSub : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure.{0} ℂ), DMSLemmaA10WholePlaneMarkedSub.{u} P γ hC hcirc μ) :
    AnnulusMassBoundByHarmonicChainStmt.{u} := by
  have d1 := HarmonicBalls.lqgMeasureExistence_forall_field.{u}
  exact HarmonicBalls.Closure.closure_11_6_derivedInputs36.{u} (hDG := hDG) (hCC := hCC) (hE := d1) (hSub := hSub)

/-- `ConeBadEventProbabilityStmt` from the hypotheses `hDG`, `hCC` of `closure_11_8` alone:
the hypothesis `hE` of that declaration is not used. -/
theorem closure_11_8_derivedInputs39
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange.{u} P γ 0 hC hcirc) :
    ConeBadEventProbabilityStmt.{u} := by
  have d1 := HarmonicBalls.lqgMeasureExistence_forall_field.{u}
  exact HarmonicBalls.Closure.closure_11_8.{u} (hDG := hDG) (hCC := hCC) (hE := d1)

/-- `SubharmonicBallUniquenessC51Stmt` from the hypotheses `hSub`, `hDG`, `hCC` of `closure_9_2_derivedInputs36` alone:
the hypothesis `hE` of that declaration is not used. -/
theorem closure_9_2_derivedInputs39
    (hSub : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure.{0} ℂ), DMSLemmaA10WholePlaneMarkedSub.{u} P γ hC hcirc μ)
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange.{u} P γ α₀ hC hcirc) :
    S9c.SubharmonicBallUniquenessC51Stmt.{u} := by
  have d1 := HarmonicBalls.lqgMeasureExistence_forall_field.{u}
  exact HarmonicBalls.Closure.closure_9_2_derivedInputs36.{u} (hSub := hSub) (hDG := hDG) (hCC := hCC) (hE := d1)

end HarmonicBalls.Closure
