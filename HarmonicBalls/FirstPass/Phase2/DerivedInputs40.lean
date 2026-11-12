import HarmonicBalls.FirstPass.Phase2.CoordChangeZeroHolds
import HarmonicBalls.FirstPass.Phase2.DerivedInputs39
import HarmonicBalls.FirstPass.Phase2.DerivedInputsContinuousShift
import HarmonicBalls.FirstPass.Phase2.LQGMeasureExistenceDerived
import HarmonicBalls.FirstPass.Phase2.SupMeasurableDerived
import HarmonicBalls.FirstPass.S5S7S8

/-!
# Derived-input forms, round 40: unused hypotheses removed

Each theorem below has the conclusion of the declaration named in its docstring and a subset of its hypotheses:
the conclusion already follows from that subset by theorems of this repository. The kept hypotheses are
unchanged; the proofs are chains of applications.

Generated from the types of the wrapped declarations; do not edit by hand.
-/

universe u

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

namespace HarmonicBalls

/-- `HarmonicBallBoundarySubsetStmt` from the hypotheses `hDG` of `firstPass_9_3_derivedInputs39` alone:
the hypothesis `hCC` of that declaration is not used. -/
theorem firstPass_9_3_derivedInputs40
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc) :
    HarmonicBallBoundarySubsetStmt.{u} := by
  have d1 := HarmonicBalls.lqgMeasureCoordChange_zero_holds.{u}
  exact HarmonicBalls.firstPass_9_3_derivedInputs39.{u} (hDG := hDG) (hCC := d1)

/-- `RegularOpenEqOfAEEqStmt` from the hypotheses `hDG` of `firstPass_9_4_derivedInputs39` alone:
the hypothesis `hCC` of that declaration is not used. -/
theorem firstPass_9_4_derivedInputs40
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc) :
    RegularOpenEqOfAEEqStmt.{u} := by
  have d1 := HarmonicBalls.lqgMeasureCoordChange_zero_holds.{u}
  exact HarmonicBalls.firstPass_9_4_derivedInputs39.{u} (hDG := hDG) (hCC := d1)

/-- `SmallMetricDiameterLargeMassStmt` from the hypotheses `hMet`, `hAx`, `h1110` of `firstPass_11_9_derivedInputs38` alone:
the hypothesis `hShift` of that declaration is not used. -/
theorem firstPass_11_9_derivedInputs40
    (hMet : LQGInternalMetricWeylAeMeasurableFrozen.{u})
    (hAx : ∀ (γ ξ α₀ : ℝ) (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMetricFieldAxioms.{u} P γ ξ α₀ hC hcirc)
    (h1110 : SmallMetricDiameterLargeMassSquareStmt.{u}) :
    SmallMetricDiameterLargeMassStmt.{u} := by
  exact HarmonicBalls.firstPass_11_9_derivedInputsContinuousShift.{u} (hMet := hMet) (hAx := hAx) (h1110 := h1110)

/-- `SubharmonicBallUniquenessWeakStmt` from the hypotheses `hDG`, `h82` of `firstPass_9_2_corrected` alone:
the hypotheses `hCC`, `hW`, `hE`, `hN` of that declaration are not used. -/
theorem firstPass_9_2_corrected_derivedInputs40
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc)
    (h82 : TypicalPointManyGoodScalesStmt.{u}) :
    SubharmonicBallUniquenessWeakStmt.{u} := by
  have d1 := HarmonicBalls.lqgMeasureCoordChange_zero_holds.{u}
  exact HarmonicBalls.firstPass_9_2_corrected_derivedInputs39.{u} (hDG := hDG) (hCC := d1) (h82 := h82)

end HarmonicBalls

namespace HarmonicBalls.Closure

/-- `LeastSupersolutionMemStmt` from the hypotheses `hDG` of `closure_3_1_derivedInputs39` alone:
the hypothesis `hCC` of that declaration is not used. -/
theorem closure_3_1_derivedInputs40
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc) :
    LeastSupersolutionMemStmt.{u} := by
  have d1 := HarmonicBalls.lqgMeasureCoordChange_zero_holds.{u}
  exact HarmonicBalls.Closure.closure_3_1_derivedInputs39.{u} (hDG := hDG) (hCC := d1)

/-- `ClusterOpenLaplacianStmt` from the hypotheses `hDG` of `closure_3_2_derivedInputs39` alone:
the hypothesis `hCC` of that declaration is not used. -/
theorem closure_3_2_derivedInputs40
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc) :
    ClusterOpenLaplacianStmt.{u} := by
  have d1 := HarmonicBalls.lqgMeasureCoordChange_zero_holds.{u}
  exact HarmonicBalls.Closure.closure_3_2_derivedInputs39.{u} (hDG := hDG) (hCC := d1)

/-- `ClusterMonotoneStmt` from the hypotheses `hDG` of `closure_3_3_derivedInputs39` alone:
the hypothesis `hCC` of that declaration is not used. -/
theorem closure_3_3_derivedInputs40
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc) :
    ClusterMonotoneStmt.{u} := by
  have d1 := HarmonicBalls.lqgMeasureCoordChange_zero_holds.{u}
  exact HarmonicBalls.Closure.closure_3_3_derivedInputs39.{u} (hDG := hDG) (hCC := d1)

/-- `ClusterConservationOfMassStmt` from the hypotheses `hDG` of `closure_3_4_derivedInputs39` alone:
the hypothesis `hCC` of that declaration is not used. -/
theorem closure_3_4_derivedInputs40
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc) :
    ClusterConservationOfMassStmt.{u} := by
  have d1 := HarmonicBalls.lqgMeasureCoordChange_zero_holds.{u}
  exact HarmonicBalls.Closure.closure_3_4_derivedInputs39.{u} (hDG := hDG) (hCC := d1)

/-- `ClusterCompatibilityStmt` from the hypotheses `hDG` of `closure_3_5_derivedInputs39` alone:
the hypothesis `hCC` of that declaration is not used. -/
theorem closure_3_5_derivedInputs40
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc) :
    ClusterCompatibilityStmt.{u} := by
  have d1 := HarmonicBalls.lqgMeasureCoordChange_zero_holds.{u}
  exact HarmonicBalls.Closure.closure_3_5_derivedInputs39.{u} (hDG := hDG) (hCC := d1)

/-- `ClusterLowerBoundStmt` from the hypotheses `hDG` of `closure_4_1_derivedInputs39` alone:
the hypothesis `hCC` of that declaration is not used. -/
theorem closure_4_1_derivedInputs40
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc) :
    ClusterLowerBoundStmt.{u} := by
  have d1 := HarmonicBalls.lqgMeasureCoordChange_zero_holds.{u}
  exact HarmonicBalls.Closure.closure_4_1_derivedInputs39.{u} (hDG := hDG) (hCC := d1)

/-- `LeastSupersolutionHolderStmt` from the hypotheses `hDG` of `closure_4_2_derivedInputs39` alone:
the hypothesis `hCC` of that declaration is not used. -/
theorem closure_4_2_derivedInputs40
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc) :
    LeastSupersolutionHolderStmt.{u} := by
  have d1 := HarmonicBalls.lqgMeasureCoordChange_zero_holds.{u}
  exact HarmonicBalls.Closure.closure_4_2_derivedInputs39.{u} (hDG := hDG) (hCC := d1)

/-- `ClusterSubharmonicBallStmt` from the hypotheses `hDG` of `closure_4_3_derivedInputs39` alone:
the hypothesis `hCC` of that declaration is not used. -/
theorem closure_4_3_derivedInputs40
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc) :
    ClusterSubharmonicBallStmt.{u} := by
  have d1 := HarmonicBalls.lqgMeasureCoordChange_zero_holds.{u}
  exact HarmonicBalls.Closure.closure_4_3_derivedInputs39.{u} (hDG := hDG) (hCC := d1)

/-- `ClusterUpperBoundStmt` from the hypotheses `hDG` of `closure_5_1_derivedInputs39` alone:
the hypothesis `hCC` of that declaration is not used. -/
theorem closure_5_1_derivedInputs40
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc) :
    ClusterUpperBoundStmt.{u} := by
  have d1 := HarmonicBalls.lqgMeasureCoordChange_zero_holds.{u}
  exact HarmonicBalls.Closure.closure_5_1_derivedInputs39.{u} (hDG := hDG) (hCC := d1)

/-- `UniquenessHarmonicBallsStmt` from the hypotheses `hDG` of `closure_5_6_derivedInputs39` alone:
the hypothesis `hCC` of that declaration is not used. -/
theorem closure_5_6_derivedInputs40
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc) :
    UniquenessHarmonicBallsStmt.{u} := by
  have d1 := HarmonicBalls.lqgMeasureCoordChange_zero_holds.{u}
  exact HarmonicBalls.Closure.closure_5_6_derivedInputs39.{u} (hDG := hDG) (hCC := d1)

/-- `ClusterStrongCompatibilityStmt` from the hypotheses `hDG` of `closure_5_8_derivedInputs39` alone:
the hypothesis `hCC` of that declaration is not used. -/
theorem closure_5_8_derivedInputs40
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc) :
    ClusterStrongCompatibilityStmt.{u} := by
  have d1 := HarmonicBalls.lqgMeasureCoordChange_zero_holds.{u}
  exact HarmonicBalls.Closure.closure_5_8_derivedInputs39.{u} (hDG := hDG) (hCC := d1)

/-- `HarnackTypeEstimateStmt` from the hypotheses `hDG` of `closure_6_1_derivedInputs39` alone:
the hypothesis `hCC` of that declaration is not used. -/
theorem closure_6_1_derivedInputs40
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc) :
    HarnackTypeEstimateStmt.{u} := by
  have d1 := HarmonicBalls.lqgMeasureCoordChange_zero_holds.{u}
  exact HarmonicBalls.Closure.closure_6_1_derivedInputs39.{u} (hDG := hDG) (hCC := d1)

/-- `HarnackTypeComponentStmt` from the hypotheses `hDG` of `closure_6_2_derivedInputs39` alone:
the hypothesis `hCC` of that declaration is not used. -/
theorem closure_6_2_derivedInputs40
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc) :
    HarnackTypeComponentStmt.{u} := by
  have d1 := HarmonicBalls.lqgMeasureCoordChange_zero_holds.{u}
  exact HarmonicBalls.Closure.closure_6_2_derivedInputs39.{u} (hDG := hDG) (hCC := d1)

/-- `ManyGoodAnnuliStmt` from the hypotheses `hDG` of `closure_6_3_derivedInputs39` alone:
the hypothesis `hCC` of that declaration is not used. -/
theorem closure_6_3_derivedInputs40
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc) :
    ManyGoodAnnuliStmt.{u} := by
  have d1 := HarmonicBalls.lqgMeasureCoordChange_zero_holds.{u}
  exact HarmonicBalls.Closure.closure_6_3_derivedInputs39.{u} (hDG := hDG) (hCC := d1)

/-- `GoodAnnulusProbabilityStmt` from the hypotheses `hDG` of `closure_6_4_derivedInputs39` alone:
the hypothesis `hCC` of that declaration is not used. -/
theorem closure_6_4_derivedInputs40
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc) :
    GoodAnnulusProbabilityStmt.{u} := by
  have d1 := HarmonicBalls.lqgMeasureCoordChange_zero_holds.{u}
  exact HarmonicBalls.Closure.closure_6_4_derivedInputs39.{u} (hDG := hDG) (hCC := d1)

/-- `ManyVeryGoodAnnuliStmt` from the hypotheses `hDG` of `closure_6_6_derivedInputs39` alone:
the hypothesis `hCC` of that declaration is not used. -/
theorem closure_6_6_derivedInputs40
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc) :
    ManyVeryGoodAnnuliStmt.{u} := by
  have d1 := HarmonicBalls.lqgMeasureCoordChange_zero_holds.{u}
  exact HarmonicBalls.Closure.closure_6_6_derivedInputs39.{u} (hDG := hDG) (hCC := d1)

/-- `VeryGoodAnnulusProbabilityStmt` from the hypotheses `hDG` of `closure_6_7_derivedInputs39` alone:
the hypothesis `hCC` of that declaration is not used. -/
theorem closure_6_7_derivedInputs40
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc) :
    VeryGoodAnnulusProbabilityStmt.{u} := by
  have d1 := HarmonicBalls.lqgMeasureCoordChange_zero_holds.{u}
  exact HarmonicBalls.Closure.closure_6_7_derivedInputs39.{u} (hDG := hDG) (hCC := d1)

/-- `AnnulusMassBoundByOdometerStmt` from the hypotheses `hDG` of `closure_6_8_derivedInputs39` alone:
the hypothesis `hCC` of that declaration is not used. -/
theorem closure_6_8_derivedInputs40
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc) :
    AnnulusMassBoundByOdometerStmt.{u} := by
  have d1 := HarmonicBalls.lqgMeasureCoordChange_zero_holds.{u}
  exact HarmonicBalls.Closure.closure_6_8_derivedInputs39.{u} (hDG := hDG) (hCC := d1)

/-- `OdometerHarmonicMeasureBoundStmt` from the hypotheses `hDG` of `closure_6_9_derivedInputs39` alone:
the hypothesis `hCC` of that declaration is not used. -/
theorem closure_6_9_derivedInputs40
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc) :
    OdometerHarmonicMeasureBoundStmt.{u} := by
  have d1 := HarmonicBalls.lqgMeasureCoordChange_zero_holds.{u}
  exact HarmonicBalls.Closure.closure_6_9_derivedInputs39.{u} (hDG := hDG) (hCC := d1)

/-- `OdometerBoundByAnnulusMassStmt` from the hypotheses `hDG` of `closure_6_10_derivedInputs39` alone:
the hypothesis `hCC` of that declaration is not used. -/
theorem closure_6_10_derivedInputs40
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc) :
    OdometerBoundByAnnulusMassStmt.{u} := by
  have d1 := HarmonicBalls.lqgMeasureCoordChange_zero_holds.{u}
  exact HarmonicBalls.Closure.closure_6_10_derivedInputs39.{u} (hDG := hDG) (hCC := d1)

/-- `VeryGoodAnnulusHarnackTypeStmt` from the hypotheses `hDG` of `closure_6_11_derivedInputs39` alone:
the hypothesis `hCC` of that declaration is not used. -/
theorem closure_6_11_derivedInputs40
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc) :
    VeryGoodAnnulusHarnackTypeStmt.{u} := by
  have d1 := HarmonicBalls.lqgMeasureCoordChange_zero_holds.{u}
  exact HarmonicBalls.Closure.closure_6_11_derivedInputs39.{u} (hDG := hDG) (hCC := d1)

/-- `LowMassSmallOdometerStmt` from the hypotheses `hDG` of `closure_6_13_derivedInputs39` alone:
the hypothesis `hCC` of that declaration is not used. -/
theorem closure_6_13_derivedInputs40
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc) :
    LowMassSmallOdometerStmt.{u} := by
  have d1 := HarmonicBalls.lqgMeasureCoordChange_zero_holds.{u}
  exact HarmonicBalls.Closure.closure_6_13_derivedInputs39.{u} (hDG := hDG) (hCC := d1)

/-- `ClusterUpperBoundPolyHighProbStmt` from the hypotheses `hDG` of `closure_7_1_derivedInputs39` alone:
the hypothesis `hCC` of that declaration is not used. -/
theorem closure_7_1_derivedInputs40
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc) :
    ClusterUpperBoundPolyHighProbStmt.{u} := by
  have d1 := HarmonicBalls.lqgMeasureCoordChange_zero_holds.{u}
  have d2 := HarmonicBalls.lqgMeasureExistence_forall_field.{u}
  exact HarmonicBalls.firstPass_7_1.{u} (hDG := hDG) (hCC := d1) (hE := d2)

/-- `ConeBadEventProbabilityStmt` from the hypotheses `hDG` of `closure_11_8_derivedInputs39` alone:
the hypothesis `hCC` of that declaration is not used. -/
theorem closure_11_8_derivedInputs40
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc) :
    ConeBadEventProbabilityStmt.{u} := by
  have d1 := HarmonicBalls.lqgMeasureCoordChange_zero_holds.{u}
  exact HarmonicBalls.Closure.closure_11_8_derivedInputs39.{u} (hDG := hDG) (hCC := d1)

end HarmonicBalls.Closure

namespace HarmonicBalls.S11c

/-- `SmallMetricDiameterLargeMassSquareStmt` from the hypotheses `hDC`, `hCM`, `hPos`, `hFin`, `hM1`, `hAx` of `firstPass_11_10_derivedInputs38` alone:
the hypotheses `hSupM`, `hFactI` of that declaration are not used. -/
theorem firstPass_11_10_derivedInputs40
    (hDC : DyadicCellDiamSmallFrozen.{u})
    (hCM : CameronMartinEventTransferFrozen.{u})
    (hPos : LQGMeasureSquarePositiveFrozen.{u})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{u})
    (hM1 : WeylShiftedSupMeasurableFrozen.{u})
    (hAx : ∀ (γ ξ α₀ : ℝ) (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMetricFieldAxioms.{u} P γ ξ α₀ hC hcirc) :
    SmallMetricDiameterLargeMassSquareStmt.{u} := by
  exact HarmonicBalls.S11c.firstPass_11_10_derivedInputsSupMeasurable.{u} (hDC := hDC) (hCM := hCM) (hPos := hPos) (hFin := hFin) (hM1 := hM1) (hAx := hAx)

end HarmonicBalls.S11c
