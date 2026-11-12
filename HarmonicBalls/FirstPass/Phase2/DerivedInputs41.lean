import HarmonicBalls.FirstPass.Phase2.CoordChangeHolds
import HarmonicBalls.FirstPass.Phase2.DerivedInputs39
import HarmonicBalls.FirstPass.Phase2.DerivedInputs40

/-!
# Derived-input forms, round 41: unused hypotheses removed

Each theorem below has the conclusion of the declaration named in its docstring and a subset of its hypotheses:
the conclusion already follows from that subset by theorems of this repository. The kept hypotheses are
unchanged; the proofs are chains of applications.

Generated from the types of the wrapped declarations; do not edit by hand.
-/

universe u

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

namespace HarmonicBalls

/-- `TypicalPointManyGoodScalesStmt` from the hypotheses `hSub`, `hDG` of `firstPass_8_2_S8d_noWeyl_derivedInputs39` alone:
the hypothesis `hCC` of that declaration is not used. -/
theorem firstPass_8_2_S8d_noWeyl_derivedInputs41
    (hSub : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure.{0} ℂ), DMSLemmaA10WholePlaneMarkedSub.{u} P γ hC hcirc μ)
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc) :
    TypicalPointManyGoodScalesStmt.{u} := by
  have d1 := HarmonicBalls.lqgMeasureCoordChange_holds.{u}
  exact HarmonicBalls.firstPass_8_2_S8d_noWeyl_derivedInputs39.{u} (hSub := hSub) (hDG := hDG) (hCC := d1)

/-- `HarmonicBallBoundarySubsetStmt` from the hypotheses `hDG` of `firstPass_9_3_derivedInputs39` alone:
the hypothesis `hCC` of that declaration is not used. -/
theorem firstPass_9_3_derivedInputs41
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc) :
    HarmonicBallBoundarySubsetStmt.{u} := by
  exact HarmonicBalls.firstPass_9_3_derivedInputs40.{u} (hDG := hDG)

/-- `RegularOpenEqOfAEEqStmt` from the hypotheses `hDG` of `firstPass_9_4_derivedInputs39` alone:
the hypothesis `hCC` of that declaration is not used. -/
theorem firstPass_9_4_derivedInputs41
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc) :
    RegularOpenEqOfAEEqStmt.{u} := by
  exact HarmonicBalls.firstPass_9_4_derivedInputs40.{u} (hDG := hDG)

/-- `SmallMetricDiameterLargeMassStmt` from the hypotheses `hMet`, `hAx`, `h1110` of `firstPass_11_9_derivedInputs38` alone:
the hypothesis `hShift` of that declaration is not used. -/
theorem firstPass_11_9_derivedInputs41
    (hMet : LQGInternalMetricWeylAeMeasurableFrozen.{u})
    (hAx : ∀ (γ ξ α₀ : ℝ) (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMetricFieldAxioms.{u} P γ ξ α₀ hC hcirc)
    (h1110 : SmallMetricDiameterLargeMassSquareStmt.{u}) :
    SmallMetricDiameterLargeMassStmt.{u} := by
  exact HarmonicBalls.firstPass_11_9_derivedInputs40.{u} (hMet := hMet) (hAx := hAx) (h1110 := h1110)

/-- `SubharmonicBallUniquenessWeakStmt` from the hypotheses `hDG`, `h82` of `firstPass_9_2_corrected` alone:
the hypotheses `hCC`, `hW`, `hE`, `hN` of that declaration are not used. -/
theorem firstPass_9_2_corrected_derivedInputs41
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc)
    (h82 : TypicalPointManyGoodScalesStmt.{u}) :
    SubharmonicBallUniquenessWeakStmt.{u} := by
  exact HarmonicBalls.firstPass_9_2_corrected_derivedInputs40.{u} (hDG := hDG) (h82 := h82)

end HarmonicBalls

namespace HarmonicBalls.Closure

/-- `HarmonicBallLocalSetStmt` from the hypotheses `hL1`, `hDG` of `closure_1_3_derivedInputs39` alone:
the hypothesis `hCC` of that declaration is not used. -/
theorem closure_1_3_derivedInputs41
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc) :
    HarmonicBallLocalSetStmt.{u} := by
  have d1 := HarmonicBalls.lqgMeasureCoordChange_holds.{u}
  exact HarmonicBalls.Closure.closure_1_3_derivedInputs39.{u} (hL1 := hL1) (hDG := hDG) (hCC := d1)

/-- `LeastSupersolutionMemStmt` from the hypotheses `hDG` of `closure_3_1_derivedInputs39` alone:
the hypothesis `hCC` of that declaration is not used. -/
theorem closure_3_1_derivedInputs41
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc) :
    LeastSupersolutionMemStmt.{u} := by
  exact HarmonicBalls.Closure.closure_3_1_derivedInputs40.{u} (hDG := hDG)

/-- `ClusterOpenLaplacianStmt` from the hypotheses `hDG` of `closure_3_2_derivedInputs39` alone:
the hypothesis `hCC` of that declaration is not used. -/
theorem closure_3_2_derivedInputs41
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc) :
    ClusterOpenLaplacianStmt.{u} := by
  exact HarmonicBalls.Closure.closure_3_2_derivedInputs40.{u} (hDG := hDG)

/-- `ClusterMonotoneStmt` from the hypotheses `hDG` of `closure_3_3_derivedInputs39` alone:
the hypothesis `hCC` of that declaration is not used. -/
theorem closure_3_3_derivedInputs41
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc) :
    ClusterMonotoneStmt.{u} := by
  exact HarmonicBalls.Closure.closure_3_3_derivedInputs40.{u} (hDG := hDG)

/-- `ClusterConservationOfMassStmt` from the hypotheses `hDG` of `closure_3_4_derivedInputs39` alone:
the hypothesis `hCC` of that declaration is not used. -/
theorem closure_3_4_derivedInputs41
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc) :
    ClusterConservationOfMassStmt.{u} := by
  exact HarmonicBalls.Closure.closure_3_4_derivedInputs40.{u} (hDG := hDG)

/-- `ClusterCompatibilityStmt` from the hypotheses `hDG` of `closure_3_5_derivedInputs39` alone:
the hypothesis `hCC` of that declaration is not used. -/
theorem closure_3_5_derivedInputs41
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc) :
    ClusterCompatibilityStmt.{u} := by
  exact HarmonicBalls.Closure.closure_3_5_derivedInputs40.{u} (hDG := hDG)

/-- `ClusterLowerBoundStmt` from the hypotheses `hDG` of `closure_4_1_derivedInputs39` alone:
the hypothesis `hCC` of that declaration is not used. -/
theorem closure_4_1_derivedInputs41
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc) :
    ClusterLowerBoundStmt.{u} := by
  exact HarmonicBalls.Closure.closure_4_1_derivedInputs40.{u} (hDG := hDG)

/-- `LeastSupersolutionHolderStmt` from the hypotheses `hDG` of `closure_4_2_derivedInputs39` alone:
the hypothesis `hCC` of that declaration is not used. -/
theorem closure_4_2_derivedInputs41
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc) :
    LeastSupersolutionHolderStmt.{u} := by
  exact HarmonicBalls.Closure.closure_4_2_derivedInputs40.{u} (hDG := hDG)

/-- `ClusterSubharmonicBallStmt` from the hypotheses `hDG` of `closure_4_3_derivedInputs39` alone:
the hypothesis `hCC` of that declaration is not used. -/
theorem closure_4_3_derivedInputs41
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc) :
    ClusterSubharmonicBallStmt.{u} := by
  exact HarmonicBalls.Closure.closure_4_3_derivedInputs40.{u} (hDG := hDG)

/-- `ClusterUpperBoundStmt` from the hypotheses `hDG` of `closure_5_1_derivedInputs39` alone:
the hypothesis `hCC` of that declaration is not used. -/
theorem closure_5_1_derivedInputs41
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc) :
    ClusterUpperBoundStmt.{u} := by
  exact HarmonicBalls.Closure.closure_5_1_derivedInputs40.{u} (hDG := hDG)

/-- `ClusterContinuityStmt` from the hypotheses `hDG`, `hSub` of `closure_5_2_derivedInputs39` alone:
the hypothesis `hCC` of that declaration is not used. -/
theorem closure_5_2_derivedInputs41
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc)
    (hSub : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure.{0} ℂ), DMSLemmaA10WholePlaneMarkedSub.{u} P γ hC hcirc μ) :
    ClusterContinuityStmt.{u} := by
  have d1 := HarmonicBalls.lqgMeasureCoordChange_holds.{u}
  exact HarmonicBalls.Closure.closure_5_2_derivedInputs39.{u} (hDG := hDG) (hCC := d1) (hSub := hSub)

/-- `ClusterBoundaryMeasureZeroStmt` from the hypotheses `hDG`, `hL1` of `closure_5_3_derivedInputs39` alone:
the hypothesis `hCC` of that declaration is not used. -/
theorem closure_5_3_derivedInputs41
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{u}) :
    ClusterBoundaryMeasureZeroStmt.{u} := by
  have d1 := HarmonicBalls.lqgMeasureCoordChange_holds.{u}
  exact HarmonicBalls.Closure.closure_5_3_derivedInputs39.{u} (hDG := hDG) (hCC := d1) (hL1 := hL1)

/-- `RegularizedClusterHarmonicBallsStmt` from the hypotheses `hDG`, `hL1` of `closure_5_4_derivedInputs39` alone:
the hypothesis `hCC` of that declaration is not used. -/
theorem closure_5_4_derivedInputs41
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{u}) :
    RegularizedClusterHarmonicBallsStmt.{u} := by
  have d1 := HarmonicBalls.lqgMeasureCoordChange_holds.{u}
  exact HarmonicBalls.Closure.closure_5_4_derivedInputs39.{u} (hDG := hDG) (hCC := d1) (hL1 := hL1)

/-- `ExistenceHarmonicBallsStmt` from the hypotheses `hDG`, `hL1` of `closure_5_5_derivedInputs39` alone:
the hypothesis `hCC` of that declaration is not used. -/
theorem closure_5_5_derivedInputs41
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{u}) :
    ExistenceHarmonicBallsStmt.{u} := by
  have d1 := HarmonicBalls.lqgMeasureCoordChange_holds.{u}
  exact HarmonicBalls.Closure.closure_5_5_derivedInputs39.{u} (hDG := hDG) (hCC := d1) (hL1 := hL1)

/-- `UniquenessHarmonicBallsStmt` from the hypotheses `hDG` of `closure_5_6_derivedInputs39` alone:
the hypothesis `hCC` of that declaration is not used. -/
theorem closure_5_6_derivedInputs41
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc) :
    UniquenessHarmonicBallsStmt.{u} := by
  exact HarmonicBalls.Closure.closure_5_6_derivedInputs40.{u} (hDG := hDG)

/-- `ClusterScaleInvarianceStmt` from the hypotheses `hDG` of `closure_5_7_derivedInputs39` alone:
the hypothesis `hCC` of that declaration is not used. -/
theorem closure_5_7_derivedInputs41
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc) :
    ClusterScaleInvarianceStmt.{u} := by
  have d1 := HarmonicBalls.lqgMeasureCoordChange_holds.{u}
  exact HarmonicBalls.Closure.closure_5_7_derivedInputs39.{u} (hDG := hDG) (hCC := d1)

/-- `ClusterStrongCompatibilityStmt` from the hypotheses `hDG` of `closure_5_8_derivedInputs39` alone:
the hypothesis `hCC` of that declaration is not used. -/
theorem closure_5_8_derivedInputs41
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc) :
    ClusterStrongCompatibilityStmt.{u} := by
  exact HarmonicBalls.Closure.closure_5_8_derivedInputs40.{u} (hDG := hDG)

/-- `HarnackTypeEstimateStmt` from the hypotheses `hDG` of `closure_6_1_derivedInputs39` alone:
the hypothesis `hCC` of that declaration is not used. -/
theorem closure_6_1_derivedInputs41
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc) :
    HarnackTypeEstimateStmt.{u} := by
  exact HarmonicBalls.Closure.closure_6_1_derivedInputs40.{u} (hDG := hDG)

/-- `HarnackTypeComponentStmt` from the hypotheses `hDG` of `closure_6_2_derivedInputs39` alone:
the hypothesis `hCC` of that declaration is not used. -/
theorem closure_6_2_derivedInputs41
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc) :
    HarnackTypeComponentStmt.{u} := by
  exact HarmonicBalls.Closure.closure_6_2_derivedInputs40.{u} (hDG := hDG)

/-- `ManyGoodAnnuliStmt` from the hypotheses `hDG` of `closure_6_3_derivedInputs39` alone:
the hypothesis `hCC` of that declaration is not used. -/
theorem closure_6_3_derivedInputs41
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc) :
    ManyGoodAnnuliStmt.{u} := by
  exact HarmonicBalls.Closure.closure_6_3_derivedInputs40.{u} (hDG := hDG)

/-- `GoodAnnulusProbabilityStmt` from the hypotheses `hDG` of `closure_6_4_derivedInputs39` alone:
the hypothesis `hCC` of that declaration is not used. -/
theorem closure_6_4_derivedInputs41
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc) :
    GoodAnnulusProbabilityStmt.{u} := by
  exact HarmonicBalls.Closure.closure_6_4_derivedInputs40.{u} (hDG := hDG)

/-- `ManyVeryGoodAnnuliStmt` from the hypotheses `hDG` of `closure_6_6_derivedInputs39` alone:
the hypothesis `hCC` of that declaration is not used. -/
theorem closure_6_6_derivedInputs41
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc) :
    ManyVeryGoodAnnuliStmt.{u} := by
  exact HarmonicBalls.Closure.closure_6_6_derivedInputs40.{u} (hDG := hDG)

/-- `VeryGoodAnnulusProbabilityStmt` from the hypotheses `hDG` of `closure_6_7_derivedInputs39` alone:
the hypothesis `hCC` of that declaration is not used. -/
theorem closure_6_7_derivedInputs41
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc) :
    VeryGoodAnnulusProbabilityStmt.{u} := by
  exact HarmonicBalls.Closure.closure_6_7_derivedInputs40.{u} (hDG := hDG)

/-- `AnnulusMassBoundByOdometerStmt` from the hypotheses `hDG` of `closure_6_8_derivedInputs39` alone:
the hypothesis `hCC` of that declaration is not used. -/
theorem closure_6_8_derivedInputs41
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc) :
    AnnulusMassBoundByOdometerStmt.{u} := by
  exact HarmonicBalls.Closure.closure_6_8_derivedInputs40.{u} (hDG := hDG)

/-- `OdometerHarmonicMeasureBoundStmt` from the hypotheses `hDG` of `closure_6_9_derivedInputs39` alone:
the hypothesis `hCC` of that declaration is not used. -/
theorem closure_6_9_derivedInputs41
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc) :
    OdometerHarmonicMeasureBoundStmt.{u} := by
  exact HarmonicBalls.Closure.closure_6_9_derivedInputs40.{u} (hDG := hDG)

/-- `OdometerBoundByAnnulusMassStmt` from the hypotheses `hDG` of `closure_6_10_derivedInputs39` alone:
the hypothesis `hCC` of that declaration is not used. -/
theorem closure_6_10_derivedInputs41
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc) :
    OdometerBoundByAnnulusMassStmt.{u} := by
  exact HarmonicBalls.Closure.closure_6_10_derivedInputs40.{u} (hDG := hDG)

/-- `VeryGoodAnnulusHarnackTypeStmt` from the hypotheses `hDG` of `closure_6_11_derivedInputs39` alone:
the hypothesis `hCC` of that declaration is not used. -/
theorem closure_6_11_derivedInputs41
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc) :
    VeryGoodAnnulusHarnackTypeStmt.{u} := by
  exact HarmonicBalls.Closure.closure_6_11_derivedInputs40.{u} (hDG := hDG)

/-- `LowMassSmallOdometerStmt` from the hypotheses `hDG` of `closure_6_13_derivedInputs39` alone:
the hypothesis `hCC` of that declaration is not used. -/
theorem closure_6_13_derivedInputs41
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc) :
    LowMassSmallOdometerStmt.{u} := by
  exact HarmonicBalls.Closure.closure_6_13_derivedInputs40.{u} (hDG := hDG)

/-- `ClusterUpperBoundPolyHighProbStmt` from the hypotheses `hDG` of `closure_7_1_derivedInputs39` alone:
the hypothesis `hCC` of that declaration is not used. -/
theorem closure_7_1_derivedInputs41
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc) :
    ClusterUpperBoundPolyHighProbStmt.{u} := by
  exact HarmonicBalls.Closure.closure_7_1_derivedInputs40.{u} (hDG := hDG)

/-- `ClusterTimeContinuityStmt` from the hypotheses `hL1`, `hDG` of `closure_7_2_derivedInputs39` alone:
the hypothesis `hCC` of that declaration is not used. -/
theorem closure_7_2_derivedInputs41
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc) :
    ClusterTimeContinuityStmt.{u} := by
  have d1 := HarmonicBalls.lqgMeasureCoordChange_holds.{u}
  exact HarmonicBalls.Closure.closure_7_2_derivedInputs39.{u} (hL1 := hL1) (hDG := hDG) (hCC := d1)

/-- `BoundaryMeasureZeroOfCompactClusterStmt` from the hypotheses `hL1`, `hDG` of `closure_8_1_derivedInputs39` alone:
the hypothesis `hCC` of that declaration is not used. -/
theorem closure_8_1_derivedInputs41
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc) :
    BoundaryMeasureZeroOfCompactClusterStmt.{u} := by
  have d1 := HarmonicBalls.lqgMeasureCoordChange_holds.{u}
  exact HarmonicBalls.Closure.closure_8_1_derivedInputs39.{u} (hL1 := hL1) (hDG := hDG) (hCC := d1)

/-- `OriginManyGoodScalesStmt` from the hypotheses `hholder`, `hDG`, `hN` of `closure_8_3_derivedInputs39` alone:
the hypothesis `hCC` of that declaration is not used. -/
theorem closure_8_3_derivedInputs41
    (hholder : GreenPotentialHolderStmt.{u})
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic.{u} P γ α₀ hC hcirc) :
    OriginManyGoodScalesStmt.{u} := by
  have d1 := HarmonicBalls.lqgMeasureCoordChange_holds.{u}
  exact HarmonicBalls.Closure.closure_8_3_derivedInputs39.{u} (hholder := hholder) (hDG := hDG) (hN := hN) (hCC := d1)

/-- `HarmonicBallComplementBoundaryJordanStmt` from the hypotheses `hL1`, `hDG`, `hTor` of `closure_10_7_derivedInputs39` alone:
the hypothesis `hCC` of that declaration is not used. -/
theorem closure_10_7_derivedInputs41
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc)
    (hTor : TorhorstSimpleLoopFrozen) :
    HarmonicBallComplementBoundaryJordanStmt.{u} := by
  have d1 := HarmonicBalls.lqgMeasureCoordChange_holds.{u}
  exact HarmonicBalls.Closure.closure_10_7_derivedInputs39.{u} (hL1 := hL1) (hDG := hDG) (hCC := d1) (hTor := hTor)

/-- `AnnulusMassBoundByHarmonicChainStmt` from the hypotheses `hDG`, `hSub` of `closure_11_6_derivedInputs39` alone:
the hypothesis `hCC` of that declaration is not used. -/
theorem closure_11_6_derivedInputs41
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc)
    (hSub : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure.{0} ℂ), DMSLemmaA10WholePlaneMarkedSub.{u} P γ hC hcirc μ) :
    AnnulusMassBoundByHarmonicChainStmt.{u} := by
  have d1 := HarmonicBalls.lqgMeasureCoordChange_holds.{u}
  exact HarmonicBalls.Closure.closure_11_6_derivedInputs39.{u} (hDG := hDG) (hCC := d1) (hSub := hSub)

/-- `ConeBadEventProbabilityStmt` from the hypotheses `hDG` of `closure_11_8_derivedInputs39` alone:
the hypothesis `hCC` of that declaration is not used. -/
theorem closure_11_8_derivedInputs41
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc) :
    ConeBadEventProbabilityStmt.{u} := by
  exact HarmonicBalls.Closure.closure_11_8_derivedInputs40.{u} (hDG := hDG)

/-- `SubharmonicBallUniquenessC51Stmt` from the hypotheses `hSub`, `hDG` of `closure_9_2_derivedInputs39` alone:
the hypothesis `hCC` of that declaration is not used. -/
theorem closure_9_2_derivedInputs41
    (hSub : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure.{0} ℂ), DMSLemmaA10WholePlaneMarkedSub.{u} P γ hC hcirc μ)
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc) :
    S9c.SubharmonicBallUniquenessC51Stmt.{u} := by
  have d1 := HarmonicBalls.lqgMeasureCoordChange_holds.{u}
  exact HarmonicBalls.Closure.closure_9_2_derivedInputs39.{u} (hSub := hSub) (hDG := hDG) (hCC := d1)

end HarmonicBalls.Closure

namespace HarmonicBalls.S11c

/-- `SmallMetricDiameterLargeMassSquareStmt` from the hypotheses `hDC`, `hCM`, `hPos`, `hFin`, `hM1`, `hAx` of `firstPass_11_10_derivedInputs38` alone:
the hypotheses `hSupM`, `hFactI` of that declaration are not used. -/
theorem firstPass_11_10_derivedInputs41
    (hDC : DyadicCellDiamSmallFrozen.{u})
    (hCM : CameronMartinEventTransferFrozen.{u})
    (hPos : LQGMeasureSquarePositiveFrozen.{u})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{u})
    (hM1 : WeylShiftedSupMeasurableFrozen.{u})
    (hAx : ∀ (γ ξ α₀ : ℝ) (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMetricFieldAxioms.{u} P γ ξ α₀ hC hcirc) :
    SmallMetricDiameterLargeMassSquareStmt.{u} := by
  exact HarmonicBalls.S11c.firstPass_11_10_derivedInputs40.{u} (hDC := hDC) (hCM := hCM) (hPos := hPos) (hFin := hFin) (hM1 := hM1) (hAx := hAx)

end HarmonicBalls.S11c
