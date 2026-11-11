import HarmonicBalls.FirstPass.Phase2.CircleAverageLocalityLinkDerived
import HarmonicBalls.FirstPass.Phase2.DerivedInputs37
import HarmonicBalls.FirstPass.Phase2.DerivedInputs9
import HarmonicBalls.FirstPass.Phase2.InternalMetricClosedDerived
import HarmonicBalls.FirstPass.Phase2.MassFunctionalDerived
import HarmonicBalls.FirstPass.Phase2.PlaneDomainDerived
import HarmonicBalls.FirstPass.Phase2.WeylInternalClosedDerived
import HarmonicBalls.FirstPass.Phase2.WeylScaledEuclideanDerived
import HarmonicBalls.FirstPass.Phase2.WeylShiftedMassDerived
import HarmonicBalls.FirstPass.S11c
import HarmonicBalls.Proofs.Sec3.DerivedInputAssembly
import HarmonicBalls.Proofs.Sec6.ShellDecomposition
import HarmonicBalls.Proofs.Sec9.HarmonicBoundaryAssembly
import HarmonicBalls.Proofs.Sec9.NumberedResultsAssembly
import HarmonicBalls.Proofs.Sec9.RegularOpenEqOfAEEq
import HarmonicBalls.Steps.Sec2.VolumeGrowth

/-!
# Derived-input forms, round 38: unused hypotheses removed

Each theorem below has the conclusion of the declaration named in its docstring and a subset of its hypotheses:
the conclusion already follows from that subset by theorems of this repository. The kept hypotheses are
unchanged; the proofs are chains of applications.

Generated from the types of the wrapped declarations; do not edit by hand.
-/

universe u

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

namespace HarmonicBalls

/-- `HarmonicBallBoundarySubsetStmt` from the hypotheses `hDG`, `hCC`, `hW`, `hE`, `hN` of `firstPass_9_3` alone:
the hypothesis `hAff` of that declaration is not used. -/
theorem firstPass_9_3_derivedInputs38
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange.{u} P γ 0 hC hcirc)
    (hW : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling.{u} P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence.{u} P γ 0 hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic.{u} P γ α₀ hC hcirc) :
    HarmonicBallBoundarySubsetStmt.{u} := by
  have d1 := HarmonicBalls.lqgVolumeGrowthAllScalesStmt_of_five_staged_inputs.{u} (hDG := hDG) (hCC := hCC) (hW := hW) (hE := hE) (hN := hN)
  exact HarmonicBalls.harmonicBallBoundarySubset_of_volumeGrowth.{u} (hI2 := d1)

/-- `RegularOpenEqOfAEEqStmt` from the hypotheses `hDG`, `hCC`, `hW`, `hE`, `hN` of `firstPass_9_4` alone:
the hypothesis `hAff` of that declaration is not used. -/
theorem firstPass_9_4_derivedInputs38
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange.{u} P γ 0 hC hcirc)
    (hW : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling.{u} P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence.{u} P γ 0 hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic.{u} P γ α₀ hC hcirc) :
    RegularOpenEqOfAEEqStmt.{u} := by
  have d1 := HarmonicBalls.lqgVolumeGrowthAllScalesStmt_of_five_staged_inputs.{u} (hDG := hDG) (hCC := hCC) (hW := hW) (hE := hE) (hN := hN)
  have d2 := HarmonicBalls.lqgMeasureFullSupportStmt_of_volumeGrowth.{u} (h := d1)
  exact HarmonicBalls.regularOpenEqOfAEEq.{u} (hI1 := d2)

/-- `SmallMetricDiameterLargeMassStmt` from the hypotheses `hMet`, `hShift`, `hAx`, `h1110` of `firstPass_11_9_derivedInputs37` alone:
the hypotheses `hCM`, `hMass`, `hFD` of that declaration are not used. -/
theorem firstPass_11_9_derivedInputs38
    (hMet : LQGInternalMetricWeylAeMeasurableFrozen.{u})
    (hShift : LQGMetricContinuousShiftFactI.{u})
    (hAx : ∀ (γ ξ α₀ : ℝ) (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMetricFieldAxioms.{u} P γ ξ α₀ hC hcirc)
    (h1110 : SmallMetricDiameterLargeMassSquareStmt.{u}) :
    SmallMetricDiameterLargeMassStmt.{u} := by
  have d1 := HarmonicBalls.DerivedInputs9.cameronMartinGFFMutualAbsCont_derived.{u}
  have d2 := HarmonicBalls.MassFunctionalDerived.lqgMassFunctionalMeasurable_derived.{u}
  have d3 := HarmonicBalls.planeDomainMinusConvexCompactPreconnected_derived
  exact HarmonicBalls.firstPass_11_9_derivedInputs37.{u} (hCM := d1) (hMet := hMet) (hMass := d2) (hShift := hShift) (hFD := d3) (hAx := hAx) (h1110 := h1110)

/-- `PinchThirdEventFaithfulStmt` from the hypotheses `h16`, `hAx`, `hdec` of `firstPass_11_17_corrected_derivedInputs37` alone:
the hypotheses `hCMGFF`, `hF`, `hK1`, `hN2` of that declaration are not used. -/
theorem firstPass_11_17_corrected_derivedInputs38
    (h16 : PinchSecondEventFaithfulStmt.{u})
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hdec : LQGInternalMetricWeylAeMeasurableFrozen.{u}) :
    PinchThirdEventFaithfulStmt.{u} := by
  have d1 := HarmonicBalls.DerivedInputs9.cameronMartinGFFMutualAbsCont_derived.{u}
  have d2 := HarmonicBalls.MassFunctionalDerived.lqgMassFunctionalMeasurable_derived.{u}
  have d3 := HarmonicBalls.internalMetricClosedEqIInfThickening_derived
  have d4 := HarmonicBalls.weylScaledEuclidean_derived
  exact HarmonicBalls.firstPass_11_17_corrected_derivedInputs37.{u} (h16 := h16) (hAx := hAx) (hCMGFF := d1) (hdec := hdec) (hF := d2) (hK1 := d3) (hN2 := d4)

end HarmonicBalls

namespace HarmonicBalls.Closure

/-- `LeastSupersolutionMemStmt` from the hypotheses `hDG`, `hCC`, `hE`, `hN` of `closure_3_1` alone:
the hypotheses `hAff`, `hW` of that declaration are not used. -/
theorem closure_3_1_derivedInputs38
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange.{u} P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence.{u} P γ 0 hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic.{u} P γ α₀ hC hcirc) :
    LeastSupersolutionMemStmt.{u} := by
  exact HarmonicBalls.leastSupersolutionMem_of_remaining_literature.{u} (hDG := hDG) (hCC := hCC) (hE := hE) (hN := hN)

/-- `ClusterOpenLaplacianStmt` from the hypotheses `hDG`, `hCC`, `hE`, `hN` of `closure_3_2` alone:
the hypotheses `hAff`, `hW` of that declaration are not used. -/
theorem closure_3_2_derivedInputs38
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange.{u} P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence.{u} P γ 0 hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic.{u} P γ α₀ hC hcirc) :
    ClusterOpenLaplacianStmt.{u} := by
  exact HarmonicBalls.clusterOpenLaplacian_of_remaining_literature.{u} (hDG := hDG) (hCC := hCC) (hE := hE) (hN := hN)

/-- `ClusterMonotoneStmt` from the hypotheses `hDG`, `hCC`, `hE`, `hN` of `closure_3_3` alone:
the hypotheses `hAff`, `hW` of that declaration are not used. -/
theorem closure_3_3_derivedInputs38
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange.{u} P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence.{u} P γ 0 hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic.{u} P γ α₀ hC hcirc) :
    ClusterMonotoneStmt.{u} := by
  exact HarmonicBalls.clusterMonotone_of_remaining_literature.{u} (hDG := hDG) (hCC := hCC) (hE := hE) (hN := hN)

/-- `ClusterConservationOfMassStmt` from the hypotheses `hDG`, `hCC`, `hE`, `hN` of `closure_3_4` alone:
the hypotheses `hAff`, `hW` of that declaration are not used. -/
theorem closure_3_4_derivedInputs38
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange.{u} P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence.{u} P γ 0 hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic.{u} P γ α₀ hC hcirc) :
    ClusterConservationOfMassStmt.{u} := by
  exact HarmonicBalls.clusterConservationOfMass_of_remaining_literature.{u} (hDG := hDG) (hCC := hCC) (hE := hE) (hN := hN)

/-- `ClusterCompatibilityStmt` from the hypotheses `hDG`, `hCC`, `hE`, `hN` of `closure_3_5` alone:
the hypotheses `hAff`, `hW` of that declaration are not used. -/
theorem closure_3_5_derivedInputs38
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange.{u} P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence.{u} P γ 0 hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic.{u} P γ α₀ hC hcirc) :
    ClusterCompatibilityStmt.{u} := by
  exact HarmonicBalls.clusterCompatibility_of_remaining_literature.{u} (hDG := hDG) (hCC := hCC) (hE := hE) (hN := hN)

/-- `ShellDecompositionStmt` with no hypothesis; the hypotheses `hDG`, `hCC`, `hE` of `closure_6_12` are not used. -/
theorem closure_6_12_derivedInputs38 :
    ShellDecompositionStmt := by
  exact HarmonicBalls.shellDecompositionStmt_proved

end HarmonicBalls.Closure

namespace HarmonicBalls.S11c

/-- `SmallMetricDiameterLargeMassSquareStmt` from the hypotheses `hDC`, `hCM`, `hPos`, `hSupM`, `hFin`, `hFactI`, `hM1`, `hAx` of `firstPass_11_10_derivedInputs17` alone:
the hypothesis `hmeasure` of that declaration is not used. -/
theorem firstPass_11_10_derivedInputs38
    (hDC : DyadicCellDiamSmallFrozen.{u})
    (hCM : CameronMartinEventTransferFrozen.{u})
    (hPos : LQGMeasureSquarePositiveFrozen.{u})
    (hSupM : LQGMetricSupMeasurableFrozen.{u})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{u})
    (hFactI : LQGMetricContinuousShiftFactI.{u})
    (hM1 : WeylShiftedSupMeasurableFrozen.{u})
    (hAx : ∀ (γ ξ α₀ : ℝ) (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMetricFieldAxioms.{u} P γ ξ α₀ hC hcirc) :
    SmallMetricDiameterLargeMassSquareStmt.{u} := by
  have d1 := HarmonicBalls.lqgMeasureSquareMeasurable_derived'.{u}
  have d2 := HarmonicBalls.weylInternalClosed_derived
  have d3 := HarmonicBalls.weylShiftedMassMeasurable_derived.{u}
  exact HarmonicBalls.S11c.firstPass_11_10.{u} (hDC := hDC) (hCM := hCM) (hPos := hPos) (hMassM := d1) (hSupM := hSupM) (hFin := hFin) (hW := d2) (hFactI := hFactI) (hM1 := hM1) (hM2 := d3) (hAx := hAx)

end HarmonicBalls.S11c
