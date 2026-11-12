import HarmonicBalls.FirstPass.Phase2.DerivedInputs41
import HarmonicBalls.FirstPass.Phase2.CampbellDerivedWrappers

/-!
# Counted forms with the marked Campbell identity supplied

The counted forms of `DerivedInputs41.lean` that still take the marked whole-plane clause of
Duplantier-Miller-Sheffield, arXiv:1409.7055v4, Lemma A.10 (`hSub`), or its consequence the rooted
field-measure domination `LocalRootedFieldMeasureDomination` (`hL1`, FirstPass/Frozen/S8c.lean:51), as a
hypothesis. Both are theorems (`CampbellDerivedWrappers.lean`: `dmsLemmaA10WholePlaneMarkedSub_forall`,
`localRootedFieldMeasureDomination_holds`). Each theorem below has the conclusion of the counted form named in
its docstring and the remaining hypotheses of that form, unchanged; the counted forms and the frozen statements
are not modified.
-/

universe u

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

namespace HarmonicBalls

/-- Result 8.2 (`TypicalPointManyGoodScalesStmt.{u}`) without the hypothesis `hSub`: the marked whole-plane Lemma A.10 of Duplantier-Miller-Sheffield `DMSLemmaA10WholePlaneMarkedSub` is supplied by `dmsLemmaA10WholePlaneMarkedSub_forall`.
The kept hypotheses are those of `HarmonicBalls.firstPass_8_2_S8d_noWeyl_derivedInputs41`, unchanged. -/
theorem firstPass_8_2_S8d_noWeyl_derivedInputsCampbell
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc) :
    TypicalPointManyGoodScalesStmt.{u} :=
  HarmonicBalls.firstPass_8_2_S8d_noWeyl_derivedInputs41 (hSub := dmsLemmaA10WholePlaneMarkedSub_forall.{u}) (hDG := hDG)

end HarmonicBalls

namespace HarmonicBalls.Closure

/-- Result 1.3 (`HarmonicBallLocalSetStmt.{u}`) without the hypothesis `hL1`: the rooted field-measure domination `LocalRootedFieldMeasureDomination` is supplied by `localRootedFieldMeasureDomination_holds`.
The kept hypotheses are those of `HarmonicBalls.Closure.closure_1_3_derivedInputs41`, unchanged. -/
theorem closure_1_3_derivedInputsCampbell
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc) :
    HarmonicBallLocalSetStmt.{u} :=
  HarmonicBalls.Closure.closure_1_3_derivedInputs41 (hL1 := localRootedFieldMeasureDomination_holds.{u}) (hDG := hDG)

/-- Result 5.2 (`ClusterContinuityStmt.{u}`) without the hypothesis `hSub`: the marked whole-plane Lemma A.10 of Duplantier-Miller-Sheffield `DMSLemmaA10WholePlaneMarkedSub` is supplied by `dmsLemmaA10WholePlaneMarkedSub_forall`.
The kept hypotheses are those of `HarmonicBalls.Closure.closure_5_2_derivedInputs41`, unchanged. -/
theorem closure_5_2_derivedInputsCampbell
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc) :
    ClusterContinuityStmt.{u} :=
  HarmonicBalls.Closure.closure_5_2_derivedInputs41 (hSub := dmsLemmaA10WholePlaneMarkedSub_forall.{u}) (hDG := hDG)

/-- Result 5.3 (`ClusterBoundaryMeasureZeroStmt.{u}`) without the hypothesis `hL1`: the rooted field-measure domination `LocalRootedFieldMeasureDomination` is supplied by `localRootedFieldMeasureDomination_holds`.
The kept hypotheses are those of `HarmonicBalls.Closure.closure_5_3_derivedInputs41`, unchanged. -/
theorem closure_5_3_derivedInputsCampbell
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc) :
    ClusterBoundaryMeasureZeroStmt.{u} :=
  HarmonicBalls.Closure.closure_5_3_derivedInputs41 (hL1 := localRootedFieldMeasureDomination_holds.{u}) (hDG := hDG)

/-- Result 5.4 (`RegularizedClusterHarmonicBallsStmt.{u}`) without the hypothesis `hL1`: the rooted field-measure domination `LocalRootedFieldMeasureDomination` is supplied by `localRootedFieldMeasureDomination_holds`.
The kept hypotheses are those of `HarmonicBalls.Closure.closure_5_4_derivedInputs41`, unchanged. -/
theorem closure_5_4_derivedInputsCampbell
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc) :
    RegularizedClusterHarmonicBallsStmt.{u} :=
  HarmonicBalls.Closure.closure_5_4_derivedInputs41 (hL1 := localRootedFieldMeasureDomination_holds.{u}) (hDG := hDG)

/-- Result 5.5 (`ExistenceHarmonicBallsStmt.{u}`) without the hypothesis `hL1`: the rooted field-measure domination `LocalRootedFieldMeasureDomination` is supplied by `localRootedFieldMeasureDomination_holds`.
The kept hypotheses are those of `HarmonicBalls.Closure.closure_5_5_derivedInputs41`, unchanged. -/
theorem closure_5_5_derivedInputsCampbell
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc) :
    ExistenceHarmonicBallsStmt.{u} :=
  HarmonicBalls.Closure.closure_5_5_derivedInputs41 (hL1 := localRootedFieldMeasureDomination_holds.{u}) (hDG := hDG)

/-- Result 7.2 (`ClusterTimeContinuityStmt.{u}`) without the hypothesis `hL1`: the rooted field-measure domination `LocalRootedFieldMeasureDomination` is supplied by `localRootedFieldMeasureDomination_holds`.
The kept hypotheses are those of `HarmonicBalls.Closure.closure_7_2_derivedInputs41`, unchanged. -/
theorem closure_7_2_derivedInputsCampbell
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc) :
    ClusterTimeContinuityStmt.{u} :=
  HarmonicBalls.Closure.closure_7_2_derivedInputs41 (hL1 := localRootedFieldMeasureDomination_holds.{u}) (hDG := hDG)

/-- Result 8.1 (`BoundaryMeasureZeroOfCompactClusterStmt.{u}`) without the hypothesis `hL1`: the rooted field-measure domination `LocalRootedFieldMeasureDomination` is supplied by `localRootedFieldMeasureDomination_holds`.
The kept hypotheses are those of `HarmonicBalls.Closure.closure_8_1_derivedInputs41`, unchanged. -/
theorem closure_8_1_derivedInputsCampbell
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc) :
    BoundaryMeasureZeroOfCompactClusterStmt.{u} :=
  HarmonicBalls.Closure.closure_8_1_derivedInputs41 (hL1 := localRootedFieldMeasureDomination_holds.{u}) (hDG := hDG)

/-- Result 10.7 (`HarmonicBallComplementBoundaryJordanStmt.{u}`) without the hypothesis `hL1`: the rooted field-measure domination `LocalRootedFieldMeasureDomination` is supplied by `localRootedFieldMeasureDomination_holds`.
The kept hypotheses are those of `HarmonicBalls.Closure.closure_10_7_derivedInputs41`, unchanged. -/
theorem closure_10_7_derivedInputsCampbell
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc)
    (hTor : TorhorstSimpleLoopFrozen) :
    HarmonicBallComplementBoundaryJordanStmt.{u} :=
  HarmonicBalls.Closure.closure_10_7_derivedInputs41 (hL1 := localRootedFieldMeasureDomination_holds.{u}) (hDG := hDG) (hTor := hTor)

/-- Result 11.6 (`AnnulusMassBoundByHarmonicChainStmt.{u}`) without the hypothesis `hSub`: the marked whole-plane Lemma A.10 of Duplantier-Miller-Sheffield `DMSLemmaA10WholePlaneMarkedSub` is supplied by `dmsLemmaA10WholePlaneMarkedSub_forall`.
The kept hypotheses are those of `HarmonicBalls.Closure.closure_11_6_derivedInputs41`, unchanged. -/
theorem closure_11_6_derivedInputsCampbell
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc) :
    AnnulusMassBoundByHarmonicChainStmt.{u} :=
  HarmonicBalls.Closure.closure_11_6_derivedInputs41 (hSub := dmsLemmaA10WholePlaneMarkedSub_forall.{u}) (hDG := hDG)

end HarmonicBalls.Closure
