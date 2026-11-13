import HarmonicBalls.Proofs.Sec5.StagedInputAssembly
import HarmonicBalls.Proofs.Sec5.BoundaryRightContinuity
import HarmonicBalls.Proofs.Sec7.ClusterUpperBound
import HarmonicBalls.Proofs.Sec7.ClusterContinuity
import HarmonicBalls.Proofs.Sec8.ClusterBoundary
import HarmonicBalls.Proofs.Sec8.OriginLiteratureAssembly
import HarmonicBalls.Proofs.Sec9.AffineInvarianceAssembly
import HarmonicBalls.Draft.Section5
import HarmonicBalls.Draft.Section7
import HarmonicBalls.Draft.Section8

/-!
# closures for Sections 5, 7 and 8

Each theorem `firstPass_<sec>_<num>` concludes the Draft statement of the numbered result. Its hypotheses are only
existing Proposed inputs of `HarmonicBalls/Proposed/LQG.lean` (`WholePlaneLQGBallMassBounds`, `LQGMeasureCoordChange`,
`LQGMeasureExistence`, `LQGMeasureWeylScaling`, `LQGMeasureNonatomic`), the Draft statement of Lemma 8.2
(`TypicalPointManyGoodScalesStmt`, a cited numbered result), and the Draft statement of Proposition 2.5 Green-potential
clause (`GreenPotentialHolderStmt`, used by Lemma 8.3 only). No new frozen input is needed.
The proofs compose the committed reductions of `Proofs/Sec5/StagedInputAssembly.lean`, `Proofs/Sec5/BoundaryRightContinuity.lean`,
`Proofs/Sec7/ClusterUpperBound.lean`, `Proofs/Sec7/ClusterContinuity.lean`, `Proofs/Sec8/ClusterBoundary.lean` and
`Proofs/Sec8/OriginLiteratureAssembly.lean`.
`wholePlaneGFFAffineInvariance_proved` (`Proofs/Sec9/AffineInvarianceAssembly.lean`) discharges the affine-invariance input.
Lemma 8.2 enters here as the hypothesis `TypicalPointManyGoodScalesStmt`.
-/

namespace HarmonicBalls

open MeasureTheory

universe u

/-! ## Section 7 -/

/-- Proposition 7.1 (prop:upper-bound-polynomially-high-prob, line 1956), from Proposed inputs only. -/
theorem firstPass_7_1
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc) :
    ClusterUpperBoundPolyHighProbStmt.{u} := by
  have hI2 := volumeGrowthI2_of_staged_inputs hDG hCC hE
  have hLiou := liouvilleVolumeGrowth_of_staged_inputs hDG hCC hE
  have hHarnack := harnackTypeEstimate_of_staged_inputs hDG hCC hE
  exact clusterUpperBoundPolyHighProb_of_steps hLiou (clusterOpenLaplacian_proved hI2)
    (clusterConservationOfMass_proved hI2) hHarnack

/-- Proposition 7.2 (prop:continuity-of-clusters, line 2021), from Proposed inputs and Lemma 8.2. -/
theorem firstPass_7_2
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hTyp : TypicalPointManyGoodScalesStmt.{u}) :
    ClusterTimeContinuityStmt.{u} := by
  have hI2 := volumeGrowthI2_of_staged_inputs hDG hCC hE
  have hLiou := liouvilleVolumeGrowth_of_staged_inputs hDG hCC hE
  have hHarnack := harnackTypeEstimate_of_staged_inputs hDG hCC hE
  exact clusterTimeContinuity_of_steps hLiou (clusterOpenLaplacian_proved hI2)
    (clusterMonotone_proved hI2) (clusterConservationOfMass_proved hI2) hHarnack
    (boundaryMeasureZeroOfCompactClusterStmt_of_steps (clusterOpenLaplacian_proved hI2)
      (Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only hI2) hTyp)

/-! ## Section 8 -/

/-- Proposition 8.1 (prop:boundary-measure-zero, line 2122), from Proposed inputs and Lemma 8.2. -/
theorem firstPass_8_1
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hTyp : TypicalPointManyGoodScalesStmt.{u}) :
    BoundaryMeasureZeroOfCompactClusterStmt.{u} := by
  have hI2 := volumeGrowthI2_of_staged_inputs hDG hCC hE
  exact boundaryMeasureZeroOfCompactClusterStmt_of_steps (clusterOpenLaplacian_proved hI2)
    (Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only hI2) hTyp

/-- Lemma 8.3 (lemma:doubling-alpha, line 2160), from Proposed inputs and the Green-potential clause of
Proposition 2.5 (`GreenPotentialHolderStmt`, cited). -/
theorem firstPass_8_3
    (hholder : GreenPotentialHolderStmt.{u})
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hatom : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α hC hcirc)
    (hex : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ 0 hC hcirc)
    (hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ 0 hC hcirc) :
    OriginManyGoodScalesStmt.{u} :=
  originManyGoodScalesStmt_of_literature hholder hDG hatom (fun _ _ P hC hcirc => wholePlaneGFFAffineInvariance_proved P hC hcirc) hCC hex hW

/-! ## Section 5 -/

/-- Proposition 5.1 (prop:upper-bound, line 815), from Proposed inputs only. -/
theorem firstPass_5_1
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc) :
    ClusterUpperBoundStmt.{u} :=
  section5_1_of_staged_inputs hDG hCC hE

/-- Proposition 5.2 (prop:continuity, line 824), from Proposed inputs, Lemma 8.2 (cited) and the boundary-touching
right-continuity step (proved in `Proofs/Sec5/BoundaryRightContinuity.lean`). -/
theorem firstPass_5_2
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ 0 hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc)
    (hTyp : TypicalPointManyGoodScalesStmt.{u}) :
    ClusterContinuityStmt.{u} :=
  section5_2_of_staged_inputs hDG (fun Ω _ P γ hC hcirc => hCC Ω P γ 0 hC hcirc) hE hTyp
    (clusterBoundaryTouching_of_fields
      (firstPass_7_1 hDG (fun Ω _ P γ hC hcirc => hCC Ω P γ 0 hC hcirc) hE)
      hDG (fun _ _ P hC hcirc => wholePlaneGFFAffineInvariance_proved P hC hcirc) hCC hW (fun Ω _ P γ hC hcirc => hE Ω P γ 0 hC hcirc) hN)

/-- Proposition 5.3 (prop:boundary-measure, line 836), from Proposed inputs and Lemma 8.2 (cited). -/
theorem firstPass_5_3
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hTyp : TypicalPointManyGoodScalesStmt.{u}) :
    ClusterBoundaryMeasureZeroStmt.{u} :=
  section5_3_of_staged_inputs hDG hCC hE hTyp

/-- Proposition 5.4 (prop:conditional, line 853), from Proposed inputs and Lemma 8.2 (cited). -/
theorem firstPass_5_4
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hTyp : TypicalPointManyGoodScalesStmt.{u}) :
    RegularizedClusterHarmonicBallsStmt.{u} :=
  section5_4_of_staged_inputs hDG hCC hE hTyp

/-- Theorem 5.5 (theorem:full-theorem-minus-uniqueness, line 863), from Proposed inputs (coordinate change at every
insertion) and Lemma 8.2 (cited). -/
theorem firstPass_5_5
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hTyp : TypicalPointManyGoodScalesStmt.{u}) :
    ExistenceHarmonicBallsStmt.{u} :=
  section5_5_of_staged_inputs hDG hCC hE hTyp

/-- Proposition 5.6 (prop:uniqueness, line 872), from Proposed inputs only. -/
theorem firstPass_5_6
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc) :
    UniquenessHarmonicBallsStmt.{u} :=
  section5_6_of_staged_inputs hDG hCC hE

/-- Lemma 5.7 (lemma:scale-invariance-flow, line 885), from Proposed inputs (coordinate change at every insertion). -/
theorem firstPass_5_7
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc) :
    ClusterScaleInvarianceStmt.{u} :=
  section5_7_of_staged_inputs hDG hCC hE

/-- Lemma 5.8 (lemma:strong-compatibility, line 1019), from Proposed inputs only. -/
theorem firstPass_5_8
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc) :
    ClusterStrongCompatibilityStmt.{u} :=
  section5_8_of_staged_inputs hDG hCC hE



end HarmonicBalls
