import HarmonicBalls.Proofs.Sec3.OpenLaplacian
import HarmonicBalls.Proofs.Sec3.Basic
import HarmonicBalls.Proofs.Sec3.ConservationOfMassLemma
import HarmonicBalls.Proofs.Sec5.ExitTime
import HarmonicBalls.Proofs.Sec5.ExistenceFromVolumeGrowth
import HarmonicBalls.Proofs.Sec5.UniquenessFromVolumeGrowth
import HarmonicBalls.Proofs.Sec5.StrongCompatibilityAssembly
import HarmonicBalls.Proofs.Sec5.PotentialMeasurableDecoder
import HarmonicBalls.Proofs.Sec6.VolumeGrowthConsequences
import HarmonicBalls.Proofs.Sec7.ClusterUpperBound
import HarmonicBalls.Proofs.Sec7.ClusterContinuity
import HarmonicBalls.Proofs.Sec8.ClusterBoundary
import HarmonicBalls.Proofs.Sec9.HarmonicBoundaryAssembly
import HarmonicBalls.Proofs.Sec9.VolumeGrowthAssembly
import HarmonicBalls.Proofs.Sec9.AffineInvarianceAssembly
import HarmonicBalls.Proofs.Sec9.WeakUniquenessDerivedInputs
import HarmonicBalls.Steps.Sec2.VolumeGrowth
import HarmonicBalls.Steps.Sec5.ClusterBounds
import HarmonicBalls.Steps.Sec5.ContinuityAssembly

/-! # Section 5 input consumption checks

Typed applications of the Section 5 producers to the frozen statements `ClusterUpperBoundStmt` (5.1),
`ClusterContinuityStmt` (5.2), `ClusterBoundaryMeasureZeroStmt` (5.3), `RegularizedClusterHarmonicBallsStmt` (5.4),
`ExistenceHarmonicBallsStmt` (5.5), `UniquenessHarmonicBallsStmt` (5.6), `ClusterScaleInvarianceStmt` (5.7) and
`ClusterStrongCompatibilityStmt` (5.8), with every premise that the producers do not discharge kept as an explicit
binder. The volume input `LQGVolumeGrowthAllScalesStmt` (I2) is the only volume-type input; `LQGMeasureFullSupportStmt`
(I1) and the affine invariance `WholePlaneGFFAffineInvariance` are derived from it or proved.

Remaining leaves, as binders: `LiouvilleVolumeGrowthStmt` (Lemma 2.4), `HarnackTypeEstimateStmt` (Proposition 6.1),
`TypicalPointManyGoodScalesStmt` (Lemma 8.2), `ClusterBoundaryTouchingRightContinuityStep` (the right-continuity step
of Proposition 5.2 at times with `closure Λ ⊄ B₁`, docs/campaign/GRAPH.md G12), and the all-insertion coordinate-change
input `LQGMeasureCoordChange` (Proposed).

Leonardo Bonanno's potential-theoretic and LatticeProb work is consumed through the imported modules, which carry Leonardo Bonanno's
credit (for example Proofs/Potential/FiniteDiscGreenReciprocity.lean and Proofs/Sec8/TypicalPointStatement.lean). No
frozen statement, definition or input is changed here; no numbered result is closed by a helper.
-/

namespace HarmonicBalls

open MeasureTheory
universe u

/-! ## Volume input I2 from its staged provider -/

/-- The all-scales volume input I2 (`LQGVolumeGrowthAllScalesStmt`, Draft/Section2.lean:122) from the three staged
Proposed inputs. The binder types are those of `lqgVolumeGrowthAllScalesStmt_of_staged_inputs`
(Proofs/Sec9/WeakUniquenessDerivedInputs.lean:53-57); the coordinate-change input there has insertion `0` only. -/
theorem section5_volumeGrowth_of_staged_inputs
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc) :
    LQGVolumeGrowthAllScalesStmt.{u} :=
  lqgVolumeGrowthAllScalesStmt_of_staged_inputs hDG hCC hE

/-! ## Numbered results 5.1-5.8 from I2 and the explicit leaves -/

/-- Proposition 5.1 (prop:upper-bound) from Proposition 7.1 (`clusterUpperBoundPolyHighProb_of_steps`), with
Lemma 2.4, Lemmas 3.2 and 3.4 (from I2) and Proposition 6.1 as explicit leaves. -/
theorem section5_clusterUpperBound_of_I2 (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hLiou : LiouvilleVolumeGrowthStmt.{u}) (hHarnack : HarnackTypeEstimateStmt.{u}) :
    ClusterUpperBoundStmt.{u} :=
  clusterUpperBound_of_steps
    (clusterUpperBoundPolyHighProb_of_steps hLiou (clusterOpenLaplacian_proved hI2)
      (clusterConservationOfMass_proved hI2) hHarnack)

/-- Proposition 5.3 (prop:boundary-measure) from Proposition 8.1 (`boundaryMeasureZeroOfCompactClusterStmt_of_steps`),
with Lemma 3.2 and Lemma 6.11 (from I2) and Lemma 8.2 as explicit leaf. -/
theorem section5_clusterBoundaryMeasureZero_of_I2 (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hTyp : TypicalPointManyGoodScalesStmt.{u}) : ClusterBoundaryMeasureZeroStmt.{u} :=
  clusterBoundaryMeasureZero_of_steps
    (boundaryMeasureZeroOfCompactClusterStmt_of_steps (clusterOpenLaplacian_proved hI2)
      (Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only hI2) hTyp)

/-- Proposition 5.2 (prop:continuity) from Propositions 7.1 and 7.2, Lemma 3.3 and the boundary-touching
right-continuity step `ClusterBoundaryTouchingRightContinuityStep` (no producer in the repository; G12). -/
theorem section5_clusterContinuity_of_I2 (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hLiou : LiouvilleVolumeGrowthStmt.{u}) (hHarnack : HarnackTypeEstimateStmt.{u})
    (hTyp : TypicalPointManyGoodScalesStmt.{u})
    (hBT : ClusterBoundaryTouchingRightContinuityStep.{u}) : ClusterContinuityStmt.{u} :=
  clusterContinuity_of_boundaryTouching
    (clusterUpperBoundPolyHighProb_of_steps hLiou (clusterOpenLaplacian_proved hI2)
      (clusterConservationOfMass_proved hI2) hHarnack)
    (clusterMonotone_proved hI2)
    (clusterTimeContinuity_of_steps hLiou (clusterOpenLaplacian_proved hI2)
      (clusterMonotone_proved hI2) (clusterConservationOfMass_proved hI2) hHarnack
      (boundaryMeasureZeroOfCompactClusterStmt_of_steps (clusterOpenLaplacian_proved hI2)
        (Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only hI2) hTyp))
    hBT

/-- Proposition 5.4 (`RegularizedClusterHarmonicBallsStmt`) from the Section 3 cluster properties, the null boundaries
of Proposition 5.3, full support (I1, derived from I2), and Propositions 7.1 and 7.2. -/
theorem section5_regularizedCluster_of_I2 (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hLiou : LiouvilleVolumeGrowthStmt.{u}) (hHarnack : HarnackTypeEstimateStmt.{u})
    (hTyp : TypicalPointManyGoodScalesStmt.{u}) : RegularizedClusterHarmonicBallsStmt.{u} :=
  regularizedClusterHarmonicBalls_of_clusterProperties (clusterOpenLaplacian_proved hI2)
    (clusterMonotone_proved hI2) (clusterConservationOfMass_proved hI2)
    (section5_clusterBoundaryMeasureZero_of_I2 hI2 hTyp)
    (lqgMeasureFullSupportStmt_of_volumeGrowth hI2)
    (clusterUpperBoundPolyHighProb_of_steps hLiou (clusterOpenLaplacian_proved hI2)
      (clusterConservationOfMass_proved hI2) hHarnack)
    (clusterTimeContinuity_of_steps hLiou (clusterOpenLaplacian_proved hI2)
      (clusterMonotone_proved hI2) (clusterConservationOfMass_proved hI2) hHarnack
      (boundaryMeasureZeroOfCompactClusterStmt_of_steps (clusterOpenLaplacian_proved hI2)
        (Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only hI2) hTyp))

/-- Theorem 5.5 (`ExistenceHarmonicBallsStmt`) from I2, Propositions 5.3, 7.1 and 7.2, and the affine invariance
(proved, `wholePlaneGFFAffineInvariance_proved`) with the all-insertion coordinate change `hCC` (Proposed). -/
theorem section5_existence_of_I2 (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hLiou : LiouvilleVolumeGrowthStmt.{u}) (hHarnack : HarnackTypeEstimateStmt.{u})
    (hTyp : TypicalPointManyGoodScalesStmt.{u})
    (hCC : ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc) :
    ExistenceHarmonicBallsStmt.{u} :=
  existenceHarmonicBalls_of_volumeGrowth_and_clusterEstimates hI2
    (section5_clusterBoundaryMeasureZero_of_I2 hI2 hTyp)
    (clusterUpperBoundPolyHighProb_of_steps hLiou (clusterOpenLaplacian_proved hI2)
      (clusterConservationOfMass_proved hI2) hHarnack)
    (clusterTimeContinuity_of_steps hLiou (clusterOpenLaplacian_proved hI2)
      (clusterMonotone_proved hI2) (clusterConservationOfMass_proved hI2) hHarnack
      (boundaryMeasureZeroOfCompactClusterStmt_of_steps (clusterOpenLaplacian_proved hI2)
        (Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only hI2) hTyp))
    wholePlaneGFFAffineInvariance_proved hCC

/-- Theorem 5.6 (`UniquenessHarmonicBallsStmt`) from I2 alone: Lemma 9.3 and Lemma 9.4 are I2 providers. -/
theorem section5_uniqueness_of_I2 (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) :
    UniquenessHarmonicBallsStmt.{u} :=
  uniquenessHarmonicBalls_of_boundary_and_volumeGrowth hI2
    (harmonicBallBoundarySubset_of_volumeGrowth hI2) (regularOpenEqOfAEEq_of_volumeGrowth hI2)

/-- Lemma 5.7 (`ClusterScaleInvarianceStmt`) from I2, the proved affine invariance and the all-insertion coordinate
change `hCC` (Proposed). -/
theorem section5_clusterScaleInvariance_of_I2 (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hCC : ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc) :
    ClusterScaleInvarianceStmt.{u} :=
  clusterScaleInvariance_of_volumeGrowth hI2 wholePlaneGFFAffineInvariance_proved hCC

/-- Lemma 5.8 (`ClusterStrongCompatibilityStmt`) from I2 alone (Green-regular exhaustions, E51/G9 semantics open). -/
theorem section5_clusterStrongCompatibility_of_I2 (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) :
    ClusterStrongCompatibilityStmt.{u} :=
  clusterStrongCompatibilityStmt_of_volumeGrowth hI2

/-! ## 5.6 and 5.8 from the three staged Proposed inputs alone -/

/-- Theorem 5.6 from the three staged inputs `hDG`, `hCC` (insertion `0`), `hE`, through I2. -/
theorem section5_uniqueness_of_staged_inputs
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc) :
    UniquenessHarmonicBallsStmt.{u} :=
  section5_uniqueness_of_I2 (section5_volumeGrowth_of_staged_inputs hDG hCC hE)

/-- Lemma 5.8 from the three staged inputs `hDG`, `hCC` (insertion `0`), `hE`, through I2. -/
theorem section5_clusterStrongCompatibility_of_staged_inputs
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc) :
    ClusterStrongCompatibilityStmt.{u} :=
  section5_clusterStrongCompatibility_of_I2 (section5_volumeGrowth_of_staged_inputs hDG hCC hE)

/-! ## Axiom checks (expected: propext, Classical.choice, Quot.sound only) -/

#print axioms section5_volumeGrowth_of_staged_inputs
#print axioms section5_clusterUpperBound_of_I2
#print axioms section5_clusterBoundaryMeasureZero_of_I2
#print axioms section5_clusterContinuity_of_I2
#print axioms section5_regularizedCluster_of_I2
#print axioms section5_existence_of_I2
#print axioms section5_uniqueness_of_I2
#print axioms section5_clusterScaleInvariance_of_I2
#print axioms section5_clusterStrongCompatibility_of_I2
#print axioms section5_uniqueness_of_staged_inputs
#print axioms section5_clusterStrongCompatibility_of_staged_inputs

end HarmonicBalls
