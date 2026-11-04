import HarmonicBalls.Proofs.Sec5.ContainmentEventNullMeasurable
import HarmonicBalls.Proofs.Sec5.ExistenceFromVolumeGrowth
import HarmonicBalls.Proofs.Sec8.ClusterBoundary

/-! # Cofinal regularized-cluster intervals from cluster estimates -/

namespace HarmonicBalls

open MeasureTheory

universe u

/-- Compact cluster continuity and the small-time estimate give the cofinal
regularized-cluster intervals. The field scaling hypotheses are staged inputs. -/
theorem cofinalRegularizedClusterIntervals_of_clusterEstimates
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h53 : ClusterBoundaryMeasureZeroStmt.{u})
    (h71 : ClusterUpperBoundPolyHighProbStmt.{u})
    (h72 : ClusterTimeContinuityStmt.{u})
    (hAff : ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ α₀ hC hcirc) :
    CofinalRegularizedClusterIntervalsStep.{u} := by
  have h32 := clusterOpenLaplacian_proved hI2
  have h33 := clusterMonotone_proved hI2
  have h34 := clusterConservationOfMass_proved hI2
  have h54 := regularizedClusterHarmonicBalls_of_clusterProperties h32 h33 h34 h53
    (lqgMeasureFullSupportStmt_of_volumeGrowth hI2) h71 h72
  exact cofinalRegularizedClusterIntervals_of_analytic_containment hI2 h32 h53 h54 h71 hAff hCC

/-- The cofinal intervals follow from volume growth, the Harnack estimate,
and nullity of compact cluster boundaries. -/
theorem cofinalRegularizedClusterIntervals_of_harnack_and_compactBoundary
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hvolume : LiouvilleVolumeGrowthStmt.{u})
    (h61 : HarnackTypeEstimateStmt.{u})
    (h81 : BoundaryMeasureZeroOfCompactClusterStmt.{u})
    (hAff : ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ α₀ hC hcirc) :
    CofinalRegularizedClusterIntervalsStep.{u} := by
  have h32 := clusterOpenLaplacian_proved hI2
  have h33 := clusterMonotone_proved hI2
  have h34 := clusterConservationOfMass_proved hI2
  exact cofinalRegularizedClusterIntervals_of_clusterEstimates hI2
    (clusterBoundaryMeasureZero_of_steps h81)
    (clusterUpperBoundPolyHighProb_of_steps hvolume h32 h34 h61)
    (clusterTimeContinuity_of_steps hvolume h32 h33 h34 h61 h81) hAff hCC

/-- The compact boundary estimate can itself be supplied by the
component-wise Harnack estimate and the typical-point good-scale estimate. -/
theorem cofinalRegularizedClusterIntervals_of_goodScales
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hvolume : LiouvilleVolumeGrowthStmt.{u})
    (h61 : HarnackTypeEstimateStmt.{u})
    (h611 : VeryGoodAnnulusHarnackTypeStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u})
    (hAff : ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ α₀ hC hcirc) :
    CofinalRegularizedClusterIntervalsStep.{u} :=
  cofinalRegularizedClusterIntervals_of_harnack_and_compactBoundary hI2 hvolume h61
    (boundaryMeasureZeroOfCompactClusterStmt_of_steps (clusterOpenLaplacian_proved hI2) h611 h82)
    hAff hCC

#print axioms cofinalRegularizedClusterIntervals_of_clusterEstimates
#print axioms cofinalRegularizedClusterIntervals_of_harnack_and_compactBoundary
#print axioms cofinalRegularizedClusterIntervals_of_goodScales

end HarmonicBalls
