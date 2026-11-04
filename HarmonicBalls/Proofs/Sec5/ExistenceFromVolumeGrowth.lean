import HarmonicBalls.Proofs.Sec5.ObstacleCentreContinuity
import HarmonicBalls.Proofs.Sec5.ExitTime
import HarmonicBalls.Proofs.Sec3.OpenLaplacian
import HarmonicBalls.Proofs.Sec3.ConservationOfMassLemma
import HarmonicBalls.Proofs.Sec4.ClusterGreenIdentity
import HarmonicBalls.Proofs.Sec7.ClusterUpperBound
import HarmonicBalls.Proofs.Sec7.ClusterContinuity
import HarmonicBalls.Steps.Sec5.ClusterBounds

/-! # Construction of harmonic balls from volume growth and cluster estimates -/

namespace HarmonicBalls

open MeasureTheory

universe u

/-- Theorem 5.5 from volume growth, the boundary-nullity and Section 7
estimates, and the staged affine field and coordinate-change inputs. -/
theorem existenceHarmonicBalls_of_volumeGrowth_and_clusterEstimates
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
    ExistenceHarmonicBallsStmt.{u} := by
  have h32 := clusterOpenLaplacian_proved hI2
  have h33 := clusterMonotone_proved hI2
  have h34 := clusterConservationOfMass_proved hI2
  have h54 := regularizedClusterHarmonicBalls_of_clusterProperties h32 h33 h34 h53
    (lqgMeasureFullSupportStmt_of_volumeGrowth hI2) h71 h72
  exact existenceHarmonicBalls_of_volumeGrowth hI2 h32 h33
    (clusterCompatibility_proved hI2) (clusterSubharmonicBall_proved hI2)
    h53 h54 h71 hAff hCC

/-- Theorem 5.5 from volume growth and the Harnack and compact-boundary
estimates in Propositions 6.1 and 8.1, with the staged affine field and
coordinate-change inputs. -/
theorem existenceHarmonicBalls_of_harnack_and_compactBoundary
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
    ExistenceHarmonicBallsStmt.{u} := by
  have h32 := clusterOpenLaplacian_proved hI2
  have h33 := clusterMonotone_proved hI2
  have h34 := clusterConservationOfMass_proved hI2
  exact existenceHarmonicBalls_of_volumeGrowth_and_clusterEstimates hI2
    (clusterBoundaryMeasureZero_of_steps h81)
    (clusterUpperBoundPolyHighProb_of_steps hvolume h32 h34 h61)
    (clusterTimeContinuity_of_steps hvolume h32 h33 h34 h61 h81) hAff hCC

end HarmonicBalls
