import HarmonicBalls.Proofs.Sec5.ExistenceFromVolumeGrowth
import HarmonicBalls.Proofs.Sec5.BufferedUniformFailure
import HarmonicBalls.Proofs.Sec5.StrongCompatibilityAssembly
import HarmonicBalls.Proofs.Sec5.ArbitraryHorizonFailure
import HarmonicBalls.Proofs.Sec5.UniformOpenHorizon

/-! # Conditional Section 5 exports

These checks consume the exact frozen propositions, with all proof inputs
explicit. The imported potential-theoretic infrastructure uses Leonardo Bonanno's work.
-/

namespace HarmonicBalls

open MeasureTheory
universe u

example (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hAff : ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ α₀ hC hcirc) : ClusterScaleInvarianceStmt.{u} :=
  clusterScaleInvariance_of_volumeGrowth hI2 hAff hCC

example (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) : ClusterStrongCompatibilityStmt.{u} :=
  clusterStrongCompatibilityStmt_of_volumeGrowth hI2

example (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h32 : ClusterOpenLaplacianStmt.{u}) (h33 : ClusterMonotoneStmt.{u})
    (h53 : ClusterBoundaryMeasureZeroStmt.{u}) (h54 : RegularizedClusterHarmonicBallsStmt.{u})
    (h71 : ClusterUpperBoundPolyHighProbStmt.{u})
    (hAff : ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ α₀ hC hcirc) : CofinalRegularizedClusterIntervalsStep.{u} :=
  cofinalRegularizedClusterIntervals_of_bufferedHorizon hI2 h32 h33 h53 h54 h71 hAff hCC

example (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h53 : ClusterBoundaryMeasureZeroStmt.{u})
    (h71 : ClusterUpperBoundPolyHighProbStmt.{u}) (h72 : ClusterTimeContinuityStmt.{u})
    (hAff : ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ α₀ hC hcirc) : ExistenceHarmonicBallsStmt.{u} :=
  existenceHarmonicBalls_of_volumeGrowth_and_clusterEstimates hI2 h53 h71 h72 hAff hCC

#print axioms clusterScaleInvariance_of_volumeGrowth
#print axioms clusterStrongCompatibilityStmt_of_volumeGrowth
#print axioms cofinalRegularizedClusterIntervals_of_bufferedHorizon
#print axioms existenceHarmonicBalls_of_volumeGrowth_and_clusterEstimates

end HarmonicBalls
