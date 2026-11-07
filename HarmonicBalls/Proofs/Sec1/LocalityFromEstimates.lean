import HarmonicBalls.Proofs.Sec1.LocalityCompatibilityAssembly
import HarmonicBalls.Proofs.Sec5.ExistenceFromVolumeGrowth
import HarmonicBalls.Proofs.Sec5.UniquenessFromVolumeGrowth
import HarmonicBalls.Proofs.Sec9.AffineInvarianceAssembly
import HarmonicBalls.Proofs.Sec9.HarmonicBoundaryAssembly
import HarmonicBalls.Proofs.Sec9.VolumeGrowthAssembly

/-! # Locality from cluster estimates

This conditional assembly retains volume growth, the Harnack and compact-boundary
estimates, and the staged general-α coordinate-change and locality predicates as
explicit hypotheses. The staged predicates await operator source review. The
potential-theoretic infrastructure uses work of Leonardo Bonanno.
-/

namespace HarmonicBalls

open MeasureTheory

universe u

/-- The frozen locality statement, including time zero, follows from the
cluster estimates and the staged LQG measure predicates. -/
theorem harmonicBallLocalSet_of_harnack_and_compactBoundary
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hvolume : LiouvilleVolumeGrowthStmt.{u})
    (h61 : HarnackTypeEstimateStmt.{u})
    (h81 : BoundaryMeasureZeroOfCompactClusterStmt.{u})
    (hCC : ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hmeasure : ∀ (γ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureLocality P γ α₀ hC hcirc) : HarmonicBallLocalSetStmt.{u} :=
  harmonicBallLocalSet_of_volumeGrowth_existence_uniqueness_and_measureLocality hI2
    (existenceHarmonicBalls_of_harnack_and_compactBoundary hI2 hvolume h61 h81
      (fun P hC hcirc => wholePlaneGFFAffineInvariance_proved P hC hcirc) hCC)
    (uniquenessHarmonicBalls_of_boundary_and_volumeGrowth hI2
      (harmonicBallBoundarySubset_of_volumeGrowth hI2)
      (regularOpenEqOfAEEq_of_volumeGrowth hI2)) hmeasure

#print axioms harmonicBallLocalSet_of_harnack_and_compactBoundary

end HarmonicBalls
