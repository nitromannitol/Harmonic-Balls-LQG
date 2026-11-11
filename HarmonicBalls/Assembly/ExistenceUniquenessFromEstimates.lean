import HarmonicBalls.Assembly.ExistenceUniqueness
import HarmonicBalls.Proofs.Sec5.ExistenceFromVolumeGrowth
import HarmonicBalls.Proofs.Sec5.UniquenessFromVolumeGrowth
import HarmonicBalls.Proofs.Sec9.AffineInvarianceAssembly
import HarmonicBalls.Proofs.Sec9.HarmonicBoundaryAssembly
import HarmonicBalls.Proofs.Sec9.VolumeGrowthAssembly

/-! # Existence and uniqueness from cluster estimates

This conditional assembly leaves I2, Liouville volume growth, Propositions 6.1
and 8.1, and the general-α LQG coordinate-change predicate as explicit
premises. In particular, it does not close Propositions 6.1 or 8.1. The staged
coordinate-change input in `HarmonicBalls.Proposed.LQG` is pending
source review; this composition does not establish its literature attribution
or source fidelity. The potential-theoretic infrastructure uses work of
Leonardo Bonanno.
-/

namespace HarmonicBalls

open MeasureTheory

universe u

/-- Theorem 1.1 from volume growth, the Harnack and compact-boundary estimates,
and the staged general-α coordinate-change input. -/
theorem existenceUniquenessHarmonicBallsStmt_of_harnack_and_compactBoundary
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hvolume : LiouvilleVolumeGrowthStmt.{u})
    (h61 : HarnackTypeEstimateStmt.{u})
    (h81 : BoundaryMeasureZeroOfCompactClusterStmt.{u})
    (hCC : ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ α₀ hC hcirc) :
    ExistenceUniquenessHarmonicBallsStmt.{u} :=
  existenceUniquenessHarmonicBallsStmt_of_sec5
    (existenceHarmonicBalls_of_harnack_and_compactBoundary hI2 hvolume h61 h81
      (fun P hC hcirc => wholePlaneGFFAffineInvariance_proved P hC hcirc) hCC)
    (uniquenessHarmonicBalls_of_boundary_and_volumeGrowth hI2
      (harmonicBallBoundarySubset_of_volumeGrowth hI2)
      (regularOpenEqOfAEEq_of_volumeGrowth hI2))


end HarmonicBalls
