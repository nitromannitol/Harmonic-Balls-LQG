import HarmonicBalls.Proofs.Sec1.ClusterContainmentLocality
import HarmonicBalls.Proofs.Sec5.StrongCompatibilityAssembly

/-! # Locality from volume growth

The strong compatibility proof uses the potential-theoretic infrastructure
of Leonardo Bonanno. The LQG measure locality input remains staged.
-/

namespace HarmonicBalls

open MeasureTheory

universe u

/-- The frozen locality statement follows from volume growth, existence,
uniqueness, and the staged locality of LQG measure. -/
theorem harmonicBallLocalSet_of_volumeGrowth_existence_uniqueness_and_measureLocality
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h55 : ExistenceHarmonicBallsStmt.{u})
    (h56 : UniquenessHarmonicBallsStmt.{u})
    (hmeasure : ∀ (γ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureLocality P γ α₀ hC hcirc) : HarmonicBallLocalSetStmt.{u} :=
  harmonicBallLocalSet_of_volumeGrowth_and_compatibility hI2 h55 h56
    (clusterStrongCompatibilityStmt_of_volumeGrowth hI2) hmeasure

#print axioms harmonicBallLocalSet_of_volumeGrowth_existence_uniqueness_and_measureLocality

end HarmonicBalls
