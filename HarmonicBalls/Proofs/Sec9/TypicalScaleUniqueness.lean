import HarmonicBalls.Proofs.Sec9.ScalingAssembly
import HarmonicBalls.Proofs.Sec8.ClusterBoundary
import HarmonicBalls.Proofs.Sec6.Assembly

/-!
# Weak uniqueness from typical-point good scales

Proposition 8.1 follows from typical-point good scales and the very-good
annulus Harnack estimate. The field-scaling assumptions remain explicit staged
literature inputs pending source review.
-/

namespace HarmonicBalls

open MeasureTheory

universe u

/-- Weak Proposition 9.2 from volume growth, Lemmas 6.11 and 8.2, and the
staged affine-invariance and coordinate-change inputs. -/
theorem subharmonicBallUniquenessWeak_of_typical_good_scales
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h611 : VeryGoodAnnulusHarnackTypeStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u})
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ α₀ hC hcirc) :
    SubharmonicBallUniquenessWeakStmt.{u} :=
  subharmonicBallUniquenessWeak_of_proved_scaling hI2
    (boundaryMeasureZeroOfCompactClusterStmt_of_steps (clusterOpenLaplacian_proved hI2) h611 h82)
    hAff hCC

/-- The same weak uniqueness conclusion with Lemma 6.11 supplied by the
annular odometer bounds and the low-mass estimate. -/
theorem subharmonicBallUniquenessWeak_of_annulus_bounds_and_typical_scales
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h68 : AnnulusMassBoundByOdometerStmt.{u})
    (h610 : OdometerBoundByAnnulusMassStmt.{u})
    (h613 : LowMassSmallOdometerStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u})
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ α₀ hC hcirc) :
    SubharmonicBallUniquenessWeakStmt.{u} :=
  subharmonicBallUniquenessWeak_of_typical_good_scales hI2
    (veryGoodAnnulusHarnackTypeStmt_of_sec3 (clusterOpenLaplacian_proved hI2) h68 h610 h613)
    h82 hAff hCC

end HarmonicBalls
