import HarmonicBalls.Proofs.Sec9.WeakUniquenessInclusions
import HarmonicBalls.Proofs.Sec6.PlanarBrownianGenerator

/-! # Weak uniqueness from volume growth and typical scales

The Brownian comparison required by the weak uniqueness assembly follows
from volume growth. The global statement still requires the typical-scale
estimate and the staged scaling inputs.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set

universe u

/-- Weak Proposition 9.2 from I2, the typical-point good-scale estimate,
and the staged affine-invariance and coordinate-change inputs. -/
theorem subharmonicBallUniquenessWeak_of_volumeGrowth_and_typical_scales
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u})
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ α₀ hC hcirc) :
    SubharmonicBallUniquenessWeakStmt.{u} :=
  subharmonicBallUniquenessWeak_of_harmonicMeasure_and_typical_scales hI2
    (Section6.odometerHarmonicMeasureBoundStmt_of_volumeGrowth hI2) h82 hAff hCC

/-- For comparison balls inside the unit disk, volume growth and the
typical-point good-scale estimate yield the set sandwich for every ambient
radius, without scaling hypotheses. -/
theorem ae_subharmonicBall_sandwich_inside_unit_disc_of_volumeGrowth
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ (A : Set ℂ) (z : ℂ) (t R : ℝ), 0 < t → 0 < R →
      z ∈ ball (0 : ℂ) R → closure A ⊆ ball 0 R → closure A ⊆ ball 0 1 →
      IsSubharmonicBall (μ ω) A z → μ ω A = ENNReal.ofReal t →
      cluster (μ ω) R z t ⊆ A ∧ A ⊆ regularizedCluster (μ ω) R z t ∧
      (IsRegularOpen A → regularizedCluster (μ ω) R z t = A) :=
  ae_subharmonicBall_sandwich_inside_unit_disc hI2
    (Section6.odometerHarmonicMeasureBoundStmt_of_volumeGrowth hI2) h82

end HarmonicBalls
