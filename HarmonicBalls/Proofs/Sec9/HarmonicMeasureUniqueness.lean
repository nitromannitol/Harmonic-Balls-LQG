import HarmonicBalls.Proofs.Sec9.TypicalScaleUniqueness
import HarmonicBalls.Proofs.Sec9.UnitDiscWeakUniqueness
import HarmonicBalls.Proofs.Sec6.VolumeGrowthAssembly

/-! # Weak uniqueness from the Brownian odometer comparison

The Section 6 volume-growth assembly supplies the very-good-annulus estimate
from the Brownian comparison. The global result retains the staged scaling
inputs; the localized result does not require them.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set

universe u

/-- Weak Proposition 9.2 from I2, Lemmas 6.9 and 8.2, and the staged
affine-invariance and coordinate-change inputs. -/
theorem subharmonicBallUniquenessWeak_of_harmonicMeasure_and_typical_scales
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h69 : OdometerHarmonicMeasureBoundStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u})
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ α₀ hC hcirc) :
    SubharmonicBallUniquenessWeakStmt.{u} :=
  subharmonicBallUniquenessWeak_of_typical_good_scales hI2
    (Section6.veryGoodAnnulusHarnackTypeStmt_of_harmonicMeasure hI2 h69) h82 hAff hCC

/-- Weak uniqueness for balls contained in the unit disk from I2 and Lemmas
6.9 and 8.2. The ambient cluster radius can be arbitrary. -/
theorem ae_subharmonicBall_weak_uniqueness_inside_unit_disc_of_harmonicMeasure
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h69 : OdometerHarmonicMeasureBoundStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ (A : Set ℂ) (z : ℂ) (t R : ℝ), 0 < t → 0 < R →
      z ∈ ball (0 : ℂ) R → closure A ⊆ ball 0 R → closure A ⊆ ball 0 1 →
      IsSubharmonicBall (μ ω) A z → μ ω A = ENNReal.ofReal t →
      cluster (μ ω) R z t ⊆ A ∧ μ ω (A \ regularizedCluster (μ ω) R z t) = 0 :=
  ae_subharmonicBall_weak_uniqueness_inside_unit_disc_of_good_scales hI2
    (Section6.veryGoodAnnulusHarnackTypeStmt_of_harmonicMeasure hI2 h69) h82

end HarmonicBalls
