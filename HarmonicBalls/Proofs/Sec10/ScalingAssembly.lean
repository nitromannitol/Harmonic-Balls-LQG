import HarmonicBalls.Proofs.Sec10.JordanScaling
import HarmonicBalls.Proofs.Sec5.SupersolutionScaling

/-!
# Jordan boundaries with proved cluster scaling

The affine invariance and coordinate-change assumptions are staged inputs
pending source review; the unit-radius Jordan theorem remains a hypothesis.
-/

namespace HarmonicBalls

open MeasureTheory

universe u

/-- The unit-radius Jordan theorem transfers to each fixed radius using the
proved pathwise scaling and the staged field inputs. -/
theorem clusterJordanFixedRadius_of_proved_scaling
    (h10 : ComplementComponentBoundarySimpleLoopStmt.{u})
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ α₀ hC hcirc) :
    ClusterJordanFixedRadius.{u} :=
  clusterJordanFixedRadius_of_scaledField h10 clusterPathwiseScaleStep_proved hAff hCC

/-- Proposition 10.7 from volume growth, existence, the unit-radius Jordan
theorem and the staged field inputs. -/
theorem harmonicBallComplementBoundaryJordan_of_proved_scaling
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hexists : ExistenceHarmonicBallsStmt.{u})
    (h10 : ComplementComponentBoundarySimpleLoopStmt.{u})
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ α₀ hC hcirc) :
    HarmonicBallComplementBoundaryJordanStmt.{u} :=
  harmonicBallComplementBoundaryJordan_of_scaledField hI2 hexists h10
    clusterPathwiseScaleStep_proved hAff hCC

end HarmonicBalls
