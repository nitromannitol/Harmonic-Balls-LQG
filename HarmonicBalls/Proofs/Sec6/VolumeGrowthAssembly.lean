import HarmonicBalls.Proofs.Sec6.Assembly
import HarmonicBalls.Proofs.Sec6.AnnulusOdometerAssembly
import HarmonicBalls.Proofs.Sec10.PoleAvoidingTruncation
import HarmonicBalls.Proofs.Sec3.OpenLaplacian

/-! # Section 6 assembly under LQG volume growth

Lemmas 3.2, 6.8 and 6.10 and the component maximum step follow from the
all-scales volume-growth statement. The very-good-annulus prevalence step and
odometer decay step remain explicit.
-/

namespace HarmonicBalls.Section6

open MeasureTheory

universe u

/-- Proposition 6.2 from volume growth, the two staged LQG inputs used in
prevalence, and the remaining prevalence and decay steps. -/
theorem harnackTypeComponentStmt_of_volumeGrowth
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (hsub : VeryGoodAnnuliSubRangeStep.{u})
    (hex : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ 0 hC hcirc)
    (hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ 0 hC hcirc)
    (hdec : GoodAnnulusOdometerDecayStep.{u}) : HarnackTypeComponentStmt.{u} :=
  harnackTypeComponentStmt_of_steps hsub hex hW (clusterOpenLaplacian_proved hI2)
    (annulusMassBoundByOdometer_of_volumeGrowth hI2)
    (odometerBoundByAnnulusMass_of_volumeGrowth hI2) hdec
    (componentOdometerDiscMaxStep_of_volumeGrowth hI2)

/-- Proposition 6.1 under the same explicit inputs and remaining steps. -/
theorem harnackTypeEstimateStmt_of_volumeGrowth
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (hsub : VeryGoodAnnuliSubRangeStep.{u})
    (hex : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ 0 hC hcirc)
    (hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ 0 hC hcirc)
    (hdec : GoodAnnulusOdometerDecayStep.{u}) : HarnackTypeEstimateStmt.{u} :=
  harnackTypeEstimateStmt_of_component (harnackTypeComponentStmt_of_volumeGrowth hI2 hsub hex hW hdec)

end HarmonicBalls.Section6
