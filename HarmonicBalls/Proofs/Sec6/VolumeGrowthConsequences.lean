import HarmonicBalls.Proofs.Sec6.PlanarBrownianGenerator
import HarmonicBalls.Proofs.Sec6.VolumeGrowthAssembly

/-! # Section 6 consequences of LQG volume growth -/

namespace HarmonicBalls.Section6

open MeasureTheory

universe u

/-- Lemma 6.13 follows from all-scales LQG volume growth. -/
theorem lowMassSmallOdometerStmt_of_volumeGrowth
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) : LowMassSmallOdometerStmt.{u} :=
  lowMassSmallOdometerStmt_of_harmonicMeasure hI2
    (odometerHarmonicMeasureBoundStmt_of_volumeGrowth hI2)

/-- Lemma 6.11 follows from all-scales LQG volume growth. -/
theorem veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) : VeryGoodAnnulusHarnackTypeStmt.{u} :=
  veryGoodAnnulusHarnackTypeStmt_of_harmonicMeasure hI2
    (odometerHarmonicMeasureBoundStmt_of_volumeGrowth hI2)

/-- Proposition 6.2 follows from volume growth, the explicit prevalence step,
and the two staged LQG inputs. -/
theorem harnackTypeComponentStmt_of_volumeGrowth_and_prevalence
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (hsub : VeryGoodAnnuliSubRangeStep.{u})
    (hex : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ 0 hC hcirc)
    (hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ 0 hC hcirc) :
    HarnackTypeComponentStmt.{u} :=
  harnackTypeComponentStmt_of_harmonicMeasure hI2
    (odometerHarmonicMeasureBoundStmt_of_volumeGrowth hI2) hsub hex hW

/-- Proposition 6.1 follows from volume growth, the explicit prevalence step,
and the two staged LQG inputs. -/
theorem harnackTypeEstimateStmt_of_volumeGrowth_and_prevalence
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (hsub : VeryGoodAnnuliSubRangeStep.{u})
    (hex : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ 0 hC hcirc)
    (hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ 0 hC hcirc) :
    HarnackTypeEstimateStmt.{u} :=
  harnackTypeEstimateStmt_of_harmonicMeasure hI2
    (odometerHarmonicMeasureBoundStmt_of_volumeGrowth hI2) hsub hex hW

end HarmonicBalls.Section6
