import HarmonicBalls.Proofs.Sec9.ExistenceResultsAssembly

/-! # Volume growth and full support from staged LQG inputs

The staged inputs await source review; the Section 6 chain awaits audit. -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology

universe u

section

variable
  (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
    WholePlaneLQGBallMassBounds P γ hC hcirc)
  (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
    LQGMeasureCoordChange P γ 0 hC hcirc)
  (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
    LQGMeasureExistence P γ α hC hcirc)

include hDG hCC hE

/-- The corrected Lemma 2.4 follows from the staged whole-plane mass bound,
zero-strength coordinate change, and existence at all singularity strengths. -/
theorem liouvilleVolumeGrowthStmt_of_existence : LiouvilleVolumeGrowthStmt.{u} := by
  have hS : WholePlaneScaledBallMassStep.{u} :=
    wholePlaneScaledBallMassStep_of_rescaled
      (rescaledBallMassUniformStep_of_DG hDG
        (fun _ _ P hC hcirc => wholePlaneGFFAffineInvariance_proved P hC hcirc)
        hCC wholePlaneGFFMixtureStep_holds)
  apply liouvilleVolumeGrowthStmt_of_literature hDG
    (fun _ _ P hC hcirc => wholePlaneGFFAffineInvariance_proved P hC hcirc) hCC
    (fun Ω _ P γ hC hcirc => Section6.lqgMeasureWeylScaling Ω P γ 0 hC hcirc)
    (fun Ω _ P γ hC hcirc => hE Ω P γ 0 hC hcirc)
  intro Ω _ P γ α hC hcirc
  exact Section6.lqgMeasureNonatomic_of_existence hS P γ α hC hcirc
    (fun β => hE Ω P γ β hC hcirc)

/-- The same staged inputs also give full support, an assumption used in the
Section 8 typical-point good-scale argument. -/
theorem lqgMeasureFullSupportStmt_of_existence : LQGMeasureFullSupportStmt.{u} := by
  have hS : WholePlaneScaledBallMassStep.{u} :=
    wholePlaneScaledBallMassStep_of_rescaled
      (rescaledBallMassUniformStep_of_DG hDG
        (fun _ _ P hC hcirc => wholePlaneGFFAffineInvariance_proved P hC hcirc)
        hCC wholePlaneGFFMixtureStep_holds)
  apply lqgMeasureFullSupportStmt_of_literature hDG
    (fun _ _ P hC hcirc => wholePlaneGFFAffineInvariance_proved P hC hcirc) hCC
    (fun Ω _ P γ hC hcirc => Section6.lqgMeasureWeylScaling Ω P γ 0 hC hcirc)
    (fun Ω _ P γ hC hcirc => hE Ω P γ 0 hC hcirc)
  intro Ω _ P γ α hC hcirc
  exact Section6.lqgMeasureNonatomic_of_existence hS P γ α hC hcirc
    (fun β => hE Ω P γ β hC hcirc)

end

end HarmonicBalls
