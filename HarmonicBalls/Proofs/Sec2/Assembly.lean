import HarmonicBalls.Proofs.Sec2.BallMassReduction
import HarmonicBalls.Proofs.Sec2.ScaledBallMass
import HarmonicBalls.Proofs.Sec2.CircleAverageTail
import HarmonicBalls.Proofs.Sec2.RescaledUniform

/-!
# Lemma 2.4, I2 and I1: assembly

Lemma 2.4 (`LiouvilleVolumeGrowthStmt`, with [C1]), I2 (`LQGVolumeGrowthAllScalesStmt`) and I1
(`LQGMeasureFullSupportStmt`) of HarmonicBalls/Draft/Section2.lean from the single remaining step
`RescaledBallMassUniformStep` (Ding-Gwynne 2020, Lemma 3.8, for the rescaled fields uniformly in the scale) and the
staged Fact 2.1 inputs `LQGMeasureWeylScaling`, `LQGMeasureExistence` (at `α₀ = 0`) and `LQGMeasureNonatomic`
(HarmonicBalls/Proposed/LQG.lean). The Gaussian tail `CircleAverageDyadicTailStep` is proved from
`IsWholePlaneGFF` (`circleAverageDyadicTailStep_holds`). `RescaledBallMassUniformStep` itself follows from
Ding-Gwynne 2020, Lemma 3.8 (`WholePlaneLQGBallMassBounds`), `WholePlaneGFFAffineInvariance`, `LQGMeasureCoordChange`
and `WholePlaneGFFMixtureStep` (`rescaledBallMassUniformStep_of_DG`); the second group of theorems below states
Lemma 2.4, I2 and I1 from these staged literature inputs and the mixture step.
-/

namespace HarmonicBalls

universe u

section Assembly

variable (hU : RescaledBallMassUniformStep.{u})
  (hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ 0 hC hcirc)
  (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ 0 hC hcirc)
  (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc)

include hU

/-- `WholePlaneScaledBallMassStep` from `RescaledBallMassUniformStep` (the Gaussian tail is proved). -/
theorem wholePlaneScaledBallMassStep_of_rescaled : WholePlaneScaledBallMassStep.{u} :=
  wholePlaneScaledBallMassStep_of_uniform hU circleAverageDyadicTailStep_holds

include hW hE hN

/-- Lemma 2.4 (with [C1]) from `RescaledBallMassUniformStep` and the staged Fact 2.1 inputs. -/
theorem liouvilleVolumeGrowthStmt_of_rescaled : LiouvilleVolumeGrowthStmt.{u} :=
  liouvilleVolumeGrowthStmt_of_scaled (wholePlaneScaledBallMassStep_of_rescaled hU) hW hE hN

/-- I2 (eq:volume-growth) from `RescaledBallMassUniformStep` and the staged Fact 2.1 inputs. -/
theorem lqgVolumeGrowthAllScalesStmt_of_rescaled : LQGVolumeGrowthAllScalesStmt.{u} :=
  lqgVolumeGrowthAllScalesStmt_of_scaled (wholePlaneScaledBallMassStep_of_rescaled hU) hW hE hN

/-- I1 (full support of `μ_h`) from `RescaledBallMassUniformStep` and the staged Fact 2.1 inputs. -/
theorem lqgMeasureFullSupportStmt_of_rescaled : LQGMeasureFullSupportStmt.{u} :=
  lqgMeasureFullSupportStmt_of_scaled (wholePlaneScaledBallMassStep_of_rescaled hU) hW hE hN

end Assembly

section FromDG

variable
  (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
  (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneGFFAffineInvariance P hC hcirc)
  (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ 0 hC hcirc)
  (hMix : WholePlaneGFFMixtureStep.{u})
  (hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ 0 hC hcirc)
  (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ 0 hC hcirc)
  (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc)

include hDG hAff hCC hMix hW hE hN

/-- Lemma 2.4 (with [C1]) from Ding-Gwynne Lemma 3.8, the staged Fact 2.1 inputs, the affine invariance of the
whole-plane GFF and `WholePlaneGFFMixtureStep`. -/
theorem liouvilleVolumeGrowthStmt_of_DG : LiouvilleVolumeGrowthStmt.{u} :=
  liouvilleVolumeGrowthStmt_of_rescaled (rescaledBallMassUniformStep_of_DG hDG hAff hCC hMix) hW hE hN

/-- I2 (eq:volume-growth) from Ding-Gwynne Lemma 3.8, the staged Fact 2.1 inputs, the affine invariance and
`WholePlaneGFFMixtureStep`. -/
theorem lqgVolumeGrowthAllScalesStmt_of_DG : LQGVolumeGrowthAllScalesStmt.{u} :=
  lqgVolumeGrowthAllScalesStmt_of_rescaled (rescaledBallMassUniformStep_of_DG hDG hAff hCC hMix) hW hE hN

/-- I1 (full support of `μ_h`) from Ding-Gwynne Lemma 3.8, the staged Fact 2.1 inputs, the affine invariance and
`WholePlaneGFFMixtureStep`. -/
theorem lqgMeasureFullSupportStmt_of_DG : LQGMeasureFullSupportStmt.{u} :=
  lqgMeasureFullSupportStmt_of_rescaled (rescaledBallMassUniformStep_of_DG hDG hAff hCC hMix) hW hE hN

end FromDG

end HarmonicBalls
