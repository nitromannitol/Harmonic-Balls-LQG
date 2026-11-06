import HarmonicBalls.Steps.Sec11.ConeProbabilityAssembly
import HarmonicBalls.Proofs.Sec6.Section6FromExistence

/-! # Lemma 11.8 from staged literature inputs -/

namespace HarmonicBalls

/-! The cone-probability development uses Leonardo Bonanno's
Lattice-Probability formalization, including its Cameron-Martin port through
the local smooth-shift and fixed-shift decoder developments. -/

open MeasureTheory

universe u

/-- Lemma 11.8 follows from the staged whole-plane ball-mass estimate,
coordinate-change property and existence of the subcritical LQG measure.
The proposed inputs remain subject to operator source review. -/
theorem coneBadEventProbability_of_literature
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureExistence P γ α hC hcirc) :
    ConeBadEventProbabilityStmt.{u} := by
  have hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneGFFAffineInvariance P hC hcirc :=
    fun _ _ P hC hcirc => wholePlaneGFFAffineInvariance_proved P hC hcirc
  have hS : WholePlaneScaledBallMassStep.{u} :=
    wholePlaneScaledBallMassStep_of_rescaled
      (rescaledBallMassUniformStep_of_DG hDG hAff hCC wholePlaneGFFMixtureStep_holds)
  have hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureWeylScaling P γ 0 hC hcirc :=
    fun Ω _ P γ hC hcirc => Section6.lqgMeasureWeylScaling Ω P γ 0 hC hcirc
  have hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureNonatomic P γ α hC hcirc :=
    fun Ω _ P γ α hC hcirc => Section6.lqgMeasureNonatomic_of_existence hS P γ α hC hcirc
      (fun β => hE Ω P γ β hC hcirc)
  have hgrowth : LQGVolumeGrowthAllScalesStmt.{u} :=
    lqgVolumeGrowthAllScalesStmt_of_scaled hS hW
      (fun Ω _ P γ hC hcirc => hE Ω P γ 0 hC hcirc) hN
  exact coneBadEventProbability_of_existence hS hgrowth hE

end HarmonicBalls

#print axioms HarmonicBalls.coneBadEventProbability_of_literature
