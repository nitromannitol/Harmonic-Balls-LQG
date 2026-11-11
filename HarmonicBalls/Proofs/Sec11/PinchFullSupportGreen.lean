import HarmonicBalls.Proofs.Sec9.LQGExistenceConsequences
import HarmonicBalls.Proofs.Sec6.SimultaneousSingularMeasure
import HarmonicBalls.Steps.Sec11.PinchGreenFinite

/-! # Full support and finite annular Green potential

The three LQG literature inputs used here are staged and await source
review. The full-support development uses Leonardo Bonanno's
Lattice-Probability formalization. -/

namespace HarmonicBalls
open MeasureTheory Set Filter
open scoped ENNReal

/-- The staged mass bound, coordinate change, and LQG existence supply both
full support and finite annular Green potential for the singular LQG measure. -/
theorem IsWholePlaneGFF.ae_fullSupport_and_pinchGreen_of_existence
    (hDG : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureExistence P γ α hC hcirc)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hα : α < lqgQ γ) :
    (∀ᵐ ω ∂P, ∀ A : Set ℂ, IsOpen A → A.Nonempty → 0 < μ ω A) ∧
      ∀ᵐ ω ∂P, annulusGreenPotentialSup (μ ω) 0 3 6 ≠ ∞ := by
  have hS : WholePlaneScaledBallMassStep :=
    wholePlaneScaledBallMassStep_of_rescaled
      (rescaledBallMassUniformStep_of_DG hDG
        (fun _ _ P' hC' hcirc' => wholePlaneGFFAffineInvariance_proved P' hC' hcirc')
        hCC wholePlaneGFFMixtureStep_holds)
  constructor
  · filter_upwards [Section6.ae_fullSupport_all_singular_limits hS P γ hγ hγ₂ hC hcirc h
      (hE Ω P γ 0 hC hcirc), hμ] with ω hsupport hμω
    exact hsupport α (μ ω) hμω
  · exact ae_annulusGreenPotentialSup_ne_top_of_lqgVolumeGrowth
      (lqgVolumeGrowthAllScalesStmt_of_existence hDG hCC hE) hγ hγ₂ hα h hμ 3 (by norm_num)

end HarmonicBalls
