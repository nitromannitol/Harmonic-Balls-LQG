import HarmonicBalls.Proofs.Sec8.GoodRadiusVersions
import HarmonicBalls.Proofs.Sec8.LQGRandomGoodAnnulus
import HarmonicBalls.Proofs.Sec8.BallMassCountable

/-! # Measurable very-good-annulus versions for LQG measures -/

open Set Metric MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace HarmonicBalls

universe u

open MarkovProcess in
/-- At the origin, an LQG very-good-annulus event has a measurable version
under Brownian point avoidance. Nonatomicity remains a staged input. -/
theorem exists_measurable_lqg_isVeryGoodAnnulus_zero_of_ae_point_avoidance
    (hfull : LQGMeasureFullSupportStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    (γ α₀ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hatom : LQGMeasureNonatomic P γ α₀ hC hcirc)
    (βminus ρ : ℝ) (hρ : 0 < ρ) (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ : ℝ) (ha : 0 < a)
    (hpolar : ∀ (u x : ℂ), x ≠ u →
      ∀ᵐ p ∂(planarBrownianMotion u), ∀ t : ℝ≥0, p t ≠ x) :
    ∃ A : Set Ω, MeasurableSet A ∧ ∀ᵐ ω ∂P,
      (ω ∈ A ↔ IsVeryGoodAnnulus (μ ω) βminus ρ 0 N₀ a b C₁m C₁p C₂m C₂p C₃) := by
  apply exists_measurable_isVeryGoodAnnulus_version P μ βminus ρ hρ 0 N₀ a b C₁m C₁p C₂m C₂p C₃
  · exact (measurable_annulusBallMassSize_ratio βminus ρ 0 hρ).comp_aemeasurable
      (hGFF.aemeasurable_lqgMeasure hμ)
  · exact (measurable_annulusGreenPotentialRatio_zero ρ).comp_aemeasurable
      (hGFF.aemeasurable_lqgMeasure hμ)
  · intro n j k l
    apply exists_measurable_lqg_isGoodAnnulus_of_ae_point_avoidance hfull P γ α₀ hγ hγ2 hα
      hC hcirc μ hGFF hμ hatom (ρ * (7 : ℝ)⁻¹ ^ l)
      (mul_pos hρ (pow_pos (by norm_num) l))
      (((dyadicScale n * ρ / 100 : ℝ) : ℂ) * ((j : ℂ) + (k : ℂ) * Complex.I)) a b ha
    intro u _ x _ hxu
    exact hpolar u x hxu

end HarmonicBalls
