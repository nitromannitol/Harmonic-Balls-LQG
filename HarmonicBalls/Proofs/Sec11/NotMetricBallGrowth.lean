import HarmonicBalls.Proofs.Sec11.NotMetricBall
import HarmonicBalls.Proofs.SecA.ObstacleNonCoincidenceHarmonic
import HarmonicBalls.Steps.Sec3.Basic

/-! # Non-atomicity from LQG volume growth -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter

universe u

/-- Volume growth implies the non-atomicity property used in the Section 11
boundary-point arguments. -/
theorem lqgMeasureNonatomic_of_volumeGrowth
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) :
    LQGMeasureNonatomic P γ α₀ hC hcirc := by
  intro hG hγ hγ₂ hα μ hμ
  obtain ⟨βm, βp, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hgrowth hγ hγ₂ hα hG hμ
  filter_upwards [hV] with ω hV
  intro x
  have hR : 0 < ‖x‖ + 1 := by positivity
  have hx : x ∈ ball (0 : ℂ) (‖x‖ + 1) := by
    simp only [mem_ball, dist_zero_right]
    linarith
  exact (hV.2 (‖x‖ + 1) hR).measure_singleton hx

/-- Proposition 11.11 at fixed field parameters from the annulus comparison,
pinch scales, volume growth, and the staged metric-field axioms. -/
theorem harmonicBallNotMetricBall_of_comparison_pinch_and_volumeGrowth
    (hbound : AnnulusMassBoundByHarmonicChainStmt.{u})
    (hmany : ManyPinchScalesStmt.{u})
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    (γ α₀ ξ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2) (hα : α₀ < lqgQ γ)
    (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ) (Λ : Ω → ℝ → Set ℂ)
    (hmetricAxioms : LQGMetricFieldAxioms P γ ξ α₀ hC hcirc)
    (hgff : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hmetric : IsLQGMetricOfField P γ ξ α₀ hC D)
    (hfamily : ∀ᵐ ω ∂P, IsHarmonicBallFamily (μ ω) (Λ ω) 0) :
    ∀ᵐ ω ∂P, ∀ᵐ t ∂volume, 0 < t → ∀ w : ℂ, ∀ r : ℝ,
      Λ ω t ≠ lqgMetricBall (D ω) w r :=
  harmonicBallNotMetricBall_of_comparison_and_pinch hbound hmany γ α₀ ξ hγ hγ₂ hα
    Ω P hC hcirc μ D Λ hmetricAxioms
    (lqgMeasureNonatomic_of_volumeGrowth hgrowth P γ α₀ hC hcirc)
    hgff hμ hmetric hfamily

/-- The frozen statement of Proposition 11.11 follows from the annulus
comparison, pinch scales, volume growth, and metric-field axioms at the
actual field parameters. The metric-field axioms are staged literature
inputs and remain subject to source checking. -/
theorem harmonicBallNotMetricBallStmt_of_comparison_pinch_and_volumeGrowth
    (hbound : AnnulusMassBoundByHarmonicChainStmt.{u})
    (hmany : ManyPinchScalesStmt.{u})
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    (hmetricAxioms : ∀ γ α₀ ξ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
        IsWholePlaneGFF P hC hcirc → LQGMetricFieldAxioms P γ ξ α₀ hC hcirc) :
    HarmonicBallNotMetricBallStmt.{u} := by
  intro γ α₀ ξ hγ hγ₂ hα Ω _ P hC hcirc μ D hgff hμ hmetric Λ hfamily
  exact harmonicBallNotMetricBall_of_comparison_pinch_and_volumeGrowth hbound hmany hgrowth
    γ α₀ ξ hγ hγ₂ hα Ω P hC hcirc μ D Λ
    (hmetricAxioms γ α₀ ξ hγ hγ₂ hα Ω P hC hcirc hgff)
    hgff hμ hmetric hfamily

end HarmonicBalls
