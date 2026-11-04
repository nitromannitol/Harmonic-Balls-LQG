import HarmonicBalls.Proofs.Sec11.TimeMetricBallAE

/-! # Conditional reduction of Proposition 11.11 -/

namespace HarmonicBalls

open MeasureTheory Set Filter

universe u

/-- Proposition 11.11 at fixed parameters follows from the annulus comparison,
the abundance of pinch scales, and the explicitly staged metric and
non-atomicity inputs. -/
theorem harmonicBallNotMetricBall_of_comparison_and_pinch
    (hbound : AnnulusMassBoundByHarmonicChainStmt.{u})
    (hmany : ManyPinchScalesStmt.{u})
    (γ α₀ ξ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2) (hα : α₀ < lqgQ γ)
    (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ) (Λ : Ω → ℝ → Set ℂ)
    (hmetricAxioms : LQGMetricFieldAxioms P γ ξ α₀ hC hcirc)
    (hnonatomic : LQGMeasureNonatomic P γ α₀ hC hcirc)
    (hgff : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hmetric : IsLQGMetricOfField P γ ξ α₀ hC D)
    (hfamily : ∀ᵐ ω ∂P, IsHarmonicBallFamily (μ ω) (Λ ω) 0) :
    ∀ᵐ ω ∂P, ∀ᵐ t ∂volume, 0 < t → ∀ w : ℂ, ∀ r : ℝ,
      Λ ω t ≠ lqgMetricBall (D ω) w r := by
  filter_upwards [typical_boundary_ne_metricBall hbound hmany γ α₀ ξ hγ hγ₂ hα
      Ω P hC hcirc μ D Λ hmetricAxioms hnonatomic hgff hμ hmetric hfamily,
    ae_isEuclideanLengthMetric_of_metricFieldAxioms P γ ξ α₀ hC hcirc D
      hmetricAxioms hgff hγ hγ₂ hα hmetric,
    hμ, hfamily] with ω hpoint hD hμω hfamilyω
  let : IsLocallyFiniteMeasure (μ ω) := hμω.isLocallyFiniteMeasure
  have hnonneg : ∀ x y, 0 ≤ D ω x y := by
    intro x y
    have ht := hD.triangle x y x
    rw [hD.self_eq_zero, hD.symm y x] at ht
    linarith
  exact ae_time_ne_metricBall_of_ae_boundary_exclusion (μ ω) (Λ ω) (D ω) 0
    hfamilyω.2 hpoint hnonneg

end HarmonicBalls
