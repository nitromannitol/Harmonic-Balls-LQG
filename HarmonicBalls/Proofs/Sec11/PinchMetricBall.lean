import HarmonicBalls.Proofs.Sec11.PinchInner
import HarmonicBalls.Proofs.Sec11.PinchOuter
import HarmonicBalls.Steps.Sec11.MetricField

/-!
# Lemma 11.14 from the staged metric-field proposition

The deterministic result is proved using almost-minimizing paths. The
singular-field metric proposition remains an explicit staged hypothesis.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter

universe u

/-- Lemma 11.14 for one probability space, conditional on the staged
singular-field metric proposition at its actual parameters. -/
theorem pinchEventMetricBallConsequence_of_metricFieldAxioms
    (U T Q' Q : Set ℂ) (hconfig : IsPinchPointConfiguration U T Q' Q)
    (γ α₀ ξ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2) (hα : α₀ < lqgQ γ)
    (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ)
    (haxioms : LQGMetricFieldAxioms P γ ξ α₀ hC hcirc)
    (hgff : IsWholePlaneGFF P hC hcirc) (hmetric : IsLQGMetricOfField P γ ξ α₀ hC D) :
    ∀ᵐ ω ∂P, ∀ M : ℝ, 0 < M → ∀ z : ℂ, ∀ r : ℝ, 0 < r → (0 : ℂ) ∉ ball z (10 * r) →
      ∀ u : ℝ, 0 < u → pinchPointEvent (μ ω) (D ω) U T Q' Q M r z →
      z ∈ frontier (lqgMetricBall (D ω) 0 u) →
      rescaledSet Q' r z ⊆ (lqgMetricBall (D ω) 0 u)ᶜ ∧
        rescaledSet T r z ⊆ lqgMetricBall (D ω) 0 u := by
  filter_upwards [ae_isEuclideanLengthMetric_of_metricFieldAxioms P γ ξ α₀ hC hcirc D
    haxioms hgff hγ hγ₂ hα hmetric] with ω hD
  have hnonneg : ∀ x y, 0 ≤ D ω x y := by
    intro x y
    have ht := hD.triangle x y x
    rw [hD.self_eq_zero, hD.symm y x] at ht
    linarith
  intro M _ z r hr hw u _ hp hz
  exact ⟨pinchPointEvent_outer_subset_compl_metricBall (μ ω) (D ω) U T Q' Q M r u 0 z
      hconfig hD hnonneg hp hr hw hz,
    pinchPointEvent_keyhole_subset_metricBall (μ ω) (D ω) U T Q' Q M r u 0 z
      hconfig hD hnonneg hp hr hw hz⟩

/-- The frozen Lemma 11.14 statement follows from the staged proposition for
all relevant probability spaces and parameters. This does not assert that the
staged proposition has been source-checked. -/
theorem pinchEventMetricBallConsequenceStmt_of_metricFieldAxioms
    (haxioms : ∀ (γ ξ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMetricFieldAxioms P γ ξ α₀ hC hcirc) :
    PinchEventMetricBallConsequenceStmt.{u} := by
  intro U T Q' Q hconfig γ α₀ ξ hγ hγ₂ hα Ω _ P hC hcirc μ D hgff _ hmetric
  exact pinchEventMetricBallConsequence_of_metricFieldAxioms U T Q' Q hconfig γ α₀ ξ hγ hγ₂ hα
    Ω P hC hcirc μ D (haxioms γ ξ α₀ Ω P hC hcirc) hgff hmetric

end HarmonicBalls
