import HarmonicBalls.Proofs.Sec11.SingularFieldInternalPinchWeyl
import HarmonicBalls.Steps.Sec11.SingularWeylBumpInverse

/-! # Singular-field pinch assembly with derived Weyl identities

The metric-field axioms are staged and await source check. Positivity of the
initial constrained event remains an explicit hypothesis.
-/

namespace HarmonicBalls

open MeasureTheory Set Metric Filter
open scoped ENNReal

/-- Conditional strengthened pinch assembly for the logarithmically singular
field, with the shifted length and Weyl identities derived from the staged
metric-field axioms. -/
theorem IsPinchPointProofConfiguration.exists_positive_measure_singularField_internal_pinch_shift_of_metricFieldAxioms
    {U V W T Q' Q : Set ℂ} {δ ξ : ℝ}
    (h : IsPinchPointProofConfiguration U V W T Q' Q δ) (hξ : 0 < ξ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ M : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (D : Ω → ℂ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (haxioms : LQGMetricFieldAxioms P γ ξ α₀ hC hcirc)
    (hgff : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (hα : α₀ < lqgQ γ) (hD : IsLQGMetricOfField P γ ξ α₀ hC D)
    (hA : 0 < P {ω | pinchFirstEvent (D ω) W T Q' Q δ ∧
      pinchSecondEvent (μ ω) (D ω) U V δ M ∧
      (⨆ x ∈ sphere (0 : ℂ) 5,
        internalMetric (D ω) ((thickening (2 * δ) (Q ∪ W))ᶜ ∩ ball 0 6) 0 x) <
        ENNReal.ofReal (setDist (D ω) Q' (frontier Q))}) :
    ∃ f : ℂ → ℝ, IsTestFunction univ f ∧ (∀ x, f x ≤ 0) ∧
      (∀ x ∈ closure U ∪ (annulus 0 1 2)ᶜ, f x = 0) ∧
      (∀ x ∈ closedBall 0 (3 * δ), f x = 0) ∧
      0 < P {ω | HarmonicBalls.pinchPointEventWithInternalBounds
        ((μ ω).withDensity (fun x => ENNReal.ofReal (Real.exp (γ * f x))))
        (fun x y => (weylScaling (D ω) ξ f x y).toReal) U T Q' Q M 1 0} := by
  apply h.exists_positive_measure_singularField_internal_pinch_shift hξ P γ α₀ M hC hcirc D μ
    haxioms hgff hγ hγ₂ hα hD ?_ hA
  intro f htest hfneg _
  filter_upwards [ae_singularField_weylBump_identities_of_metricFieldAxioms
    P γ ξ α₀ hC hcirc D haxioms hgff hγ hγ₂ hα hD hξ.le] with ω hω
  exact hω f htest.1.continuous htest.2.1 hfneg

#print axioms IsPinchPointProofConfiguration.exists_positive_measure_singularField_internal_pinch_shift_of_metricFieldAxioms

end HarmonicBalls
