import HarmonicBalls.Proofs.Sec11.BufferedPinchShiftLaw
import HarmonicBalls.Steps.Sec11.PinchBufferCompatibility
import HarmonicBalls.Proofs.Sec6.LQGWeylScaling

/-! # Radial product-gap event and singular-field shift

The metric-field axioms are staged and pending source review. The existence
of the compatible field shift and the positive joint product-gap event remain
explicit hypotheses. Measure Weyl scaling follows from the LQG limit. -/

namespace HarmonicBalls

open MeasureTheory Filter Set Metric
open scoped ENNReal

/-- Positive probability for the joint radial product-gap event transfers to
unit-scale internal pinch probability under a compatible field shift. -/
theorem IsPinchPointProofConfiguration.positive_singular_internal_pinch_of_radial_product
    {U V W T Q' Q : Set ℂ} {δ ξ : ℝ}
    (h : IsPinchPointProofConfiguration U V W T Q' Q δ) (hξ : 0 < ξ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (γ α M : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (D : Ω → ℂ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (haxioms : LQGMetricFieldAxioms P γ ξ α hC hcirc)
    (hgff : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (hα : α < lqgQ γ) (hD : IsLQGMetricOfField P γ ξ α hC D)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hshift : ∀ f : ℂ → ℝ, IsTestFunction univ f → (∀ x, f x ≤ 0) →
      (∀ x ∈ closure U ∪ (annulus 0 1 2)ᶜ, f x = 0) →
      (∀ x ∈ closedBall 0 (3 * δ), f x = 0) →
      ∃ τ : Ω → Ω, Measure.QuasiMeasurePreserving τ P P ∧
        (∀ᵐ ω ∂P, fieldCircleAverage α (hcirc (τ ω)) =
          addCircleAverage (fieldCircleAverage α (hcirc ω)) f) ∧
        (∀ᵐ ω ∂P, D (τ ω) = fun x y => (weylScaling (D ω) ξ f x y).toReal))
    (hA : 0 < P {ω | pinchFirstEvent (D ω) W T Q' Q δ ∧
      pinchSecondEvent (μ ω) (D ω) U V δ M ∧
      (let b := setDist (D ω) {0} (sphere 0 5) +
        setDist (D ω) (sphere 0 5) (ball 0 6)ᶜ
       let L := ⨆ x ∈ sphere (0 : ℂ) 5,
         internalMetric (D ω) (thickening (2 * δ) (Q ∪ W))ᶜ 0 x
       let C := internalDiam (D ω) δ (thickening (3 * δ) W \ V)
       L.toReal < b ∧ L.toReal * C.toReal <
         b * setDist (D ω) (sphere 0 (2 * δ)) (sphere 0 (3 * δ)))}) :
    0 < P {ω | HarmonicBalls.pinchPointEventWithInternalBounds (μ ω) (D ω)
      U T Q' Q M 1 0} := by
  have hm := ae_isEuclideanLengthMetric_of_metricFieldAxioms P γ ξ α hC hcirc D
    haxioms hgff hγ hγ₂ hα hD
  obtain ⟨q, b, hq, hq1, hp⟩ := h.exists_positive_measure_buffer_of_radial_product P D μ hm hA
  exact h.positive_singular_internal_pinch_of_buffer_shiftMap hξ hq hq1 P γ α M hC hcirc D μ
    haxioms (Section6.lqgMeasureWeylScaling Ω P γ α hC hcirc) hgff hγ hγ₂ hα hD hμ hshift hp

#print axioms IsPinchPointProofConfiguration.positive_singular_internal_pinch_of_radial_product

end HarmonicBalls
