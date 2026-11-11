import HarmonicBalls.Proofs.Sec11.BufferedPinchObservableLaw
import HarmonicBalls.Steps.Sec11.PinchMetricMeasureObservable

/-! # Transfer through the canonical metric-measure observable -/

namespace HarmonicBalls

open MeasureTheory Filter Set Metric
open scoped ENNReal

open Classical in
/-- Transfer the buffered pinch event through the canonical metric-measure
observable law. The shift-law comparison and buffered-event positivity remain
explicit hypotheses; the metric-field axioms are staged for source review. -/
theorem IsPinchPointProofConfiguration.positive_singular_internal_pinch_of_canonicalLaw
    {U V W T Q' Q : Set ℂ} {δ ξ q b : ℝ}
    (h : IsPinchPointProofConfiguration U V W T Q' Q δ)
    (hξ : 0 < ξ) (hq : 0 < q) (hq1 : q ≤ 1)
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (γ α M : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (D : Ω → ℂ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (haxioms : LQGMetricFieldAxioms P γ ξ α hC hcirc)
    (hgff : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (hα : α < lqgQ γ) (hD : IsLQGMetricOfField P γ ξ α hC D)
    (X : Ω → Measure ℂ × {d : ℂ → ℂ → ℝ // IsEuclideanLengthMetric d})
    (hX : AEMeasurable X P)
    (hdecode : ∀ᵐ ω ∂P, (X ω).1 = μ ω ∧ (X ω).2.1 = D ω)
    (hshiftLaw : ∀ f : ℂ → ℝ, IsTestFunction univ f → (∀ x, f x ≤ 0) →
      (∀ x ∈ closure U ∪ (annulus 0 1 2)ᶜ, f x = 0) →
      (∀ x ∈ closedBall 0 (3 * δ), f x = 0) →
      ∃ Y : Ω → Measure ℂ × {d : ℂ → ℂ → ℝ // IsEuclideanLengthMetric d}, AEMeasurable Y P ∧ P.map Y ≪ P.map X ∧
        (∀ᵐ ω ∂P, (Y ω).1 =
            (μ ω).withDensity (fun x => ENNReal.ofReal (Real.exp (γ * f x))) ∧
          (Y ω).2.1 = fun x y => (weylScaling (D ω) ξ f x y).toReal))
    (hA : 0 < P {ω | pinchFirstEvent (D ω) W T Q' Q δ ∧
      pinchSecondEvent (μ ω) (D ω) U V δ M ∧
      (∀ w ∉ ball (0 : ℂ) 6, b ≤ D ω 0 w) ∧
      (⨆ x ∈ sphere (0 : ℂ) 5,
        internalMetric (D ω) (thickening (2 * δ) (Q ∪ W))ᶜ 0 x) <
          ENNReal.ofReal (q * b) ∧
      ENNReal.ofReal q * internalDiam (D ω) δ (thickening (3 * δ) W \ V) <
        ENNReal.ofReal (setDist (D ω) (sphere 0 (2 * δ)) (sphere 0 (3 * δ)))}) :
    0 < P {ω | HarmonicBalls.pinchPointEventWithInternalBounds (μ ω) (D ω)
      U T Q' Q M 1 0} := by
  exact h.positive_singular_internal_pinch_of_observableLaw hξ hq hq1 P γ α M
    hC hcirc D μ haxioms hgff hγ hγ₂ hα hD X Prod.fst (fun p => p.2.1)
    hX hdecode
    (measurableSet_pinchPointEventWithInternalBounds_on_lengthMetrics
      h.toIsPinchPointConfiguration M 0 (by norm_num : (0 : ℝ) < 1)) hshiftLaw hA


end HarmonicBalls
