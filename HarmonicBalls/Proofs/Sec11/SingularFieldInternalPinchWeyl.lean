import HarmonicBalls.Proofs.Sec11.MetricInternalPinchWeyl
import HarmonicBalls.Steps.Sec11.SingularFieldWeylForward

/-! # Strengthened pinch event for a singular-field Weyl shift

The metric-field axioms are staged and pending source check. Positivity of the
initial constrained event, and the shifted metric's length, zero-weight and
inverse identities, remain explicit hypotheses. No change of law is asserted.
-/

namespace HarmonicBalls

open MeasureTheory Set Metric Filter
open scoped ENNReal

/-- Conditional strengthened pinch assembly for the logarithmically singular
field. The shifted metric is the real representative of its Weyl scaling. -/
theorem IsPinchPointProofConfiguration.exists_positive_measure_singularField_internal_pinch_shift
    {U V W T Q' Q : Set ℂ} {δ ξ : ℝ}
    (h : IsPinchPointProofConfiguration U V W T Q' Q δ) (hξ : 0 < ξ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ M : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (D : Ω → ℂ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (haxioms : LQGMetricFieldAxioms P γ ξ α₀ hC hcirc)
    (hgff : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (hα : α₀ < lqgQ γ) (hD : IsLQGMetricOfField P γ ξ α₀ hC D)
    (hshift : ∀ f : ℂ → ℝ, IsTestFunction univ f → (∀ x, f x ≤ 0) →
      (∀ x ∈ closure U ∪ (annulus 0 1 2)ᶜ, f x = 0) →
      ∀ᵐ ω ∂P,
        let E : ℂ → ℂ → ℝ := fun x y => (weylScaling (D ω) ξ f x y).toReal
        IsEuclideanLengthMetric E ∧
        (∀ x y, weylScaling E ξ 0 x y = ENNReal.ofReal (E x y)) ∧
        (∀ x y, ENNReal.ofReal (D ω x y) =
          weylScaling E ξ (fun z => -f z) x y))
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
  have hmetric := ae_isEuclideanLengthMetric_of_metricFieldAxioms P γ ξ α₀ hC hcirc D
    haxioms hgff hγ hγ₂ hα hD
  have hzero := ae_weylScaling_zero_of_metricFieldAxioms P γ ξ α₀ hC hcirc D
    haxioms hgff hγ hγ₂ hα hD
  have hfinite := ae_singularField_negative_weylScaling_finite P γ ξ α₀ hC hcirc D
    haxioms hgff hγ hγ₂ hα hD hξ.le
  apply h.exists_positive_measure_internal_pinch_shift_of_weyl_identities hξ P γ M D
    (fun f ω x y => (weylScaling (D ω) ξ f x y).toReal) μ hmetric ?_ hA
  intro f htest hfneg hfsupport
  filter_upwards [hmetric, hzero, hfinite, hshift f htest hfneg hfsupport] with ω hm hz hf hs
  refine ⟨hm, hs.1, hz, ?_, hs.2.1, hs.2.2⟩
  intro x y
  exact (hf f hfneg x y).2

end HarmonicBalls
