import HarmonicBalls.Proofs.Sec11.CorrectedPinchFirstEventTransfer

/-! Uniform deterministic thresholds for the first Weyl-shifted pinch event. -/

namespace HarmonicBalls

open Set Metric
open scoped ENNReal

/-- Strict bounds on the four unshifted quantities and two numerical
inequalities imply the first auxiliary event after the Weyl shift. -/
theorem IsPinchPointProofConfiguration.first_event_of_thresholds
    {U V W T Q' Q : Set ℂ} {δ ξ a b : ℝ}
    (h : IsPinchPointProofConfiguration U V W T Q' Q δ)
    {D E : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hE : IsEuclideanLengthMetric E) {f : ℂ → ℝ}
    (hEnonneg : ∀ x y, 0 ≤ E x y)
    (hforward : ∀ x y, ENNReal.ofReal (E x y) = weylScaling D ξ f x y)
    (hreverse : ∀ x y, ENNReal.ofReal (D x y) =
      weylScaling E ξ (fun z => -f z) x y)
    (hcorridor : ∀ z ∈ ball (0 : ℂ) 6 \ (closure (thickening (2 * δ) Q) ∪
      closure (thickening (2 * δ) W)), ξ * f z ≤ ξ * b)
    (hQ : ∀ z ∈ thickening (δ / 2) Q, f z = a)
    (hroot : ∀ z ∈ ball 0 (3 * δ / 4), f z = b)
    (houter : ∀ z ∈ thickening δ (T \ thickening (3 * δ) W), f z = 0)
    {n m k l : ℕ}
    (hgapQ : (n : ℝ≥0∞)⁻¹ ≤ ENNReal.ofReal (setDist D Q' (frontier Q)))
    (hpath : (⨆ y ∈ sphere (0 : ℂ) 5, internalMetric D
      (ball 0 6 \ (closure (thickening (2 * δ) Q) ∪
        closure (thickening (2 * δ) W))) 0 y) ≤ m)
    (hgap0 : (k : ℝ≥0∞)⁻¹ ≤ ENNReal.ofReal (setDist D {0} (sphere 0 (δ / 2))))
    (hdiam : internalDiam D δ (T \ thickening (3 * δ) W) ≤ l)
    (hnumQ : ENNReal.ofReal (Real.exp (ξ * b)) * m <
      ENNReal.ofReal (Real.exp (ξ * a)) * (n : ℝ≥0∞)⁻¹)
    (hnum0 : (l : ℝ≥0∞) < ENNReal.ofReal (Real.exp (ξ * b)) * (k : ℝ≥0∞)⁻¹) :
    pinchFirstEvent E W T Q' Q δ := by
  apply h.first_event_of_buffered_weyl_bounds hD hE hEnonneg hforward hreverse
    hcorridor hQ hroot houter
  · apply lt_of_le_of_lt (show _ ≤ ENNReal.ofReal (Real.exp (ξ * b)) * m by gcongr)
    exact lt_of_lt_of_le hnumQ (by gcongr)
  · exact lt_of_le_of_lt hdiam (lt_of_lt_of_le hnum0 (by gcongr))


end HarmonicBalls
