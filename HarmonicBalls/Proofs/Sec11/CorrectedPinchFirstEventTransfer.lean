import HarmonicBalls.Proofs.Sec11.CorrectedPinchBufferedGaps
import HarmonicBalls.Proofs.Sec11.CorrectedPinchFirstWeight
import HarmonicBalls.Steps.Sec11.PinchMetricBarrier

/-! Transfer of the first pinch-event inequalities through a Weyl shift. -/

namespace HarmonicBalls

open Set Metric
open scoped ENNReal

/-- In a Euclidean length metric, the distance from a center to a sphere is
nondecreasing in its radius. -/
theorem IsEuclideanLengthMetric.ofReal_setDist_center_sphere_mono
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y) {z : ℂ} {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) :
    ENNReal.ofReal (setDist D {z} (sphere z a)) ≤
      ENNReal.ofReal (setDist D {z} (sphere z b)) := by
  have hb : 0 ≤ b := ha.trans hab
  have hnonneg' : 0 ≤ setDist D (sphere z a) (ball z b)ᶜ := by
    unfold setDist
    apply Real.sInf_nonneg
    rintro _ ⟨x, hx, y, hy, rfl⟩
    exact hnonneg x y
  rw [ofReal_setDist_eq_iInf (singleton_nonempty z) (NormedSpace.sphere_nonempty.mpr hb)]
  simp only [iInf_singleton]
  refine le_iInf fun y => le_iInf fun hy => ?_
  apply ENNReal.ofReal_le_ofReal
  have hy' : y ∉ ball z b := by
    rw [mem_sphere] at hy
    rw [mem_ball]
    linarith
  have hp := hD.center_to_complement_lower_bound hnonneg ha hab hy'
  linarith

/-- The buffered plateau estimates and strict numerical bounds imply the
first auxiliary pinch event for the shifted metric. -/
theorem IsPinchPointProofConfiguration.first_event_of_buffered_weyl_bounds
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
    (hfirst : ENNReal.ofReal (Real.exp (ξ * b)) *
        (⨆ y ∈ sphere (0 : ℂ) 5, internalMetric D
          (ball 0 6 \ (closure (thickening (2 * δ) Q) ∪
            closure (thickening (2 * δ) W))) 0 y) <
      ENNReal.ofReal (Real.exp (ξ * a)) * ENNReal.ofReal (setDist D Q' (frontier Q)))
    (hsecond : internalDiam D δ (T \ thickening (3 * δ) W) <
      ENNReal.ofReal (Real.exp (ξ * b)) *
        ENNReal.ofReal (setDist D {0} (sphere 0 (δ / 2)))) :
    pinchFirstEvent E W T Q' Q δ := by
  have hb := hD.first_weight_metric_bounds hE hEnonneg hforward hcorridor houter
  have hq := h.obstacle_boundary_weyl_lower_bound hD hE hQ hreverse
  have hr := h.root_boundary_weyl_lower_bound hD hE hroot hreverse
  have hm := hE.ofReal_setDist_center_sphere_mono hEnonneg
    (show 0 ≤ δ / 2 by linarith [h.δ₀_mem.1])
    (show δ / 2 ≤ δ by linarith [h.δ₀_mem.1]) (z := 0)
  constructor
  · apply lt_of_le_of_lt ?_ ((lt_of_lt_of_le hfirst hq))
    apply le_trans ?_ hb.1
    apply iSup_le
    intro y
    apply iSup_le
    intro hy
    exact le_iSup_of_le y (le_iSup_of_le hy
      (internalMetric_anti E (inter_subset_left) 0 y))
  · exact lt_of_le_of_lt hb.2 (lt_of_lt_of_le hsecond (hr.trans hm))


end HarmonicBalls
