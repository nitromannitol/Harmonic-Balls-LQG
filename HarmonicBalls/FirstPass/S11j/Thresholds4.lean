import HarmonicBalls.FirstPass.S11j.Geometry
import HarmonicBalls.FirstPass.S11h.SetDistPos
import HarmonicBalls.Steps.Sec11.PinchDistancePositivity

/-!
# Section 11: deterministic positivity of two thresholds for the faithful first event

For a Euclidean length metric `D`, the two variables `setDist D Q' (frontier Q)` (`X1`) and `setDist D {0} (sphere 0 (δ/2))`
(`X3`, the threshold of the core `exists_uniform_first_event_shift`) are strictly positive. Only the faithful geometry
with nonempty `U` is used (`IsBufferedPinchGeometry.toPinchPointProofConfiguration`, `FirstPass/S11j/Geometry.lean`).
-/

namespace HarmonicBalls

open MeasureTheory Set Metric
open scoped ENNReal

/-- `X1 > 0` on the faithful geometry: `D(Q', ∂Q) > 0` for a Euclidean length metric (paper eq:first-event, line 3257). -/
theorem IsBufferedPinchGeometry.setDist_Q'_frontier_pos {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (h : IsBufferedPinchGeometry U V W T Q' Q δ) (hU : U.Nonempty) {D : ℂ → ℂ → ℝ}
    (hD : IsEuclideanLengthMetric D) : 0 < setDist D Q' (frontier Q) :=
  (h.toPinchPointProofConfiguration hU).toIsPinchPointConfiguration.setDist_frontier_pos hD

/-- `X3 > 0`: `D(0, ∂B_r) > 0` for a Euclidean length metric and `r > 0` (the threshold `k⁻¹ ≤ setDist D {0} (sphere 0 (δ/2))`). -/
theorem setDist_zero_sphere_pos_of_isEuclideanLengthMetric {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {r : ℝ} (hr : 0 < r) : 0 < setDist D {0} (sphere (0 : ℂ) r) := by
  refine setDist_pos_of_isEuclideanLengthMetric hD isCompact_singleton (isCompact_sphere _ _)
    (singleton_nonempty _) (NormedSpace.sphere_nonempty.2 hr.le) ?_
  rw [disjoint_singleton_left, mem_sphere, dist_self]
  exact fun h0 => hr.ne' h0.symm

#print axioms IsBufferedPinchGeometry.setDist_Q'_frontier_pos
#print axioms setDist_zero_sphere_pos_of_isEuclideanLengthMetric

end HarmonicBalls
