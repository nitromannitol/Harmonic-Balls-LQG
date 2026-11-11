import HarmonicBalls.FirstPass.S11i.Faithful
import HarmonicBalls.FirstPass.S11h.LocalEvents
import HarmonicBalls.FirstPass.S11e.Include
import HarmonicBalls.FirstPass.S11j.Geometry

/-!
# Deterministic implication of the local certificate into the pinch-point event

The one-sided local certificate of Lemma 11.12 asks that the local events of the bounded corridor imply the pinch-point event
`Ĝ₁(0; M)` (`pinchPointEvent`). This file gives the deterministic part (a.s. under `IsLQGMetricOfField`):
the local events `E₁ = {L > A, a₀ > d₀}`, `E₂(M) = {a₁ > d₁, μ(U) > M S}`, `E₃ = {a₂ > d₂}`
(`pinchFirstEventLocal`, `pinchSecondEventLocal`, `pinchThirdEventLocal`, `FirstPass/S11h/LocalEvents.lean`) imply the
whole-plane auxiliary events (monotonicity, note eq. (3.2)), which imply the pinch-point event by the already proved
`pinchPointEvent_of_auxiliary_events` (`FirstPass/S11e/Include.lean:30`, paper lem:include, lines 3637-3657).

No probability and no decoder is used here.
-/

namespace HarmonicBalls

open MeasureTheory Set Metric
open scoped ENNReal

/-- Deterministic implication (paper lem:include with the local events of [C44]): for a buffered pinch geometry, a metric
`D` which is a Euclidean length metric and nonnegative, and `M`, the local events `E₁ ∩ E₂(M) ∩ E₃` imply the pinch-point
event `Ĝ₁(0; M)` of the true measure `μ` and metric `D`. -/
theorem pinchPointEvent_of_local_events
    {U V W T Q' Q : Set ℂ} {δ : ℝ} (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ)
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) (hnonneg : ∀ x y, 0 ≤ D x y)
    (μ : Measure ℂ) (M : ℝ)
    (hfirst : pinchFirstEventLocal D W T Q' Q δ)
    (hsecond : pinchSecondEventLocal μ D U V δ M)
    (hthird : pinchThirdEventLocal D V W δ) :
    pinchPointEvent μ D U T Q' Q M 1 0 :=
  pinchPointEvent_of_auxiliary_events (hgeo.toPinchPointProofConfiguration hgeo.U_nonempty) hD hnonneg μ M
    (pinchFirstEventLocal_subset D hnonneg W T Q' Q δ hfirst)
    (pinchSecondEventLocal_subset μ D U V δ M hsecond)
    (pinchThirdEventLocal_subset D V W δ hthird)

end HarmonicBalls
