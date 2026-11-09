import HarmonicBalls.FirstPass.S11j.Geometry
import HarmonicBalls.Draft.Section11Corrected

/-!
# First pass, Section 11: the faithful buffered geometry as a corrected pinch configuration (fp-S11j, owner n4)

`IsCorrectedPinchConfiguration` (`Draft/Section11Corrected.lean`) is the corpus structure of the corrected fixed
geometry: the pinch proof configuration, the six buffer fields, `δ < 10⁻³`, and the corridor field
`corridor_contains : {0} ∪ sphere 0 5 ⊆ pinchCorridor W Q δ`. For nonempty `U`, a faithful
`IsBufferedPinchGeometry` (`FirstPass/S11h/Faithful.lean`) supplies every field except the corridor. The corridor
is the open point F4 of `reports/n4.md`: it is not a field of `IsBufferedPinchGeometry`, so it enters here as an
explicit hypothesis, and nothing is claimed about it.
-/

namespace HarmonicBalls

open MeasureTheory Set Metric

/-- The faithful buffered geometry with nonempty `U`, together with the corridor containment `hcor` (F4), is a corpus
corrected pinch configuration. The fields are those of `IsBufferedPinchGeometry`: `δ < 10⁻³` (`delta_lt`) and the six
buffer conditions of eq:buffers (corrected paper lines 3184-3189), in the same form as the corpus structure. -/
theorem IsBufferedPinchGeometry.toIsCorrectedPinchConfiguration
    {U V W T Q' Q : Set ℂ} {δ : ℝ} (h : IsBufferedPinchGeometry U V W T Q' Q δ) (hU : U.Nonempty)
    (hcor : ({0} ∪ sphere (0 : ℂ) 5) ⊆ pinchCorridor W Q δ) :
    IsCorrectedPinchConfiguration U V W T Q' Q δ where
  toIsPinchPointProofConfiguration := h.toPinchPointProofConfiguration hU
  delta_small := h.delta_lt
  buffer_T := h.buffer_T
  buffer_U := h.buffer_U
  buffer_V := h.buffer_V
  buffer_W := h.buffer_W
  buffer_Q' := h.buffer_Q'
  buffer_Q := h.buffer_Q
  corridor_contains := hcor

#print axioms IsBufferedPinchGeometry.toIsCorrectedPinchConfiguration

end HarmonicBalls
