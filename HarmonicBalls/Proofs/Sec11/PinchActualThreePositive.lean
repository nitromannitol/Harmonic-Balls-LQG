import HarmonicBalls.Proofs.Sec11.PinchActualThirdProbability
import HarmonicBalls.Proofs.Sec11.PinchActualFirstTwoPositive

/-! # Positive probability of all three local pinch events -/

namespace HarmonicBalls

open MeasureTheory Set

/-- The three local pinch events have positive joint probability for the inserted
measure and metric of the same field. -/
theorem IsWholePlaneGFF.pinchLocal_three_positive
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {γ ξ α M δ : ℝ} {μ : Ω → Measure ℂ} {D : Ω → ℂ → ℂ → ℝ}
    {U V W T Qprime Q : Set ℂ}
    (hh : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hα : α < lqgQ γ)
    (hD : IsLQGMetricOfField P γ ξ α hC D)
    (hgeo : IsBufferedPinchGeometry U V W T Qprime Q δ)
    (hconfig : IsPinchPointProofConfiguration U V W T Qprime Q δ) :
    0 < P {ω | pinchFirstEventLocal (D ω) W T Qprime Q δ ∧
      pinchSecondEventLocal (μ ω) (D ω) U V δ M ∧
      pinchThirdEventLocal (D ω) V W δ} := by
  exact hh.pinchLocal_three_positive_of_first_two hμ hγ hγ₂ hα hD hgeo hconfig
    (hh.pinchLocal_first_two_positive hγ hγ₂ hα hμ hD hgeo)

end HarmonicBalls
