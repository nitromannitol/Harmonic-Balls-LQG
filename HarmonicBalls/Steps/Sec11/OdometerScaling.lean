import HarmonicBalls.Proofs.Sec5.SupersolutionScaling
import HarmonicBalls.Draft.Section6

/-!
# Dilation of the finite-radius odometer

The deterministic scaling identity needed to transfer the annular comparison
estimates from the unit disk to other radii.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Section6

/-- Positive dilation of the domain, together with positive multiplication of
the measure and time, scales the odometer by the same multiplicative factor. -/
theorem odometer_comp_real_smul {μ : Measure ℂ} {R k c t : ℝ} {p x : ℂ}
    (hk : 0 < k) (hc : 0 < c) (ht : 0 ≤ t)
    (hx : x ∈ closedBall (0 : ℂ) R) (hxp : x ≠ p) :
    odometer (ENNReal.ofReal c • Measure.map (fun y : ℂ => k⁻¹ • y) μ)
      R p (c * t) x = c * odometer μ (k * R) (k • p) t (k • x) := by
  simp only [odometer]
  rw [leastSupersolution_comp_real_smul hk hc ht hx hxp, greenFunction_ball_smul hk]
  ring

/-- At every point of the closed unit disk, including the pole, the extended
unit-disk odometer scales to the extended odometer in the larger disk. -/
theorem odometerExt_comp_real_smul {μ : Measure ℂ} {k c t : ℝ} {p x : ℂ}
    (hk : 0 < k) (hc : 0 < c) (ht : 0 ≤ t)
    (hx : x ∈ closedBall (0 : ℂ) 1) :
    odometerExt (ENNReal.ofReal c • Measure.map (fun y : ℂ => k⁻¹ • y) μ)
      p (c * t) x = if x = p then ⊤ else
        ENNReal.ofReal c * ENNReal.ofReal (odometer μ k (k • p) t (k • x)) := by
  by_cases hxp : x = p
  · simp only [hxp, odometerExt_self, ↓reduceIte]
  · simp only [odometerExt, hxp, ↓reduceIte]
    rw [odometer_comp_real_smul hk hc ht hx hxp, mul_one,
      ENNReal.ofReal_mul hc.le]

end HarmonicBalls
