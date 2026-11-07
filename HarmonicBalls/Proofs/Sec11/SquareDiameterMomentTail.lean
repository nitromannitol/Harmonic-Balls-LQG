import HarmonicBalls.Proofs.Sec11.PinchTailExponent
import HarmonicBalls.Steps.Sec11.NormalizedDiameterMoment

/-! # Power-scale moment bounds and diameter tails

The moment estimate is an explicit hypothesis; no LQG metric estimate is
asserted in this module. -/

namespace HarmonicBalls
open MeasureTheory Set
open scoped ENNReal

/-- Markov's inequality converts a positive moment estimate at a positive
side length into a power-law diameter tail. -/
theorem measure_power_threshold_le_of_lintegral_rpow_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → ℝ≥0∞)
    (r s a p : ℝ) (hr : 0 < r) (hp : 0 < p) (hX : AEMeasurable X P)
    (hmoment : (∫⁻ ω, (X ω) ^ p ∂P) ≤ ENNReal.ofReal (r ^ a)) :
    P {ω | ENNReal.ofReal (r ^ s) < X ω} ≤
      ENNReal.ofReal (r ^ (a - s * p)) := by
  have ht : ENNReal.ofReal (r ^ s) ^ p = ENNReal.ofReal (r ^ (s * p)) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hr.le _) hp.le,
      ← Real.rpow_mul hr.le]
  have hzero : ENNReal.ofReal (r ^ (s * p)) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hr _)).ne'
  calc
    _ ≤ P {ω | ENNReal.ofReal (r ^ (s * p)) ≤ (X ω) ^ p} := by
      apply measure_mono
      intro ω hω
      rw [← ht]
      exact ENNReal.rpow_le_rpow hω.le hp.le
    _ ≤ (∫⁻ ω, (X ω) ^ p ∂P) / ENNReal.ofReal (r ^ (s * p)) :=
      meas_ge_le_lintegral_div
        (ENNReal.continuous_rpow_const.measurable.comp_aemeasurable hX)
        hzero ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (r ^ a) / ENNReal.ofReal (r ^ (s * p)) := by gcongr
    _ = _ := by
      rw [← ENNReal.ofReal_div_of_pos (Real.rpow_pos_of_pos hr _),
        ← Real.rpow_sub hr]

/-- The optimizing moment turns the quadratic moment exponent into the
square-diameter tail exponent of DFGPS (3.65). -/
theorem measure_power_threshold_le_of_optimized_moment
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → ℝ≥0∞)
    (r ξ Q s e : ℝ) (hr : 0 < r) (hξ : 0 < ξ) (hs : s < ξ * Q)
    (hX : AEMeasurable X P)
    (hmoment : let t := (ξ * Q - s) / ξ ^ 2
      (∫⁻ ω, (X ω) ^ t ∂P) ≤ ENNReal.ofReal
        (r ^ (ξ * Q * t - ξ ^ 2 * t ^ 2 / 2 + e))) :
    P {ω | ENNReal.ofReal (r ^ s) < X ω} ≤
      ENNReal.ofReal (r ^ ((ξ * Q - s) ^ 2 / (2 * ξ ^ 2) + e)) := by
  let t := (ξ * Q - s) / ξ ^ 2
  have ht : 0 < t := div_pos (by linarith) (sq_pos_of_pos hξ)
  have heq : ξ * Q * t - ξ ^ 2 * t ^ 2 / 2 + e - s * t =
      (ξ * Q - s) ^ 2 / (2 * ξ ^ 2) + e := by
    dsimp [t]
    field_simp
    ring
  simpa only [heq] using measure_power_threshold_le_of_lintegral_rpow_le P X r s
    (ξ * Q * t - ξ ^ 2 * t ^ 2 / 2 + e) t hr ht hX hmoment

#print axioms measure_power_threshold_le_of_lintegral_rpow_le
#print axioms measure_power_threshold_le_of_optimized_moment
end HarmonicBalls
