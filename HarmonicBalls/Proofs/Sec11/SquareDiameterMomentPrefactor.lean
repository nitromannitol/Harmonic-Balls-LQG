import HarmonicBalls.Proofs.Sec11.SquareDiameterMomentTail

/-! # Diameter moment bounds with fixed prefactors

These estimates convert an explicit moment hypothesis into a tail bound;
they do not assert an LQG metric moment estimate. -/

namespace HarmonicBalls
open MeasureTheory Set
open scoped ENNReal

/-- Markov's inequality retains a nonnegative fixed moment prefactor. -/
theorem measure_power_threshold_le_of_lintegral_rpow_le_prefactor
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → ℝ≥0∞)
    (r s a p A : ℝ) (hr : 0 < r) (hp : 0 < p)
    (hX : AEMeasurable X P)
    (hmoment : (∫⁻ ω, (X ω) ^ p ∂P) ≤ ENNReal.ofReal (A * r ^ a)) :
    P {ω | ENNReal.ofReal (r ^ s) < X ω} ≤
      ENNReal.ofReal (A * r ^ (a - s * p)) := by
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
    _ ≤ ENNReal.ofReal (A * r ^ a) / ENNReal.ofReal (r ^ (s * p)) := by gcongr
    _ = _ := by
      rw [← ENNReal.ofReal_div_of_pos (Real.rpow_pos_of_pos hr _),
        mul_div_assoc, ← Real.rpow_sub hr]

/-- The optimizing moment preserves the prefactor in the quadratic tail. -/
theorem measure_power_threshold_le_of_optimized_moment_prefactor
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → ℝ≥0∞)
    (r ξ Q s e A : ℝ) (hr : 0 < r) (hξ : 0 < ξ) (hs : s < ξ * Q)
    (hX : AEMeasurable X P)
    (hmoment : let t := (ξ * Q - s) / ξ ^ 2
      (∫⁻ ω, (X ω) ^ t ∂P) ≤ ENNReal.ofReal
        (A * r ^ (ξ * Q * t - ξ ^ 2 * t ^ 2 / 2 + e))) :
    P {ω | ENNReal.ofReal (r ^ s) < X ω} ≤
      ENNReal.ofReal (A * r ^ ((ξ * Q - s) ^ 2 / (2 * ξ ^ 2) + e)) := by
  let t := (ξ * Q - s) / ξ ^ 2
  have ht : 0 < t := div_pos (by linarith) (sq_pos_of_pos hξ)
  have heq : ξ * Q * t - ξ ^ 2 * t ^ 2 / 2 + e - s * t =
      (ξ * Q - s) ^ 2 / (2 * ξ ^ 2) + e := by
    dsimp [t]
    field_simp
    ring
  simpa only [heq] using measure_power_threshold_le_of_lintegral_rpow_le_prefactor
    P X r s (ξ * Q * t - ξ ^ 2 * t ^ 2 / 2 + e) t A hr ht hX hmoment

/-- Restore the normalization and unit-circle factor in the prefactor tail. -/
theorem IsWholePlaneGFF.measure_scaled_power_tail_of_optimized_moment_prefactor
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (X : Ω → ℝ≥0∞)
    (c r ξ Q s e A : ℝ) (hc : 0 < c) (hr : 0 < r) (hξ : 0 < ξ)
    (hs : s < ξ * Q)
    (hX : AEMeasurable (fun ω => (ENNReal.ofReal c)⁻¹ * X ω) P)
    (hmoment : let t := (ξ * Q - s) / ξ ^ 2
      (∫⁻ ω, ((ENNReal.ofReal c)⁻¹ * X ω) ^ t ∂P) ≤ ENNReal.ofReal
        (A * r ^ (ξ * Q * t - ξ ^ 2 * t ^ 2 / 2 + e))) :
    P {ω | ENNReal.ofReal (c * r ^ s) *
      ENNReal.ofReal (Real.exp (ξ * hcirc ω 1 0)) < X ω} ≤
      ENNReal.ofReal (A * r ^ ((ξ * Q - s) ^ 2 / (2 * ξ ^ 2) + e)) := by
  rw [h.measure_tail_with_unit_circle_factor ξ (ENNReal.ofReal (c * r ^ s)) X]
  have hc0 : ENNReal.ofReal c ≠ 0 := (ENNReal.ofReal_pos.mpr hc).ne'
  have hct : ENNReal.ofReal c ≠ ∞ := ENNReal.ofReal_ne_top
  calc
    _ ≤ P {ω | ENNReal.ofReal (r ^ s) < (ENNReal.ofReal c)⁻¹ * X ω} := by
      apply measure_mono
      intro ω hω
      simp only [Set.mem_ofPred_eq] at hω ⊢
      apply (ENNReal.mul_lt_mul_iff_left hc0 hct).1
      rw [mul_comm ((ENNReal.ofReal c)⁻¹ * X ω) (ENNReal.ofReal c), ← mul_assoc,
        ENNReal.mul_inv_cancel hc0 hct, one_mul]
      simpa only [ENNReal.ofReal_mul hc.le, mul_comm] using hω
    _ ≤ _ := measure_power_threshold_le_of_optimized_moment_prefactor P _ r ξ Q s e A
      hr hξ hs hX hmoment

end HarmonicBalls
