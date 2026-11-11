import HarmonicBalls.Steps.Sec11.ExplicitNormalizedDiameter

/-! # Comparison of deterministic normalization constants

A first-moment bound for a diameter normalized by one positive finite scale
constant transfers to another scale when their ratio is uniformly bounded.
-/

namespace HarmonicBalls
open MeasureTheory
open scoped ENNReal

/-- Replacing a positive finite normalization constant changes a normalized
nonnegative variable by the ratio of the constants. -/
theorem normalized_diameter_change_scale
    (F B c d : ℝ≥0∞) (hc0 : c ≠ 0) (hctop : c ≠ ∞)
    (hd0 : d ≠ 0) (hdtop : d ≠ ∞) :
    F / (d * B) = (c / d) * (F / (c * B)) := by
  simp only [div_eq_mul_inv]
  rw [ENNReal.mul_inv (a := d) (b := B) (Or.inl hd0) (Or.inl hdtop),
    ENNReal.mul_inv (a := c) (b := B) (Or.inl hc0) (Or.inl hctop)]
  symm
  calc
    _ = (c * c⁻¹) * (F * (d⁻¹ * B⁻¹)) := by ac_rfl
    _ = _ := by rw [ENNReal.mul_inv_cancel hc0 hctop, one_mul]

/-- A bounded ratio of deterministic scale constants transfers a normalized
first-moment bound, without imposing measurability on the sample functions. -/
theorem lintegral_normalized_diameter_le_of_scale_ratio
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (F B : Ω → ℝ≥0∞) (c d A C : ℝ≥0∞)
    (hc0 : c ≠ 0) (hctop : c ≠ ∞) (hd0 : d ≠ 0) (hdtop : d ≠ ∞)
    (hAtop : A ≠ ∞)
    (hscale : c / d ≤ A) (hmoment : (∫⁻ ω, F ω / (c * B ω) ∂P) ≤ C) :
    (∫⁻ ω, F ω / (d * B ω) ∂P) ≤ A * C := by
  calc
    _ = ∫⁻ ω, (c / d) * (F ω / (c * B ω)) ∂P := by
      apply lintegral_congr
      intro ω
      exact normalized_diameter_change_scale _ _ _ _ hc0 hctop hd0 hdtop
    _ ≤ ∫⁻ ω, A * (F ω / (c * B ω)) ∂P := by
      apply lintegral_mono
      intro ω
      change (c / d) * (F ω / (c * B ω)) ≤ A * (F ω / (c * B ω))
      gcongr
    _ = A * (∫⁻ ω, F ω / (c * B ω) ∂P) := lintegral_const_mul' A _ hAtop
    _ ≤ A * C := by gcongr


end HarmonicBalls
