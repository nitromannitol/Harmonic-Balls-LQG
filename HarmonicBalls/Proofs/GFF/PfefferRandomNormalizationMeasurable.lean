import HarmonicBalls.Proposed.PfefferMetricScaling

/-! # Measurability of random-shift normalizations

Joint measurability of a random shift gives measurability of its circle averages
and of the positive-radius Pfeffer normalizations of a whole-plane GFF.
-/

namespace HarmonicBalls

open MeasureTheory Set

/-- Joint measurability gives measurability of each circle average. -/
theorem measurable_pfefferCircleAverage {Ω : Type*} [MeasurableSpace Ω]
    {f : Ω → ℂ → ℝ} (hf : Measurable (Function.uncurry f)) (r : ℝ) (z : ℂ) :
    Measurable (fun ω => pfefferCircleAverage (f ω) r z) := by
  have hm : Measurable (fun p : Ω × ℝ =>
      f p.1 (z + (r : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I))) := by
    exact hf.comp (measurable_fst.prodMk (by fun_prop))
  have hi := (hm.stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Ioc 0 (2 * Real.pi)))).const_smul (2 * Real.pi)⁻¹
  convert hi.measurable using 1
  funext ω
  simp only [pfefferCircleAverage, intervalIntegral.integral_of_le Real.two_pi_pos.le]
  rfl

/-- Joint measurability of the shift gives measurable positive-radius normalizations. -/
theorem IsWholePlaneGFF.measurable_pfefferNormalization_random_shift
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hgff : IsWholePlaneGFF P hC hcirc) (ξ : ℝ) (f : Ω → ℂ → ℝ)
    (hf : Measurable (Function.uncurry f)) (c : ℝ → ℝ)
    {r : ℝ} (hr : 0 < r) :
    Measurable (pfefferNormalization ξ hcirc f c r) := by
  unfold pfefferNormalization
  exact (((((hgff.measurable_circle r 0 hr).add
    (measurable_pfefferCircleAverage hf r 0)).const_mul ξ).neg.exp).const_mul _).ennreal_ofReal

/-- Positive-radius random-shift normalizations are almost everywhere measurable. -/
theorem IsWholePlaneGFF.aemeasurable_pfefferNormalization_random_shift
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hgff : IsWholePlaneGFF P hC hcirc) (ξ : ℝ) (f : Ω → ℂ → ℝ)
    (hf : Measurable (Function.uncurry f)) (c : ℝ → ℝ)
    {r : ℝ} (hr : 0 < r) :
    AEMeasurable (pfefferNormalization ξ hcirc f c r) P :=
  (hgff.measurable_pfefferNormalization_random_shift ξ f hf c hr).aemeasurable

/-- Pointwise measurable continuous shifts also give measurable normalizations. -/
theorem IsWholePlaneGFF.aemeasurable_pfefferNormalization_continuous_shift
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hgff : IsWholePlaneGFF P hC hcirc) (ξ : ℝ) (f : Ω → ℂ → ℝ)
    (hfcont : ∀ ω, Continuous (f ω)) (hfmeas : ∀ z, Measurable (fun ω => f ω z))
    (c : ℝ → ℝ) {r : ℝ} (hr : 0 < r) :
    AEMeasurable (pfefferNormalization ξ hcirc f c r) P := by
  have hf : Measurable (Function.uncurry f) := by
    exact (measurable_uncurry_of_continuous_of_measurable hfcont hfmeas).comp measurable_swap
  exact hgff.aemeasurable_pfefferNormalization_random_shift ξ f hf c hr

end HarmonicBalls
