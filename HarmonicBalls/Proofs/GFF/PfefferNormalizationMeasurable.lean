import HarmonicBalls.Proposed.PfefferMetricScaling

/-! # Measurability of deterministic-shift normalizations

The positive-radius Pfeffer normalizations of a whole-plane GFF and its
fixed deterministic shifts are measurable.
-/

namespace HarmonicBalls

open MeasureTheory

/-- A deterministic shift preserves measurability of the normalization. -/
theorem IsWholePlaneGFF.measurable_pfefferNormalization_const_shift
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hgff : IsWholePlaneGFF P hC hcirc) (ξ : ℝ) (g : ℂ → ℝ) (c : ℝ → ℝ)
    {r : ℝ} (hr : 0 < r) :
    Measurable (pfefferNormalization ξ hcirc (fun _ => g) c r) := by
  unfold pfefferNormalization
  exact (((((hgff.measurable_circle r 0 hr).add_const _).const_mul ξ).neg.exp).const_mul _).ennreal_ofReal

/-- The pure whole-plane field has measurable positive-radius normalizations. -/
theorem IsWholePlaneGFF.aemeasurable_pfefferNormalization_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hgff : IsWholePlaneGFF P hC hcirc) (ξ : ℝ) (c : ℝ → ℝ)
    {r : ℝ} (hr : 0 < r) :
    AEMeasurable (pfefferNormalization ξ hcirc (fun _ _ => 0) c r) P :=
  (hgff.measurable_pfefferNormalization_const_shift ξ (fun _ => 0) c hr).aemeasurable

/-- The deterministic quadratic shift has measurable positive-radius normalizations. -/
theorem IsWholePlaneGFF.aemeasurable_pfefferNormalization_quadratic
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hgff : IsWholePlaneGFF P hC hcirc) (ξ : ℝ) (c : ℝ → ℝ)
    {r : ℝ} (hr : 0 < r) :
    AEMeasurable (pfefferNormalization ξ hcirc (fun _ z => ‖z‖ ^ 2) c r) P :=
  (hgff.measurable_pfefferNormalization_const_shift ξ (fun z => ‖z‖ ^ 2) c hr).aemeasurable

end HarmonicBalls
