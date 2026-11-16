import HarmonicBalls.Proofs.Potential.GreenOccupationCharacterization

/-! # Occupation measures at exterior starting points

For the first exit from an open set, the killed occupation measure vanishes
when the starting point is outside the set.
-/

open MeasureTheory Set Filter MarkovProcess HarmonicBalls HarmonicBalls.Section6
open scoped ENNReal

namespace HarmonicBalls.GreenOccupation

/-- A planar Brownian motion started outside a set exits at time zero. -/
theorem ae_exitTime_eq_zero_of_not_mem {D : Set ℂ} {x : ℂ} (hx : x ∉ D) :
    ∀ᵐ p ∂planarBrownianMotion x, ContinuousPath.exitTime D p = 0 := by
  filter_upwards [ae_planarBrownianMotion_eval_zero x] with p hp
  apply le_antisymm _ bot_le
  have h := ContinuousPath.exitTime_le_of_notMem D p 0 (by simpa [hp] using hx)
  simpa using h

/-- The killed occupation measure is zero for a starting point outside the open set. -/
theorem occupationMeasure_eq_zero_of_not_mem {D : Set ℂ} (hD : IsOpen D)
    {x : ℂ} (hx : x ∉ D) : occupationMeasure D hD x = 0 := by
  apply Measure.ext
  intro A hA
  rw [← lintegral_indicator_one hA]
  change (∫⁻ y, A.indicator (fun _ => (1 : ℝ≥0∞)) y ∂occupationMeasure D hD x) = _
  rw [lintegral_occupationMeasure hD x (measurable_const.indicator hA)]
  simp only [Measure.coe_zero, Pi.zero_apply]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [ae_exitTime_eq_zero_of_not_mem hx] with p hp
  simp [hp]

/-- The Brownian occupation measure equals twice the Green density for every
starting point, including the boundary, with the zero extension of the kernel. -/
theorem occupationMeasure_eq_greenMeasure_all {D : Set ℂ} (hD : IsSmoothBoundedOpen D)
    (x : ℂ) : occupationMeasure D (GreenGeneral.isOpen_of_isSmoothBoundedOpen hD) x =
      greenMeasure D x := by
  by_cases hx : x ∈ D
  · exact occupationMeasure_eq_greenMeasure hD hx
  · rw [occupationMeasure_eq_zero_of_not_mem _ hx, greenMeasure]
    simp [greenFunction, hx]

end HarmonicBalls.GreenOccupation
