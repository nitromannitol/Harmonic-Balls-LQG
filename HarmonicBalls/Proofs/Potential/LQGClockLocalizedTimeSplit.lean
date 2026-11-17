import HarmonicBalls.Proofs.Potential.LQGClockInnerOccupationTransfer
import HarmonicBalls.Proofs.Potential.LQGClockInnerUniformTime

/-! # Localized increments and inner time occupations

A localized density increment is bounded by an annular increment and two
nonnegative time occupations on the inner ball.
-/

open MeasureTheory MarkovProcess Set
open scoped ENNReal NNReal

namespace HarmonicBalls

private theorem integrable_continuous_unit_occupation (b : ContinuousPath ℂ)
    (f : ℂ → ℝ) (hf : Continuous f) :
    Integrable f (Measure.map (fun t => b t)
      (Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1)))) := by
  let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  have hν : Integrable (fun t => f (b t)) ν := by
    apply (integrable_map_measure (hf.comp b.continuous).aestronglyMeasurable
      continuous_real_toNNReal.measurable.aemeasurable).2
    exact (hf.comp (b.continuous.comp continuous_real_toNNReal)).continuousOn.integrableOn_Icc
  exact (integrable_map_measure hf.aestronglyMeasurable b.continuous.measurable.aemeasurable).2 hν

/-- The absolute localized increment is controlled by the annular increment
and the two inner occupations, with the inner boundary included in the annulus. -/
theorem ofReal_abs_localized_increment_le_annulus_add_inner_time
    (b : ContinuousPath ℂ) (ε δ : ℝ) (hε : ε ≤ 1/2)
    (f g : ℂ → ℝ) (hf : Continuous f) (hg : Continuous g)
    (hf0 : ∀ z, 0 ≤ f z) (hg0 : ∀ z, 0 ≤ g z) :
    let μ := Measure.map (fun t => b t)
      (Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1)))
    ENNReal.ofReal |∫ z, {z : ℂ | ‖z‖ ≤ δ ∧ ‖z‖ ≤ 1/2}.indicator
        (fun z => f z - g z) z ∂μ| ≤
      ENNReal.ofReal |∫ z, {z : ℂ | ε ≤ ‖z‖ ∧ ‖z‖ ≤ δ ∧ ‖z‖ ≤ 1/2}.indicator
        (fun z => f z - g z) z ∂μ| +
      (∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal
        ({z : ℂ | ‖z‖ < ε}.indicator f (b s.toNNReal))) +
      ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal
        ({z : ℂ | ‖z‖ < ε}.indicator g (b s.toNNReal)) := by
  let μ := Measure.map (fun t => b t)
    (Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1)))
  have h := abs_integral_closedBall_sub_le_annulus_add_inner μ ε δ f g
    (integrable_continuous_unit_occupation b f hf)
    (integrable_continuous_unit_occupation b g hg) hf0 hg0
  have hfi : 0 ≤ ∫ z, {z : ℂ | ‖z‖ < ε}.indicator f z ∂μ := by
    apply integral_nonneg
    intro z
    by_cases hz : ‖z‖ < ε
    · simpa [hz] using hf0 z
    · simp [hz]
  have hgi : 0 ≤ ∫ z, {z : ℂ | ‖z‖ < ε}.indicator g z ∂μ := by
    apply integral_nonneg
    intro z
    by_cases hz : ‖z‖ < ε
    · simpa [hz] using hg0 z
    · simp [hz]
  have hfT := (inner_indicator_integrable_and_lintegral_eq b f hf hf0 hε).2
  have hgT := (inner_indicator_integrable_and_lintegral_eq b g hg hg0 hε).2
  change ENNReal.ofReal |∫ z, {z : ℂ | ‖z‖ ≤ δ ∧ ‖z‖ ≤ 1/2}.indicator
    (fun z => f z - g z) z ∂μ| ≤ _
  rw [hfT, hgT, ← ENNReal.ofReal_add (abs_nonneg _), ← ENNReal.ofReal_add (add_nonneg (abs_nonneg _) hfi)]
  · exact ENNReal.ofReal_le_ofReal h
  · exact hgi
  · exact hfi

end HarmonicBalls
