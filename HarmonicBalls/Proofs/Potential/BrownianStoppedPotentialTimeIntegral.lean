import HarmonicBalls.Proofs.Potential.BrownianStoppedLogPotentialContinuity

/-! # Stopped Brownian potential as a time integral

The Newtonian potential of stopped occupation equals the integral over the strict
extended-exit time window, and this time integral is continuous in its center.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Set
open scoped NNReal ENNReal

namespace HarmonicBalls

/-- Integrability and integration against stopped occupation transfer to the original
strict time window. -/
theorem stoppedBrownianOccupation_time_integral (D : Set ℂ) (b : ContinuousPath ℂ)
    (z : ℂ) (h : Integrable (newtonKernel z) (stoppedBrownianOccupation D b)) :
    IntegrableOn (fun t : ℝ => newtonKernel z (b t.toNNReal))
      {t : ℝ | 0 < t ∧ ((t.toNNReal : ℝ≥0) : ℝ≥0∞) < ContinuousPath.exitTime D b} ∧
    (∫ t in {t : ℝ | 0 < t ∧ ((t.toNNReal : ℝ≥0) : ℝ≥0∞) <
        ContinuousPath.exitTime D b}, newtonKernel z (b t.toNNReal)) =
      ∫ w, newtonKernel z w ∂(stoppedBrownianOccupation D b) := by
  have hm : Measurable (fun t : ℝ => b t.toNNReal) :=
    b.continuous.measurable.comp continuous_real_toNNReal.measurable
  have hs := h.aestronglyMeasurable
  change AEStronglyMeasurable (newtonKernel z) (Measure.map (fun t : ℝ => b t.toNNReal)
    (volume.restrict {t : ℝ | 0 < t ∧ ((t.toNNReal : ℝ≥0) : ℝ≥0∞) <
      ContinuousPath.exitTime D b})) at hs
  have hi := (integrable_map_measure hs hm.aemeasurable).1 h
  refine ⟨hi, ?_⟩
  exact (integral_map hm.aemeasurable hs).symm

/-- For every bounded domain, the stopped Newtonian time integral is integrable
at every center and depends continuously on the center, on one full-mass event. -/
theorem planarBrownianMotion_stopped_newton_time_integral_continuous (x : ℂ) :
    ∀ᵐ b ∂(planarBrownianMotion x), ∀ D : Set ℂ, Bornology.IsBounded D →
      (∀ z : ℂ, IntegrableOn (fun t : ℝ => newtonKernel z (b t.toNNReal))
        {t : ℝ | 0 < t ∧ ((t.toNNReal : ℝ≥0) : ℝ≥0∞) < ContinuousPath.exitTime D b}) ∧
      (∀ z : ℂ, (∫ t in {t : ℝ | 0 < t ∧ ((t.toNNReal : ℝ≥0) : ℝ≥0∞) <
        ContinuousPath.exitTime D b}, newtonKernel z (b t.toNNReal)) =
        ∫ w, newtonKernel z w ∂(stoppedBrownianOccupation D b)) ∧
      Continuous (fun z : ℂ => ∫ t in {t : ℝ | 0 < t ∧
        ((t.toNNReal : ℝ≥0) : ℝ≥0∞) < ContinuousPath.exitTime D b},
        newtonKernel z (b t.toNNReal)) := by
  filter_upwards [planarBrownianMotion_stopped_newton_potential_continuous x] with b hb D hD
  obtain ⟨hi, hc⟩ := hb D hD
  have ht := fun z => stoppedBrownianOccupation_time_integral D b z (hi z)
  refine ⟨fun z => (ht z).1, fun z => (ht z).2, ?_⟩
  have heq : (fun z : ℂ => ∫ t in {t : ℝ | 0 < t ∧
      ((t.toNNReal : ℝ≥0) : ℝ≥0∞) < ContinuousPath.exitTime D b},
      newtonKernel z (b t.toNNReal)) =
      (fun z => ∫ w, newtonKernel z w ∂(stoppedBrownianOccupation D b)) :=
    funext (fun z => (ht z).2)
  rw [heq]
  exact hc

end HarmonicBalls
