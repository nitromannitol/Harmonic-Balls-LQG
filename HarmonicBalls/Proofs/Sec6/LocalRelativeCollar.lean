import HarmonicBalls.Proofs.Sec6.RelativeCollarScaling

/-! # Locality of relative collar events -/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set
open scoped ENNReal

/-- A relative collar at unit scale with width at most one depends only on the
measure inside the open ball of radius seven. -/
theorem relativeCollarFailure_restrict_ball (μ : Measure ℂ) {η : ℝ}
    (hη : η ≤ 1) (d : ℝ≥0∞) :
    RelativeCollarFailure (μ.restrict (ball 0 7)) 1 η d ↔
      RelativeCollarFailure μ 1 η d := by
  have hmain : annulus (0 : ℂ) (3*1) (5*1) ⊆ ball 0 7 := by
    intro x hx
    have hx' : x ∈ ball (0 : ℂ) (5*1) := hx.1
    exact Metric.mem_ball.mpr (lt_trans (Metric.mem_ball.mp hx') (by norm_num))
  have houter : annulus (0 : ℂ) (3*1-η*1) (5*1+η*1) ⊆ ball 0 7 := by
    intro x hx
    have hx' : x ∈ ball (0 : ℂ) (5*1+η*1) := hx.1
    exact Metric.mem_ball.mpr (lt_of_lt_of_le (Metric.mem_ball.mp hx') (by linarith))
  unfold RelativeCollarFailure
  rw [Measure.restrict_apply' measurableSet_ball, Measure.restrict_apply' measurableSet_ball,
    Set.inter_eq_left.mpr hmain, Set.inter_eq_left.mpr (Set.Subset.trans sdiff_subset houter)]

/-- Restriction of measures to a fixed measurable set is measurable. -/
theorem measurable_measure_restrict (A : Set ℂ) (hA : MeasurableSet A) :
    Measurable (fun μ : Measure ℂ => μ.restrict A) := by
  apply Measure.measurable_of_measurable_coe
  intro B hB
  simp only [Measure.restrict_apply hB]
  exact Measure.measurable_coe (hB.inter hA)

end HarmonicBalls.Section6
