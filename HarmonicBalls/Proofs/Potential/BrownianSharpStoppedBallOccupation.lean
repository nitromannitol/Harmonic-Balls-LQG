import HarmonicBalls.Proofs.Potential.BrownianSharpLogOccupationAllHorizon
import HarmonicBalls.Proofs.Sec6.CompactHittingStopping

/-! # Sharp stopped Brownian occupation

The occupation measure up to a bounded-domain exit satisfies the sharp logarithmic ball bound.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Set
open scoped NNReal ENNReal

namespace HarmonicBalls

/-- Spatial occupation before the extended exit time of a continuous path. -/
noncomputable def stoppedBrownianOccupation (D : Set ℂ) (b : ContinuousPath ℂ) : Measure ℂ :=
  Measure.map (fun t : ℝ => b t.toNNReal)
    (volume.restrict {t : ℝ | 0 < t ∧
      ((t.toNNReal : ℝ≥0) : ℝ≥0∞) < ContinuousPath.exitTime D b})

/-- The stopped occupation of a finite-exit path is bounded by its finite-horizon occupation. -/
theorem stoppedBrownianOccupation_ball_le (D : Set ℂ) (b : ContinuousPath ℂ)
    (hfin : ContinuousPath.exitTime D b ≠ ∞) (z : ℂ) (r : ℝ) :
    stoppedBrownianOccupation D b (Metric.ball z r) ≤
      volume {t : ℝ | t ∈ Icc (0 : ℝ) (ContinuousPath.exitTime D b).toReal ∧
        ‖b t.toNNReal - z‖ < r} := by
  have hm : Measurable (fun t : ℝ => b t.toNNReal) :=
    b.continuous.measurable.comp continuous_real_toNNReal.measurable
  rw [stoppedBrownianOccupation, Measure.map_apply hm Metric.isOpen_ball.measurableSet,
    Measure.restrict_apply (hm Metric.isOpen_ball.measurableSet)]
  apply measure_mono
  intro t ht
  have hs := ContinuousPath.survivalSet_ne_top (ContinuousPath.exitTime D b) hfin
  have ht' : t ∈ {t : ℝ | ((t.toNNReal : ℝ≥0) : ℝ≥0∞) <
      ContinuousPath.exitTime D b} ∩ Ioi 0 := ⟨ht.2.2, ht.2.1⟩
  rw [hs] at ht'
  exact ⟨⟨ht'.1.le, ht'.2.le⟩, by simpa [Metric.mem_ball, dist_eq_norm] using ht.1⟩

/-- The sharp occupation bound holds almost surely until exit from any bounded domain. -/
theorem planarBrownianMotion_stopped_uniform_ball_occupation_log (x : ℂ) {D : Set ℂ}
    (hD : Bornology.IsBounded D) :
    ∀ᵐ b ∂(planarBrownianMotion x),
      ∃ C : ℝ, 0 < C ∧ ∃ r₀ : ℝ, 0 < r₀ ∧
        ∀ (z : ℂ) (r : ℝ), 0 < r → r < r₀ →
          stoppedBrownianOccupation D b (Metric.ball z r) ≤
            ENNReal.ofReal (C * r ^ 2 * (Real.log (1 / r)) ^ 2) := by
  filter_upwards [planarBrownianMotion_uniform_ball_occupation_log_all_horizons x,
    Section6.ae_planarBrownian_exitTime_bounded_lt_top x hD] with b hb hfin
  obtain ⟨C, hC, r₀, hr₀, hbound⟩ := hb (ContinuousPath.exitTime D b).toReal ENNReal.toReal_nonneg
  refine ⟨C, hC, r₀, hr₀, fun z r hr hrsmall => ?_⟩
  exact (stoppedBrownianOccupation_ball_le D b hfin.ne z r).trans (hbound z r hr hrsmall)

end HarmonicBalls
