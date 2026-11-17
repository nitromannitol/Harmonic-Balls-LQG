import HarmonicBalls.Proofs.Potential.BrownianSharpStoppedBallOccupation
import HarmonicBalls.Proofs.Potential.BrownianAllHorizonBallOccupation

/-! # Atomless stopped Brownian occupation

The extended-exit occupation measure has zero mass at every point on one
almost-sure event for all bounded domains.
-/

open MeasureTheory MarkovProcess Set Filter
open scoped NNReal ENNReal Topology

namespace HarmonicBalls

/-- For each starting point, one event gives atomless stopped occupation for all bounded sets. -/
theorem planarBrownianMotion_stoppedOccupation_nullSingleton_all_domains (x : ℂ) :
    ∀ᵐ b ∂(planarBrownianMotion x), ∀ D : Set ℂ, Bornology.IsBounded D →
      NullSingletonClass (stoppedBrownianOccupation D b) := by
  have hballs : ∀ᵐ b ∂(planarBrownianMotion x), ∀ n : ℕ,
      ContinuousPath.exitTime (Metric.ball x (n : ℝ)) b < ∞ := by
    simp only [ae_all_iff]
    exact fun n => Section6.ae_planarBrownianMotion_exitTime_ball_lt_top x n
  filter_upwards [planarBrownianMotion_uniform_ball_occupation_all_horizons x,
    hballs] with b hb hball D hD
  obtain ⟨R, hR⟩ := hD.subset_ball x
  obtain ⟨n, hn⟩ := exists_nat_ge R
  have hsub : D ⊆ Metric.ball x (n : ℝ) := hR.trans (Metric.ball_subset_ball hn)
  have hfin : ContinuousPath.exitTime D b < ∞ :=
    lt_of_le_of_lt (ContinuousPath.exitTime_mono hsub b) (hball n)
  obtain ⟨C, hC, hbound⟩ := hb (ContinuousPath.exitTime D b).toReal 1 (by norm_num) (by norm_num)
  constructor
  intro z
  have hlim : Tendsto (fun k : ℕ => ENNReal.ofReal (C * (1 / 2 : ℝ) ^ k)) atTop (𝓝 0) := by
    have hp : Tendsto (fun k : ℕ => (1 / 2 : ℝ) ^ k) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    simpa using ENNReal.tendsto_ofReal (tendsto_const_nhds.mul hp)
  apply le_antisymm ?_ bot_le
  apply ge_of_tendsto hlim
  filter_upwards [] with k
  have hr : 0 < (1 / 2 : ℝ) ^ k := by positivity
  have hr1 : (1 / 2 : ℝ) ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  calc
    stoppedBrownianOccupation D b {z} ≤ stoppedBrownianOccupation D b (Metric.ball z ((1 / 2 : ℝ) ^ k)) :=
      measure_mono (singleton_subset_iff.mpr (Metric.mem_ball_self hr))
    _ ≤ volume {t : ℝ | t ∈ Icc (0 : ℝ) (ContinuousPath.exitTime D b).toReal ∧
        ‖b t.toNNReal - z‖ < (1 / 2 : ℝ) ^ k} :=
      stoppedBrownianOccupation_ball_le D b hfin.ne z _
    _ ≤ ENNReal.ofReal (C * (1 / 2 : ℝ) ^ k) := by
      simpa using hbound z _ hr hr1

/-- The singleton assertion applies to the strict extended-exit time window. -/
theorem planarBrownianMotion_stoppedOccupation_singleton_time_all_domains (x : ℂ) :
    ∀ᵐ b ∂(planarBrownianMotion x), ∀ D : Set ℂ, Bornology.IsBounded D → ∀ z : ℂ,
      volume {t : ℝ | b t.toNNReal = z ∧ 0 < t ∧
        ((t.toNNReal : ℝ≥0) : ℝ≥0∞) < ContinuousPath.exitTime D b} = 0 := by
  filter_upwards [planarBrownianMotion_stoppedOccupation_nullSingleton_all_domains x] with b hb D hD z
  have hm : Measurable (fun t : ℝ => b t.toNNReal) :=
    b.continuous.measurable.comp continuous_real_toNNReal.measurable
  have h := (hb D hD).measure_singleton z
  rw [stoppedBrownianOccupation, Measure.map_apply hm (measurableSet_singleton z),
    Measure.restrict_apply (hm (measurableSet_singleton z))] at h
  exact h

end HarmonicBalls
