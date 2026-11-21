import HarmonicBalls.Proofs.Potential.LQGClockInnerStoppedIncrement
import HarmonicBalls.Proofs.Potential.LQGClockExitIncrementUniformIntegrability
import HarmonicBalls.Proofs.Potential.LQGClockOfLocallyUniformLimit

/-! # Expected exit times of the inserted clock from regional increment bounds

Split the plane into the inner disc `‖z‖ < δ`, the annulus `δ ≤ ‖z‖ ≤ 1/2` and the exterior
`1/2 < ‖z‖`. For the clocks stopped at the exit time from a smooth bounded domain and capped
at time one, the inner increments have a summable bound uniform over the start whenever
`0 < γ * α` and `γ ^ 2 / 2 < 2 - γ * α`. Given summable bounds of the same kind for the
annular and the exterior increments, uniform over starts in the domain, the exit-time clock
approximations are uniformly integrable for almost every field, and every LQG clock that is
almost surely a time-change clock has finite expected exit time equal to the limit of the
expected Green integrals of the approximating measures.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Real Set Filter Topology
open scoped ENNReal NNReal
namespace HarmonicBalls

/-- An interval integral along a path up to a time at most one is the integral against the
occupation measure of the path up to that time. -/
theorem intervalIntegral_path_eq_integral_occupation (F : ℂ → ℝ) (hF : Measurable F)
    (b : ContinuousPath ℂ) {u : ℝ≥0} (hu : u ≤ 1) :
    (∫ s in (0 : ℝ)..(u : ℝ), F (b s.toNNReal)) =
      ∫ z, F z ∂(Measure.map (fun t => b t)
        ((Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))).restrict (Iic u))) := by
  rw [integral_map b.continuous.measurable.aemeasurable hF.aestronglyMeasurable]
  rw [Measure.restrict_map continuous_real_toNNReal.measurable measurableSet_Iic]
  rw [Measure.restrict_restrict (continuous_real_toNNReal.measurable measurableSet_Iic)]
  rw [integral_map (f := fun t : ℝ≥0 => F (b t)) continuous_real_toNNReal.measurable.aemeasurable
    (hF.comp b.continuous.measurable).aestronglyMeasurable]
  rw [intervalIntegral.integral_of_le u.coe_nonneg, ← integral_Icc_eq_integral_Ioc]
  congr 1
  congr 1
  ext s
  simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_Icc]
  constructor
  · rintro ⟨h0, hT⟩
    exact ⟨(Real.toNNReal_le_iff_le_coe).mpr hT, h0, le_trans hT (by exact_mod_cast hu)⟩
  · rintro ⟨hs, h0, _⟩
    exact ⟨h0, (Real.toNNReal_le_iff_le_coe).mp hs⟩

end HarmonicBalls
