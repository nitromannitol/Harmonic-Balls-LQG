import HarmonicBalls.Proofs.Potential.LQGClockLocalizedTimeSplit

/-! # Inserted localized increments

The actual inserted density increment splits into a recentered annular
increment and two inner time occupations on a common field event.
-/

open MeasureTheory MarkovProcess Set
open scoped ENNReal NNReal

namespace HarmonicBalls

/-- The localized increment of the inserted circle-average densities is
bounded by its recentered annular increment and its two inner occupations. -/
theorem ae_inserted_localized_increment_le_annulus_add_inner_time
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (γ α : ℝ) :
    ∀ᵐ ω ∂P, ∀ (b : ContinuousPath ℂ) (ε δ : ℝ), 0 < ε → ε ≤ 1/2 →
      let μ := Measure.map (fun t => b t)
        (Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1)))
      ENNReal.ofReal |∫ z, {z : ℂ | ‖z‖ ≤ δ ∧ ‖z‖ ≤ 1/2}.indicator
        (fun z => (ε/2)^(γ^2/2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (ε/2) z) -
          ε^(γ^2/2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z)) z ∂μ| ≤
      ENNReal.ofReal |∫ z, {z : ℂ | ε ≤ ‖z‖ ∧ ‖z‖ ≤ δ ∧ ‖z‖ ≤ 1/2}.indicator
        (fun z => (ε/2)^(γ^2/2) * Real.exp (γ *
          (hcirc ω (ε/2) z - hcirc ω 1 0 - α * Real.log (max (ε/2) ‖z‖))) -
          ε^(γ^2/2) * Real.exp (γ *
          (hcirc ω ε z - hcirc ω 1 0 - α * Real.log (max ε ‖z‖)))) z ∂μ| +
      (∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal
        ({z : ℂ | ‖z‖ < ε}.indicator (fun z => (ε/2)^(γ^2/2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (ε/2) z)) (b s.toNNReal))) +
      ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal
        ({z : ℂ | ‖z‖ < ε}.indicator (fun z => ε^(γ^2/2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z)) (b s.toNNReal)) := by
  obtain ⟨H, hHc, _, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  have hcont : ∀ᵐ ω ∂P, ∀ r, 0 < r → Continuous (hcirc ω r) := by
    filter_upwards [hHae] with ω hω r hr
    rw [← funext (hω r)]
    exact hHc ω r hr
  filter_upwards [hcont, ae_recentered_inserted_circle_average hh α] with ω hc hr b ε δ hε hεhalf
  have hF (r : ℝ) (hr0 : 0 < r) : Continuous (fun z => r^(γ^2/2) * Real.exp (γ *
      LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) r z)) := by
    have heq : (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) r z) =
        fun z => hcirc ω r z - hcirc ω 1 0 - α * Real.log (max r ‖z‖) := by
      funext z
      exact (hr r z hr0).symm
    have hcircins : Continuous (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) r z) := by
      rw [heq]
      exact ((hc r hr0).sub continuous_const).sub (continuous_const.mul
        ((continuous_const.max continuous_norm).log (fun _ => (lt_max_of_lt_left hr0).ne')))
    exact continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hcircins))
  have hF0 (r : ℝ) (hr0 : 0 < r) (z : ℂ) : 0 ≤ r^(γ^2/2) * Real.exp (γ *
      LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) r z) :=
    mul_nonneg (Real.rpow_nonneg hr0.le _) (Real.exp_pos _).le
  have hs := ofReal_abs_localized_increment_le_annulus_add_inner_time b ε δ hεhalf
    (fun z => (ε/2)^(γ^2/2) * Real.exp (γ *
      LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (ε/2) z))
    (fun z => ε^(γ^2/2) * Real.exp (γ *
      LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z))
    (hF (ε/2) (half_pos hε)) (hF ε hε) (hF0 (ε/2) (half_pos hε)) (hF0 ε hε)
  simp_rw [hr (ε/2) _ (half_pos hε), hr ε _ hε]
  exact hs

end HarmonicBalls
