import HarmonicBalls.Proofs.Potential.LQGClockInsertedLocalizedOccupation

/-! # Increments of inserted cutoff occupations

Consecutive cutoff occupations satisfy the localized annular and inner bound.
-/

open MeasureTheory MarkovProcess Set
open scoped ENNReal NNReal

namespace HarmonicBalls

private theorem integrable_continuous_unit_path (b : ContinuousPath ℂ)
    (f : ℂ → ℝ) (hf : Continuous f) :
    Integrable f (Measure.map (fun t => b t)
      (Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1)))) := by
  have ht : Integrable (fun s : ℝ => f (b s.toNNReal))
      (volume.restrict (Icc (0 : ℝ) 1)) :=
    (hf.comp (b.continuous.comp continuous_real_toNNReal)).integrableOn_Icc
  have hν : Integrable (fun t : ℝ≥0 => f (b t))
      (Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))) :=
    (integrable_map_measure (hf.comp b.continuous).aestronglyMeasurable
      continuous_real_toNNReal.measurable.aemeasurable).2 ht
  exact (integrable_map_measure hf.aestronglyMeasurable b.continuous.measurable.aemeasurable).2 hν

/-- On a common field event, the difference of two inserted cutoff occupations
is bounded by the corresponding annular increment and inner occupations. -/
theorem ae_inserted_closedBall_occupation_increment_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (γ α : ℝ) :
    ∀ᵐ ω ∂P, ∀ (b : ContinuousPath ℂ) (ε δ : ℝ), 0 < ε → ε ≤ 1/2 →
      let μ := Measure.map (fun t => b t)
        (Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1)))
      ENNReal.ofReal |(∫ z, {z : ℂ | ‖z‖ ≤ δ ∧ ‖z‖ ≤ 1/2}.indicator
        (fun z => (ε/2)^(γ^2/2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (ε/2) z)) z ∂μ) -
        ∫ z, {z : ℂ | ‖z‖ ≤ δ ∧ ‖z‖ ≤ 1/2}.indicator
        (fun z => ε^(γ^2/2) * Real.exp (γ *
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
  filter_upwards [hcont, ae_recentered_inserted_circle_average hh α,
    ae_inserted_localized_increment_le_annulus_add_inner_time hh γ α] with ω hc hr hs b ε δ hε hhalf
  let μ := Measure.map (fun t => b t)
    (Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1)))
  let E : Set ℂ := {z | ‖z‖ ≤ δ ∧ ‖z‖ ≤ 1/2}
  let D (r : ℝ) (z : ℂ) := r^(γ^2/2) * Real.exp (γ *
    LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) r z)
  have hE : MeasurableSet E := (measurableSet_le measurable_norm measurable_const).inter
    (measurableSet_le measurable_norm measurable_const)
  have hD (r : ℝ) (hpos : 0 < r) : Continuous (D r) := by
    have heq : (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) r z) =
        fun z => hcirc ω r z - hcirc ω 1 0 - α * Real.log (max r ‖z‖) := by
      funext z
      exact (hr r z hpos).symm
    have hi : Continuous (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) r z) := by
      rw [heq]
      exact ((hc r hpos).sub continuous_const).sub (continuous_const.mul
        ((continuous_const.max continuous_norm).log (fun _ => (lt_max_of_lt_left hpos).ne')))
    exact continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hi))
  have hint (r : ℝ) (hpos : 0 < r) : Integrable (E.indicator (D r)) μ :=
    (integrable_continuous_unit_path b (D r) (hD r hpos)).indicator hE
  have heq : E.indicator (fun z => D (ε/2) z - D ε z) =
      fun z => E.indicator (D (ε/2)) z - E.indicator (D ε) z := by
    funext z
    by_cases hz : z ∈ E <;> simp [hz]
  have h := hs b ε δ hε hhalf
  change ENNReal.ofReal |(∫ z, E.indicator (D (ε/2)) z ∂μ) -
    ∫ z, E.indicator (D ε) z ∂μ| ≤ _
  rw [← integral_sub (hint (ε/2) (half_pos hε)) (hint ε hε), ← heq]
  exact h

end HarmonicBalls
