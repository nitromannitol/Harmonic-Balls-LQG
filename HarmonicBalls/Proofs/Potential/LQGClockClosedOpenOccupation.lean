import HarmonicBalls.Proofs.Potential.LQGClockInnerOccupationTransfer

/-! # Closed and open cutoff occupations

A larger open cutoff controls the occupation of a closed cutoff.
-/

open MeasureTheory MarkovProcess Set
open scoped ENNReal NNReal

namespace HarmonicBalls

/-- A closed-cutoff occupation is bounded by the time occupation in any larger
open ball, without an assumption on the cutoff boundary. -/
theorem closed_unit_occupation_le_lintegral_inner_time
    (b : ContinuousPath ℂ) (f : ℂ → ℝ) (hf : Continuous f) (hf0 : ∀ z, 0 ≤ f z)
    {δ ρ : ℝ} (hδρ : δ < ρ) (hρ : ρ ≤ 1/2) :
    ENNReal.ofReal |∫ z, {z : ℂ | ‖z‖ ≤ δ ∧ ‖z‖ ≤ 1/2}.indicator f z
      ∂(Measure.map (fun t => b t) (Measure.map Real.toNNReal
        (volume.restrict (Icc (0 : ℝ) 1))))| ≤
    ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal
      ({z : ℂ | ‖z‖ < ρ}.indicator f (b s.toNNReal)) := by
  let μ := Measure.map (fun t => b t) (Measure.map Real.toNNReal
    (volume.restrict (Icc (0 : ℝ) 1)))
  let E : Set ℂ := {z | ‖z‖ ≤ δ ∧ ‖z‖ ≤ 1/2}
  let U : Set ℂ := {z | ‖z‖ < ρ}
  have hE : MeasurableSet E := (measurableSet_le measurable_norm measurable_const).inter
    (measurableSet_le measurable_norm measurable_const)
  have ht : Integrable (fun s : ℝ => f (b s.toNNReal))
      (volume.restrict (Icc (0 : ℝ) 1)) :=
    (hf.comp (b.continuous.comp continuous_real_toNNReal)).integrableOn_Icc
  have hν : Integrable (fun t : ℝ≥0 => f (b t))
      (Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))) :=
    (integrable_map_measure (hf.comp b.continuous).aestronglyMeasurable
      continuous_real_toNNReal.measurable.aemeasurable).2 ht
  have hfint : Integrable f μ :=
    (integrable_map_measure hf.aestronglyMeasurable b.continuous.measurable.aemeasurable).2 hν
  have hEi : Integrable (E.indicator f) μ := hfint.indicator hE
  obtain ⟨hUi, hUeq⟩ := inner_indicator_integrable_and_lintegral_eq b f hf hf0 hρ
  have hE0 : 0 ≤ ∫ z, E.indicator f z ∂μ := by
    apply integral_nonneg
    intro z
    by_cases hz : z ∈ E
    · simpa [hz] using hf0 z
    · simp [hz]
  have hle : (∫ z, E.indicator f z ∂μ) ≤ ∫ z, U.indicator f z ∂μ := by
    apply integral_mono hEi hUi
    intro z
    exact Set.indicator_le_indicator_of_subset (fun _ hz => lt_of_le_of_lt hz.1 hδρ) hf0 z
  change ENNReal.ofReal |∫ z, E.indicator f z ∂μ| ≤ _
  rw [abs_of_nonneg hE0, hUeq]
  exact ENNReal.ofReal_le_ofReal hle

end HarmonicBalls
