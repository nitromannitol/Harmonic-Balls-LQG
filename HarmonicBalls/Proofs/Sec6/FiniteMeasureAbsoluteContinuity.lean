import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-! Uniform absolute continuity of a finite measure, used for rooted laws. -/

namespace HarmonicBalls.Section6

open MeasureTheory Set
open scoped ENNReal

/-- Absolute continuity of a finite measure is uniform over measurable sets. -/
theorem finiteMeasure_uniform_absoluteContinuity
    {α : Type*} [MeasurableSpace α] (μ ν : Measure α)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμν : μ ≪ ν)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ δ : ℝ≥0∞, 0 < δ ∧ ∀ s, MeasurableSet s → ν s ≤ δ → μ s ≤ ε := by
  let f : α → ℝ := fun x => (μ.rnDeriv ν x).toReal
  have hf : Integrable f ν := by
    simpa only [IntegrableOn, Measure.restrict_univ] using
      (Measure.integrableOn_toReal_rnDeriv (μ := μ) (ν := ν)
        (s := Set.univ) (measure_ne_top μ Set.univ))
  obtain ⟨δ, hδ, hbound⟩ := (memLp_one_iff_integrable.mpr hf).eLpNorm_indicator_le
    (by simp) (by simp) hε
  refine ⟨δ, hδ, fun s hs hνs => ?_⟩
  have hnorm : eLpNorm (s.indicator f) 1 ν = μ s := by
    rw [eLpNorm_indicator_eq_eLpNorm_restrict hs,
      eLpNorm_one_eq_lintegral_enorm hf.aestronglyMeasurable.restrict,
      ← Measure.setLIntegral_rnDeriv hμν s]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_of_ae (μ.rnDeriv_lt_top ν)] with x hx
    simp only [f, Real.enorm_eq_ofReal ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hx.ne]
  rw [← hnorm]
  exact hbound s hs hνs

end HarmonicBalls.Section6
