import HarmonicBalls.Proofs.Sec6.PositiveRecurrence

/-!
# Measurability of potential ratios

A Green-potential ratio in the fine-support argument is the infimum over a circle divided
by the supremum over an annulus. Separable parameter spaces and continuity of each potential
reduce these extrema to countably many points. This file isolates that measurability step;
it does not assert joint measurability or continuity of the LQG Green potential itself.
-/

namespace HarmonicBalls.Section6

open MeasureTheory
open scoped ENNReal

/-- Infimum over a separable space of continuous nonnegative potentials is measurable in the
other parameter. -/
theorem measurable_inf_of_continuous_potential
    {Θ S : Type*} [MeasurableSpace Θ] [TopologicalSpace S] [TopologicalSpace.SeparableSpace S]
    (q : Θ → S → ℝ) (hq : ∀ s, Measurable fun θ => q θ s)
    (hc : ∀ θ, Continuous fun s => q θ s) :
    Measurable fun θ => ⨅ s, ENNReal.ofReal (q θ s) := by
  convert measurable_iInf_of_upperSemicontinuous
    (fun s => ENNReal.measurable_ofReal.comp (hq s))
    (fun θ => (ENNReal.continuous_ofReal.comp (hc θ)).upperSemicontinuous) using 1
  ext θ
  simp only [iInf_apply, Function.comp_apply]

/-- Supremum over a separable space of continuous nonnegative potentials is measurable in the
other parameter. -/
theorem measurable_sup_of_continuous_potential
    {Θ S : Type*} [MeasurableSpace Θ] [TopologicalSpace S] [TopologicalSpace.SeparableSpace S]
    (q : Θ → S → ℝ) (hq : ∀ s, Measurable fun θ => q θ s)
    (hc : ∀ θ, Continuous fun s => q θ s) :
    Measurable fun θ => ⨆ s, ENNReal.ofReal (q θ s) := by
  convert measurable_iSup_of_lowerSemicontinuous
    (fun s => ENNReal.measurable_ofReal.comp (hq s))
    (fun θ => (ENNReal.continuous_ofReal.comp (hc θ)).lowerSemicontinuous) using 1
  ext θ
  simp only [iSup_apply, Function.comp_apply]

/-- A ratio of an infimum and a supremum of continuous potentials is measurable. -/
theorem measurable_potential_extrema_ratio
    {Θ S T : Type*} [MeasurableSpace Θ]
    [TopologicalSpace S] [TopologicalSpace.SeparableSpace S] [TopologicalSpace T] [TopologicalSpace.SeparableSpace T]
    (qS : Θ → S → ℝ) (qT : Θ → T → ℝ)
    (hS : ∀ s, Measurable fun θ => qS θ s) (hSc : ∀ θ, Continuous fun s => qS θ s)
    (hT : ∀ t, Measurable fun θ => qT θ t) (hTc : ∀ θ, Continuous fun t => qT θ t) :
    Measurable fun θ =>
      ((⨅ s, ENNReal.ofReal (qS θ s)) / (⨆ t, ENNReal.ofReal (qT θ t))).toReal := by
  exact ENNReal.measurable_toReal.comp
    ((measurable_inf_of_continuous_potential qS hS hSc).div
      (measurable_sup_of_continuous_potential qT hT hTc))

end HarmonicBalls.Section6
