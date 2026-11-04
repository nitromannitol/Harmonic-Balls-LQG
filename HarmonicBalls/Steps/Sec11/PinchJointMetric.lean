import HarmonicBalls.Steps.Sec11.ProperMetricDyadic
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap

/-! # Joint measurability of random metric evaluations -/

namespace HarmonicBalls

open MeasureTheory

/-- A pointwise measurable family of Euclidean length metrics is jointly
measurable in the realization and both spatial arguments. -/
theorem measurable_euclideanLengthMetric_pair
    {Ω : Type*} [MeasurableSpace Ω] {D : Ω → ℂ → ℂ → ℝ}
    (hD : ∀ x y, Measurable fun ω => D ω x y)
    (hmetric : ∀ ω, IsEuclideanLengthMetric (D ω)) :
    Measurable fun p : Ω × (ℂ × ℂ) => D p.1 p.2.1 p.2.2 := by
  let F : Ω → C(ℂ × ℂ, ℝ) := fun ω => ⟨fun p => D ω p.1 p.2, (hmetric ω).continuous_pair⟩
  have hF : Measurable F := ContinuousMap.measurable_iff_eval.mpr fun p => hD p.1 p.2
  exact continuous_eval.measurable.comp ((hF.comp measurable_fst).prodMk measurable_snd)

/-- Evaluations of a random length metric at two points translated by the same
moving center are jointly measurable. -/
theorem measurable_euclideanLengthMetric_translate
    {Ω : Type*} [MeasurableSpace Ω] {D : Ω → ℂ → ℂ → ℝ}
    (hD : ∀ x y, Measurable fun ω => D ω x y)
    (hmetric : ∀ ω, IsEuclideanLengthMetric (D ω)) (x y : ℂ) :
    Measurable fun p : Ω × ℂ => D p.1 (x + p.2) (y + p.2) := by
  have hm : Measurable (fun p : Ω × ℂ => (p.1, (x + p.2, y + p.2))) :=
    measurable_fst.prodMk ((measurable_const.add measurable_snd).prodMk
      (measurable_const.add measurable_snd))
  exact (measurable_euclideanLengthMetric_pair hD hmetric).comp hm

#print axioms measurable_euclideanLengthMetric_pair
#print axioms measurable_euclideanLengthMetric_translate

end HarmonicBalls
