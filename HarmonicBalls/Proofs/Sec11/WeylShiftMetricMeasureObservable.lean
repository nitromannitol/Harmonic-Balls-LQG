import HarmonicBalls.Proofs.Sec11.CanonicalMetricMeasureObservable
import HarmonicBalls.Proofs.Sec11.PinchRootedKernel
import HarmonicBalls.Steps.Sec11.SingularWeylBumpInverse

/-! # The metric-measure observable after a Weyl shift

The shifted metric modification is an explicit hypothesis. The metric-field
axioms used below are staged and await source review.
-/

namespace HarmonicBalls

open MeasureTheory
open scoped ENNReal

/-- A simultaneous pointwise-measurable modification of the Weyl-shifted
metric determines the canonical shifted metric-measure observable. -/
theorem exists_canonicalWeylShiftObservable_of_metric_modification
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {D D' : Ω → ℂ → ℂ → ℝ} {μ : Ω → Measure ℂ} {f : ℂ → ℝ}
    (haxioms : LQGMetricFieldAxioms P γ ξ α hC hcirc)
    (hgff : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (hα : α < lqgQ γ) (hD : IsLQGMetricOfField P γ ξ α hC D)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ) (hξ : 0 ≤ ξ)
    (hf : Continuous f) (hcompact : HasCompactSupport f) (hneg : ∀ x, f x ≤ 0)
    (hD' : ∀ x y, Measurable fun ω => D' ω x y)
    (hEq : ∀ᵐ ω ∂P, D' ω = fun x y => (weylScaling (D ω) ξ f x y).toReal) :
    ∃ Y : Ω → Measure ℂ × {d : ℂ → ℂ → ℝ // IsEuclideanLengthMetric d},
      AEMeasurable Y P ∧ ∀ᵐ ω ∂P,
        (Y ω).1 = (μ ω).withDensity (fun x => ENNReal.ofReal (Real.exp (γ * f x))) ∧
        (Y ω).2.1 = fun x y => (weylScaling (D ω) ξ f x y).toReal := by
  have hm : ∀ᵐ ω ∂P, IsEuclideanLengthMetric
      (fun x y => (weylScaling (D ω) ξ f x y).toReal) := by
    filter_upwards [ae_singularField_weylBump_identities_of_metricFieldAxioms
      P γ ξ α hC hcirc D haxioms hgff hγ hγ₂ hα hD hξ] with ω hω
    exact (hω f hf hcompact hneg).1
  have hw : Measurable (fun x => ENNReal.ofReal (Real.exp (γ * f x))) :=
    (Real.continuous_exp.comp (continuous_const.mul hf)).measurable.ennreal_ofReal
  have hmeasure : AEMeasurable
      (fun ω => (μ ω).withDensity (fun x => ENNReal.ofReal (Real.exp (γ * f x)))) P :=
    (measurable_measure_withDensity _ hw).comp_aemeasurable (hgff.aemeasurable_lqgMeasure hμ)
  exact exists_canonicalMetricMeasureObservable hD' hEq hm hmeasure

#print axioms exists_canonicalWeylShiftObservable_of_metric_modification

end HarmonicBalls
